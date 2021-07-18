// SPDX-License-Identifier: MIT

pragma solidity ^0.6.12;

import "@openzeppelin/contracts/utils/ReentrancyGuard.sol";
import '@openzeppelin/contracts/token/ERC20/IERC20.sol';
import '@openzeppelin/contracts/access/Ownable.sol';
import "./libs/CarefulMath.sol";
import "./libs/Types.sol";

contract SoulStream is ReentrancyGuard, CarefulMath, Ownable {

    bool public isWithdrawable;
    uint public nextStream = 1;

    // stream objects, by their ids.
    mapping(uint => Types.Stream) private streams;

    /*** MODIFIERS ***/

    /**
     * @dev Throws if the caller is not the sender of the recipient of the stream.
     */
    modifier onlySenderOrRecipient(uint sid) {
        require(
            msg.sender == streams[sid].sender || msg.sender == streams[sid].recipient,
            "caller is not the sender or the recipient of the stream"
        );
        _;
    }

    /**
     * @dev Throws if the provided id does not point to a valid stream.
     */
    modifier streamExists(uint sid) {
        require(streams[sid].isEntity, "stream does not exist");
        _;
    }

    //  EVENTS //

    event CreateStream(
        uint256 indexed streamId,
        address indexed sender,
        address indexed recipient,
        uint256 deposit,
        address tokenAddress,
        uint256 startTime,
        uint256 stopTime
    );

        event WithdrawFromStream(
        uint256 indexed streamId,
        address indexed recipient,
        uint256 amount
    );

    // PUBLIC VIEWS //

    function getStream(uint sid)
        external
        view
        streamExists(sid)
        returns (
            address sender,
            address recipient,
            uint deposit,
            address tokenAddress,
            uint startTime,
            uint stopTime,
            uint remainingBalance,
            uint ratePerSecond
        )
    {
        sender = streams[sid].sender;
        recipient = streams[sid].recipient;
        deposit = streams[sid].deposit;
        tokenAddress = streams[sid].tokenAddress;
        startTime = streams[sid].startTime;
        stopTime = streams[sid].stopTime;
        remainingBalance = streams[sid].remainingBalance;
        ratePerSecond = streams[sid].ratePerSecond;
    }

    function deltaOf(uint sid) public view streamExists(sid) returns (uint delta) {
        Types.Stream memory stream = streams[sid];
        if (block.timestamp <= stream.startTime) return 0;
        if (block.timestamp < stream.stopTime) return block.timestamp - stream.startTime;
        return stream.stopTime - stream.startTime;
    }

    struct BalanceOfLocalVars {
        MathError mathErr;
        uint recipientBalance;
        uint withdrawalAmount;
        uint senderBalance;
    }

    function balanceOf(uint sid, address who) public view streamExists(sid) returns (uint balance) {
        Types.Stream memory stream = streams[sid];
        BalanceOfLocalVars memory vars;

        uint delta = deltaOf(sid);
        (vars.mathErr, vars.recipientBalance) = mulUInt(delta, stream.ratePerSecond);
        require(vars.mathErr == MathError.NO_ERROR, "recipient balance calculation error");

        /*
         * If the stream `balance` does not equal `deposit`, it means there have been withdrawals.
         * We have to subtract the total amount withdrawn from the amount of money that has been
         * streamed until now.
         */
        if (stream.deposit > stream.remainingBalance) {
            (vars.mathErr, vars.withdrawalAmount) = subUInt(stream.deposit, stream.remainingBalance);
            assert(vars.mathErr == MathError.NO_ERROR);
            (vars.mathErr, vars.recipientBalance) = subUInt(vars.recipientBalance, vars.withdrawalAmount);
            /* `withdrawalAmount` cannot and should not be bigger than `recipientBalance`. */
            assert(vars.mathErr == MathError.NO_ERROR);
        }

        if (who == stream.recipient) return vars.recipientBalance;
        if (who == stream.sender) {
            (vars.mathErr, vars.senderBalance) = subUInt(stream.remainingBalance, vars.recipientBalance);
            /* `recipientBalance` cannot and should not be bigger than `remainingBalance`. */
            assert(vars.mathErr == MathError.NO_ERROR);
            return vars.senderBalance;
        }
        return 0;
    }

    /*** Public Effects & Interactions Functions ***/

    struct CreateStreamLocalVars {
        MathError mathErr;
        uint duration;
        uint ratePerSecond;
    }

    /**
     * @notice Creates a new stream funded by `msg.sender` and paid towards `recipient`.
     * @param recipient The address towards which the money is streamed.
     * @param deposit The amount of money to be streamed.
     * @param tokenAddress The ERC20 token to use as streaming currency.
     * @return The uint id of the newly created stream.
     */
    function createStream(address recipient, uint deposit, address tokenAddress, uint lag) public returns (uint) {
        require(recipient != address(0x00), "stream to the zero address");
        require(recipient != address(this), "stream to the contract itself");
        require(deposit > 0, "deposit is zero");

        uint startTime = lag + block.timestamp - 4448000; // 20M (UINT) - 180 DAYS
        uint stopTime = lag + block.timestamp + 180 days; // 6 MONTHS

        CreateStreamLocalVars memory vars;
        (vars.mathErr, vars.duration) = subUInt(stopTime, startTime);
        /* `subUInt` can only return MathError.INTEGER_UNDERFLOW but we know `stopTime` is higher than `startTime`. */
        assert(vars.mathErr == MathError.NO_ERROR);

        /* Without this, the rate per second would be zero. */
        require(deposit >= vars.duration, "deposit smaller than time delta");

        /* This condition avoids dealing with remainders */
        require(deposit % vars.duration == 0, "deposit not multiple of time delta");

        (vars.mathErr, vars.ratePerSecond) = divUInt(deposit, vars.duration);
        /* `divUInt` can only return MathError.DIVISION_BY_ZERO but we know `duration` is not zero. */
        assert(vars.mathErr == MathError.NO_ERROR);

        /* Create and store the stream object. */
        uint sid = nextStream;
        streams[sid] = Types.Stream({
            remainingBalance: deposit,
            deposit: deposit,
            isEntity: true,
            ratePerSecond: vars.ratePerSecond,
            recipient: recipient,
            sender: msg.sender,
            startTime: startTime,
            stopTime: stopTime,
            tokenAddress: tokenAddress
        });

        /* Increment the next stream id. */
        (vars.mathErr, nextStream) = addUInt(nextStream, uint(1));
        require(vars.mathErr == MathError.NO_ERROR, "next stream id calculation error");

        require(IERC20(tokenAddress).transferFrom(msg.sender, address(this), deposit), "token transfer failure");
        emit CreateStream(sid, msg.sender, recipient, deposit, tokenAddress, startTime, stopTime);
        return sid;
    }

    struct WithdrawFromStreamLocalVars {
        MathError mathErr;
    }

    /**
     * @notice Withdraws from the contract to the recipient's account.
     * @dev Throws if the id does not point to a valid stream.
     *  Throws if the caller is not the sender or the recipient of the stream.
     *  Throws if the amount exceeds the available balance.
     *  Throws if there is a token transfer failure.
     * @param sid The id of the stream to withdraw tokens from.
     * @param amount The amount of tokens to withdraw.
     * @return bool true=success, otherwise false.
     */
    function withdrawFromStream(uint sid, uint amount)
        external
        nonReentrant
        streamExists(sid)
        onlySenderOrRecipient(sid)
        returns (bool)
    {
        require(isWithdrawable, "not withdrawable");
        require(amount > 0, "amount is zero");
        Types.Stream memory stream = streams[sid];
        WithdrawFromStreamLocalVars memory vars;

        uint balance = balanceOf(sid, stream.recipient);
        require(balance >= amount, "amount exceeds the available balance");

        (vars.mathErr, streams[sid].remainingBalance) = subUInt(stream.remainingBalance, amount);
        /**
         * `subUInt` can only return MathError.INTEGER_UNDERFLOW but we know that `remainingBalance` is at least
         * as big as `amount`.
         */
        assert(vars.mathErr == MathError.NO_ERROR);

        if (streams[sid].remainingBalance == 0) delete streams[sid];

        require(IERC20(stream.tokenAddress).transfer(stream.recipient, amount), "token transfer failure");
        emit WithdrawFromStream(sid, stream.recipient, amount);
    }

    /**
     * @notice Cancels the stream and transfers the tokens back on a pro rata basis.
     * @dev Throws if the id does not point to a valid stream.
     *  Throws if the caller is not the sender or the recipient of the stream.
     *  Throws if there is a token transfer failure.
     * @param sid The id of the stream to cancel.
     * @return bool true=success, otherwise false.
     */
    function cancelStream(uint sid)
        external
        nonReentrant
        streamExists(sid)
        onlySenderOrRecipient(sid)
        returns (bool)
    {
        require(isWithdrawable, "not withdrawable");
        Types.Stream memory stream = streams[sid];
        uint senderBalance = balanceOf(sid, stream.sender);
        uint recipientBalance = balanceOf(sid, stream.recipient);

        delete streams[sid];

        IERC20 token = IERC20(stream.tokenAddress);
        if (recipientBalance > 0)
            require(token.transfer(stream.recipient, recipientBalance), "recipient token transfer failure");
        if (senderBalance > 0) require(token.transfer(stream.sender, senderBalance), "sender token transfer failure");

        emit CancelStream(sid, stream.sender, stream.recipient, senderBalance, recipientBalance);
    }

    event CancelStream(
        uint indexed streamId,
        address indexed sender,
        address indexed recipient,
        uint senderBalance,
        uint recipientBalance
    );

    function toggleWithdrawable() external onlyOwner {
        require(!isWithdrawable, "turnOnWithdrawals: withdrawals already enabled");
        isWithdrawable = true;
    }
}
