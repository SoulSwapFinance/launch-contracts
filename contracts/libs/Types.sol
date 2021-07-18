// SPDX-License-Identifier: MIT

pragma solidity ^0.6.12;

library Types {
    struct Stream {
        uint256 deposit;
        uint256 ratePerSecond;
        uint256 remainingBalance;
        uint256 startTime;
        uint256 stopTime;
        address recipient;
        address sender;
        address tokenAddress;
        bool isEntity;
    }

    struct Pack {
        uint level; // classification bronze-platinum
        uint rate; // soul per fantom
        uint unitCost; // ftm per pack
        uint deposited; // deposited ftm
        uint limit; // max packs
        uint supply; // soul in contract
        bool isEntity; // pack exists
    }
}