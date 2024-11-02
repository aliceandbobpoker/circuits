pragma circom 2.0.5;

include "cards.circom";
// 6 is number of bits to encode card
component main{public [c2x, decryptx]} = reveal(5, 6);