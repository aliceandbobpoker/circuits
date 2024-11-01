pragma circom 2.0.5;
include "cards.circom"; 

component main{ public [pubKey_x, pubKey_y]} = zero_encrypt(52, 13, 16, 1, 13);