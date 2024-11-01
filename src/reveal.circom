pragma circom 2.0.5;
include "cards.circom"; 

component main {public [card, pubKey_x, pubKey_y]} = encrypt_card();