pragma circom 2.0.5;

include "../node_modules/circomlib/circuits/escalarmulany.circom";
include "../node_modules/circomlib/circuits/babyjub.circom";
include "../node_modules/circomlib/circuits/bitify.circom";
include "../node_modules/circomlib/circuits/comparators.circom";
include "../node_modules/circomlib/circuits/compconstant.circom";
include "../node_modules/circomlib/circuits/poseidon.circom";

template decrypt() {
    signal input c1_x;
    signal input c1_y;
    signal input privKey;

    signal output pub_x;
    signal output pub_y;
    signal output out_x;
    signal output out_y;

    component check = BabyCheck();
    check.x <== c1_x;
    check.y <== c1_y;

    component pubKey = BabyPbk();
    pubKey.in <== privKey;

    // Convert the private key to bits
    component privKeyBits = Num2Bits(253);
    privKeyBits.in <== privKey;
    
    // c1 ** x
    component c1x = EscalarMulAny(253);
    for (var i = 0; i < 253; i ++) {
        c1x.e[i] <== privKeyBits.out[i];
    }
    c1x.p[0] <== c1_x;
    c1x.p[1] <== c1_y;

    pub_x <== pubKey.Ax;
    pub_y <== pubKey.Ay;
    out_x <== c1x.out[0];
    out_y <== c1x.out[1];
}

template reveal(n, m) {
    signal input card;
    signal input c2x;
    signal input c2y;
    signal input decryptx[n];
    signal input decrypty[n];
    signal output flags;
    signal output out_x;
    signal flagsBits[n + 2 + m];
    component adders[n - 1];
    component num2bits[n + 2];
    component compressors[n + 2];

    var i;
    adders[0] = BabyAdd();
    adders[0].x1 <== decryptx[0];
    adders[0].y1 <== decrypty[0];
    for (i = 0; i < n - 1; i ++) {
        adders[i].x2 <== decryptx[i + 1];
        adders[i].y2 <== decrypty[i + 1];
        if (i < n - 2) {
            adders[i + 1] = BabyAdd();
            adders[i + 1].x1 <== adders[i].xout;
            adders[i + 1].y1 <== adders[i].yout;
        }
    }
    component subtract = BabyAdd();
    subtract.x1 <== 0 - adders[n - 2].xout;
    subtract.y1 <== adders[n - 2].yout;
    subtract.x2 <== c2x;
    subtract.y2 <== c2y;

    out_x <== subtract.xout;

    component checks[n+1];

    for (i = 0; i < n; i ++) {
        checks[i] = BabyCheck();
        checks[i].x <== decryptx[i];
        checks[i].y <== decrypty[i];

        num2bits[i] = Num2Bits(254);
        num2bits[i].in <== decrypty[i];
        compressors[i] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
        compressors[i].in <== num2bits[i].out;
        flagsBits[i] <== compressors[i].out;
    }
    checks[n]= BabyCheck();
    checks[n].x <== c2x;
    checks[n].y <== c2y;

    num2bits[n] = Num2Bits(254);
    num2bits[n].in <== c2y;
    compressors[n] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
    compressors[n].in <== num2bits[n].out;
    flagsBits[n] <== compressors[n].out;

    num2bits[n + 1] = Num2Bits(254);
    num2bits[n + 1].in <== subtract.yout;
    compressors[n + 1] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
    compressors[n + 1].in <== num2bits[n + 1].out;
    flagsBits[n + 1] <== compressors[n + 1].out;

    var BASE8[2] = [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];
    component cardMult = EscalarMulFix(m, BASE8);
    component cardBits = Num2Bits(m);
    cardBits.in <== card;

    component flagsNum = Bits2Num(n + 2 + m);
    for (i = 0; i < m; i ++) {
        cardMult.e[i] <== cardBits.out[i];
        flagsBits[n + 2 + i] <== cardBits.out[i];
    }

    cardMult.out[0] === subtract.xout;
    cardMult.out[1] === subtract.yout;

    flagsNum.in <== flagsBits;
    flags <== flagsNum.out;
}

template point_sum(n_points) {
    signal input x[n_points];
    signal input y[n_points];

    signal output flags;
    signal output compressed[n_points];
    signal output out_x;
    signal output out_y;

    signal interm_flags[n_points];
    signal intermediate_x[n_points];
    signal intermediate_y[n_points];
    var k;

    component comps[n_points];
    component yBits[n_points];
    component adders[n_points - 1];
    component babyChecks[n_points];

    yBits[0] = Num2Bits(254);
    yBits[0].in <== y[0];

    comps[0] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
    comps[0].in <== yBits[0].out;

    compressed[0] <== x[0];
    interm_flags[0] <== comps[0].out;

    babyChecks[0] = BabyCheck();
    babyChecks[0].x <== x[0];
    babyChecks[0].y <== y[0];

    intermediate_x[0] <== x[0];
    intermediate_y[0] <== y[0];
    
    for (k = 1; k < n_points; k++) {
        adders[k - 1] = BabyAdd();
        adders[k - 1].x1 <== x[k];
        adders[k - 1].y1 <== y[k];
        adders[k - 1].x2 <== intermediate_x[k - 1];
        adders[k - 1].y2 <== intermediate_y[k - 1];
        intermediate_x[k] <== adders[k - 1].xout;
        intermediate_y[k] <== adders[k - 1].yout;

        yBits[k] = Num2Bits(254);
        yBits[k].in <== y[k];

        comps[k] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
        comps[k].in <== yBits[k].out;

        compressed[k] <== x[k];
        interm_flags[k] <== comps[k].out;

        babyChecks[k] = BabyCheck();
        babyChecks[k].x <== x[k];
        babyChecks[k].y <== y[k];
    }
    component flagsNum = Bits2Num(n_points);
    flagsNum.in <== interm_flags;

    flags <== flagsNum.out;
    out_x <== intermediate_x[n_points - 1];
    out_y <== intermediate_y[n_points - 1];
}

template BitElementMulAnyArr(m) {
    signal input sel[m];
    signal input dblIn[2];
    signal input addIn[m][2];
    signal output dblOut[2];
    signal output addOut[m][2];

    component doubler = MontgomeryDouble();

    component adders[m];
    component selectors[m];

    dblIn[0] ==> doubler.in[0];
    dblIn[1] ==> doubler.in[1];

    var j;
    for (j=0; j < m; j ++){
        selectors[j] = Multiplexor2();
        sel[j] ==> selectors[j].sel;

        adders[j] = MontgomeryAdd();

        doubler.out[0] ==> adders[j].in1[0];
        doubler.out[1] ==> adders[j].in1[1];
        addIn[j][0] ==> adders[j].in2[0];
        addIn[j][1] ==> adders[j].in2[1];
        addIn[j][0] ==> selectors[j].in[0][0];
        addIn[j][1] ==> selectors[j].in[0][1];
        adders[j].out[0] ==> selectors[j].in[1][0];
        adders[j].out[1] ==> selectors[j].in[1][1];

        selectors[j].out[0] ==> addOut[j][0];
        selectors[j].out[1] ==> addOut[j][1];
    }
    doubler.out[0] ==> dblOut[0];
    doubler.out[1] ==> dblOut[1];
}


template SegmentMulAnyArr(n, m) {
    signal input e[m][n];
    signal input p[2];
    signal output out[m][2];
    signal output dbl[2];

    component bits[n-1];
    component e2m = Edwards2Montgomery();

    p[0] ==> e2m.in[0];
    p[1] ==> e2m.in[1];

    var i;
    var j;
    bits[0] = BitElementMulAnyArr(m);
    e2m.out[0] ==> bits[0].dblIn[0];
    e2m.out[1] ==> bits[0].dblIn[1];

    for (j=0; j < m; j ++) {
        e2m.out[0] ==> bits[0].addIn[j][0];
        e2m.out[1] ==> bits[0].addIn[j][1];
        e[j][1] ==> bits[0].sel[j];
    }

    for (i=1; i<n-1; i++) {
        bits[i] = BitElementMulAnyArr(m);

        bits[i-1].dblOut[0] ==> bits[i].dblIn[0];
        bits[i-1].dblOut[1] ==> bits[i].dblIn[1];
        for (j=0; j < m; j ++) {
            bits[i-1].addOut[j][0] ==> bits[i].addIn[j][0];
            bits[i-1].addOut[j][1] ==> bits[i].addIn[j][1];
            e[j][i+1] ==> bits[i].sel[j];
        }
    }
    bits[n-2].dblOut[0] ==> dbl[0];
    bits[n-2].dblOut[1] ==> dbl[1];

    component m2es[m];
    component eadders[m];
    component lastSels[m];

    for (j=0; j < m; j ++) {
        m2es[j] = Montgomery2Edwards();
        bits[n-2].addOut[j][0] ==> m2es[j].in[0];
        bits[n-2].addOut[j][1] ==> m2es[j].in[1];

        eadders[j] = BabyAdd();
        m2es[j].out[0] ==> eadders[j].x1;
        m2es[j].out[1] ==> eadders[j].y1;
        -p[0] ==> eadders[j].x2;
        p[1] ==> eadders[j].y2;

        lastSels[j] = Multiplexor2();
        e[j][0] ==> lastSels[j].sel;
        eadders[j].xout ==> lastSels[j].in[0][0];
        eadders[j].yout ==> lastSels[j].in[0][1];
        m2es[j].out[0] ==> lastSels[j].in[1][0];
        m2es[j].out[1] ==> lastSels[j].in[1][1];
        lastSels[j].out[0] ==> out[j][0];
        lastSels[j].out[1] ==> out[j][1];
    }
}

template EscalarMulAnyArr(n, m) {
    signal input e[m][n];              // Inputs in binary format
    signal input p[2];              // Point (Twisted format)
    signal output out[m][2];           // Point (Twisted format)

    var nsegments = (n-1)\148 +1;
    var nlastsegment = n - (nsegments-1)*148;

    component segments[nsegments];
    component doublers[nsegments-1];
    component m2e[nsegments-1];
    component adders[m][nsegments-1];
    component zeropoint = IsZero();
    zeropoint.in <== p[0];

    var s;
    var i;
    var nseg;
    var j;


    for (s=0; s<nsegments; s++) {

        nseg = (s < nsegments-1) ? 148 : nlastsegment;

        segments[s] = SegmentMulAnyArr(nseg, m);

        for (j = 0; j < m; j++){
            for (i=0; i<nseg; i++) {
                e[j][s*148+i] ==> segments[s].e[j][i];
            }
        }

        if (s==0) {
        // force G8 point if input point is zero
            segments[s].p[0] <== p[0] + (5299619240641551281634865583518297030282874472190772894086521144482721001553 - p[0])*zeropoint.out;
            segments[s].p[1] <== p[1] + (16950150798460657717958625567821834550301663161624707787222815936182638968203 - p[1])*zeropoint.out;
        } else {
            doublers[s-1] = MontgomeryDouble();
            m2e[s-1] = Montgomery2Edwards();
            segments[s-1].dbl[0] ==> doublers[s-1].in[0];
            segments[s-1].dbl[1] ==> doublers[s-1].in[1];

            doublers[s-1].out[0] ==> m2e[s-1].in[0];
            doublers[s-1].out[1] ==> m2e[s-1].in[1];

            m2e[s-1].out[0] ==> segments[s].p[0];
            m2e[s-1].out[1] ==> segments[s].p[1];
            for (j = 0; j < m; j++){
                adders[j][s-1] = BabyAdd();
                if (s==1) {
                    segments[s-1].out[j][0] ==> adders[j][s-1].x1;
                    segments[s-1].out[j][1] ==> adders[j][s-1].y1;
                } else {
                    adders[j][s-2].xout ==> adders[j][s-1].x1;
                    adders[j][s-2].yout ==> adders[j][s-1].y1;
                }
                segments[s].out[j][0] ==> adders[j][s-1].x2;
                segments[s].out[j][1] ==> adders[j][s-1].y2;
            }
        }
    }

    for (j = 0; j < m; j++) {
        if (nsegments == 1) {
            segments[0].out[j][0]*(1-zeropoint.out) ==> out[j][0];
            segments[0].out[j][1]+(1-segments[0].out[j][1])*zeropoint.out ==> out[j][1];
        } else {
            adders[j][nsegments-2].xout*(1-zeropoint.out) ==> out[j][0];
            adders[j][nsegments-2].yout+(1-adders[j][nsegments-2].yout)*zeropoint.out ==> out[j][1];
        }
    }
}

template compress_ciphertexts(n) {
    signal input c1y[n];
    signal input c2y[n];

    signal output flags;
    signal flagsBits[2 * n];

    component comps1[n];
    component comps2[n];

    component num2bits1[n];
    component num2bits2[n];

    var i;
    for (i = 0; i < n; i ++){
        comps1[i] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
        comps2[i] = CompConstant(10944121435919637611123202872628637544274182200208017171849102093287904247808);
        num2bits1[i] = Num2Bits(254);
        num2bits2[i] = Num2Bits(254);
        num2bits1[i].in <== c1y[i];
        num2bits2[i].in <== c2y[i];
        comps1[i].in <== num2bits1[i].out;
        comps2[i].in <== num2bits2[i].out;

        flagsBits[i] <== comps1[i].out;
        flagsBits[i + n] <== comps2[i].out;
    }
    component flagsNum = Bits2Num(2 * n);
    flagsNum.in <== flagsBits;
    flags <== flagsNum.out;
}

template hash_compressed(n, m1, num1, m2, num2) {
    signal input c1x[n];
    signal input c2x[n];
    signal input flags;
    signal output out;

    signal flattened[2 * n + 1];
    component poseidons[m1];
    component poseidons2[m2];
    component poseidon3 = Poseidon(m2);
    var i;
    var j;
    var k;

    for (k = 0; k < n; k ++) {
        flattened[k] <== c1x[k];
        flattened[k + n] <== c2x[k];
    }
    flattened[2 * n] <== flags;

    for (i = 0; i < m1; i ++ ){
        poseidons[i] = Poseidon(num1);
        for (j = 0; j < num1; j ++){
            poseidons[i].inputs[j] <== flattened[i * num1 + j];
        }
    }

    for (i = 0; i < m2; i ++ ){
        poseidons2[i] = Poseidon(num2);
        for (j = 0; j < num2; j ++){
            poseidons2[i].inputs[j] <== poseidons[i * num2 + j].out;
        }
        poseidon3.inputs[i] <== poseidons2[i].out;
    }
    out <== poseidon3.out;
}

template hash_uncompressed(n, m1, num1, m2, num2) {
    signal input c1x[n];
    signal input c2x[n];
    signal input c1y[n];
    signal input c2y[n];
    signal output out;

    signal flattened[4 * n];
    component poseidons[m1];
    component poseidons2[m2];
    var i;
    var j;
    var k;

    for (k = 0; k < n; k ++) {
        flattened[k] <== c1x[k];
        flattened[k + n] <== c1y[k];
        flattened[k + 2 * n] <== c2x[k];
        flattened[k + 3 * n] <== c2y[k];
    }

    for (i = 0; i < m1; i ++ ){
        var input_length;
        if (i == m1 - 1) {
            input_length = 4 * n - i * num1;
        } else {
            input_length = num1;
        }
        poseidons[i] = Poseidon(input_length);
        for (j = 0; j < input_length; j ++){
            poseidons[i].inputs[j] <== flattened[i * num1 + j];
        }
    }

    for (i = 0; i < m2; i ++){
        var input_length;
        if (i == m2 - 1) {
            input_length = m1 - i * num2;
        } else {
            input_length = num2;
        }
        poseidons2[i] = Poseidon(input_length);
        for (j = 0; j < input_length; j ++){
            poseidons2[i].inputs[j] <== poseidons[i * num2 + j].out;
        }
    }
    if (m2 == 1) {
        out <== poseidons2[0].out;
    } else {
        component poseidon3 = Poseidon(m2);
        for (i = 0; i < m2; i ++){
            poseidon3.inputs[i] <== poseidons2[i].out;
        }
        out <== poseidon3.out;
    }
}


template test_zero_encrypt(n) {
    signal input randomVal[n];
    signal input pubKey_x;
    signal input pubKey_y;
    signal output c1x[n];
    signal output c1y[n];
    signal output c2x[n];
    signal output c2y[n];
    component num2bits[n];
    // component gz[n];
    component yz[n];
    
    var BASE8[2] = [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];

    for (var j = 0; j < n; j ++){
        num2bits[j] = Num2Bits(254);
        num2bits[j].in <== randomVal[j];
        
        yz[j] = EscalarMulAny(253);
        yz[j].p[0] <== pubKey_x;
        yz[j].p[1] <== pubKey_y;

        for (var i = 0; i < 253; i ++) {
            yz[j].e[i] <== num2bits[j].out[i];
        }
    }
    for (var j = 0; j < n; j ++){
        c2x[j] <== yz[j].out[0];
        c2y[j] <== yz[j].out[1];
    }
}

template zero_encrypt(n, m1, num1, m2, num2) {
    signal input randomVal[n];
    signal input pubKey_x;
    signal input pubKey_y;
    signal output out;
    component num2bits[n];
    component gz[n];
    
    var BASE8[2] = [
        5299619240641551281634865583518297030282874472190772894086521144482721001553,
        16950150798460657717958625567821834550301663161624707787222815936182638968203
    ];
    component mulArr = EscalarMulAnyArr(253, n);
    mulArr.p[0] <== pubKey_x;
    mulArr.p[1] <== pubKey_y;

    for (var j = 0; j < n; j ++){
        num2bits[j] = Num2Bits(254);
        num2bits[j].in <== randomVal[j];
        for (var i = 0; i < 253; i ++) {
            mulArr.e[j][i] <== num2bits[j].out[i];
        }
        
        gz[j] = EscalarMulFix(253, BASE8);
        for (var i = 0; i < 253; i ++) {
            gz[j].e[i] <== num2bits[j].out[i];
        }
    }
    component hash = hash_uncompressed(n, m1, num1, m2, num2);

    for (var j = 0; j < n; j ++){
        hash.c1x[j] <== gz[j].out[0];
        hash.c1y[j] <== gz[j].out[1];
        hash.c2x[j] <== mulArr.out[j][0];
        hash.c2y[j] <== mulArr.out[j][1];

    }
    out <== hash.out;
}

template permute2(n) {
    signal input in[n];
    signal input selectors[(1+n)*n/2];
    signal vals[(1+n)*n/2];
    signal valns[(1+n)*n/2];
    signal output out[n];

    for (var i=0; i<n; i++) {
        vals[i] <== in[i];
    }

    var o=0;
    for (var i=n; i>0; i--) {
        var accOut = 0;
        for (var j=0; j<i; j++) {
            if (j<i-1) {
                vals[o+i+j] <== selectors[o+j] * ( vals[o+i-1] - vals[o+j] )    + vals[o+j];
            }
            valns[o+j] <== vals[o+j] * selectors[o+j];
            accOut += valns[o+j];
        }
        out[i-1] <== accOut;
        o = o + i;
    }

}

template permute(n) {
    signal input M[n][n];
    signal input in_c1x[n];
    signal input in_c1y[n];
    signal input in_c2x[n];
    signal input in_c2y[n];
    signal output out_c1x[n];
    signal output out_c1y[n];
    signal output out_c2x[n];
    signal output out_c2y[n];
    var i;
    var j;

    signal intermediate_c1x[n][n];
    signal intermediate_c1y[n][n];
    signal intermediate_c2x[n][n];
    signal intermediate_c2y[n][n];

    for (i = 0; i < n; i ++) {
        var rowSum = 0;
        var colSum = 0;
        for (j = 0; j < n; j ++) {
            (M[i][j] - 1) * M[i][j] === 0;
            rowSum = rowSum + M[i][j];
            colSum = colSum + M[j][i];

            if (j == 0) {
                intermediate_c1x[i][j] <== M[i][j] * in_c1x[j];
            } else {
                intermediate_c1x[i][j] <== intermediate_c1x[i][j - 1] + M[i][j] * in_c1x[j];
            }

            if (j == 0) {
                intermediate_c1y[i][j] <== M[i][j] * in_c1y[j];
            } else {
                intermediate_c1y[i][j] <== intermediate_c1y[i][j - 1] + M[i][j] * in_c1y[j];
            }

            if (j == 0) {
                intermediate_c2x[i][j] <== M[i][j] * in_c2x[j];
            } else {
                intermediate_c2x[i][j] <== intermediate_c2x[i][j - 1] + M[i][j] * in_c2x[j];
            }

            if (j == 0) {
                intermediate_c2y[i][j] <== M[i][j] * in_c2y[j];
            } else {
                intermediate_c2y[i][j] <== intermediate_c2y[i][j - 1] + M[i][j] * in_c2y[j];
            }
        }
        rowSum === 1;
        colSum === 1;
    }

    for (i = 0; i < n; i ++) {
        out_c1x[i] <== intermediate_c1x[i][n - 1];
        out_c1y[i] <== intermediate_c1y[i][n - 1];
        out_c2x[i] <== intermediate_c2x[i][n - 1];
        out_c2y[i] <== intermediate_c2y[i][n - 1];
    }
}

template encrypt_shuffle(n, m1, num1, m2, num2) {
    signal input in_c1x[n];
    signal input in_c1y[n];
    signal input in_c2x[n];
    signal input in_c2y[n];
    signal input M[n][n];
    signal input zeros_c1x[n];
    signal input zeros_c1y[n];
    signal input zeros_c2x[n];
    signal input zeros_c2y[n];
    signal output input_hash;
    signal output zero_hash;
    signal output output_hash;

    signal added_c1x[n];
    signal added_c1y[n];
    signal added_c2x[n];
    signal added_c2y[n];


    component adders_c1[n];
    component adders_c2[n];

    var i;

    component hash_zero = hash_uncompressed(n, m1, num1, m2, num2);
    component hash_input = hash_uncompressed(n, m1, num1, m2, num2);
    component perm = permute(n);
    perm.M <== M;

    for (i = 0; i < n; i ++){
        hash_zero.c1x[i] <== zeros_c1x[i];
        hash_zero.c1y[i] <== zeros_c1y[i];
        hash_zero.c2x[i] <== zeros_c2x[i];
        hash_zero.c2y[i] <== zeros_c2y[i];
        hash_input.c1x[i] <== in_c1x[i];
        hash_input.c1y[i] <== in_c1y[i];
        hash_input.c2x[i] <== in_c2x[i];
        hash_input.c2y[i] <== in_c2y[i];

        adders_c1[i] = BabyAdd();
        adders_c1[i].x1 <== zeros_c1x[i];
        adders_c1[i].y1 <== zeros_c1y[i];
        adders_c1[i].x2 <== in_c1x[i];
        adders_c1[i].y2 <== in_c1y[i];

        adders_c2[i] = BabyAdd();
        adders_c2[i].x1 <== zeros_c2x[i];
        adders_c2[i].y1 <== zeros_c2y[i];
        adders_c2[i].x2 <== in_c2x[i];
        adders_c2[i].y2 <== in_c2y[i];

        perm.in_c1x[i] <== adders_c1[i].xout;
        perm.in_c1y[i] <== adders_c1[i].yout;
        perm.in_c2x[i] <== adders_c2[i].xout;
        perm.in_c2y[i] <== adders_c2[i].yout;
    }

    component hash_output = hash_uncompressed(n, m1, num1, m2, num2);
    for (i = 0; i < n; i ++){
        hash_output.c1x[i] <== perm.out_c1x[i];
        hash_output.c1y[i] <== perm.out_c1y[i];
        hash_output.c2x[i] <== perm.out_c2x[i];
        hash_output.c2y[i] <== perm.out_c2y[i];
    }
    output_hash <== hash_output.out;
    input_hash <== hash_input.out;
    zero_hash <== hash_zero.out;
}
