using SHA

# return a random prime <= 2^KLPT_secret_key_prime_size and = 3 mod 4
function random_secret_prime()
    B = BigInt(floor(p^(1/4)))
    n = rand(1:B)
    while !is_probable_prime(n)
        n = rand(1:B)
    end
    return n
end

function key_gen(global_data::GlobalData)
    a24pk, xP2pk, xQ2pk, xPQ2pk, xP3pk, xQ3pk, xPQ3pk, J3, J2, alpha = FastDoublePath(true, global_data)
    Apk = Montgomery_coeff(a24pk)

    xP3pk_fix, xQ3pk_fix, xPQ3pk_fix = torsion_basis(a24pk, 3, ExponentOfThree)

    n1, n2, n3, n4 = ec_bi_dlog_odd_prime_power(Apk, xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, xP3pk, xQ3pk, xPQ3pk, 3, ExponentOfThree)
    M = [n1 n3; n2 n4]
 
    return Apk, (xP2pk, xQ2pk, xPQ2pk, xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, M, J3, J2, alpha)
end

function commitment(global_data::GlobalData)
    return FastDoublePath(false, global_data)
end

function challenge(A::FqFieldElem, m::String)
    if Is256Hash
        h = sha3_256(string(A) * m)
    else
        h = sha3_512(string(A) * m)
    end

    c = BigInt(0)
    for i in 1:ChallengeByteLength
        c += BigInt(h[i]) << (8*(i-1))
    end

    return c % ChallengeDegree
end

function signing(pk::FqFieldElem, sk, m::String, global_data::GlobalData)
    Apk = pk
    a24pk = A_to_a24(Apk)
    xP2pk, xQ2pk, xPQ2pk, xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, M3pk, I3sk, I2sk, alpha_sk = sk

    # commitment
    a24mid, a24com, xK1, xK2, xP2mid, xQ2mid, xPQmid, xP2com, xQ2com, xPQ2com, Icom = commitment(global_data)
    Acom = Montgomery_coeff(a24com)

    # challenge
    chl = challenge(Acom, m)
    a, b = M3pk * [1, chl]
    a, b, c, d = global_data.E0_data.M44inv_chall * [b, 0, -a, 0]
    alpha = QOrderElem(a, b, c, d)
    Ichl = LeftIdeal(alpha, ChallengeDegree)
    Kchl = ladder3pt(chl, xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, a24pk)
    a24chl, (xP2chl, xQ2chl, xPQ2chl) = three_e_iso(a24pk, Kchl, ExponentOfThree, [xP2pk, xQ2pk, xPQ2pk], StrategiesDim1Three[ExponentOfThree])
    a24chl, (xP2chl, xQ2chl, xPQ2chl) = Montgomery_normalize(a24chl, [xP2chl, xQ2chl, xPQ2chl])
    Achl = Montgomery_coeff(a24chl)

    # find alpha in bar(Icom)IskIcha suitable for the response
    IskIchl = intersection(I2sk, Ichl)
    IskIchl = div(IskIchl * alpha_sk, two_to_e2^2)
    I = involution_product(Icom, IskIchl)
    @assert norm(I) == three_to_e3^5
    alpha, q, found = element_for_response(I, norm(I), ExponentOfTwo)
    @assert found
end

function verify_compact(pk::FqFieldElem, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    Apub = pk
    a24pub = A_to_a24(Apub)

    # decompress the signature
    idx = 1
    Aaux = bytes_to_Fq(sign[idx:idx+SQISIGN2D_Fp2_length-1], global_data.Fp2)
    a24aux = A_to_a24(Aaux)
    idx += SQISIGN2D_Fp2_length
    is_n1_odd = sign[idx] & 1 == 0x00
    is_adjust_sqrt = sign[idx] & 2 == 0x00
    idx += 1
    n = Vector{BigInt}(undef, 3)
    for i in 1:3
        n[i] = bytes_to_integer(sign[idx:idx+SQISIGN2D_2a_length-1])
        idx += SQISIGN2D_2a_length
    end
    xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentForDim2)
    if is_n1_odd
        n1, n2, n3, n4 = 1, n[1], n[2], n[3]
    else
        n1, n2, n3, n4 = n[1], 1, n[2], n[3]
    end

    xPaux, xQaux, xPQaux = action_of_matrix([n1 n3; n2 n4], a24aux, xPfix, xQfix, xPQfix, ExponentForDim2)

    bit_s = sign[idx]
    idx += 1
    s = bytes_to_integer(sign[idx:idx+SQISIGN2D_challenge_byte_length-1])
    idx += SQISIGN2D_challenge_byte_length
    r = bytes_to_integer(sign[idx:idx+SQISIGN2D_challenge_byte_length-1])
    idx += SQISIGN2D_challenge_byte_length
    d2cod_bit = sign[idx]
    idx += 1

    # adjust <(Ppub, Paux), (Qpub, Qaux)> to be isotropic w.r.t.the Weil pairing
    xPpub, xQpub, xPQpub = torsion_basis(a24pub, ExponentFull)
    xPpub = xDBLe(xPpub, a24pub, ExponentFull - ExponentForDim2)
    xQpub = xDBLe(xQpub, a24pub, ExponentFull - ExponentForDim2)
    xPQpub = xDBLe(xPQpub, a24pub, ExponentFull - ExponentForDim2)
    two_to_a = BigInt(1) << ExponentForDim2
    w_aux = Weil_pairing_2power(Aaux, xPaux, xQaux, xPQaux, ExponentForDim2)
    w_pub = Weil_pairing_2power(Apub, xPpub, xQpub, xPQpub, ExponentForDim2)
    e_aux = fq_dlog_power_of_2_opt(w_aux, global_data.E0_data.dlog_data[ExponentForDim2])
    e_pub = fq_dlog_power_of_2_opt(w_pub, global_data.E0_data.dlog_data[ExponentForDim2])
    e = e_pub * invmod(-e_aux, two_to_a) % two_to_a
    ed = sqrt_mod_2power(e, ExponentForDim2)
    is_adjust_sqrt && (ed += two_to_a >> 1)
    xPaux = ladder(ed, xPaux, a24aux)
    xQaux = ladder(ed, xQaux, a24aux)
    xPQaux = ladder(ed, xPQaux, a24aux)

    # isogeny of dimension 2
    P1P2 = CouplePoint(xPpub, xPaux)
    Q1Q2 = CouplePoint(xQpub, xQaux)
    PQ1PQ2 = CouplePoint(xPQpub, xPQaux)
    Es, _ = product_isogeny_sqrt(a24pub, a24aux, P1P2, Q1Q2, PQ1PQ2, CouplePoint{FqFieldElem}[], CouplePoint{FqFieldElem}[], ExponentForDim2, StrategiesDim2[ExponentForDim2])
    A1, _ = Montgomery_normalize(A_to_a24(Es[1]), Proj1{FqFieldElem}[])
    A2, _ = Montgomery_normalize(A_to_a24(Es[2]), Proj1{FqFieldElem}[])
    A1 = Montgomery_coeff(A1)
    A2 = Montgomery_coeff(A2)
    !lex_order(A1, A2) && ((A1, A2) = (A2, A1))
    if d2cod_bit == 1
        Acha = A1
    else
        Acha = A2
    end

    a24cha = A_to_a24(Acha)
    xPcha, xQcha, xPQcha = torsion_basis(Acha, SQISIGN_challenge_length)
    if bit_s == 1
        Kcha_dual = ladder3pt(s, xPcha, xQcha, xPQcha, a24cha)
        P = xQcha
    else
        Kcha_dual = ladder3pt(s, xQcha, xPcha, xPQcha, a24cha)
        P = xPcha
    end
    a24com, tmp = two_e_iso(a24cha, Kcha_dual, SQISIGN_challenge_length, [P], StrategiesDim1[SQISIGN_challenge_length])
    a24com, tmp = Montgomery_normalize(a24com, [tmp[1]])
    Kcha_d = tmp[1]
    Acom = Montgomery_coeff(a24com)
    c = challenge(Acom, m)
    xPcom, xQcom, xPQcom = torsion_basis(Acom, SQISIGN_challenge_length)
    Kcha = ladder3pt(c, xPcom, xQcom, xPQcom, a24com)

    return Kcha == ladder(r, Kcha_d, a24com)
end