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
    two_to_ab = BigInt(1) << ExponentSum
    two_to_chall = BigInt(1) << SQISIGN_challenge_length
    a24_0 = global_data.E0_data.a24_0
    xP0, xQ0, xPQ0 = global_data.E0_data.xP2e, global_data.E0_data.xQ2e, global_data.E0_data.xPQ2e
    xP0 = xDBLe(xP0, a24_0, ExponentFull - ExponentSum)
    xQ0 = xDBLe(xQ0, a24_0, ExponentFull - ExponentSum)
    xPQ0 = xDBLe(xPQ0, a24_0, ExponentFull - ExponentSum)
    xP0c = xDBLe(xP0, a24_0, ExponentSum - ExponentForDim1)
    xQ0c = xDBLe(xQ0, a24_0, ExponentSum - ExponentForDim1)
    xPQ0c = xDBLe(xPQ0, a24_0, ExponentSum - ExponentForDim1)

    s0, s1 = rand(1:two_to_chall), rand(1:two_to_chall)

    # the first 2^c-isogeny
    K0 = ladder3pt(s0, xP0c, xQ0c, xPQ0c, a24_0)
    a24m, (xP0m, xQ0m, xPQ0m) = two_e_iso(a24_0, K0, ExponentForDim1, [xP0, xQ0, xPQ0], StrategiesDim1[ExponentForDim1])
    a24m, (xP0m, xQ0m, xPQ0m) = Montgomery_normalize(a24m, [xP0m, xQ0m, xPQ0m])

    # solving the DLog problem
    xQm, xPm, xPQm = complete_basis(a24m, xQ0m, xDBLe(xQ0m, a24m, ExponentSum-1), global_data.Fp2(1), ExponentSum)
    if s0 % 2 == 0
        n1, n2, n3, n4 = ec_bi_dlog(Montgomery_coeff(a24m), xPQ0m, xQ0m, xP0m, xPm, xQm, xPQm, global_data.E0_data.dlog_data[ExponentSum])
        n1 = -n1 + n3
        n2 = -n2 + n4
    else
        n1, n2, n3, n4 = ec_bi_dlog(Montgomery_coeff(a24m), xP0m, xQ0m, xPQ0m, xPm, xQm, xPQm, global_data.E0_data.dlog_data[ExponentSum])
    end

    # compute the ideal corresponding to the composition of the two isogenies
    a, b, c, d = global_data.E0_data.Matrix_2ed2_inv * [-n2 + n1*s1, 0, -n4 + n3*s1, 0]
    alpha = QOrderElem(a, b, c, d)
    I = LeftIdeal(alpha, two_to_chall << ExponentForDim1)

    # ideal to isogeny
    a24 = a24_0
    xP, xQ, xPQ = global_data.E0_data.xP2e, global_data.E0_data.xQ2e, global_data.E0_data.xPQ2e
    M = BigInt[1 0; 0 1]
    D = 1
    e = 2 * ExponentForDim1
    while e > 0
        ed = min(e, ExponentForId2IsoDim1)
        is_normalized = e <= ExponentForId2IsoDim1
        n_I_d = D * BigInt(2)^ed
        I_d = larger_ideal(I, n_I_d)
        a24, xP, xQ, xPQ, M, beta, D = short_ideal_to_isogeny(I_d, a24, xP, xQ, xPQ, M, D, ed, global_data, is_normalized, Quaternion_0, 0, 0)
        I = ideal_transform(I, beta, n_I_d)
        e -= ed
    end
    xP = xDBLe(xP, a24, ExponentFull - ExponentSum)
    xQ = xDBLe(xQ, a24, ExponentFull - ExponentSum)
    xPQ = xDBLe(xPQ, a24, ExponentFull - ExponentSum)
    xP, xQ, xPQ = action_of_matrix(M, a24, xP, xQ, xPQ, ExponentSum)

    # the dual isogeny of the first 2^c-isogeny
    K = xDBLe(xQm, a24m, ExponentSum - ExponentForDim1)
    a24_0d, (xP0d, xQ0d, xPQ0d) = two_e_iso(a24m, K, ExponentForDim1, [xPm, xQm, xPQm], StrategiesDim1[ExponentForDim1])
    xP0d, xQ0d, xPQ0d = global_data.E0_data.isomorphism_to_A0(a24_to_A(a24_0d), [xP0d, xQ0d, xPQ0d])
    if xQ0d != xDBLe(xQ0, a24_0, ExponentForDim1)
        # adjust the action by i
        xP0d = -xP0d
        xQ0d = -xQ0d
        xPQ0d = -xPQ0d
    end
    n1, n2, n3, n4 = ec_bi_dlog(global_data.E0_data.A0, xP0d, xPQ0d, xQ0d, xP0, xQ0, xPQ0, global_data.E0_data.dlog_data[ExponentSum])
    n3 = -n3 + n1
    n4 = -n4 + n2
    M0 = [n1 n3; n2 n4] .% two_to_ab

    # the second 2^c-isogeny
    xPm_c = xDBLe(xPm, a24m, ExponentSum - ExponentForDim1)
    xQm_c = xDBLe(xQm, a24m, ExponentSum - ExponentForDim1)
    xPQm_c = xDBLe(xPQm, a24m, ExponentSum - ExponentForDim1)
    K1 = ladder3pt(s1, xPm_c, xQm_c, xPQm_c, a24m)
    a24pub, image = two_e_iso(a24m, K1, ExponentForDim1, [xQm], StrategiesDim1[ExponentForDim1])
    xQm_p = image[1]
    a24pub, image = Montgomery_normalize(a24pub, [xQm_p])
    xQm_p = image[1]
    @assert a24 == a24pub
    K1dual = xDBLe(xQm_p, a24pub, ExponentSum - ExponentForDim1)
    a24md, (xPmd, xQmd, xPQmd) = two_e_iso(a24pub, K1dual, ExponentForDim1, [xP, xQ, xPQ], StrategiesDim1[ExponentForDim1])
    _, (xPmd, xQmd, xPQmd) = Montgomery_normalize(a24md, [xPmd, xQmd, xPQmd])
    if is_infinity(xDBLe(xPmd, a24m, ExponentSum-1))
        n1, n2, n3, n4 = ec_bi_dlog(Montgomery_coeff(a24m), xPQmd, xQmd, xPmd, xPm, xQm, xPQm, global_data.E0_data.dlog_data[ExponentSum])
        n1 = -n1 + n3
        n2 = -n2 + n4
    elseif is_infinity(xDBLe(xQmd, a24m, ExponentSum-1))
        n1, n2, n3, n4 = ec_bi_dlog(Montgomery_coeff(a24m), xPmd, xPQmd, xQmd, xPm, xQm, xPQm, global_data.E0_data.dlog_data[ExponentSum])
        n3 = -n3 + n1
        n4 = -n4 + n2
    else
        n1, n2, n3, n4 = ec_bi_dlog(Montgomery_coeff(a24m), xPmd, xQmd, xPQmd, xPm, xQm, xPQm, global_data.E0_data.dlog_data[ExponentSum])
    end
    M1 = [n1 n3; n2 n4] .% two_to_ab

    return Montgomery_coeff(a24), (a24m, s0, s1, M0, M1, xPm, xQm, xPQm, invmod_2x2(M, two_to_ab), I, D)
end

function commitment(global_data::GlobalData)
    a24, xP, xQ, xPQ, I_sec = RandIsogImages(SQISIGN2D_commitment_degree, global_data, false)
    a24, (xP, xQ, xPQ) = Montgomery_normalize(a24, [xP, xQ, xPQ])
    A = Montgomery_coeff(a24)
    xPc, xQc, xPQc = torsion_basis(A, SQISIGN_challenge_length)
    xPd = xDBLe(xP, a24, ExponentSum - SQISIGN_challenge_length)
    xQd = xDBLe(xQ, a24, ExponentSum - SQISIGN_challenge_length)
    xPQd = xDBLe(xPQ, a24, ExponentSum - SQISIGN_challenge_length)
    n1, n2, n3, n4 = ec_bi_dlog(A, xPc, xQc, xPQc, xPd, xQd, xPQd, global_data.E0_data.dlog_data[SQISIGN_challenge_length])
    M = [n1 n3; n2 n4]
    return A, (I_sec, xP, xQ, xPQ, xPc, xQc, xPQc), M
end

function challenge(A::FqFieldElem, m::String)
    if SQISIGN_challenge_length <= 256
        h = sha3_256(string(A) * m)
    else
        h = sha3_512(string(A) * m)
    end

    c = BigInt(0)
    len = SQISIGN_challenge_length
    n, r = divrem(len, 8)
    for i in 1:(n+1)
        c += BigInt(h[i]) << (8*(i-1))
    end
    c >>= 8 - r

    return c
end

function signing(pk::FqFieldElem, sk, m::String, global_data::GlobalData, is_compact::Bool)
    two_to_a = BigInt(1) << ExponentForDim2
    Apub = pk
    a24pub = A_to_a24(Apub)
    a24m, s0, sm, M0, Mm, xPm, xQm, xPQm, Mpub, Isec, Dsec = sk

    while true
        # commitment
        Acom, (Icom, xPcom, xQcom, xPQcom, xPcom_fix, xQcom_fix, xPQcom_fix), Mcom = commitment(global_data)
        a24com = A_to_a24(Acom)

        # challenge
        cha = challenge(Acom, m)
        a, b = Mcom * [1, cha]
        a, b, c, d = global_data.E0_data.Matrix_2ed_inv * [b, 0, -a, 0]
        alpha = QOrderElem(a, b, c, d)
        Icha = LeftIdeal(alpha, BigInt(1) << SQISIGN_challenge_length)
        Kcha = ladder3pt(cha, xPcom_fix, xQcom_fix, xPQcom_fix, a24com)
        if !is_compact
            a24cha, (xPcha, xQcha, xPQcha) = two_e_iso(a24com, Kcha, SQISIGN_challenge_length, [xPcom, xQcom, xPQcom])
            a24cha, (xPcha, xQcha, xPQcha) = Montgomery_normalize(a24cha, [xPcha, xQcha, xPQcha])
        else
            a24cha, (xPcha, xQcha, xPQcha, Kcha_dual) = two_e_iso(a24com, Kcha, SQISIGN_challenge_length, [xPcom, xQcom, xPQcom, xQcom_fix], StrategiesDim1[SQISIGN_challenge_length])
            a24cha, (xPcha, xQcha, xPQcha, Kcha_dual) = Montgomery_normalize(a24cha, [xPcha, xQcha, xPQcha, Kcha_dual])
        end
        Acha = Montgomery_coeff(a24cha)

        # find alpha in bar(Isec)IcomIcha suitable for the response
        Icomcha = intersection(Icom, Icha)
        I = involution_product(Isec, Icomcha)
        nI = Dsec * SQISIGN2D_commitment_degree << SQISIGN_challenge_length
        alpha, q, found = element_for_response(I, nI, ExponentForDim2)
        !found && continue

        # compute the image under the response sigma
        Malpha = quaternion_to_matrix(involution(alpha), global_data.E0_data.Matrices_2e)
        xPres, xQres, xPQres = action_of_matrix(Malpha, a24cha, xPcha, xQcha, xPQcha, ExponentSum)
        if is_compact
            xPres = ladder(SQISIGN2D_commitment_degree_inv, xPres, a24cha)
            xQres = ladder(SQISIGN2D_commitment_degree_inv, xQres, a24cha)
            xPQres = ladder(SQISIGN2D_commitment_degree_inv, xPQres, a24cha)
        end

        # compute an auxiliary path by PushRandIsog
        a24aux, (xPaux, xQaux, xPQaux) = PushRandIsog(two_to_a - q, a24m, s0, sm, xPm, xQm, xPQm, M0, Mm, global_data)
        Aaux = Montgomery_coeff(a24aux)

        if !is_compact
            # adjust (Paux, Qaux) to be the preimage of the fixed basis of Echa[2^a]
            xPfix, xQfix, xPQfix = torsion_basis(Acha, ExponentForDim2)
            n1, n2, n3, n4 = ec_bi_dlog(Acha, xPfix, xQfix, xPQfix, xPres, xQres, xPQres, global_data.E0_data.dlog_data[ExponentForDim2])
            n1 = n1 * SQISIGN2D_commitment_degree % two_to_a
            n2 = n2 * SQISIGN2D_commitment_degree % two_to_a
            n3 = n3 * SQISIGN2D_commitment_degree % two_to_a
            n4 = n4 * SQISIGN2D_commitment_degree % two_to_a
            Maux = [n1 n3; n2 n4]

            # compress the signature
            sign = Vector{UInt8}(undef, SQISIGN2D_signature_length)
            idx = 1
            Acom_byte = Fq_to_bytes(Acom)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Acom_byte
            idx += SQISIGN2D_Fp2_length
            Aaux_byte = Fq_to_bytes(Aaux)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Aaux_byte
            idx += SQISIGN2D_Fp2_length
            xPfix, xQfix, xPQfix = torsion_basis(Aaux, ExponentForDim2)
            n1, n2, n3, n4 = ec_bi_dlog(Aaux, xPaux, xQaux, xPQaux, xPfix, xQfix, xPQfix, global_data.E0_data.dlog_data[ExponentForDim2])
            M = ([n1 n3; n2 n4] * Maux) .% two_to_a
            n1, n2, n3, n4 = M
            if n1 & 1 == 1
                n1inv = invmod(n1, two_to_a)
                n1d = sqrt_mod_2power(n1^2 % two_to_a, ExponentForDim2)
                sign[idx] = ((n1d - n1) % two_to_a == 0 || (n1d + n1) % two_to_a == 0) ? 0x02 : 0x00
                idx += 1
                n2 = (n2 * n1inv) % two_to_a
                n3 = (n3 * n1inv) % two_to_a
                n4 = (n4 * n1inv) % two_to_a
                for n in [n2, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_2a_length)
                    sign[idx:idx+SQISIGN2D_2a_length-1] = n_bytes
                    idx += SQISIGN2D_2a_length
                end
            else
                n2inv = invmod(n2, two_to_a)
                n2d = sqrt_mod_2power(n2^2 % two_to_a, ExponentForDim2)
                sign[idx] = ((n2d - n2) % two_to_a == 0 || (n2d + n2) % two_to_a == 0) ? 0x03 : 0x01
                idx += 1
                n1 = (n1 * n2inv) % two_to_a
                n3 = (n3 * n2inv) % two_to_a
                n4 = (n4 * n2inv) % two_to_a
                for n in [n1, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_2a_length)
                    sign[idx:idx+SQISIGN2D_2a_length-1] = n_bytes
                    idx += SQISIGN2D_2a_length
                end
            end
        else
            # (2^a, 2^a)-isogeny
            O = infinity_point(global_data.Fp2)
            xT1 = xDBLe(xPres, a24cha, ExponentForDim2 - 2)
            xT2 = xDBLe(xPaux, a24aux, ExponentForDim2 - 2)
            PresO = CouplePoint(xPres, O)
            QresO = CouplePoint(xQres, O)
            PQresO = CouplePoint(xPQres, O)
            xPresT1 = ladder(1 + (two_to_a >> 2), xPres, a24cha)
            xQresT1 = ladder3pt(two_to_a >> 2, xQres, xPres, xPQres, a24cha)
            xPQresT1 = ladder3pt(two_to_a - 1 - (two_to_a >> 2), xQres, xPres, xPQres, a24cha)
            PresT1T2 = CouplePoint(xPresT1, xT2)
            QresT1T2 = CouplePoint(xQresT1, xT2)
            PQresT1T2 = CouplePoint(xPQresT1, xT2)
            Es, images = product_isogeny_sqrt(a24cha, a24aux, CouplePoint(xPres, xPaux), CouplePoint(xQres, xQaux), CouplePoint(xPQres, xPQaux), [PresO, QresO, PQresO], [PresT1T2, QresT1T2, PQresT1T2], ExponentForDim2, StrategiesDim2[ExponentForDim2])
            idx = 1
            xPauxd, xQauxd, xPQauxd = images[1][idx], images[2][idx], images[3][idx]
            w0 = Weil_pairing_2power(Acha, xPres, xQres, xPQres, ExponentForDim2)
            w1 = Weil_pairing_2power(affine(Es[idx]), xPauxd, xQauxd, xPQauxd, ExponentForDim2)
            if w1 != w0^(-q)
                idx = 2
            end
            a24auxd = A_to_a24(Es[idx])
            xPauxd, xQauxd, xPQauxd = images[1][idx], images[2][idx], images[3][idx]
            a24auxd, (xPauxd, xQauxd, xPQauxd) = Montgomery_normalize(a24auxd, [xPauxd, xQauxd, xPQauxd])
            Aauxd = Montgomery_coeff(a24auxd)
            xPfix, xQfix, xPQfix = torsion_basis(Aauxd, ExponentForDim2)
            n1, n2, n3, n4 = ec_bi_dlog(Aauxd, xPauxd, xQauxd, xPQauxd, xPfix, xQfix, xPQfix, global_data.E0_data.dlog_data[ExponentForDim2])
            Mauxd = [n1 n3; n2 n4] * Mpub * invmod(q, two_to_a)
            xPauxd, xQauxd, xPQauxd = action_of_matrix(Mauxd, a24auxd, xPfix, xQfix, xPQfix, ExponentForDim2)

            # information to recover the commitment
            xPcha, xQcha, xPQcha = torsion_basis(Acha, SQISIGN_challenge_length)
            a, b = ec_bi_dlog(Acha, Kcha_dual, xPcha, xQcha, xPQcha, global_data.E0_data.dlog_data[SQISIGN_challenge_length])

            # compress the signature
            sign = Vector{UInt8}(undef, CompactSQISIGN2D_signature_length)
            idx = 1
            Aauxd_byte = Fq_to_bytes(Aauxd)
            sign[idx:idx+SQISIGN2D_Fp2_length-1] = Aauxd_byte
            idx += SQISIGN2D_Fp2_length

            n1, n2, n3, n4 = Mauxd .% two_to_a
            if n1 & 1 == 1
                n1inv = invmod(n1, two_to_a)
                n1d = sqrt_mod_2power(n1^2 % two_to_a, ExponentForDim2)
                sign[idx] = ((n1d - n1) % two_to_a == 0 || (n1d + n1) % two_to_a == 0) ? 0x02 : 0x00
                idx += 1
                n2 = (n2 * n1inv) % two_to_a
                n3 = (n3 * n1inv) % two_to_a
                n4 = (n4 * n1inv) % two_to_a
                for n in [n2, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_2a_length)
                    sign[idx:idx+SQISIGN2D_2a_length-1] = n_bytes
                    idx += SQISIGN2D_2a_length
                end
            else
                n2inv = invmod(n2, two_to_a)
                n2d = sqrt_mod_2power(n2^2 % two_to_a, ExponentForDim2)
                sign[idx] = ((n2d - n2) % two_to_a == 0 || (n2d + n2) % two_to_a == 0) ? 0x03 : 0x01
                idx += 1
                n1 = (n1 * n2inv) % two_to_a
                n3 = (n3 * n2inv) % two_to_a
                n4 = (n4 * n2inv) % two_to_a
                for n in [n1, n3, n4]
                    n_bytes = integer_to_bytes(n, SQISIGN2D_2a_length)
                    sign[idx:idx+SQISIGN2D_2a_length-1] = n_bytes
                    idx += SQISIGN2D_2a_length
                end
            end

            two_to_chall = BigInt(1) << SQISIGN_challenge_length
            if a % 2 == 1
                sign[idx] = 0x01
                idx += 1
                b = (b * invmod(a, two_to_chall)) % two_to_chall
                b_bytes = integer_to_bytes(b, SQISIGN2D_challenge_byte_length)
                sign[idx:idx+SQISIGN2D_challenge_byte_length-1] = b_bytes
                idx += SQISIGN2D_challenge_byte_length
                xP = xQcha
            else
                sign[idx] = 0x00
                idx += 1
                a = (a * invmod(b, two_to_chall)) % two_to_chall
                a_bytes = integer_to_bytes(a, SQISIGN2D_challenge_byte_length)
                sign[idx:idx+SQISIGN2D_challenge_byte_length-1] = a_bytes
                idx += SQISIGN2D_challenge_byte_length
                xP = xPcha
            end
            a24com_d, image = two_e_iso(a24cha, Kcha_dual, SQISIGN_challenge_length, [xP], StrategiesDim1[SQISIGN_challenge_length])
            a24com_d, image = Montgomery_normalize(a24com_d, image)
            Kcha_d = image[1]
            r = ec_dlog(Acom, Kcha, Kcha_d, xQcom_fix, global_data.E0_data)
            sign[idx: idx+SQISIGN2D_challenge_byte_length-1] = integer_to_bytes(r, SQISIGN2D_challenge_byte_length)
            idx += SQISIGN2D_challenge_byte_length
            sign[idx] = lex_order(Aaux, Acha) ? 0x00 : 0x01
        end

        return sign
    end
end

function verify(pk::FqFieldElem, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    # decompress the signature
    idx = 1
    Acom = bytes_to_Fq(sign[idx:idx+SQISIGN2D_Fp2_length-1], global_data.Fp2)
    a24com = A_to_a24(Acom)
    idx += SQISIGN2D_Fp2_length
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

    a24com = A_to_a24(Acom)
    a24aux = A_to_a24(Aaux)
    a24pub = A_to_a24(pk)

    # compute the challenge
    c = challenge(Acom, m)
    xPcom, xQcom, xPQcom = torsion_basis(Acom, SQISIGN_challenge_length)
    Kcha = ladder3pt(c, xPcom, xQcom, xPQcom, a24com)
    a24cha, _ = two_e_iso(a24com, Kcha, SQISIGN_challenge_length, Proj1{FqFieldElem}[], StrategiesDim1[SQISIGN_challenge_length])
    a24cha, _ = Montgomery_normalize(a24cha, Proj1{FqFieldElem}[])
    Acha = Montgomery_coeff(a24cha)
    xPres, xQres, xPQres = torsion_basis(Acha, ExponentForDim2)

    # adjust <(Pcha, Paux), (Qcha, Qaux)> to be isotropic w.r.t.the Weil pairing
    two_to_a = BigInt(1) << ExponentForDim2
    w_aux = Weil_pairing_2power(Aaux, xPaux, xQaux, xPQaux, ExponentForDim2)
    w_res = Weil_pairing_2power(Acha, xPres, xQres, xPQres, ExponentForDim2)
    e_aux = fq_dlog_power_of_2_opt(w_aux, global_data.E0_data.dlog_data[ExponentForDim2])
    e_res = fq_dlog_power_of_2_opt(w_res, global_data.E0_data.dlog_data[ExponentForDim2])
    e = e_res * invmod(-e_aux, two_to_a) % two_to_a
    ed = sqrt_mod_2power(e, ExponentForDim2)
    is_adjust_sqrt && (ed += two_to_a >> 1)
    xPaux = ladder(ed, xPaux, a24aux)
    xQaux = ladder(ed, xQaux, a24aux)
    xPQaux = ladder(ed, xPQaux, a24aux)

    # isogeny of dimension 2
    P1P2 = CouplePoint(xPres, xPaux)
    Q1Q2 = CouplePoint(xQres, xQaux)
    PQ1PQ2 = CouplePoint(xPQres, xPQaux)
    Es, _ = product_isogeny_sqrt(a24cha, a24aux, P1P2, Q1Q2, PQ1PQ2, CouplePoint{FqFieldElem}[], CouplePoint{FqFieldElem}[], ExponentForDim2, StrategiesDim2[ExponentForDim2])

    j0 = jInvariant_a24(a24pub)
    j1 = jInvariant_A(Es[1])
    j2 = jInvariant_A(Es[2])

    return j1 == j0 || j2 == j0
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