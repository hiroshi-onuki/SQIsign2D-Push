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

    xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, hint1, hint2 = basis_3e(Apk, CofactorWRT3, ExponentOfThree, global_data)

    n1, n2, n3, n4 = ec_bi_dlog(a24pk, BasisData(xP3pk_fix, xQ3pk_fix, xPQ3pk_fix), BasisData(xP3pk, xQ3pk, xPQ3pk), 3, ExponentOfThree)
    M = [n1 n3; n2 n4]

    pk = Vector{UInt8}(undef, SignatureByteLength)
    idx = 1
    pk[idx:idx+Fp2ByteLength-1] = Fq_to_bytes(Apk)
    idx += Fp2ByteLength
    pk[idx] = integer_to_bytes(hint1, 1)[1]
    pk[idx+1] = integer_to_bytes(hint2, 1)[1]

    return pk, (xP2pk, xQ2pk, xPQ2pk, xP3pk_fix, xQ3pk_fix, xPQ3pk_fix, M, J3, J2, alpha)
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

function signing(pk::Vector{UInt8}, sk, m::String, global_data::GlobalData)
    Apk = bytes_to_Fq(pk[1:Fp2ByteLength], global_data.Fp2)
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

    # find alpha in bar(Icom)IskIcha suitable for the response
    IskIchl = intersection(I2sk, Ichl)
    IskIchl = div(IskIchl * alpha_sk, two_to_e2^2)
    gen_com = element_exact_norm(Icom, three_to_e3^2, 3)
    e3 = valuation(gcd(involution(gen_com) * IskIchl), 3)
    I = involution_product(Icom, IskIchl)
    alpha, q, found = element_for_response(I, three_to_e3^4 * ChallengeDegree, ExponentOfTwo, e3, IskIchl)
    if found
        return true, BigInt[], nothing, false
    else
        q(x, y) = quadratic_form(QOrderElem(x), QOrderElem(y))
        Imatrix = ideal_to_matrix(I)
        H = integral_LLL([Imatrix[:, i] for i in 1:4], q)
        LLLmat = Imatrix * H
        red_basis = [LLLmat[:, i] for i in 1:4]
        bs = [QOrderElem(red_basis[i][1], red_basis[i][2], red_basis[i][3], red_basis[i][4]) for i in 1:4]
        return false, [div(norm(b), norm(I)) for b in bs], bs, LeftIdeal(bs[1], norm(I) * 3) == LeftIdeal(bs[2], norm(I) * 3)
    end

    f2 = BigInt(1) << valuation(gcd(alpha), 2)
    alpha = div(alpha, f2)
    q = div(q, f2^2)

    # compute (q', e_dim1, e_dim2) s.t. q = q' * 2^e_dim1 and q' < 2^e_dim2
    e_dim1 = valuation(q, 2)
    two_to_e_dim1 = BigInt(1) << e_dim1
    qd = q >> e_dim1
    e_dim2 = 0
    two_to_e_dim2 = BigInt(1)
    while two_to_e_dim2 < qd
        e_dim2 += 1
        two_to_e_dim2 <<= 1
    end
    e = ExponentOfTwo - e_dim1 - e_dim2
    if e >= 2
        e_dim2_torsion = e_dim2 + 2
    else
        e_dim2_torsion = e_dim2
    end

    # compute the image of phi_rsp(P2com, Q2com)
    c = invmod(three_to_e3^2 * ChallengeDegree, two_to_e2)
    xP2rsp, xQ2rsp, xPQ2rsp = action_on_torsion_basis(involution(alpha), a24chl, xP2chl, xQ2chl, xPQ2chl, global_data.E0_data, c)
    
    # find the kernel of dual of the even part of the response isogeny
    xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, hint1chl, hint2chl = basis_2e(Montgomery_coeff(a24chl), CofactorWRT2, global_data)
    n1, n2, n3, n4 = ec_bi_dlog(a24chl, BasisData(xP2rsp, xQ2rsp, xPQ2rsp), BasisData(xP2chl_fix, xQ2chl_fix, xPQ2chl_fix), 2, ExponentOfTwo)
    Mchl = [n1 n3; n2 n4]

    # compute an auxiliary isogeny
    d_aux = two_to_e_dim2 - qd
    e3_dim1 = valuation(d_aux, 3)
    d_aux_d = div(d_aux, BigInt(3)^e3_dim1)
    a24aux, xP2aux, xQ2aux, xPQ2aux = PushRandIsog(d_aux_d, a24mid, xK1, xK2, xP2mid, xQ2mid, xPQmid, global_data)
    if e3_dim1 > 0
        xK3aux = random_point_order_l_power(a24aux, p + 1, 3, e3_dim1)
        a24aux, (xP2aux, xQ2aux, xPQ2aux) = three_e_iso(a24aux, xK3aux, e3_dim1, [xP2aux, xQ2aux, xPQ2aux])
    end
    a24aux, (xP2aux, xQ2aux, xPQ2aux) = Montgomery_normalize(a24aux, [xP2aux, xQ2aux, xPQ2aux])
    Aaux = Montgomery_coeff(a24aux)
    xP2aux_fix, xQ2aux_fix, xPQ2aux_fix, hint1aux, hint2aux = basis_2e(Aaux, CofactorWRT2, global_data)
    n1, n2, n3, n4 = ec_bi_dlog(a24aux, BasisData(xP2aux, xQ2aux, xPQ2aux), BasisData(xP2aux_fix, xQ2aux_fix, xPQ2aux_fix), 2, ExponentOfTwo)
    Maux = [n1 n3; n2 n4]

    # matrix represent (Pchl, Qchl) = M(Pchl_fix, Qchl_fix) such that
    # [2^(e2 - e_dim1)]P or [2^(e2 - e_dim1)]Q is the kernel of the dual isogeny of the even part of the response isogeny
    # and the images of (Pchl, Qchl) under that isogeny and (Paux_fix, Qaux_fix) give the kernel of the 2-dimensional isogeny in the verification
    Mrsp = (Mchl * invmod_2x2(Maux, two_to_e2)) .% two_to_e2

    # make the signature
    sign = Vector{UInt8}(undef, SignatureByteLength)
    idx = 1
    sign[idx:idx+Fp2ByteLength-1] = Fq_to_bytes(Aaux)
    idx += Fp2ByteLength
    sign[idx:idx+ChallengeByteLength-1] = integer_to_bytes(chl, ChallengeByteLength)
    idx += ChallengeByteLength
    sign[idx:idx+DegreeExponentByteLength-1] = integer_to_bytes(e_dim1, DegreeExponentByteLength)
    idx += DegreeExponentByteLength
    sign[idx:idx+DegreeExponentByteLength-1] = integer_to_bytes(e_dim2, DegreeExponentByteLength)
    idx += DegreeExponentByteLength
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(Mrsp[1, 1], Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(Mrsp[2, 1], Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(Mrsp[1, 2], Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(Mrsp[2, 2], Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx] = integer_to_bytes(hint1chl, 1)[1]
    sign[idx+1] = integer_to_bytes(hint2chl, 1)[1]
    sign[idx+2] = integer_to_bytes(hint1aux, 1)[1]
    sign[idx+3] = integer_to_bytes(hint2aux, 1)[1]

    return sign
end

function verify(pk::Vector{UInt8}, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    Apk = bytes_to_Fq(pk[1:Fp2ByteLength], global_data.Fp2)
    hint1pk = Int(pk[Fp2ByteLength+1])
    hint2pk = Int(pk[Fp2ByteLength+2])
    a24pk = A_to_a24(Apk)

    # decompress the signature
    idx = 1
    Aaux = bytes_to_Fq(sign[idx:idx+Fp2ByteLength-1], global_data.Fp2)
    idx += Fp2ByteLength
    chl = bytes_to_integer(sign[idx:idx+ChallengeByteLength-1])
    idx += ChallengeByteLength
    e_dim1 = Int(bytes_to_integer(sign[idx:idx+DegreeExponentByteLength-1]))
    idx += DegreeExponentByteLength
    e_dim2 = Int(bytes_to_integer(sign[idx:idx+DegreeExponentByteLength-1]))
    idx += DegreeExponentByteLength
    Mrsp = Matrix{BigInt}(undef, 2, 2)
    Mrsp[1, 1] = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    Mrsp[2, 1] = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    Mrsp[1, 2] = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    Mrsp[2, 2] = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    hint1chl = Int(sign[idx])
    hint2chl = Int(sign[idx+1])
    hint1aux = Int(sign[idx+2])
    hint2aux = Int(sign[idx+3])
    if ExponentOfTwo - e_dim1 - e_dim2 >= 2
        e_dim2_torsion = e_dim2 + 2
    else
        e_dim2_torsion = e_dim2
    end

    # compute Echl
    xP3pk, xQ3pk, xPQ3pk = basis_3e_from_hint(Apk, CofactorWRT3, hint1pk, hint2pk, global_data)
    xKchl = ladder3pt(chl, xP3pk, xQ3pk, xPQ3pk, a24pk)
    a24chl, image_check = three_e_iso(a24pk, xKchl, ExponentOfThree, [xQ3pk], StrategiesDim1Three[ExponentOfThree])
    a24chl, image_check = Montgomery_normalize(a24chl, image_check)
    Achl = Montgomery_coeff(a24chl)
    xP2chl, xQ2chl, xPQ2chl = basis_2e_from_hint(Achl, CofactorWRT2, hint1chl, hint2chl, global_data)
    xP2chl, xQ2chl, xPQ2chl = action_of_matrix(Mrsp, a24chl, xP2chl, xQ2chl, xPQ2chl, ExponentOfTwo)

    # compute Echl_d
    if e_dim1 > 0
        if Mrsp[1, 1] % 2 != 0 || Mrsp[2, 1] % 2 != 0
            xKchl_d = xDBLe(xP2chl, a24chl, ExponentOfTwo - e_dim1)
        else
            xKchl_d = xDBLe(xQ2chl, a24chl, ExponentOfTwo - e_dim1)
        end
        eval_points = vcat(image_check, [xP2chl, xQ2chl, xPQ2chl])
        a24chl_d, images = two_e_iso(a24chl, xKchl_d, e_dim1, eval_points)
        a24chl_d, images = Montgomery_normalize(a24chl_d, images)
        xP3check, xP2chl_d, xQ2chl_d, xPQ2chl_d = images
    else
        a24chl_d = a24chl
        xP3check = image_check[1]
        xP2chl_d, xQ2chl_d, xPQ2chl_d = xP2chl, xQ2chl, xPQ2chl
    end
    xP2chl_d = xDBLe(xP2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)
    xQ2chl_d = xDBLe(xQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)
    xPQ2chl_d = xDBLe(xPQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)

    # compute the deterministic basis on Eaux
    a24aux = A_to_a24(Aaux)
    xP2aux, xQ2aux, xPQ2aux = basis_2e_from_hint(Aaux, CofactorWRT2, hint1aux, hint2aux, global_data)
    xP2aux = xDBLe(xP2aux, a24aux, ExponentOfTwo - e_dim2_torsion)
    xQ2aux = xDBLe(xQ2aux, a24aux, ExponentOfTwo - e_dim2_torsion)
    xPQ2aux = xDBLe(xPQ2aux, a24aux, ExponentOfTwo - e_dim2_torsion)

    # dim2 isogeny
    K1 = CouplePoint(xP2chl_d, xP2aux)
    K2 = CouplePoint(xQ2chl_d, xQ2aux)
    K12 = CouplePoint(xPQ2chl_d, xPQ2aux)
    O = infinity_point(global_data.Fp2)
    eval_point = [CouplePoint(xP3check, O)]
    if e_dim2_torsion > e_dim2
        Es, image_dim2 = product_isogeny(a24chl_d, a24aux, K1, K2, K12, eval_point, e_dim2, StrategiesDim2[e_dim2])
    else
        Es, image_dim2 = product_isogeny_sqrt(a24chl_d, a24aux, K1, K2, K12, eval_point, e_dim2, StrategiesDim2[e_dim2])
    end

    # check
    for i in 1:2
        a24 = A_to_a24(Es[i])
        a24, image_check = Montgomery_normalize(a24, [image_dim2[1][i]])
        A = Montgomery_coeff(a24)
        xP3check = image_check[1]
        if challenge(A, m) == chl
            return !is_infinity(xTPLe(xP3check, a24_to_a24pm(a24), ExponentOfThree - 1))
        end
    end
    @assert false
    return false
end