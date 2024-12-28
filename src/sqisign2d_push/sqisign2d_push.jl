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

    # find alpha in bar(Icom)IskIcha suitable for the response
    IskIchl = intersection(I2sk, Ichl)
    IskIchl = div(IskIchl * alpha_sk, two_to_e2^2)
    I = involution_product(Icom, IskIchl)
    @assert norm(I) == three_to_e3^5
    alpha, q, found = element_for_response(I, norm(I), ExponentOfTwo)
    @assert found
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

    # compute Echl_d
    if e_dim1 > 0
        xP2chl_fix, xQ2chl_fix, xPQ2chl_fix = torsion_basis(a24chl, e_dim1)
        xP2chl_short = xDBLe(xP2chl, a24chl, ExponentOfTwo - e_dim1)
        xQ2chl_short = xDBLe(xQ2chl, a24chl, ExponentOfTwo - e_dim1)
        xPQ2chl_short = xDBLe(xPQ2chl, a24chl, ExponentOfTwo - e_dim1)
        n1, n2, n3, n4 = ec_bi_dlog_odd_prime_power(Montgomery_coeff(a24chl), xP2chl_short, xQ2chl_short, xPQ2chl_short, xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, 2, e_dim1)
        M = [n1 n3; n2 n4]
        @assert xP2chl_short == linear_comb_2_e(n1, n2, xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, a24chl, e_dim1)
        @assert xQ2chl_short == linear_comb_2_e(n3, n4, xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, a24chl, e_dim1)
        @assert xPQ2chl_short == linear_comb_2_e(n1 - n3, n2 - n4, xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, a24chl, e_dim1)
        a, b = kernel_coefficients(alpha, 2, e_dim1, global_data.E0_data.Matrices_2e)
        a, b = M * [a, b]
        if a % 2 != 0
            coeff_ker_dim1 = (b * invmod(a, two_to_e_dim1)) % two_to_e_dim1
            coeff_ker_dim1_isP = 0
            xKchl_d = ladder3pt(coeff_ker_dim1, xP2chl_fix, xQ2chl_fix, xPQ2chl_fix, a24chl)
        else
            coeff_ker_dim1 = (a * invmod(b, two_to_e_dim1)) % two_to_e_dim1
            coeff_ker_dim1_isP = 1
            xKchl_d = ladder3pt(coeff_ker_dim1, xQ2chl_fix, xP2chl_fix, xPQ2chl_fix, a24chl)
        end
        a24chl_d, (xP2chl_d, xQ2chl_d, xPQ2chl_d) = two_e_iso(a24chl, xKchl_d, e_dim1, [xP2chl, xQ2chl, xPQ2chl])
        a24chl_d, (xP2chl_d, xQ2chl_d, xPQ2chl_d) = Montgomery_normalize(a24chl_d, [xP2chl_d, xQ2chl_d, xPQ2chl_d])
    else
        coeff_ker_dim1 = 0
        coeff_ker_dim1_isP = 0
        a24chl_d = a24chl
        xP2chl_d = xP2chl
        xQ2chl_d = xQ2chl
        xPQ2chl_d = xPQ2chl
    end
    c = invmod(three_to_e3^2 * ChallengeDegree, two_to_e2)
    xP2chl_d, xQ2chl_d, xPQ2chl_d = action_on_torsion_basis(involution(alpha), a24chl_d, xP2chl_d, xQ2chl_d, xPQ2chl_d, global_data.E0_data, c)
    @assert is_infinity(xDBLe(xP2chl_d, a24chl_d, ExponentOfTwo - e_dim1))
    @assert is_infinity(xDBLe(xQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1))
    @assert is_infinity(xDBLe(xPQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1))
    @assert !is_infinity(xDBLe(xP2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - 1))
    @assert !is_infinity(xDBLe(xQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - 1))
    @assert !is_infinity(xDBLe(xPQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - 1))

    e = ExponentOfTwo - e_dim1 - e_dim2
    if e >= 2
        e_dim2_torsion = e_dim2 + 2
    else
        e_dim2_torsion = e_dim2
    end
    xP2chl_d = xDBLe(xP2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)
    xQ2chl_d = xDBLe(xQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)
    xPQ2chl_d = xDBLe(xPQ2chl_d, a24chl_d, ExponentOfTwo - e_dim1 - e_dim2_torsion)

    xP2chl_d_fix, xQ2chl_d_fix, xPQ2chl_d_fix = torsion_basis(a24chl_d, e_dim2_torsion)
    n1, n2, n3, n4 = ec_bi_dlog_odd_prime_power(Montgomery_coeff(a24chl_d), xP2chl_d, xQ2chl_d, xPQ2chl_d, xP2chl_d_fix, xQ2chl_d_fix, xPQ2chl_d_fix, 2, e_dim2_torsion)
    Mchl_d = [n1 n3; n2 n4]

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
    xP2aux = xDBLe(xP2aux, a24aux, ExponentOfTwo - e_dim2_torsion)
    xQ2aux = xDBLe(xQ2aux, a24aux, ExponentOfTwo - e_dim2_torsion)
    xPQ2aux = xDBLe(xPQ2aux, a24aux, ExponentOfTwo - e_dim2_torsion)
    xP2aux_fix, xQ2aux_fix, xPQ2aux_fix = torsion_basis(a24aux, e_dim2_torsion)
    n1, n2, n3, n4 = ec_bi_dlog_odd_prime_power(Montgomery_coeff(a24aux), xP2aux, xQ2aux, xPQ2aux, xP2aux_fix, xQ2aux_fix, xPQ2aux_fix, 2, e_dim2_torsion)
    Maux = [n1 n3; n2 n4]
    two_to_e_dim2_torsion = BigInt(1) << e_dim2_torsion
    M = (Maux * invmod_2x2(Mchl_d, two_to_e_dim2_torsion)) .% two_to_e_dim2_torsion
    a, b, c, d = M
    if a % 2 == 0
        b_inv = invmod(b, two_to_e_dim2_torsion)
        coeff_ker_dim2_1 = (a * b_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_2 = (c * b_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_3 = (d * b_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_isP = 1
        b_sqrt = sqrt_mod_2power(b^2 % two_to_e_dim2, e_dim2)
        is_adjust_sqrt = ((b - b_sqrt) % two_to_e_dim2 == 0 || (b + b_sqrt) % two_to_e_dim2 == 0) ? 0 : 1
    else
        a_inv = invmod(a, two_to_e_dim2_torsion)
        coeff_ker_dim2_1 = (b * a_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_2 = (c * a_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_3 = (d * a_inv) % two_to_e_dim2_torsion
        coeff_ker_dim2_isP = 0
        a_sqrt = sqrt_mod_2power(a^2 % two_to_e_dim2, e_dim2)
        is_adjust_sqrt = ((a - a_sqrt) % two_to_e_dim2 == 0 || (a + a_sqrt) % two_to_e_dim2 == 0) ? 0 : 1
    end

    xPcheck = linear_comb_2_e(M[1, 1], M[2, 1], xP2aux_fix, xQ2aux_fix, xPQ2aux_fix, a24aux, e_dim2_torsion)
    xQcheck = linear_comb_2_e(M[1, 2], M[2, 2], xP2aux_fix, xQ2aux_fix, xPQ2aux_fix, a24aux, e_dim2_torsion)
    xPQcheck = linear_comb_2_e(M[1, 1] - M[1, 2], M[2, 1] - M[2, 2], xP2aux_fix, xQ2aux_fix, xPQ2aux_fix, a24aux, e_dim2_torsion)

    # check by dim2 isogeny
    K1 = CouplePoint(xP2chl_d_fix, xPcheck)
    K2 = CouplePoint(xQ2chl_d_fix, xQcheck)
    K12 = CouplePoint(xPQ2chl_d_fix, xPQcheck)
    if e_dim2_torsion > e_dim2
        Es, _ = product_isogeny(a24chl_d, a24aux, K1, K2, K12, CouplePoint{FqFieldElem}[], e_dim2, StrategiesDim2[e_dim2])
    else
        Es, _ = product_isogeny_sqrt(a24chl_d, a24aux, K1, K2, K12, CouplePoint{FqFieldElem}[], e_dim2, StrategiesDim2[e_dim2])
    end
    @assert jInvariant_A(Es[1]) == jInvariant_a24(a24com) || jInvariant_A(Es[2]) == jInvariant_a24(a24com)

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
    len_coeff_dim1 = max(Int(ceil(e_dim1/8)), 1)
    len_coeff_dim2 = Dim2KernelCoeffByteLength + 1 - len_coeff_dim1
    sign[idx:idx+len_coeff_dim1-1] = integer_to_bytes(coeff_ker_dim1, len_coeff_dim1)
    idx += len_coeff_dim1
    sign[idx:idx+len_coeff_dim2-1] = integer_to_bytes(coeff_ker_dim2_1, len_coeff_dim2)
    idx += len_coeff_dim2
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(coeff_ker_dim2_2, Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx:idx+Dim2KernelCoeffByteLength-1] = integer_to_bytes(coeff_ker_dim2_3, Dim2KernelCoeffByteLength)
    idx += Dim2KernelCoeffByteLength
    sign[idx] = coeff_ker_dim1_isP
    idx += 1
    sign[idx] = (coeff_ker_dim2_isP << 1) | is_adjust_sqrt

    return sign
end

function verify(pk::FqFieldElem, sign::Vector{UInt8}, m::String, global_data::GlobalData)
    Apk = pk
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
    len_coeff_dim1 = max(Int(ceil(e_dim1/8)), 1)
    len_coeff_dim2 = Dim2KernelCoeffByteLength + 1 - len_coeff_dim1
    coeff_ker_dim1 = bytes_to_integer(sign[idx:idx+len_coeff_dim1-1])
    idx += len_coeff_dim1
    coeff_ker_dim2_1 = bytes_to_integer(sign[idx:idx+len_coeff_dim2-1])
    idx += len_coeff_dim2
    coeff_ker_dim2_2 = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    coeff_ker_dim2_3 = bytes_to_integer(sign[idx:idx+Dim2KernelCoeffByteLength-1])
    idx += Dim2KernelCoeffByteLength
    coeff_ker_dim1_isP = sign[idx]
    idx += 1
    coeff_ker_dim2_isP = sign[idx] >> 1
    is_adjust_sqrt = sign[idx] & 1
    println("e_dim2 = ", e_dim2, ", e_dim1 = ", e_dim1)

    # compute Echl
    xP3pk, xQ3pk, xPQ3pk = torsion_basis(a24pk, 3, ExponentOfThree)
    xKchl = ladder3pt(chl, xP3pk, xQ3pk, xPQ3pk, a24pk)
    a24chl, image_check = three_e_iso(a24pk, xKchl, ExponentOfThree, [xQ3pk], StrategiesDim1Three[ExponentOfThree])
    a24chl, image_check = Montgomery_normalize(a24chl, image_check)

    # compute Echl_d
    if e_dim1 > 0
        xP2chl, xQ2chl, xPQ2chl = torsion_basis(a24chl, e_dim1)
        if coeff_ker_dim1_isP == 1
            xKchl_d = ladder3pt(coeff_ker_dim1, xQ2chl, xP2chl, xPQ2chl, a24chl)
        else
            xKchl_d = ladder3pt(coeff_ker_dim1, xP2chl, xQ2chl, xPQ2chl, a24chl)
        end
        a24chl_d, image_check = two_e_iso(a24chl, xKchl_d, e_dim1, image_check)
        a24chl_d, image_check = Montgomery_normalize(a24chl_d, image_check)
    else
        a24chl_d = a24chl
    end
    if ExponentOfTwo - e_dim1 - e_dim2 >= 2
        e_dim2_torsion = e_dim2 + 2
    else
        e_dim2_torsion = e_dim2
    end
    xP2chl_d, xQ2chl_d, xPQ2chl_d = torsion_basis(a24chl_d, e_dim2_torsion)

    # compute kernel of dim2 isogeny on Eaux
    a24aux = A_to_a24(Aaux)
    xP2aux, xQ2aux, xPQ2aux = torsion_basis(a24aux, e_dim2_torsion)
    if coeff_ker_dim2_isP == 1
        xP2aux, xQ2aux, xPQ2aux = action_of_matrix([coeff_ker_dim2_1 coeff_ker_dim2_2; 1 coeff_ker_dim2_3], a24aux, xP2aux, xQ2aux, xPQ2aux, e_dim2_torsion)
    else
        xP2aux, xQ2aux, xPQ2aux = action_of_matrix([1 coeff_ker_dim2_2; coeff_ker_dim2_1 coeff_ker_dim2_3], a24aux, xP2aux, xQ2aux, xPQ2aux, e_dim2_torsion)
    end

    # adjust by scalar multiplication
    w_chl_prj, w_aux_prj = multi_Weil_pairing_2power([PairingData(a24chl_d, xP2chl_d, xQ2chl_d, xPQ2chl_d), PairingData(a24aux, xP2aux, xQ2aux, xPQ2aux)], e_dim2_torsion)
    w_chl_Zinv, w_aux_Zinv = batched_inversion([w_chl_prj.Z, w_aux_prj.Z])
    w_chl = w_chl_prj.X .* w_chl_Zinv
    w_aux = w_aux_prj.X .* w_aux_Zinv
    two_to_e_dim2 = BigInt(1) << e_dim2
    c = two_to_e_dim2 - (fp2_dlog(w_chl, w_aux, 2, e_dim2_torsion) % two_to_e_dim2)
    c = sqrt_mod_2power(c, e_dim2)
    if is_adjust_sqrt == 1
        c = (c + (two_to_e_dim2 >> 1)) % two_to_e_dim2
    end
    xP2aux = ladder(c, xP2aux, a24aux)
    xQ2aux = ladder(c, xQ2aux, a24aux)
    xPQ2aux = ladder(c, xPQ2aux, a24aux)

    # dim2 isogeny
    K1 = CouplePoint(xP2chl_d, xP2aux)
    K2 = CouplePoint(xQ2chl_d, xQ2aux)
    K12 = CouplePoint(xPQ2chl_d, xPQ2aux)
    O = infinity_point(global_data.Fp2)
    eval_point = [CouplePoint(image_check[1], O)]
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
            @assert is_infinity(xTPLe(xP3check, a24_to_a24pm(a24), ExponentOfThree))
            return !is_infinity(xTPLe(xP3check, a24_to_a24pm(a24), ExponentOfThree - 1))
        end
    end
    return false
end