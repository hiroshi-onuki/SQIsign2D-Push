# return alpha = (ai + bj + cij)/N s.t. alpha^2 = -d
function sqrt_in_quaternion(d::Integer)
    N = p
    while true
        N = rand(p+2:10*p)
        !is_prime(N) && continue
        a = (BigInt(sqrtmod(ZZ(d), ZZ(p))) * N) % p
        M = div(d * N^2 - a^2, p)
        b, c, found = sum_of_two_squares(M)
        if found
            return a, b, c, N
        end
    end
end

# compute the information of the elliptic curve with CM by Z[\sqrt{-d}], wherd d is a small prime 
function compute_order_d(E0::E0Data, d::Int)
    order2e = BigInt(2)^ExponentFull

    found = false
    a24 = E0.a24_0
    xP, xQ, xPQ = E0.xP2e, E0.xQ2e, E0.xPQ2e
    alpha = QOrderElem(0)
    I = LeftIdeal(Quaternion_0, Quaternion_0, Quaternion_0, Quaternion_0)
    M = BigInt[1 0; 0 1]
    Ma = BigInt[1 0; 0 1]
    N = 1
    D = 1
    while !found
        a, b, c, N = sqrt_in_quaternion(d)
        alpha = order_elem_from_standard_basis(0, a, b, c)
        Ma = alpha[1] * [1 0; 0 1] + alpha[2] * E0.Matrices_2e[1] + alpha[3] * E0.Matrices_2e[2] + alpha[4] * E0.Matrices_2e[3]
        @assert alpha * alpha == QOrderElem(-d * N^2)

        I = LeftIdeal(alpha, N)
        alpha, found = KLPT(I, N)
        !found && continue
        alpha = div(alpha, gcd(alpha))
        J = ideal_transform(I, alpha, N)

        e = Int(round(log(2, div(norm(alpha), N*ExtraDegree))))
        @assert norm(J) == BigInt(2)^e * ExtraDegree
        alpha = involution(alpha)
        a24 = E0.a24_0
        xP, xQ, xPQ = E0.xP2e, E0.xQ2e, E0.xPQ2e
        M = BigInt[1 0; 0 1]
        is_first = true
        extdeg = ExtraDegree
        D = 1
        while e > 0
            ed = min(e, ExponentForIsogenyDim1Precompute)
            n_I_d = D * extdeg * BigInt(2)^ed
            I_d = larger_ideal(J, n_I_d)
            a24, xP, xQ, xPQ, M, beta, D, found = short_ideal_to_isogeny_for_precomputation(I_d, a24, xP, xQ, xPQ, M, D, ed, E0, is_first, Quaternion_0, 0, 0)
            !found && break
            J = ideal_transform(J, beta, n_I_d)
            alpha = div(alpha * involution(beta), n_I_d)
            e -= ed
            is_first = false
            extdeg = 1
        end
    end

    alpha = involution(alpha)
    Malpha = alpha[1] * [1 0; 0 1] + alpha[2] * E0.Matrices_2e[1] + alpha[3] * E0.Matrices_2e[2] + alpha[4] * E0.Matrices_2e[3]
    M = (M * Malpha * invmod(D, order2e)) .% order2e
    Minv = invmod_2x2(M, order2e)
    Mdual = (Minv * N) .% order2e
    Msqrtd = (M * Ma * Minv * invmod(N, order2e)) .% order2e

    xPs = xDBLe(xP, a24, ExponentFull - ExponentForTorsion)
    xQs = xDBLe(xQ, a24, ExponentFull - ExponentForTorsion)
    xPQs = xDBLe(xPQ, a24, ExponentFull - ExponentForTorsion)

    A = Montgomery_coeff(a24)
    P = Point(A, xP)
    Q = Point(A, xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    tp_table_P = make_pairing_table(A, P, ExponentFull)
    tp_table_Q = make_pairing_table(A, Q, ExponentFull)
    tp_PQ = Tate_pairing_P0(Q, tp_table_P, Cofactor)
    base_dlog = fq_dlog_power_of_2_opt(tp_PQ, E0.dlog_data_full)
    base_dlog = invmod(base_dlog, order2e)

    return OrderData(d, A, jInvariant_a24(a24), a24, xP, xQ, xPQ, xPs, xQs, xPQs, I, Mdual, N, Msqrtd, tp_table_P, tp_table_Q, base_dlog)
end

# compute the information of the elliptic curve with CM by Z[\sqrt{-d}] from precomputed values
function compute_order(Fp2::FqField, E0::E0Data, order_data::Function)
    d, A, I, M, N, M_sqrt_d = order_data()
    A = Fp2(A)
    a24 = A_to_a24(A)

    xP, xQ, xPQ = torsion_basis(a24, ExponentFull)
    xPs = xDBLe(xP, a24, ExponentFull - ExponentForTorsion)
    xQs = xDBLe(xQ, a24, ExponentFull - ExponentForTorsion)
    xPQs = xDBLe(xPQ, a24, ExponentFull - ExponentForTorsion)

    P = Point(A, xP)
    Q = Point(A, xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    tp_table_P = make_pairing_table(A, P, ExponentFull)
    tp_table_Q = make_pairing_table(A, Q, ExponentFull)
    tp_PQ = Tate_pairing_P0(Q, tp_table_P, Cofactor)
    base_dlog = fq_dlog_power_of_2_opt(tp_PQ, E0.dlog_data_full)
    base_dlog = invmod(base_dlog, BigInt(2)^ExponentFull)

    return OrderData(d, A, jInvariant_a24(a24), a24, xP, xQ, xPQ, xPs, xQs, xPQs, I, M, N, M_sqrt_d, tp_table_P, tp_table_Q, base_dlog)
end