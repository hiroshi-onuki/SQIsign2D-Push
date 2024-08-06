# return (a, b) s.t. E[phi_*I] = <[a]P, [b]Q>, where (P, Q) = (phi(P0), phi(Q0))M
function kernel_coefficients(I::LeftIdeal, M::Matrix{BigInt}, l::Int, e::Int, Ms::Vector{Matrix{T}}) where T <: Integer
    N = BigInt(l)^e
    a, b = kernel_coefficients_E0(I, l, e, Ms)
    a, b = M * [a, b]
    if a % l != 0
        b = (b * invmod(a, N)) % N
        b < 0 && (b += N)
        return 1, b
    else
        a = (a * invmod(b, N)) % N
        a < 0 && (a += N)
        return a, 1
    end
end

# return (a, b) s.t. E0[I] = <[a]P0, [b]Q0>
function kernel_coefficients_E0(I::LeftIdeal, l::Int, e::Int, Ms::Vector{Matrix{T}}) where T <: Integer
    alpha = element_prime_to(I, l)
    M = alpha[1]*[1 0; 0 1] + alpha[2]*Ms[1] + alpha[3]*Ms[2] + alpha[4]*Ms[3]
    N = BigInt(l)^e
    if M[1, 1] % l != 0 || M[1, 2] % l != 0
        return M[1, 2], -M[1, 1]
    else
        return M[2, 2], -M[2, 1]
    end
end

# return a generator of E[I]
function kernel_generator(xP::Proj1{FqFieldElem}, xQ::Proj1{FqFieldElem}, xPQ::Proj1{FqFieldElem}, a24::Proj1{FqFieldElem},
        I::LeftIdeal, M::Matrix{BigInt}, l::Int, e::Int, Ms::Vector{Matrix{T}}) where T <: Integer
    a, b = kernel_coefficients(I, M, l, e, Ms)
    if a == 1
        return ladder3pt(b, xP, xQ, xPQ, a24)
    else
        return ladder3pt(a, xQ, xP, xPQ, a24)
    end
end

# I : left ideal of O0 s.t. I = I_1 I_2, n(I_1) = D and n(I_2) = 2^e for e <= ExponentForIsogeny
# a24 : the coefficient of E := E_0 / E_0[I_1]
# xP, xQ, xPQ : the fixed basis of E[2^ExponentFull] s.t. phi_I_2(P_0, Q_0)^t = (P, Q)M
# return the coefficient a24d of E' := E_0 / E_0[I_1 I_2],
# the fixed basis (P', Q') of E'[2^ExponentFull], and M' s.t. phi_J(P_0, Q_0) = (P', Q')M'
function short_ideal_to_isogeny(I::LeftIdeal, a24::Proj1{T}, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T},
    M::Matrix{BigInt}, D::Integer, e::Int, global_data::GlobalData,
    is_normalized::Bool, precomp_beta::QOrderElem, precomp_a::Integer, precomp_b::Integer) where T <: RingElem
    E0 = global_data.E0_data
    Fp2 = parent(a24.X)
    xPd = xDBLe(xP, a24, ExponentFull - e)
    xQd = xDBLe(xQ, a24, ExponentFull - e)
    xPQd = xDBLe(xPQ, a24, ExponentFull - e)

    # 2^e-isogeny corresponding to I_2
    ker = kernel_generator(xPd, xQd, xPQd, a24, I, M, 2, e, E0.Matrices_2e)
    eval_points = [xP, xQ, xPQ]
    if haskey(StrategiesDim1, e)
        a24d, images = two_e_iso(a24, ker, e, eval_points, StrategiesDim1[e])
    else
        strategy = compute_strategy(div(e, 2)-1, 1, 1)
        a24d, images = two_e_iso(a24, ker, e, eval_points, strategy)
    end
    if is_normalized
        a24d, images = Montgomery_normalize(a24d, images)
    end

    # compute beta in I s.t. J := I*\bar{beta}/n(I) has norm 2^ExpTor - a^2 - b^2
    a24_0 = E0.a24_0
    xP0 = E0.xP2e_id2iso_d2
    xQ0 = E0.xQ2e_id2iso_d2
    xPQ0 = E0.xPQ2e_id2iso_d2
    Mc = BigInt[1 0; 0 1]
    M_sqrt_d = E0.Matrices_2e[1]
    d = 1
    order_id = 0
    if precomp_beta == Quaternion_0
        cor_func(argN) = sum_of_two_squares(BigInt(2)^ExponentForId2IsoDim2 - argN)
        nI = BigInt(2)^e * D
        bound = nI << ExponentForId2IsoDim2
        beta, a, b, found = two_e_good_element(I, nI, cor_func, bound, IdealToIsogeny_2_e_good_attempts)
        while !found && order_id < length(global_data.orders_data)
            order_id += 1
            E0d = global_data.orders_data[order_id]
            d = E0d.d
            a24_0 = E0d.a24_0
            xP0 = E0d.xP2e_id2iso_d2
            xQ0 = E0d.xQ2e_id2iso_d2
            xPQ0 = E0d.xPQ2e_id2iso_d2
            M_sqrt_d = E0d.M_sqrt_d
            cor_func_d(argN) = sum_of_two_squares_d(BigInt(2)^ExponentForId2IsoDim2 - argN, d)
            nI = BigInt(2)^e * D * E0d.connecting_deg
            Id = involution_product(E0d.I, I)
            bound = nI << ExponentForId2IsoDim2
            beta, a, b, found = two_e_good_element(Id, nI, cor_func_d, bound, IdealToIsogeny_2_e_good_attempts)
            Mc = E0d.M
        end
        @assert found
    else
        beta, a, b = precomp_beta, precomp_a, precomp_b
    end
    order_id > 0 && (D *= global_data.orders_data[order_id].connecting_deg)

    # compute the images of the basis of E_0[2^ExponentFull] under the isogeny corresponding to J
    xP2t, xQ2t, xPQ2t = images
    beta_bar = involution(beta) # beta_bar = J \bar{I}
    M_beta_bar = beta_bar[1]*[1 0; 0 1] + beta_bar[2]*E0.Matrices_2e[1] + beta_bar[3]*E0.Matrices_2e[2] + beta_bar[4]*E0.Matrices_2e[3]
    c11, c21, c12, c22 = M * M_beta_bar * Mc
    xP2 = linear_comb_2_e(c11, c21, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    xQ2 = linear_comb_2_e(c12, c22, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    xPQ2 = linear_comb_2_e(c11-c12, c21-c22, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    xP2 = xDBLe(xP2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)
    xQ2 = xDBLe(xQ2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)
    xPQ2 = xDBLe(xPQ2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)

    # compute the images of the basis of E_0[2^ExponentFull] under norm(I_2)(a + bi)
    c11, c21, c12, c22 = D * ([a 0; 0 a] + b * M_sqrt_d)
    xP1 = linear_comb_2_e(c11, c21, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)
    xQ1 = linear_comb_2_e(c12, c22, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)
    xPQ1 = linear_comb_2_e(c11-c12, c21-c22, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)

    # fixed basis of E'[2^ExponentFull]
    xPd, xQd, xPQd = torsion_basis(a24d, ExponentFull)
    xP2_I = linear_comb_2_e(M[1,1], M[2,1], xP2t, xQ2t, xPQ2t, a24d, ExponentFull)

    # compute (2,2)-isogenies
    P1P2 = CouplePoint(xP1, xP2)
    Q1Q2 = CouplePoint(xQ1, xQ2)
    PQ1PQ2 = CouplePoint(xPQ1, xPQ2)
    O1 = infinity_point(Fp2)
    O1Pd = CouplePoint(O1, xPd)
    O1Qd = CouplePoint(O1, xQd)
    O1PQd = CouplePoint(O1, xPQd)
    eval_points = [O1Pd, O1Qd, O1PQd]
    order_id == 0 && push!(eval_points, CouplePoint(O1, xP2_I))
    Es, images = product_isogeny(a24_0, a24d, P1P2, Q1Q2, PQ1PQ2, eval_points, ExponentForId2IsoDim2, StrategyId2IsoDim2)

    # isomorphism to E0 or E0d
    if order_id == 0
        if Es[1] == Proj1(E0.A0) || Es[1] == Proj1(E0.A0d) || Es[1] == Proj1(E0.A0dd)
            idx = 1
        else
            idx = 2
        end
        xPdd, xQdd, xPQdd, xP0beta = E0.isomorphism_to_A0(Es[idx], [cp[idx] for cp in images])

        # adjust the post-composition by sqrt{-1}
        M_beta = beta[1]*[1 0; 0 1] + beta[2]*E0.Matrices_2e[1] + beta[3]*E0.Matrices_2e[2] + beta[4]*E0.Matrices_2e[3]
        beta_P0 = linear_comb_2_e(M_beta[1,1], M_beta[2,1], E0.xP2e, E0.xQ2e, E0.xPQ2e, E0.a24_0, ExponentFull)
        if xP0beta == beta_P0
        elseif xP0beta == -beta_P0
            # muliply by i
            xPdd = -xPdd
            xQdd = -xQdd
            xPQdd = -xPQdd
        else
            throw(ArgumentError("No good isogeny found"))
        end
    else
        E0d = global_data.orders_data[order_id]
        if jInvariant_A(Es[1]) == E0d.j_inv
            idx = 1
        else
            @assert jInvariant_A(Es[2]) == E0d.j_inv
            idx = 2
        end
        a24_0d = A_to_a24(Es[idx])
        if a24_0d != a24_0
            _, (xPdd, xQdd, xPQdd) = Montgomery_normalize(a24_0d, [cp[idx] for cp in images])
        else
            xPdd, xQdd, xPQdd = [cp[idx] for cp in images]
        end
    end

    # compute the matrix M' s.t. phi_J(P0, Q0) = (Pd, Qd)M'
    if order_id == 0
        Dc = 1
        c11, c21, c12, c22 = ec_bi_dlog_E0(xPdd, xQdd, xPQdd, E0)
    else
        Dc = E0d.connecting_deg
        c11, c21, c12, c22 = ec_bi_dlog_E0d(xPdd, xQdd, xPQdd, global_data, order_id)
    end
    D = (BigInt(2)^ExponentForId2IsoDim2 - a^2 - d * b^2) * Dc
    Md = invmod_2x2([c11 c12; c21 c22], BigInt(2)^ExponentFull) * D
    Md = (Md * invmod_2x2(Mc, BigInt(2)^ExponentFull)) .% BigInt(2)^ExponentFull

    return a24d, xPd, xQd, xPQd, Md, beta, D
end

# Almost the same as the previous function, but using extra degrees
# This function is used for precomputing isogenies between elliptic curves with CM by imaginary quadratic orders with small distriminants
function short_ideal_to_isogeny_for_precomputation(I::LeftIdeal, a24::Proj1{T}, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T},
    M::Matrix{BigInt}, D::Integer, e::Int, E0::E0Data, use_extdeg::Bool,
    precomp_beta::QOrderElem, precomp_a::Integer, precomp_b::Integer) where T <: RingElem
    Fp2 = parent(a24.X)
    xPd = xDBLe(xP, a24, ExponentFull - e)
    xQd = xDBLe(xQ, a24, ExponentFull - e)
    xPQd = xDBLe(xPQ, a24, ExponentFull - e)

    # 2^e-isogeny corresponding to I_2
    ker = kernel_generator(xPd, xQd, xPQd, a24, I, M, 2, e, E0.Matrices_2e)
    eval_points = [xP, xQ, xPQ]
    if use_extdeg
        push!(eval_points, ker)
        degs = Vector{Int}[]
        for i in 1:length(E0.DegreesOddTorsionBases)
            l = E0.DegreesOddTorsionBases[i]
            el = E0.ExponentsOddTorsionBases[i]
            push!(degs, [l, el])
            xPl, xQl, xPQl = E0.OddTorsionBases[i]
            ker_l = kernel_generator(xPl, xQl, xPQl, a24, I, M, l, el, E0.Matrices_odd[i])
            push!(eval_points, ker_l)
        end
        while length(degs) > 0
            # compute l^el-isogeny (no strategy because el is small)
            l, el = pop!(degs)
            for i in 1:el-1
                ker = eval_points[end]
                ker = ladder(l^(el-i), ker, a24)
                a24, eval_points = odd_isogeny(a24, ker, l, eval_points)
            end
            ker = pop!(eval_points)
            a24, eval_points = odd_isogeny(a24, ker, l, eval_points)
        end
        ker = pop!(eval_points)
    end
    if haskey(StrategiesDim1, e)
        a24d, images = two_e_iso(a24, ker, e, eval_points, StrategiesDim1[e])
    else
        strategy = compute_strategy(div(e, 2)-1, 1, 1)
        a24d, images = two_e_iso(a24, ker, e, eval_points, strategy)
    end
    a24d, images = Montgomery_normalize(a24d, images)

    # compute beta in I s.t. J := I*\bar{beta}/n(I) has norm 2^ExpTor - a^2 - b^2
    if precomp_beta == Quaternion_0
        cor_func(argN) = sum_of_two_squares(BigInt(2)^ExponentForId2IsoDim2 - argN)
        nI = BigInt(2)^e * D
        use_extdeg && (nI *= ExtraDegree)
        bound = nI << ExponentForId2IsoDim2
        beta, a, b, found = two_e_good_element(I, nI, cor_func, bound, IdealToIsogeny_2_e_good_attempts)
        !found && return infinity_point(Fp2), infinity_point(Fp2), infinity_point(Fp2), infinity_point(Fp2), BigInt[0 0; 0 0], Quaternion_0, BigInt(0), false
    else
        beta, a, b = precomp_beta, precomp_a, precomp_b
    end
    @assert isin(beta, I)
    @assert div(norm(beta), norm(I)) == BigInt(2)^ExponentForId2IsoDim2 - a^2 - b^2

    # compute the images of the basis of E_0[2^ExponentFull] under the isogeny corresponding to J
    xP2t, xQ2t, xPQ2t = images
    beta_bar = involution(beta) # beta_bar = J \bar{I}
    M_beta_bar = beta_bar[1]*[1 0; 0 1] + beta_bar[2]*E0.Matrices_2e[1] + beta_bar[3]*E0.Matrices_2e[2] + beta_bar[4]*E0.Matrices_2e[3]
    c11, c21, c12, c22 = M * M_beta_bar
    xP2 = linear_comb_2_e(c11, c21, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    xQ2 = linear_comb_2_e(c12, c22, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    xPQ2 = linear_comb_2_e(c11-c12, c21-c22, xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    @assert is_infinity(xDBLe(xP2, a24d, ExponentFull - e))
    @assert is_infinity(xDBLe(xQ2, a24d, ExponentFull - e))
    @assert is_infinity(xDBLe(xPQ2, a24d, ExponentFull - e))
    xP2 = xDBLe(xP2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)
    xQ2 = xDBLe(xQ2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)
    xPQ2 = xDBLe(xPQ2, a24d, ExponentFull - e - ExponentForId2IsoDim2 - 2)

    # compute the images of the basis of E_0[2^ExponentFull] under norm(I_2)(a + bi)
    c11, c21, c12, c22 = D * ([a 0; 0 a] + b * E0.Matrices_2e[1])
    a24_0 = E0.a24_0
    xP0 = xDBLe(E0.xP2e, a24_0, ExponentForId2IsoDim1)
    xQ0 = xDBLe(E0.xQ2e, a24_0, ExponentForId2IsoDim1)
    xPQ0 = xDBLe(E0.xPQ2e, a24_0, ExponentForId2IsoDim1)
    if use_extdeg # norm(I_2) = 2^e * ExtraDegree
        xP0 = ladder(ExtraDegree, xP0, a24_0)
        xQ0 = ladder(ExtraDegree, xQ0, a24_0)
        xPQ0 = ladder(ExtraDegree, xPQ0, a24_0)
    end
    xP1 = linear_comb_2_e(c11, c21, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)
    xQ1 = linear_comb_2_e(c12, c22, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)
    xPQ1 = linear_comb_2_e(c11-c12, c21-c22, xP0, xQ0, xPQ0, a24_0, ExponentForId2IsoDim2 + 2)

    # pairing check
    A1 = E0.A0
    P1 = Point(A1, xP1)
    Q1 = Point(A1, xQ1)
    PQ1 = add(P1, -Q1, Proj1(A1))
    if xPQ1 != Proj1(PQ1.X, PQ1.Z)
        Q1 = -Q1
    end
    PQ1 = add(P1, -Q1, Proj1(A1))
    @assert xPQ1 == Proj1(PQ1.X, PQ1.Z)

    A2 = Montgomery_coeff(a24d)
    P2 = Point(A2, xP2)
    Q2 = Point(A2, xQ2)
    PQ2 = add(P2, -Q2, Proj1(A2))
    if xPQ2 != Proj1(PQ2.X, PQ2.Z)
        Q2 = -Q2
    end
    PQ2 = add(P2, -Q2, Proj1(A2))
    @assert xPQ2 == Proj1(PQ2.X, PQ2.Z)

    Ptmp = Point(A1, xP0)
    Qtmp = Point(A1, xQ0)
    PQtmp = add(Ptmp, -Qtmp, Proj1(A1))
    if xPQ0 != Proj1(PQtmp.X, PQtmp.Z)
        Qtmp = -Qtmp
    end
    PQtmp = add(Ptmp, -Qtmp, Proj1(A1))
    @assert xPQ0 == Proj1(PQtmp.X, PQtmp.Z)

    @assert Weil_pairing_2power(A1, P1, Q1, ExponentForId2IsoDim2 + 2) == Weil_pairing_2power(A1, Ptmp, Qtmp, ExponentForId2IsoDim2 + 2)^(D^2 * (a^2 + b^2))
    @assert Weil_pairing_2power(A1, P1, Q1, ExponentForId2IsoDim2 + 2)^BigInt(2)^(ExponentForId2IsoDim2 + 1) != 1
    @assert Weil_pairing_2power(A2, P2, Q2, ExponentForId2IsoDim2 + 2)^BigInt(2)^(ExponentForId2IsoDim2 + 1) != 1
    # end of pairing check

    # fixed basis of E'[2^ExponentFull]
    xPd, xQd, xPQd = torsion_basis(a24d, ExponentFull)
    xP2_I = linear_comb_2_e(M[1,1], M[2,1], xP2t, xQ2t, xPQ2t, a24d, ExponentFull)
    @assert is_infinity(xDBLe(xP2t, a24d, ExponentFull))
    @assert is_infinity(xDBLe(xP2_I, a24d, ExponentFull))

    # compute (2,2)-isogenies
    P1P2 = CouplePoint(xP1, xP2)
    Q1Q2 = CouplePoint(xQ1, xQ2)
    PQ1PQ2 = CouplePoint(xPQ1, xPQ2)
    O1 = infinity_point(Fp2)
    O1Pd = CouplePoint(O1, xPd)
    O1Qd = CouplePoint(O1, xQd)
    O1PQd = CouplePoint(O1, xPQd)
    O1P2_I = CouplePoint(O1, xP2_I)
    Es, images = product_isogeny(a24_0, a24d, P1P2, Q1Q2, PQ1PQ2, [O1Pd, O1Qd, O1PQd, O1P2_I], ExponentForId2IsoDim2, StrategyId2IsoDim2)

    # isomorphism to A0
    if Es[1] == Proj1(E0.A0) || Es[1] == Proj1(E0.A0d) || Es[1] == Proj1(E0.A0dd)
        idx = 1
    else
        idx = 2
    end
    xPdd, xQdd, xPQdd, xP0beta = E0.isomorphism_to_A0(Es[idx], [cp[idx] for cp in images])
    @assert is_infinity(xDBLe(xPdd, a24_0, ExponentFull))
    @assert is_infinity(xDBLe(xQdd, a24_0, ExponentFull))
    @assert is_infinity(xDBLe(xPQdd, a24_0, ExponentFull))
    @assert is_infinity(xDBLe(xP0beta, a24_0, ExponentFull))

    M_beta = beta[1]*[1 0; 0 1] + beta[2]*E0.Matrices_2e[1] + beta[3]*E0.Matrices_2e[2] + beta[4]*E0.Matrices_2e[3]
    beta_P0 = linear_comb_2_e(M_beta[1,1], M_beta[2,1], E0.xP2e, E0.xQ2e, E0.xPQ2e, E0.a24_0, ExponentFull)
    if xP0beta == beta_P0
    elseif xP0beta == -beta_P0
        # muliply by i
        xPdd = -xPdd
        xQdd = -xQdd
        xPQdd = -xPQdd
    else
        throw(ArgumentError("No good isogeny found"))
    end

    # pairing check
    A0 = E0.A0
    P0 = Point(A0, xPdd)
    Q0 = Point(A0, xQdd)
    PQ0 = add(P0, -Q0, Proj1(A0))
    if xPQdd != Proj1(PQ0.X, PQ0.Z)
        Q0 = -Q0
    end
    PQ0 = add(P0, -Q0, Proj1(A0))
    @assert xPQdd == Proj1(PQ0.X, PQ0.Z)
    P2 = Point(A2, xPd)
    Q2 = Point(A2, xQd)
    PQ2 = add(P2, -Q2, Proj1(A2))
    if xPQd != Proj1(PQ2.X, PQ2.Z)
        Q2 = -Q2
    end
    PQ2 = add(P2, -Q2, Proj1(A2))
    @assert xPQd == Proj1(PQ2.X, PQ2.Z)
    @assert Weil_pairing_2power(A0, P0, Q0, ExponentFull) == Weil_pairing_2power(A2, P2, Q2, ExponentFull)^(BigInt(2)^ExponentForId2IsoDim2 - a^2 - b^2)
    # end of pairing check  

    # compute the matrix M' s.t. phi_J(P0, Q0) = (Pd, Qd)M'
    c11, c21, c12, c22 = ec_bi_dlog_E0(xPdd, xQdd, xPQdd, E0)
    @assert xPdd == linear_comb_2_e(c11, c21, E0.xP2e, E0.xQ2e, E0.xPQ2e, E0.a24_0, ExponentFull)
    @assert xQdd == linear_comb_2_e(c12, c22, E0.xP2e, E0.xQ2e, E0.xPQ2e, E0.a24_0, ExponentFull)
    @assert xPQdd == linear_comb_2_e(c11-c12, c21-c22, E0.xP2e, E0.xQ2e, E0.xPQ2e, E0.a24_0, ExponentFull)
    Md = [c22 -c12; -c21 c11] * invmod((c11 * c22 - c12 * c21), BigInt(2)^ExponentFull) * (BigInt(2)^ExponentForId2IsoDim2 - a^2 - b^2)

    return a24d, xPd, xQd, xPQd, Md, beta, BigInt(2)^ExponentForId2IsoDim2 - a^2 - b^2, true
end


# isogeny E0 to E0/E0[I], where n(I) = ExtraDegree*2^e
# This is used only in test
function ideal_to_isogeny_from_O0(I::LeftIdeal, e::Int, global_data::GlobalData)
    E0 = global_data.E0
    a24 = E0.a24_0
    xP = E0.xP2e
    xQ = E0.xQ2e
    xPQ = E0.xPQ2e
    M = BigInt[1 0; 0 1]
    D = 1

    while e > 0
        println("e = ", e)
        e_d = min(e, ExponentForIsogenyDim1)
        I_d = larger_ideal(I, D*BigInt(2)^e_d)
        a24, xP, xQ, xPQ, M, beta, D_new = short_ideal_to_isogeny(I_d, a24, xP, xQ, xPQ, M, D, e_d, global_data, false, Quaternion_0, 0, 0)
        I = ideal_transform(I, beta, D*BigInt(2)^e_d)
        e -= e_d
        D = D_new
    end

    return a24, xP, xQ, xPQ, M, I, D
end