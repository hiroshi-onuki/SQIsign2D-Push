
# return the codomain of a random d-isogeny from E0 and the images of the basis points
function RandIsogImages(d::BigInt, global_data::GlobalData, compute_odd_points::Bool=false)
    deg_dim2 = BigInt(1) << ExponentSum
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e
    xP0 = xDBLe(xP0, a24_0, ExponentFull - ExponentSum)
    xQ0 = xDBLe(xQ0, a24_0, ExponentFull - ExponentSum)
    xPQ0 = xDBLe(xPQ0, a24_0, ExponentFull - ExponentSum)

    alpha, _ = FullRepresentInteger(d*(deg_dim2 - d))

    a24, xP, xQ, xPQ, odd_images = d2isogeny_form_Esquare(a24_0, d, alpha, xP0, xQ0, xPQ0, global_data, compute_odd_points)
    if compute_odd_points
        return a24, xP, xQ, xPQ, odd_images, LeftIdeal(alpha, d)
    else
        return a24, xP, xQ, xPQ, LeftIdeal(alpha, d)
    end
end

# input: odd integer d s.t. 2^e2 - d is not divisible by 3, a point xK in E0 of order 3^e3
# output: the codomain of a random (d(2^e2 - d))-isogeny f, [c]f(xK), log_3(order(f(xK)), 
#    and [d^{-1}](f(P2e), f(Q2e)), where c in some integer not divisible by 3
function ComposedRandIsog(d::BigInt, xK::Proj1{T}, global_data::GlobalData) where T <: RingElem
    two_to_e2 = BigInt(1) << ExponentOfTwo
    three_to_e3 = BigInt(3)^ExponentOfThree
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.basis2e3e.xP, E0_data.basis2e3e.xQ, E0_data.basis2e3e.xPQ
    xP2e, xQ2e, xPQ2e = E0_data.basis2e.xP, E0_data.basis2e.xQ, E0_data.basis2e.xPQ
    xP3e, xQ3e, xPQ3e = E0_data.basis3e.xP, E0_data.basis3e.xQ, E0_data.basis3e.xPQ

    # alpha in End(E0) s.t. n(alpha) = d*(2^e2 - d)*3^e3
    # we decompose alpha = hat(phi)*hat(rho)*tau, where deg(phi) = 3^e3, deg(rho) = 2^e2 - d, deg(tau) = d
    alpha = Quaternion_0
    while gcd(alpha) % 3 == 0
        alpha, _ = FullRepresentInteger(d*(two_to_e2 - d)*three_to_e3)
    end

    # (3^e3)-isogeny phi: E0 -> Ed
    K = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, involution(alpha), 3, ExponentOfThree, E0_data.Matrices_3e)
    a24d, images = three_e_iso(a24_0, K, ExponentOfThree, [xP2e, xQ2e, xPQ2e], StrategiesDim1Three[ExponentOfThree])

    # (Pd, Qd) = [d^{-1}]hat(rho)*tau(P2, Q2) = [(3^e3 * d)^{-1}]phi*alpha(P2e, Q2e)
    xPd, xQd, xPQd = images
    c = invmod(d*three_to_e3, two_to_e2)
    xPd, xQd, xPQd = action_on_torsion_basis(alpha, a24d, xPd, xQd, xPQd, E0_data, c)

    # the kernel of the (2^e2, 2^e2)-isogeny is <(P2e, Pd), (Q2e, Qd)>
    K1 = CouplePoint(xP2e, xPd)
    K2 = CouplePoint(xQ2e, xQd)
    K12 = CouplePoint(xPQ2e, xPQd)

    # points to be evaluated by the isogeny
    O = infinity_point(global_data.Fp2)
    xP2e_d, xQ2e_d, xPQ2e_d = torsion_basis(a24d, ExponentOfTwo)
    xP3e_d, xQ3e_d, xPQ3e_d = torsion_basis(a24d, 3, ExponentOfThree)
    OP2e_d = CouplePoint(O, xP2e_d)
    OQ2e_d = CouplePoint(O, xQ2e_d)
    OPQ2e_d = CouplePoint(O, xPQ2e_d)
    OP3e_d = CouplePoint(O, xP3e_d)
    OQ3e_d = CouplePoint(O, xQ3e_d)
    OPQ3e_d = CouplePoint(O, xPQ3e_d)
    KO = CouplePoint(xK, O)

    eval_points = [OP2e_d, OQ2e_d, OPQ2e_d, OP3e_d, OQ3e_d, OPQ3e_d, KO]

    # (2^e2, 2^e2)-isogeny
    Es, images = product_isogeny_sqrt(a24_0, a24d, K1, K2, K12, eval_points, ExponentOfTwo, StrategiesDim2[ExponentOfTwo])

    idx = 1
    a24 = A_to_a24(Es[idx])
    x_hatrho_P2e_d, x_hatrho_Q2e_d, x_hatrho_PQ2e_d = images[1][idx], images[2][idx], images[3][idx]

    w0 = Weil_pairing_2power(Montgomery_coeff(a24d), xP2e_d, xQ2e_d, xPQ2e_d, ExponentOfTwo)
    w1 = Weil_pairing_2power(affine(Es[idx]), x_hatrho_P2e_d, x_hatrho_Q2e_d, x_hatrho_PQ2e_d, ExponentOfTwo)
    if w1 != w0^(two_to_e2 - d)
        idx = 2
    end
    a24 = A_to_a24(Es[idx])

    # check
    x_hatrho_P2e_d, x_hatrho_Q2e_d, x_hatrho_PQ2e_d = images[1][idx], images[2][idx], images[3][idx]
    w1 = Weil_pairing_2power(affine(Es[idx]), x_hatrho_P2e_d, x_hatrho_Q2e_d, x_hatrho_PQ2e_d, ExponentOfTwo)
    @assert w1 == w0^(two_to_e2 - d)

    x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d = images[4][idx], images[5][idx], images[6][idx]
    x_tau_K = images[7][idx]
    @assert is_infinity(ladder(three_to_e3, x_hatrho_P3e_d, a24))
    @assert is_infinity(ladder(three_to_e3, x_hatrho_Q3e_d, a24))
    @assert is_infinity(ladder(three_to_e3, x_hatrho_PQ3e_d, a24))
    @assert is_infinity(ladder(three_to_e3, x_tau_K, a24))
    @assert !is_infinity(ladder(div(three_to_e3, 3), x_hatrho_P3e_d, a24))
    @assert !is_infinity(ladder(div(three_to_e3, 3), x_hatrho_Q3e_d, a24))
    @assert !is_infinity(ladder(div(three_to_e3, 3), x_hatrho_PQ3e_d, a24))
    u, v = bi_dlog_odd_prime_power(Montgomery_coeff(a24), x_tau_K, x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d, 3, ExponentOfThree)
    u < 0 && (u += three_to_e3)
    v < 0 && (v += three_to_e3)
    e_u = valuation(u, 3)
    e_v = valuation(v, 3)
    if e_u < e_v
        u = div(u, BigInt(3)^e_u)
        v = div(v, BigInt(3)^e_u)
        xP3e_d = ladder(BigInt(3)^e_u, xP3e_d, a24)
        xQ3e_d = ladder(BigInt(3)^e_u, xQ3e_d, a24)
        xPQ3e_d = ladder(BigInt(3)^e_u, xPQ3e_d, a24)
        u_inv = invmod(u, BigInt(3)^(ExponentOfThree - e_u))
        xKd = ladder3pt(v * u_inv, xP3e_d, xQ3e_d, xPQ3e_d, a24d)

        # check
        x_hatrho_P3e_d = ladder(BigInt(3)^e_u, x_hatrho_P3e_d, a24)
        x_hatrho_Q3e_d = ladder(BigInt(3)^e_u, x_hatrho_Q3e_d, a24)
        x_hatrho_PQ3e_d = ladder(BigInt(3)^e_u, x_hatrho_PQ3e_d, a24)
        x_tau_K = ladder(u_inv, x_tau_K, a24)
        @assert x_tau_K == ladder3pt(v * u_inv, x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d, a24)
    else
        u = div(u, BigInt(3)^e_v)
        v = div(v, BigInt(3)^e_v)
        xP3e_d = ladder(BigInt(3)^e_v, xP3e_d, a24)
        xQ3e_d = ladder(BigInt(3)^e_v, xQ3e_d, a24)
        xPQ3e_d = ladder(BigInt(3)^e_v, xPQ3e_d, a24)
        v_inv = invmod(v, BigInt(3)^(ExponentOfThree - e_v))
        xKd = ladder3pt(u * v_inv, xQ3e_d, xP3e_d, xPQ3e_d, a24d)

        # check
        x_hatrho_P3e_d = ladder(BigInt(3)^e_v, x_hatrho_P3e_d, a24)
        x_hatrho_Q3e_d = ladder(BigInt(3)^e_v, x_hatrho_Q3e_d, a24)
        x_hatrho_PQ3e_d = ladder(BigInt(3)^e_v, x_hatrho_PQ3e_d, a24)
        x_tau_K = ladder(v_inv, x_tau_K, a24)
        @assert x_tau_K == ladder3pt(u * v_inv, x_hatrho_Q3e_d, x_hatrho_P3e_d, x_hatrho_PQ3e_d, a24)
    end

    return a24d, xKd, ExponentOfThree - min(e_u, e_v), xPd, xQd, xPQd
end

# return the codomain of a random d-isogeny from E and the image of (P, Q),
# where there exist 2^b-isogenies E0 -(tau_1)-> Em -tau_2-> E
# s.t. ker(tau_1) = <P0 + s0 Q0> and ker(tau_2) = <Pm + sm Qm>,
# and P, Q are in E[2^(a+b)] satisfying hat(tau_2) * hat(tau_1)(P, Q) = (P0, Q0) Mm M0
function PushRandIsog(d::BigInt, a24m::Proj1{T}, s0::BigInt, sm::BigInt, xPm::Proj1{T}, xQm::Proj1{T}, xPQm::Proj1{T}, 
        M0::Matrix{BigInt}, Mm::Matrix{BigInt}, global_data::GlobalData) where T <: RingElem
    two_to_ab = BigInt(1) << ExponentSum

    # d*(D1 - d)-isogeny: E0 -> F0d
    a24F0d, xR0d, xS0d, xRS0d = ComposedRandIsog(d, global_data)

    # D2-isogeny: F0d -> Fmd
    xR_D1 = xDBLe(xR0d, a24F0d, ExponentForDim2)
    xS_D1 = xDBLe(xS0d, a24F0d, ExponentForDim2)
    xRS_D1 = xDBLe(xRS0d, a24F0d, ExponentForDim2)
    K = ladder3pt(s0, xR_D1, xS_D1, xRS_D1, a24F0d)
    a24Fmd, (xRd, xSd, xRSd) = two_e_iso(a24F0d, K, ExponentForDim1, [xR0d, xS0d, xRS0d], StrategiesDim1[ExponentForDim1])
    xRmd, xSmd, xRSmd = action_of_matrix(M0, a24Fmd, xRd, xSd, xRSd, ExponentSum)

    # (D1, D1)-isogeny: Em times Fmd -> Fm times _
    # kernel
    xP1 = ladder(d << ExponentForDim1, xPm, a24m)
    xQ1 = ladder(d << ExponentForDim1, xQm, a24m)
    xPQ1 = ladder(d << ExponentForDim1, xPQm, a24m)
    P1P2 = CouplePoint(xP1, xRmd)
    Q1Q2 = CouplePoint(xQ1, xSmd)
    PQ1PQ2 = CouplePoint(xPQ1, xRSmd)
    # points evaluated by the isogeny
    O = infinity_point(global_data.Fp2)
    T1 = xDBLe(xP1, a24m, ExponentForDim2 - 2)
    T2 = xDBLe(xRmd, a24Fmd, ExponentForDim2 - 2)
    PmO = CouplePoint(xPm, O)
    QmO = CouplePoint(xQm, O)
    PQmO = CouplePoint(xPQm, O)
    xPmT1 = ladder(1 + d << (ExponentSum - 2), xPm, a24m)
    xQmT1 = ladder3pt(d << (ExponentSum - 2), xQm, xPm, xPQm, a24m)
    xPQmT1 = ladder3pt(two_to_ab - 1 - (d << (ExponentSum - 2) % two_to_ab), xQm, xPm, xPQm, a24m)
    PmT1T2 = CouplePoint(xPmT1, T2)
    QmT1T2 = CouplePoint(xQmT1, T2)
    PQmT1T2 = CouplePoint(xPQmT1, T2)
    eval_points = [PmO, QmO, PQmO]
    eval_points_T = [PmT1T2, QmT1T2, PQmT1T2]
    # isogeny
    Es, images = product_isogeny_sqrt(a24m, a24Fmd, P1P2, Q1Q2, PQ1PQ2, eval_points, eval_points_T, ExponentForDim2, StrategiesDim2[ExponentForDim2])
    idx = 1
    xRm, xSm, xRSm = images[1][idx], images[2][idx], images[3][idx]
    w0 = Weil_pairing_2power(Montgomery_coeff(a24m), xPm, xQm, xPQm, ExponentSum)
    w1 = Weil_pairing_2power(Montgomery_coeff(A_to_a24(Es[idx])), xRm, xSm, xRSm, ExponentSum)
    if w1 != w0^d
        idx = 2
    end
    a24Fm = A_to_a24(Es[idx])
    xRm, xSm, xRSm = images[1][idx], images[2][idx], images[3][idx]

    # D2-isogeny: Fm -> F
    Rm_c = xDBLe(xRm, a24Fm, ExponentForDim2)
    Sm_c = xDBLe(xSm, a24Fm, ExponentForDim2)
    RSm_c = xDBLe(xRSm, a24Fm, ExponentForDim2)
    K = ladder3pt(sm, Rm_c, Sm_c, RSm_c, a24Fm)
    a24F, images = two_e_iso(a24Fm, K, ExponentForDim1, [xRm, xSm, xRSm], StrategiesDim1[ExponentForDim1])
    xR, xS, xRS = action_of_matrix(Mm, a24F, images[1], images[2], images[3], ExponentSum)
 
    return Montgomery_normalize(a24F, [xR, xS, xRS])
end