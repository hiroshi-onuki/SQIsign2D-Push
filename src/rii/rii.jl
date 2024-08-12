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

# return the codomain of a random d-isogeny from E and the images of (P, Q),
# where P, Q is the image of the fixed basis of E0[2^ExponentFull] under an isogeny corresponding to I
function GeneralizedRandomIsogImages(d::BigInt, a24::Proj1{T}, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T},
            I::LeftIdeal, nI::BigInt, global_data::GlobalData) where T <: RingElem
    N = d*((BigInt(1) << ExponentFull) - d)
    alpha = Quaternion_0

    # make alpha in I + Z s.t. n(alpha) = N
    C, D = EichlerModConstraint(I, nI, Quaternion_1, Quaternion_1, false)
    N_CD = p * (C^2 + D^2)
    N_N_CD = (N * invmod(N_CD, nI)) % nI
    lambda = sqrt_mod(4*N_N_CD, nI)
    tries = KLPT_keygen_number_strong_approx
    found = false
    for _ in 1:10
        alpha, found = FullStrongApproximation(nI, C, D, lambda, 4*N, tries)
        found && break
        tries *= 2
    end
    @assert found

    a24, xP, xQ, xPQ, _ = d2isogeny_form_Esquare(a24, d, alpha, xP, xQ, xPQ, global_data)

    return a24, xP, xQ, xPQ
end

# return Ed, (R, S) s.t. there exists a (d(D1 - d))-isogeny E0 -> Ed sending (P0, Q0) to (R, S)
function ComposedRandIsog(d::BigInt, global_data::GlobalData)
    D1 = BigInt(1) << ExponentForDim2
    D2 = BigInt(1) << ExponentForDim1
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e
    xP0 = xDBLe(xP0, a24_0, ExponentFull - ExponentSum)
    xQ0 = xDBLe(xQ0, a24_0, ExponentFull - ExponentSum)
    xPQ0 = xDBLe(xPQ0, a24_0, ExponentFull - ExponentSum)

    # alpha in End(E0) s.t. n(alpha) = d*(D1 - d)*D2
    # we decompose alpha = hat(phi)*hat(rho)*tau, where deg(phi) = D2, deg(rho) = D1 - d, deg(tau) = d
    alpha = Quaternion_0
    while gcd(alpha) % 2 == 0
        alpha, _ = FullRepresentInteger(d*(D1 - d)*D2)
    end

    # D2-isogeny phi: E0 -> Ed
    xP0D2 = xDBLe(xP0, a24_0, ExponentForDim2)
    xQ0D2 = xDBLe(xQ0, a24_0, ExponentForDim2)
    xPQ0D2 = xDBLe(xPQ0, a24_0, ExponentForDim2)
    K = kernel_generator(xP0D2, xQ0D2, xPQ0D2, a24_0, involution(alpha), 2, ExponentForDim1, E0_data.Matrices_2e)
    a24d, images = two_e_iso(a24_0, K, ExponentForDim1, [xP0, xQ0, xPQ0], StrategiesDim1[ExponentForDim1])

    # (P1, Q1) = [d*D2] (P0, Q0)
    xP1 = ladder(d << ExponentForDim1, xP0, a24_0)
    xQ1 = ladder(d << ExponentForDim1, xQ0, a24_0)
    xPQ1 = ladder(d << ExponentForDim1, xPQ0, a24_0)

    # (P2, Q2) = phi * alpha (P0, Q0) = hat(rho)*tau([D2] (P0, Q0))
    xPd, xQd, xPQd = images
    xP2, xQ2, xPQ2 = action_on_torsion_basis(alpha, a24d, xPd, xQd, xPQd, E0_data)

    # the kernel of the (D2, D2)-isogeny is <(P1, P2), (Q1, Q2)>
    P1P2 = CouplePoint(xP1, xP2)
    Q1Q2 = CouplePoint(xQ1, xQ2)
    PQ1PQ2 = CouplePoint(xPQ1, xPQ2)

    # compute points evaluated by the (D2, D2)-isogeny with kernel <(P1, P2), (Q1, Q2)>
    xT1 = xDBLe(xP1, a24_0, ExponentForDim2 - 2)
    xT2 = xDBLe(xP2, a24d, ExponentForDim2 - 2)
    O = infinity_point(global_data.Fp2)
    P0O = CouplePoint(xP0, O)
    Q0O = CouplePoint(xQ0, O)
    P0Q0 = CouplePoint(xPQ0, O)
    xP0T1 = ladder(1 + d << (ExponentSum - 2), xP0, a24_0)
    xQ0T1 = ladder3pt(d << (ExponentSum - 2), xQ0, xP0, xPQ0, a24_0)
    xPQ0T1 = ladder3pt(D1*D2 - 1 - (d << (ExponentSum - 2) % D1*D2), xQ0, xP0, xPQ0, a24_0)
    P0T1T2 = CouplePoint(xP0T1, xT2)
    Q0T1T2 = CouplePoint(xQ0T1, xT2)
    P0Q0T1 = CouplePoint(xP0T1, xT2)
    xPd, xQd, xPQd = torsion_basis(a24d, ExponentSum)
    OPd = CouplePoint(O, xPd)
    OQd = CouplePoint(O, xQd)
    OPQd = CouplePoint(O, xPQd)
    xPdT2 = x_add_sub(xPd, xT2, a24d)
    xQdT2 = x_add_sub(xQd, xT2, a24d)
    xPQdT2 = x_add_sub(xPQd, xT2, a24d)
    T1PdT2 = CouplePoint(xT1, xPdT2)
    T1QdT2 = CouplePoint(xT1, xQdT2)
    T1PQdT2 = CouplePoint(xT1, xPQdT2)
    eval_points = [P0O, Q0O, P0Q0, OPd, OQd, OPQd]
    eval_points_T = [P0T1T2, Q0T1T2, P0Q0T1, T1PdT2, T1QdT2, T1PQdT2]

    # (D1, D1)-isogeny
    Es, images = product_isogeny_sqrt(a24_0, a24d, P1P2, Q1Q2, PQ1PQ2, eval_points, eval_points_T, ExponentForDim2, StrategiesDim2[ExponentForDim2])

    idx = 1
    x_tau_P0, x_tau_Q0, x_tau_PQ0 = images[1][idx], images[2][idx], images[3][idx]
    w0 = global_data.E0_data.Weil_P2eQ2e^(BigInt(1) << (ExponentFull - ExponentSum))
    w1 = Weil_pairing_2power(affine(Es[idx]), x_tau_P0, x_tau_Q0, x_tau_PQ0, ExponentSum)
    if w1 != w0^d
        idx = 2
    end
    a24 = A_to_a24(Es[idx])
    x_tau_P0, x_tau_Q0, x_tau_PQ0 = images[1][idx], images[2][idx], images[3][idx]
    x_rho_P0, x_rho_Q0, x_rho_PQ0 = images[4][idx], images[5][idx], images[6][idx]

    # compute the images (R, S) := (hat(rho)*tau)(P0, Q0)
    n1, n2, n3, n4 = ec_bi_dlog(affine(Es[idx]), x_tau_P0, x_tau_Q0, x_tau_PQ0, x_rho_P0, x_rho_Q0, x_rho_PQ0, E0_data.dlog_data[ExponentSum])
    xR, xS, xRS = action_of_matrix([n1 n3; n2 n4], a24d, xPd, xQd, xPQd, ExponentSum)
    xR = ladder(D1 - d, xR, a24d)
    xS = ladder(D1 - d, xS, a24d)
    xRS = ladder(D1 - d, xRS, a24d)

    return a24d, xR, xS, xRS
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
    w1 = Weil_pairing_2power(Montgomery_coeff(a24m), xP1, xQ1, xPQ1, ExponentForDim2)
    w2 = Weil_pairing_2power(Montgomery_coeff(a24Fmd), xRmd, xSmd, xRSmd, ExponentForDim2)
    @assert w1 * w2 == 1
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