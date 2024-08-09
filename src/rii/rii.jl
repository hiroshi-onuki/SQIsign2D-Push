# return the codomain of a random d-isogeny from E0 and the images of the basis points
function RandIsogImages(d::BigInt, global_data::GlobalData, compute_odd_points::Bool=false)
    deg_dim2 = BigInt(1) << ExponentFull
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e

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
    xP0 = xDBLe(xP0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)
    xQ0 = xDBLe(xQ0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)
    xPQ0 = xDBLe(xPQ0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)

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
    xP0T1 = ladder(1 + d << (ExponentForDim1 + ExponentForDim2 - 2), xP0, a24_0)
    xQ0T1 = ladder3pt(d << (ExponentForDim1 + ExponentForDim2 - 2), xQ0, xP0, xPQ0, a24_0)
    xPQ0T1 = ladder3pt(D1*D2 - 1 - (d << (ExponentForDim1 + ExponentForDim2 - 2) % D1*D2), xQ0, xP0, xPQ0, a24_0)
    P0T1T2 = CouplePoint(xP0T1, xT2)
    Q0T1T2 = CouplePoint(xQ0T1, xT2)
    P0Q0T1 = CouplePoint(xP0T1, xT2)
    xPd, xQd, xPQd = torsion_basis(a24d, ExponentForDim1 + ExponentForDim2)
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
    w0 = global_data.E0_data.Weil_P2eQ2e^(BigInt(1) << (ExponentFull - ExponentForDim1 - ExponentForDim2))
    w1 = Weil_pairing_2power(affine(Es[idx]), x_tau_P0, x_tau_Q0, x_tau_PQ0, ExponentForDim1 + ExponentForDim2)
    if w1 != w0^d
        idx = 2
    end
    a24 = A_to_a24(Es[idx])
    x_tau_P0, x_tau_Q0, x_tau_PQ0 = images[1][idx], images[2][idx], images[3][idx]
    x_rho_P0, x_rho_Q0, x_rho_PQ0 = images[4][idx], images[5][idx], images[6][idx]

    # compute the images (R, S) := (hat(rho)*tau)(P0, Q0)
    n1, n2, n3, n4 = ec_bi_dlog(affine(Es[idx]), x_tau_P0, x_tau_Q0, x_tau_PQ0, x_rho_P0, x_rho_Q0, x_rho_PQ0, E0_data.dlog_data[ExponentForDim1 + ExponentForDim2])
    xR = linear_comb_2_e(n1, n2, xPd, xQd, xPQd, a24d, ExponentForDim1 + ExponentForDim2)
    xS = linear_comb_2_e(n3, n4, xPd, xQd, xPQd, a24d, ExponentForDim1 + ExponentForDim2)
    xRS = linear_comb_2_e(n1 - n3, n2 - n4, xPd, xQd, xPQd, a24d, ExponentForDim1 + ExponentForDim2)
    xR = ladder(D1 - d, xR, a24d)
    xS = ladder(D1 - d, xS, a24d)
    xRS = ladder(D1 - d, xRS, a24d)

    return a24d, xR, xS, xRS
end