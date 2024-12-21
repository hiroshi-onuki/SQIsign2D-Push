
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
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.basis2e3e.xP, E0_data.basis2e3e.xQ, E0_data.basis2e3e.xPQ
    xP2e, xQ2e, xPQ2e = E0_data.basis2e.xP, E0_data.basis2e.xQ, E0_data.basis2e.xPQ
    xP3e, xQ3e, xPQ3e = E0_data.basis3e.xP, E0_data.basis3e.xQ, E0_data.basis3e.xPQ

    # alpha in End(E0) s.t. n(alpha) = d*(2^e2 - d)*3^e3
    # we decompose alpha = hat(phi)*hat(rho)*tau, where deg(phi) = 3^e3, deg(rho) = 2^e2 - d, deg(tau) = d
    alpha, found = FullRepresentInteger(d*(two_to_e2 - d)*three_to_e3)
    @assert found
    e = valuation(gcd(alpha), 3)
    
    # (3^e3)-isogeny phi: E0 -> Ed
    K = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, involution(div(alpha, BigInt(3)^e)), 3, ExponentOfThree, E0_data.Matrices_3e)
    K = ladder(BigInt(3)^(2*e), K, a24_0)
    a24d, images = three_e_iso(a24_0, K, ExponentOfThree - 2*e, [xP2e, xQ2e, xPQ2e], StrategiesDim1Three[ExponentOfThree - 2*e])

    # (Pd, Qd) = [d^{-1}]hat(rho)*tau(P2, Q2) = [(3^e3 * d)^{-1}]phi*alpha(P2e, Q2e)
    xPd, xQd, xPQd = images
    c = invmod(d*div(three_to_e3, BigInt(3)^e), two_to_e2)
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
        #xP3e_d = ladder(BigInt(3)^e_u, xP3e_d, a24)
        #xQ3e_d = ladder(BigInt(3)^e_u, xQ3e_d, a24)
        #xPQ3e_d = ladder(BigInt(3)^e_u, xPQ3e_d, a24)
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
        #xP3e_d = ladder(BigInt(3)^e_v, xP3e_d, a24)
        #xQ3e_d = ladder(BigInt(3)^e_v, xQ3e_d, a24)
        #xPQ3e_d = ladder(BigInt(3)^e_v, xPQ3e_d, a24)
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

# algorithm for computing auxiliary isogenies
# input: integer d, the codomain a24m of the isogeny phi of kernel <xK1>, the point xK2 on a24m, phi(P2), phi(Q2)
# output: the codomain a24aux of a d-isogeny from the codomain of the isogeny psi of kernel <xK2>,
#    the images of psi*phi(P2), psi*phi(Q2), under the isogeny
function PushRandIsog(d::BigInt, a24m::Proj1{T}, xK1::Proj1{T}, xK2::Proj1{T},
        xP2m::Proj1{T}, xQ2m::Proj1{T}, xPQ2m::Proj1{T}, global_data::GlobalData) where T <: RingElem

    a24d, xKd, e, xP2d, xQ2d, xPQ2d = ComposedRandIsog(d, xK1, global_data)

    a24md, images = three_e_iso(a24d, xKd, ExponentOfThree, [xP2d, xQ2d, xPQ2d], StrategiesDim1Three[ExponentOfThree])
    xP2md, xQ2md, xPQ2md = images

    # kernel of (2^e2, 2^e2)-isogeny
    K1 = CouplePoint(xP2m, xP2md)
    K2 = CouplePoint(xQ2m, xQ2md)
    K12 = CouplePoint(xPQ2m, xPQ2md)

    # points to be evaluated by the isogeny
    O = infinity_point(global_data.Fp2)
    xK2O = CouplePoint(xK2, O)
    xP2mO = CouplePoint(xP2m, O)
    xQ2mO = CouplePoint(xQ2m, O)
    xPQ2mO = CouplePoint(xPQ2m, O)
    eval_points = [xP2mO, xQ2mO, xPQ2mO, xK2O]

    # (2^e2, 2^e2)-isogeny
    Es, images = product_isogeny_sqrt(a24m, a24md, K1, K2, K12, eval_points, ExponentOfTwo, StrategiesDim2[ExponentOfTwo])

    idx = 1
    a24mm = A_to_a24(Es[idx])
    xP2mm, xQ2mm, xPQ2mm = images[1][idx], images[2][idx], images[3][idx]
    w_m = Weil_pairing_2power(Montgomery_coeff(a24m), xP2m, xQ2m, xPQ2m, ExponentOfTwo)
    w_mm = Weil_pairing_2power(affine(Es[idx]), xP2mm, xQ2mm, xPQ2mm, ExponentOfTwo)
    if w_mm != w_m^d
        idx = 2
    end
    a24mm = A_to_a24(Es[idx])
    xP2mm, xQ2mm, xPQ2mm, xK2mm = images[1][idx], images[2][idx], images[3][idx], images[4][idx]

    # check
    w_mm = Weil_pairing_2power(affine(Es[idx]), xP2mm, xQ2mm, xPQ2mm, ExponentOfTwo)
    @assert w_mm == w_m^d

    # order of xK2mm
    e = 0
    tmp = xK2mm
    a24mm_pm = a24_to_a24pm(a24mm)
    while !is_infinity(tmp)
        tmp = xTPL(tmp, a24mm_pm)
        e += 1
    end

    a24aux, images = three_e_iso(a24mm, xK2mm, e, [xP2mm, xQ2mm, xPQ2mm], StrategiesDim1Three[e])
    if e < ExponentOfThree
        # here, we don't use any strategy because the degree of the isogeny is small
        xK = random_point_order_l_power(a24aux, p + 1, 3, ExponentOfThree - e)
        a24aux, images = three_e_iso(a24aux, xK, ExponentOfThree - e, images)
    end
    xP2aux, xQ2aux, xPQ2aux = images

    return a24aux, xP2aux, xQ2aux, xPQ2aux
end