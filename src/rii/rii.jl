# input: odd integer d s.t. 2^e_dim2 - d is not divisible by 3, a point xK in E0 of order 3^e3
# output: the codomain of a random (d(2^e2 - d))-isogeny f, [c]f(xK),
#    and [d^{-1}](f(P2e), f(Q2e)), where c in some integer not divisible by 3
function ComposedRandIsog(d::BigInt, e_dim2::Int, xK::Proj1{T}, global_data::GlobalData) where T <: RingElem
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP2e, xQ2e, xPQ2e = E0_data.basis2e.xP, E0_data.basis2e.xQ, E0_data.basis2e.xPQ
    xP3e, xQ3e, xPQ3e = E0_data.basis3e.xP, E0_data.basis3e.xQ, E0_data.basis3e.xPQ
    two_to_e_dim2 = BigInt(1) << e_dim2

    # To distinguish the image of the dim2 isogeny by the 3^e3-Weil pairing,
    # we require d neq 2^e_dim2 - d mod 3^e3
    @assert (2*d - two_to_e_dim2) % three_to_e3 != 0

    # alpha in End(E0) s.t. n(alpha) = d*(2^e2 - d)*3^e3
    # we decompose alpha = hat(phi)*hat(rho)*tau, where deg(phi) = 3^e3, deg(rho) = 2^e2 - d, deg(tau) = d
    alpha = Quaternion_0
    while gcd(alpha) != 1
        alpha, _ = FullRepresentInteger(d*(two_to_e_dim2 - d)*three_to_e3)
    end
    
    # (3^e3)-isogeny phi: E0 -> Ed
    K = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, involution(alpha), 3, ExponentOfThree, E0_data.Matrices_3e)
    a24d, images = three_e_iso(a24_0, K, ExponentOfThree, [xP2e, xQ2e, xPQ2e], StrategiesDim1Three[ExponentOfThree])

    # (Pd, Qd) = [d^{-1}]hat(rho)*tau(P2, Q2) = [(3^e3 * d)^{-1}]phi*alpha(P2e, Q2e)
    xPd, xQd, xPQd = images
    c = invmod(d*three_to_e3, two_to_e2)
    xPd, xQd, xPQd = action_on_torsion_basis(alpha, a24d, xPd, xQd, xPQd, E0_data, c)

    # points to be evaluated by the isogeny
    O = infinity_point(global_data.Fp2)
    xP3e_d, xQ3e_d, xPQ3e_d = torsion_basis(a24d, 3, ExponentOfThree)
    OP3e_d = CouplePoint(O, xP3e_d)
    OQ3e_d = CouplePoint(O, xQ3e_d)
    OPQ3e_d = CouplePoint(O, xPQ3e_d)
    KO = CouplePoint(xK, O)

    eval_points = [OP3e_d, OQ3e_d, OPQ3e_d, KO]

    # (2^e_dim2, 2^e_dim2)-isogeny
    # the kernel of the (2^e_dim2, 2^e_dim2)-isogeny is [2^(e2 - e_dim2)]<(P2e, Pd), (Q2e, Qd)>
    if ExponentOfTwo - e_dim2 >= 2
        xK11 = xDBLe(xP2e, a24_0, ExponentOfTwo - e_dim2 - 2)
        xK12 = xDBLe(xPd, a24d, ExponentOfTwo - e_dim2 - 2)
        xK21 = xDBLe(xQ2e, a24_0, ExponentOfTwo - e_dim2 - 2)
        xK22 = xDBLe(xQd, a24d, ExponentOfTwo - e_dim2 - 2)
        xK121 = xDBLe(xPQ2e, a24_0, ExponentOfTwo - e_dim2 - 2)
        xK122 = xDBLe(xPQd, a24d, ExponentOfTwo - e_dim2 - 2)
        K1 = CouplePoint(xK11, xK12)
        K2 = CouplePoint(xK21, xK22)
        K12 = CouplePoint(xK121, xK122)

        Es, images = product_isogeny(a24_0, a24d, K1, K2, K12, eval_points, e_dim2, StrategiesDim2[e_dim2])
    else 
        xK11 = xDBLe(xP2e, a24_0, ExponentOfTwo - e_dim2)
        xK12 = xDBLe(xPd, a24d, ExponentOfTwo - e_dim2)
        xK21 = xDBLe(xQ2e, a24_0, ExponentOfTwo - e_dim2)
        xK22 = xDBLe(xQd, a24d, ExponentOfTwo - e_dim2)
        xK121 = xDBLe(xPQ2e, a24_0, ExponentOfTwo - e_dim2)
        xK122 = xDBLe(xPQd, a24d, ExponentOfTwo - e_dim2)
        K1 = CouplePoint(xK11, xK12)
        K2 = CouplePoint(xK21, xK22)
        K12 = CouplePoint(xK121, xK122)

        Es, images = product_isogeny_sqrt(a24_0, a24d, K1, K2, K12, eval_points, e_dim2, StrategiesDim2[e_dim2])
    end

    idx = 1
    a24 = A_to_a24(Es[idx])
    x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d = images[1][idx], images[2][idx], images[3][idx]

    if !check_degree_by_pairing(a24, a24d, x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d, xP3e_d, xQ3e_d, xPQ3e_d, 3, ExponentOfThree, two_to_e_dim2 - d)
        idx = 2
    end
    a24 = A_to_a24(Es[idx])
    x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d = images[1][idx], images[2][idx], images[3][idx]
    x_tau_K = images[4][idx]

    u, v = ec_bi_dlog_one_point(a24, x_tau_K, BasisData(x_hatrho_P3e_d, x_hatrho_Q3e_d, x_hatrho_PQ3e_d), 3, ExponentOfThree)
    if u == 1
        xKd = ladder3pt(v, xP3e_d, xQ3e_d, xPQ3e_d, a24d)
    else
        xKd = ladder3pt(u, xQ3e_d, xP3e_d, xPQ3e_d, a24d)
    end

    return a24d, xKd, xPd, xQd, xPQd
end

# algorithm for computing auxiliary isogenies
# input: integer d \neq 0 mod 3, the codomain a24m of the isogeny phi of kernel <xK1>, the point xK2 on a24m, phi(P2), phi(Q2)
# output: the codomain a24aux of a d-isogeny from the codomain of the isogeny psi of kernel <xK2>,
#    the images of psi*phi(P2), psi*phi(Q2), under the isogeny
function PushRandIsog(d::BigInt, a24m::Proj1{T}, xK1::Proj1{T}, xK2::Proj1{T},
        xP2m::Proj1{T}, xQ2m::Proj1{T}, xPQ2m::Proj1{T}, global_data::GlobalData) where T <: RingElem
    
    @assert d % 3 != 0

    # find e_dim2 s.t. 2^e_dim2 > d and 2^e_dim2 - d is not divisible by 3
    e_dim2 = 0
    two_to_e_dim2 = BigInt(1)
    while two_to_e_dim2 < d
        e_dim2 += 1
        two_to_e_dim2 <<= 1
    end
    if (two_to_e_dim2 - d) % 3 == 0
        e_dim2 += 1
        two_to_e_dim2 <<= 1
    end
    @assert (two_to_e_dim2 - d) % 3 != 0

    a24d, xKd, xP2d, xQ2d, xPQ2d = ComposedRandIsog(d, e_dim2, xK1, global_data)

    a24md, images = three_e_iso(a24d, xKd, ExponentOfThree, [xP2d, xQ2d, xPQ2d], StrategiesDim1Three[ExponentOfThree])
    xP2md, xQ2md, xPQ2md = images

    # points to be evaluated by the isogeny
    O = infinity_point(global_data.Fp2)
    xK2O = CouplePoint(xK2, O)
    xP2mO = CouplePoint(xP2m, O)
    xQ2mO = CouplePoint(xQ2m, O)
    xPQ2mO = CouplePoint(xPQ2m, O)
    eval_points = [xP2mO, xQ2mO, xPQ2mO, xK2O]

    # (2^e_dim2, 2^e_dim2)-isogeny
    if ExponentOfTwo - e_dim2 >= 2
        xK11 = xDBLe(xP2m, a24m, ExponentOfTwo - e_dim2 - 2)
        xK12 = xDBLe(xP2md, a24md, ExponentOfTwo - e_dim2 - 2)
        xK21 = xDBLe(xQ2m, a24m, ExponentOfTwo - e_dim2 - 2)
        xK22 = xDBLe(xQ2md, a24md, ExponentOfTwo - e_dim2 - 2)
        xK121 = xDBLe(xPQ2m, a24m, ExponentOfTwo - e_dim2 - 2)
        xK122 = xDBLe(xPQ2md, a24md, ExponentOfTwo - e_dim2 - 2)
        K1 = CouplePoint(xK11, xK12)
        K2 = CouplePoint(xK21, xK22)
        K12 = CouplePoint(xK121, xK122)

        Es, images = product_isogeny(a24m, a24md, K1, K2, K12, eval_points, e_dim2, StrategiesDim2[e_dim2])
    else
        xK11 = xDBLe(xP2m, a24m, ExponentOfTwo - e_dim2)
        xK12 = xDBLe(xP2md, a24md, ExponentOfTwo - e_dim2)
        xK21 = xDBLe(xQ2m, a24m, ExponentOfTwo - e_dim2)
        xK22 = xDBLe(xQ2md, a24md, ExponentOfTwo - e_dim2)
        xK121 = xDBLe(xPQ2m, a24m, ExponentOfTwo - e_dim2)
        xK122 = xDBLe(xPQ2md, a24md, ExponentOfTwo - e_dim2)
        K1 = CouplePoint(xK11, xK12)
        K2 = CouplePoint(xK21, xK22)
        K12 = CouplePoint(xK121, xK122)

        Es, images = product_isogeny_sqrt(a24m, a24md, K1, K2, K12, eval_points, e_dim2, StrategiesDim2[e_dim2])
    end

    idx = 1
    a24mm = A_to_a24(Es[idx])
    xP2mm, xQ2mm, xPQ2mm = images[1][idx], images[2][idx], images[3][idx]
    if !check_degree_by_pairing(a24mm, a24m, xP2mm, xQ2mm, xPQ2mm, xP2m, xQ2m, xPQ2m, 2, ExponentOfTwo, d)
        idx = 2
    end
    a24mm = A_to_a24(Es[idx])
    xP2mm, xQ2mm, xPQ2mm, xK2mm = images[1][idx], images[2][idx], images[3][idx], images[4][idx]

    a24aux, images = three_e_iso(a24mm, xK2mm, ExponentOfThree, [xP2mm, xQ2mm, xPQ2mm], StrategiesDim1Three[ExponentOfThree])
    xP2aux, xQ2aux, xPQ2aux = images

    return a24aux, xP2aux, xQ2aux, xPQ2aux
end