# FastDoublePath from SQIsignHD
# phi2, psi2 : E0 -> E2 -> E; (2^e2)-isogenies s.t. the composition corresponds to an ideal J2 = bar{alpha} + 2^2e2*O0
# phi3, psi3 : E0 -> E3 -> E; (3^e3)-isogenies s.t. the composition corresponds to an ideal J3 = alpha + 3^2e3*O0
# If is_both is true, then the function returns
#    E, psi3*phi3(P2), psi3*phi3(Q2), psi2*phi2(P3), psi2*phi2(Q3), J3, J2
# Otherwise, the function returns
#    E3, E, ker(phi3), ker(psi3), phi3(P2), phi3(Q2), psi3*phi3(P2), psi3*phi3(Q2), J3, alpha
function FastDoublePath(is_both::Bool, global_data::GlobalData)
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP2e, xQ2e, xPQ2e = E0_data.basis2e.xP, E0_data.basis2e.xQ, E0_data.basis2e.xPQ
    xP3e, xQ3e, xPQ3e = E0_data.basis3e.xP, E0_data.basis3e.xQ, E0_data.basis3e.xPQ

    alpha = Quaternion_0
    while gcd(alpha) != 1
        alpha, _ = FullRepresentInteger(two_to_e2^2*three_to_e3^2)
    end

    # 3^e3-isogeny: E0 -> E3 and 2^e2-isogeny: E3 -> Ed s.t. the kernel of the composition is alpha + 2^e2*3^e3*O0
    K3 = kernel_generator(xP3e, xQ3e, xPQ3e, a24_0, alpha, 3, ExponentOfThree, E0_data.Matrices_3e)
    a24_3, images = three_e_iso(a24_0, K3, ExponentOfThree, [xP2e, xQ2e, xPQ2e], StrategiesDim1Three[ExponentOfThree])
    xP2e3, xQ2e3, xPQ2e3 = images
    a, b = kernel_coefficients(alpha, 2, ExponentOfTwo, E0_data.Matrices_2e)
    xP3e3, xQ3e3, xPQ3e3, _, _ = basis_3e(Montgomery_coeff(a24_3), CofactorWRT3, ExponentOfThree, global_data)
    eval_points = [xP3e3, xQ3e3, xPQ3e3]
    if a == 1
        xK2d = ladder3pt(b, xP2e3, xQ2e3, xPQ2e3, a24_3)
        is_both && push!(eval_points, xQ2e3)
    else
        xK2d = ladder3pt(a, xQ2e3, xP2e3, xPQ2e3, a24_3)
        is_both && push!(eval_points, xP2e3)
    end
    a24d, images = two_e_iso(a24_3, xK2d, ExponentOfTwo, eval_points, StrategiesDim1Two[ExponentOfTwo])
    if is_both
        xP3e_d, xQ3e_d, xPQ3e_d, xK_dual2 = images
    else
        xP3e_d, xQ3e_d, xPQ3e_d = images
    end

    # 2^e2-isogeny: E0 -> E2 and 3^e3-isogeny: E2 -> Ed s.t. the kernel of the composition is bar{alpha} + 2^e2*3^e3*O0
    K2 = kernel_generator(xP2e, xQ2e, xPQ2e, a24_0, involution(alpha), 2, ExponentOfTwo, E0_data.Matrices_2e)
    a24_2, images = two_e_iso(a24_0, K2, ExponentOfTwo, [xP3e, xQ3e, xPQ3e], StrategiesDim1Two[ExponentOfTwo])
    xP3e2, xQ3e2, xPQ3e2 = images
    a, b = kernel_coefficients(involution(alpha), 3, ExponentOfThree, E0_data.Matrices_3e)
    xP2e2, xQ2e2, xPQ2e2, _ = basis_2e(Montgomery_coeff(a24_2), CofactorWRT2, global_data)
    eval_points = [xP2e2, xQ2e2, xPQ2e2]
    if a == 1
        xK3d = ladder3pt(b, xP3e2, xQ3e2, xPQ3e2, a24_2)
        push!(eval_points, xQ3e2)
    else
        xK3d = ladder3pt(a, xQ3e2, xP3e2, xPQ3e2, a24_2)
        push!(eval_points, xP3e2)
    end
    a24dd, images = three_e_iso(a24_2, xK3d, ExponentOfThree, eval_points, StrategiesDim1Three[ExponentOfThree])
    images = IsomorphismMontgomery(a24dd, a24d, images)
    xP2e_d, xQ2e_d, xPQ2e_d, xK_dual3 = images

    # 3^e3-isogeny: E3 -> E, the latter part of 3^(2e3)-isogeny from E0 with kernel alpha + 3^(2e3)*O0
    a, b = ec_bi_dlog_one_point(a24d, xK_dual3, BasisData(xP3e_d, xQ3e_d, xPQ3e_d), 3, ExponentOfThree)
    if a == 1
        xK = ladder3pt(b, xP3e3, xQ3e3, xPQ3e3, a24_3)
    else
        xK = ladder3pt(a, xQ3e3, xP3e3, xPQ3e3, a24_3)
    end
    a24, images = three_e_iso(a24_3, xK, ExponentOfThree, [xP2e3, xQ2e3, xPQ2e3], StrategiesDim1Three[ExponentOfThree])
    xP2e3d, xQ2e3d, xPQ2e3d = images
    J3 = LeftIdeal(alpha, three_to_e3^2)
    !is_both && return a24_3, a24, K3, xK, xP2e3, xQ2e3, xPQ2e3, xP2e3d, xQ2e3d, xPQ2e3d, J3

    # 2^e2-isogeny: E2 -> E, the latter part of 2^(2e2)-isogeny from E0 with kernel bar{alpha} + 2^(2e2)*O0
    a, b = ec_bi_dlog_one_point(a24d, xK_dual2, BasisData(xP2e_d, xQ2e_d, xPQ2e_d), 2, ExponentOfTwo)
    if a == 1
        xK = ladder3pt(b, xP2e2, xQ2e2, xPQ2e2, a24_2)
    else
        xK = ladder3pt(a, xQ2e2, xP2e2, xPQ2e2, a24_2)
    end
    a24d, images = two_e_iso(a24_2, xK, ExponentOfTwo, [xP3e2, xQ3e2, xPQ3e2], StrategiesDim1Two[ExponentOfTwo])
    images = IsomorphismMontgomery(a24d, a24, images)
    xP3e2d, xQ3e2d, xPQ3e2d = images
    J2 = LeftIdeal(involution(alpha), two_to_e2^2)
    return a24, xP2e3d, xQ2e3d, xPQ2e3d, xP3e2d, xQ3e2d, xPQ3e2d, J3, J2, alpha
end