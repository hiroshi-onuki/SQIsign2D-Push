# FastDoublePath from SQIsignHD
# phi2, psi2 : E0 -> E2 -> E; (2^e2)-isogenies s.t. the composition corresponds to an ideal J2
# phi3, psi3 : E0 -> E3 -> E; (3^e3)-isogenies s.t. the composition corresponds to an ideal J3
# If is_both is true, then the function returns
#    E, psi3*phi3(P2), psi3*phi3(Q2), psi2*phi2(P3), psi2*phi2(Q3), J3, J2
# Otherwise, the function returns
#    E, E3, ker(phi3), ker(psi3), phi3(P2), phi3(Q2), psi3*phi3(P2), psi3*phi3(Q2), J3
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
    if a == 1
        xK2d = ladder3pt(b, xP2e3, xQ2e3, xPQ2e3, a24_3)
        eval_point = xQ2e3
    else
        xK2d = ladder3pt(a, xQ2e3, xP2e3, xPQ2e3, a24_3)
        eval_point = xP2e3
    end
    a24d, images = two_e_iso(a24_3, xK2d, ExponentOfTwo, [eval_point], StrategiesDim1Two[ExponentOfTwo])
    a24d, images = Montgomery_normalize(a24d, images)
    xK_dual2 = images[1]

    # 2^e2-isogeny: E0 -> E2 and 3^e3-isogeny: E2 -> Ed s.t. the kernel of the composition is bar{alpha} + 2^e2*3^e3*O0
    K2 = kernel_generator(xP2e, xQ2e, xPQ2e, a24_0, involution(alpha), 2, ExponentOfTwo, E0_data.Matrices_2e)
    a24_2, images = two_e_iso(a24_0, K2, ExponentOfTwo, [xP3e, xQ3e, xPQ3e], StrategiesDim1Two[ExponentOfTwo])
    xP3e2, xQ3e2, xPQ3e2 = images
    a, b = kernel_coefficients(involution(alpha), 3, ExponentOfThree, E0_data.Matrices_3e)
    if a == 1
        xK3d = ladder3pt(b, xP3e2, xQ3e2, xPQ3e2, a24_2)
        eval_point = xQ3e2
    else
        xK3d = ladder3pt(a, xQ3e2, xP3e2, xPQ3e2, a24_2)
        eval_point = xP3e2
    end
    a24dd, images = three_e_iso(a24_2, xK3d, ExponentOfThree, [eval_point], StrategiesDim1Three[ExponentOfThree])
    a24dd, images = Montgomery_normalize(a24dd, images)
    xK_dual3 = images[1]

    @assert a24d == a24dd

    # 3^e3-isogeny: E3 -> E, the latter part of 3^(2e3)-isogeny from E0 with kernel alpha + 3^(2e3)*O0
    a24_3, images2 = Montgomery_normalize(a24_3, [xP2e3, xQ2e3, xPQ2e3])
    xP2e3, xQ2e3, xPQ2e3 = images2
    a24_3d, images = two_e_iso(a24d, xK_dual2, ExponentOfTwo, [xK_dual3], StrategiesDim1Two[ExponentOfTwo])
    a24_3d, images = Montgomery_normalize(a24_3d, images)
    @assert a24_3 == a24_3d
    xK = images[1]
    a24, images = three_e_iso(a24_3, xK, ExponentOfThree, images2, StrategiesDim1Three[ExponentOfThree])
    a24, images = Montgomery_normalize(a24, images)
    xP2e_d, xQ2e_d, xPQ2e_d = images
    J3 = LeftIdeal(alpha, three_to_e3^2)
    !is_both && return a24_3, a24, K3, xK, xP2e3, xQ2e3, xPQ2e3, xP2e_d, xQ2e_d, xPQ2e_d, J3

    # 2^e2-isogeny: E2 -> E, the latter part of 2^(2e2)-isogeny from E0 with kernel bar{alpha} + 2^(2e2)*O0
    a24_2, images3 = Montgomery_normalize(a24_2, [xP3e2, xQ3e2, xPQ3e2])
    a24_2d, images = three_e_iso(a24d, xK_dual3, ExponentOfThree, [xK_dual2], StrategiesDim1Three[ExponentOfThree])
    a24_2d, images = Montgomery_normalize(a24_2d, images)
    @assert a24_2 == a24_2d
    xK = images[1]
    a24d, images = two_e_iso(a24_2, xK, ExponentOfTwo, images3, StrategiesDim1Two[ExponentOfTwo])
    a24d, images = Montgomery_normalize(a24, images)
    @assert a24 == a24d
    xP3e_d, xQ3e_d, xPQ3e_d = images
    J2 = LeftIdeal(involution(alpha), two_to_e2^2)
    return a24, xP2e_d, xQ2e_d, xPQ2e_d, xP3e_d, xQ3e_d, xPQ3e_d, J3, J2
end