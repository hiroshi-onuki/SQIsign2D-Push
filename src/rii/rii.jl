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

function ComposedRandIsog(d::BigInt, global_data::GlobalData)
    D1 = BigInt(1) << ExponentForDim2
    D2 = BigInt(1) << ExponentForDim1
    E0_data = global_data.E0_data
    a24_0 = E0_data.a24_0
    xP0, xQ0, xPQ0 = E0_data.xP2e, E0_data.xQ2e, E0_data.xPQ2e
    xP0 = xDBLe(xP0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)
    xQ0 = xDBLe(xQ0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)
    xPQ0 = xDBLe(xPQ0, a24_0, ExponentFull - ExponentForDim1 - ExponentForDim2)

    alpha = Quaternion_0
    while gcd(alpha) % 2 == 0
        alpha, _ = FullRepresentInteger(d*(D1 - d)*D2)
    end

    xP0D2 = xDBLe(xP0, a24_0, ExponentForDim2)
    xQ0D2 = xDBLe(xQ0, a24_0, ExponentForDim2)
    xPQ0D2 = xDBLe(xPQ0, a24_0, ExponentForDim2)
    K = kernel_generator(xP0D2, xQ0D2, xPQ0D2, a24_0, involution(alpha), 2, ExponentForDim1, E0_data.Matrices_2e)
    a24d, images = two_e_iso(a24_0, K, ExponentForDim1, [xP0, xQ0, xPQ0], StrategiesDim1[ExponentForDim1])

    xP1 = ladder(d << ExponentForDim1, xP0, a24_0)
    xQ1 = ladder(d << ExponentForDim1, xQ0, a24_0)
    xPQ1 = ladder(d << ExponentForDim1, xPQ0, a24_0)
    xPd, xQd, xPQd = images
    xP2, xQ2, xPQ2 = action_on_torsion_basis(alpha, a24d, xPd, xQd, xPQd, E0_data)

    a24, xP, xQ, xPQ, _ = d2isogeny(a24_0, a24d, xP1, xQ1, xPQ1, xP2, xQ2, xPQ2, ExponentForDim2, d, Proj1{FqFieldElem}[], global_data)

    return a24
end