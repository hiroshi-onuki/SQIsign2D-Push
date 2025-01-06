export Weil_pairing_2power, check_degree_by_pairing, two_Weil_pairings_2power, Weil_pairing_odd

"""
The following algorithms are based on the paper:
D. Robert, "Fast pairings via biextensions and cubical arithmetic
Preliminary"
https://eprint.iacr.org/2024/517.pdf
"""

# return [2](X, Z)
function CubicalDbl(a24::T, X::T, Z::T) where T <: RingElem
    a = (X + Z)^2
    b = (X - Z)^2
    c = a - b
    X2 = a * b
    Z2 = c * (b + a24 * c)
    return X2, Z2
end

# return P + Q
function CubicalDiffAdd(a24::T, XP::T, ZP::T, XQ::T, ZQ::T, PmQXinv::T) where T <: RingElem
    a = XP + ZP
    b = XP - ZP
    c = XQ + ZQ
    d = XQ - ZQ
    a *= d
    b *= c
    X2 = (a + b)^2 * PmQXinv
    Z2 = (a - b)^2
    return X2, Z2
end

# return [2^e]P and [2^e]P + Q
function CubicalLadderDbl(a24::T, e::Int, XPQ::T, ZPQ::T, XP::T, ZP::T, XQinv::T) where T <: RingElem
    XnPQ, ZnPQ = XPQ, ZPQ
    XnP, ZnP = XP, ZP
    for i in 1:e
        XnPQ, ZnPQ = CubicalDiffAdd(a24, XnPQ, ZnPQ, XnP, ZnP, XQinv)
        XnP, ZnP = CubicalDbl(a24, XnP, ZnP)
    end
    return XnP, ZnP, XnPQ, ZnPQ
end

# return [n]P and [n]P + Q
function CubicalLadder(a24::T, n::BigInt, XPQ::T, XPQinv::T, XP::T, XPinv::T, XQinv::T) where T <: RingElem
    F = parent(a24)
    XnP, ZnP = XP, F(1)
    Xn1P, Zn1P = CubicalDbl(a24, XP, F(1))
    Xn1PQ, Zn1PQ = CubicalDiffAdd(a24, XPQ, F(1), XP, F(1), XQinv)

    t = (n - 1) >> 1
    b = BigInt(1)
    while t != 1
        t >>= 1
        b <<= 1 
    end

    while b != 0
        if (n - 1) & b == 0
            Xn1PQ, Zn1PQ = CubicalDiffAdd(a24, Xn1PQ, Zn1PQ, XnP, ZnP, XPQinv)
            Xn1P, Zn1P = CubicalDiffAdd(a24, Xn1P, Zn1P, XnP, ZnP, XPinv)
            XnP, ZnP = CubicalDbl(a24, XnP, ZnP)
        else
            XnP, ZnP = CubicalDiffAdd(a24, Xn1P, Zn1P, XnP, ZnP, XPinv)
            Xn1PQ, Zn1PQ = CubicalDiffAdd(a24, Xn1PQ, Zn1PQ, Xn1P, Zn1P, XQinv)
            Xn1P, Zn1P = CubicalDbl(a24, Xn1P, Zn1P)
        end
        b >>= 1
    end
    return Xn1P, Zn1P, Xn1PQ, Zn1PQ
end

# return (num, den) s.t. num/den = g_{P, Q}, the biextension element above P, Q in E[2^e]
function Monodromy(a24::T, e::Int, XP::T, XQinv::T, XPQ::T) where T <: RingElem
    F = parent(a24)
    XnP, ZnP, XnPQ, ZnPQ = CubicalLadderDbl(a24, e - 1, XPQ, F(1), XP, F(1), XQinv)
    if XnP == 0
        den = ZnP^2
    else
        den = XnP^2 - ZnP^2
    end
    if ZnP == 0
        num = ZnPQ * XnP
    else
        num = XnPQ * ZnP - ZnPQ * XnP
    end
    return num, den
end

# the 2^e-Weil pairing of P, Q, where XPQ is x(P - Q)
function Weil_pairing_2power(a24::T, XP::T, XPinv::T, XQ::T, XQinv::T, XPQ::T, e::Int) where T <: RingElem
    lamPn, lamPd = Monodromy(a24, e, XP, XQinv, XPQ)
    lamQn, lamQd = Monodromy(a24, e, XQ, XPinv, XPQ)
    return lamPd * lamQn, lamPn * lamQd
end

# return e_{2n}(P, Q) = e_n(P, Q)^2 for P, Q in E[n], where XPQ is x(P - Q)
function Weil_pairing_odd(a24::T, XP::T, XPinv::T, XQ::T, XQinv::T, XPQ::T, XPQinv::T, n::BigInt) where T <: RingElem
    XO, _, _, ZQd = CubicalLadder(a24, n, XPQ, XPQinv, XP, XPinv, XQinv)
    lamPn, lamPd = ZQd, XO
    XO, _, _, ZPd = CubicalLadder(a24, n, XPQ, XPQinv, XQ, XQinv, XPinv)
    lamQn, lamQd = ZPd, XO
    return lamPd * lamQn, lamPn * lamQd
end

# return two Weil pairings
function two_Weil_pairings_2power(a24_1::Proj1{T}, a24_2::Proj1{T},
    xP1::Proj1{T}, xQ1::Proj1{T}, xPQ1::Proj1{T}, xP2::Proj1{T},
    xQ2::Proj1{T}, xPQ2::Proj1{T}, e::Int) where T <: RingElem

    # compute affine points
    elements_for_inv = FqFieldElem[a24_1.Z, a24_2.Z,
                                    xP1.X, xP1.Z, xQ1.X, xQ1.Z, xPQ1.Z,
                                    xP2.X, xP2.Z, xQ2.X, xQ2.Z, xPQ2.Z
                                    ]
    inv_elements = batched_inversion(elements_for_inv)
    a24_1_af = a24_1.X * inv_elements[1]
    a24_2_af = a24_2.X * inv_elements[2]
    xP1_af = xP1.X * inv_elements[4]
    xP1_inv = xP1.Z * inv_elements[3]
    xQ1_af = xQ1.X * inv_elements[6]
    xQ1_inv = xQ1.Z * inv_elements[5]
    xPQ1_af = xPQ1.X * inv_elements[7]
    xP2_af = xP2.X * inv_elements[9]
    xP2_inv = xP2.Z * inv_elements[8]
    xQ2_af = xQ2.X * inv_elements[11]
    xQ2_inv = xQ2.Z * inv_elements[10]
    xPQ2_af = xPQ2.X * inv_elements[12]

    # compute Weil pairings
    w1n, w1d = Weil_pairing_2power(a24_1_af, xP1_af, xP1_inv, xQ1_af, xQ1_inv, xPQ1_af, e)
    w2n, w2d = Weil_pairing_2power(a24_2_af, xP2_af, xP2_inv, xQ2_af, xQ2_inv, xPQ2_af, e)

    return w1n, w1d, w2n, w2d
end

# return whether e_{2^e}(P1, Q1) = e_{2^e}(P2, Q2)^d
function check_degree_by_pairing(a24_1::Proj1{T}, a24_2::Proj1{T},
    xP1::Proj1{T}, xQ1::Proj1{T}, xPQ1::Proj1{T}, xP2::Proj1{T},
    xQ2::Proj1{T}, xPQ2::Proj1{T}, l::Int, e::Int, d::BigInt) where T <: RingElem

    # compute affine points
    elements_for_inv = [a24_1.Z, a24_2.Z, xP1.X, xP1.Z, xQ1.X, xQ1.Z, xPQ1.Z,
        xP2.X, xP2.Z, xQ2.X, xQ2.Z, xPQ2.Z]
    if l != 2
        push!(elements_for_inv, xPQ1.X)
        push!(elements_for_inv, xPQ2.X)
    end
    inv_elements = batched_inversion(elements_for_inv)
    a24_1_af = a24_1.X * inv_elements[1]
    a24_2_af = a24_2.X * inv_elements[2]
    xP1_af = xP1.X * inv_elements[4]
    xP1_inv = xP1.Z * inv_elements[3]
    xQ1_af = xQ1.X * inv_elements[6]
    xQ1_inv = xQ1.Z * inv_elements[5]
    xPQ1_af = xPQ1.X * inv_elements[7]
    xP2_af = xP2.X * inv_elements[9]
    xP2_inv = xP2.Z * inv_elements[8]
    xQ2_af = xQ2.X * inv_elements[11]
    xQ2_inv = xQ2.Z * inv_elements[10]
    xPQ2_af = xPQ2.X * inv_elements[12]
    if l != 2
        xPQ1_inv = xPQ1.Z * inv_elements[13]
        xPQ2_inv = xPQ2.Z * inv_elements[14]
    end

    # compute Weil pairings
    if l == 2
        w1n, w1d = Weil_pairing_2power(a24_1_af, xP1_af, xP1_inv, xQ1_af, xQ1_inv, xPQ1_af, e)
        w2n, w2d = Weil_pairing_2power(a24_2_af, xP2_af, xP2_inv, xQ2_af, xQ2_inv, xPQ2_af, e)
    else
        n = BigInt(l)^e
        w1n, w1d = Weil_pairing_odd(a24_1_af, xP1_af, xP1_inv, xQ1_af, xQ1_inv, xPQ1_af, xPQ1_inv, n)
        w2n, w2d = Weil_pairing_odd(a24_2_af, xP2_af, xP2_inv, xQ2_af, xQ2_inv, xPQ2_af, xPQ2_inv, n)
    end

    return w1n * w2d^d == w1d * w2n^d
end
