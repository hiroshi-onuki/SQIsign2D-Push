export PairingData, Weil_pairing_2power, check_degree_by_pairing_2power, multi_Weil_pairing_2power,
    Weil_pairing_odd, check_degree_by_pairing_odd, multi_Weil_pairing_odd

"""
The following algorithms are based on the paper:
D. Robert, "Fast pairings via biextensions and cubical arithmetic
Preliminary"
https://eprint.iacr.org/2024/517.pdf
"""

struct PairingData
    a24::Proj1{FqFieldElem}
    xP::Proj1{FqFieldElem}
    xQ::Proj1{FqFieldElem}
    xPQ::Proj1{FqFieldElem}
end

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
        return XnPQ * ZnP, ZnP^2
    else
        return XnPQ * ZnP - ZnPQ * XnP, XnP^2 - ZnP^2
    end
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

# return Weil pairings
function multi_Weil_pairing_2power(data::Vector{PairingData}, e::Int)
    elements_for_inv = FqFieldElem[]
    for pdata in data
        push!(elements_for_inv, pdata.a24.Z)
        push!(elements_for_inv, pdata.xP.X)
        push!(elements_for_inv, pdata.xP.Z)
        push!(elements_for_inv, pdata.xQ.X)
        push!(elements_for_inv, pdata.xQ.Z)
        push!(elements_for_inv, pdata.xPQ.Z)
    end
    inv_elements = batched_inversion(elements_for_inv)

    n = length(data)
    ret = Vector{Proj1{FqFieldElem}}(undef, n)
    for i in 1:n
        a24af = data[i].a24.X * inv_elements[6*(i-1)+1]
        XP = data[i].xP.X * inv_elements[6*(i-1)+3]
        XPinv = data[i].xP.Z * inv_elements[6*(i-1)+2]
        XQ = data[i].xQ.X * inv_elements[6*(i-1)+5]
        XQinv = data[i].xQ.Z * inv_elements[6*(i-1)+4]
        XPQ = data[i].xPQ.X * inv_elements[6*(i-1)+6]
        wn, wd = Weil_pairing_2power(a24af, XP, XPinv, XQ, XQinv, XPQ, e)
        ret[i] = Proj1(wn, wd)
    end
    return ret
end

# return Weil pairings
function multi_Weil_pairing_odd(data::Vector{PairingData}, n::BigInt)
    elements_for_inv = FqFieldElem[]
    for pdata in data
        push!(elements_for_inv, pdata.a24.Z)
        push!(elements_for_inv, pdata.xP.X)
        push!(elements_for_inv, pdata.xP.Z)
        push!(elements_for_inv, pdata.xQ.X)
        push!(elements_for_inv, pdata.xQ.Z)
        push!(elements_for_inv, pdata.xPQ.X)
        push!(elements_for_inv, pdata.xPQ.Z)
    end
    inv_elements = batched_inversion(elements_for_inv)

    ret = Vector{Proj1{FqFieldElem}}(undef, length(data))
    for i in 1:length(data)
        a24af = data[i].a24.X * inv_elements[7*(i-1)+1]
        XP = data[i].xP.X * inv_elements[7*(i-1)+3]
        XPinv = data[i].xP.Z * inv_elements[7*(i-1)+2]
        XQ = data[i].xQ.X * inv_elements[7*(i-1)+5]
        XQinv = data[i].xQ.Z * inv_elements[7*(i-1)+4]
        XPQ = data[i].xPQ.X * inv_elements[7*(i-1)+7]
        XPQinv = data[i].xPQ.Z * inv_elements[7*(i-1)+6]
        wn, wd = Weil_pairing_odd(a24af, XP, XPinv, XQ, XQinv, XPQ, XPQinv, n)
        ret[i] = Proj1(wn, wd)
    end
    return ret
end

# return whether e_{2^e}(P1, Q1) = e_{2^e}(P2, Q2)^d
function check_degree_by_pairing_2power(a24_1::Proj1{T}, a24_2::Proj1{T},
    xP1::Proj1{T}, xQ1::Proj1{T}, xPQ1::Proj1{T}, xP2::Proj1{T},
    xQ2::Proj1{T}, xPQ2::Proj1{T}, e::Int, d::BigInt) where T <: RingElem

    pd1 = PairingData(a24_1, xP1, xQ1, xPQ1)
    pd2 = PairingData(a24_2, xP2, xQ2, xPQ2)
    ws = multi_Weil_pairing_2power([pd1, pd2], e)

    return ws[1].X * ws[2].Z^d == ws[1].Z * ws[2].X^d
end

# return whether e_n(P1, Q1) = e_n(P2, Q2)^d
function check_degree_by_pairing_odd(a24_1::Proj1{T}, a24_2::Proj1{T},
    xP1::Proj1{T}, xQ1::Proj1{T}, xPQ1::Proj1{T}, xP2::Proj1{T},
    xQ2::Proj1{T}, xPQ2::Proj1{T}, n::BigInt, d::BigInt) where T <: RingElem

    pd1 = PairingData(a24_1, xP1, xQ1, xPQ1)
    pd2 = PairingData(a24_2, xP2, xQ2, xPQ2)
    ws = multi_Weil_pairing_odd([pd1, pd2], n)

    return ws[1].X * ws[2].Z^d == ws[1].Z * ws[2].X^d
end

