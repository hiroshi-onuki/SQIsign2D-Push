export Weil_pairing_2power, Tate_pairing_P0, Tate_pairing_iP0, make_pairing_table, Tate_pairings

# Miller function f_{P}(Q)
function Miller_function(A::T, P::Point{T}, Q::Point{T}, e::Integer) where T <: RingElem
    F = parent(A)
    X, Y, Z = P.X, P.Y, P.Z
    f1, f2 = F(1), F(1)
    for i in 1:e-1
        AZ = A*Z
        QXZ = Q.X*Z
        QZX = Q.Z*X
        QZY = Q.Z*Y
        QZZ = Q.Z*Z
        lam1 = (3*X + 2*AZ) * X + Z^2
        lam12Z = lam1^2*Z
        lam2 = 2*Y*Z
        lam22 = lam2^2
        h1 = lam22 * (Q.Y*Z - QZY) - lam1*lam2 * (QXZ - QZX)
        h2 = lam22 * (QXZ + 2*QZX + A*QZZ) - lam12Z*Q.Z
        f1 = f1^2 * h1
        f2 = f2^2 * h2
        if i < e-1
            lam23 = lam2^3
            X, Y, Z = lam12Z*lam2 - lam23*(AZ + 2*X),
                lam1 * (lam22 * (3*X + AZ) - lam12Z) - Y * lam23,
                Z * lam23
        else
            X, Z = lam1^2*Z - lam22*(AZ + 2*X), Z * lam22
        end
    end
    f1 = f1^2 * (Q.X * Z - Q.Z * X)
    f2 = f2^2 * Q.Z * Z
    return f1, f2
end

# Weil pairing e_{2^e}(P, Q)
function Weil_pairing_2power(A::T, P::Point{T}, Q::Point{T}, e::Integer) where T <: RingElem
    fPQ1, fPQ2 = Miller_function(A, P, Q, e)
    if fPQ1 == 0 || fPQ2 == 0
        return parent(A)(1)
    end
    fQP1, fQP2 = Miller_function(A, Q, P, e)
    return (fPQ1*fQP2) / (fPQ2*fQP1)
end

# Weil pairng e_{2^e}(P, Q)
function Weil_pairing_2power(A::T, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T}, e::Integer) where T <: RingElem
    P = Point(A, xP)
    Q = Point(A, xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    return Weil_pairing_2power(A, P, Q, e)
end

# precomputed table for Tate pairings
function make_pairing_table(A::FqFieldElem, P::Point{FqFieldElem}, e::Integer)
    R = P
    x, y = R.X/R.Z, R.Y/R.Z
    table = [[x, y, parent(A)(0)]]
    for i in 1:e-1
        lam = (3*x^2 + 2*A*x + 1) / (2*y)
        R = double(R, Proj1(A))
        x = R.X/R.Z
        y = R.Y/R.Z
        push!(table, [x, y, lam])
    end
    return table
end

# Tate pairing t_{2^e}(P0, P) using precomputed table for P0
function Tate_pairing_P0(P::Point{FqFieldElem}, table::Vector{Vector{FqFieldElem}}, f::Integer)
    x, y, z = P.X, P.Y, P.Z
    x_frob = Frob(x)
    z_frob = Frob(z)
    x0, y0 = table[1][1], table[1][2]
    f0 = 1
    h0 = 1
    for (xt, yt, lam) in table[2:end]
        t0 = x - x0 * z
        t1 = y - y0 * z
        t0 *= lam
        g = t0 - t1
        h = x_frob - Frob(xt) * z_frob
        g *= h
        f0 = f0^2 * g
        h0 = h0^2 * z * z_frob
        x0, y0 = xt, yt
    end
    g = x - x0 * z
    f0 = f0^2 * g
    h0 = h0^2 * z
    f0 = Frob(f0) * h0 / (f0 * Frob(h0))
    f0 = f0^f
    return f0
end

# Tate pairing t_{2^e}(iP0, P) using precomputed table for P0
function Tate_pairing_iP0(P::Point{FqFieldElem}, table::Vector{Vector{FqFieldElem}}, f::Integer)
    x, y, z = P.X, P.Y, P.Z
    x_frob = Frob(x)
    z_frob = Frob(z)
    x0, y0 = table[1][1], table[1][2]
    f0 = 1
    h0 = 1
    for (xt, yt, lam) in table[2:end]
        t0 = x + x0 * z
        t1 = y - mult_by_i(y0) * z
        t0 *= -mult_by_i(lam)
        g = t0 - t1
        h = x_frob + Frob(xt) * z_frob
        g *= h
        f0 = f0^2 * g
        h0 = h0^2 * z * z_frob
        x0, y0 = xt, yt
    end
    g = x + x0 * z
    f0 = f0^2 * g
    h0 = h0^2 * z
    f0 = Frob(f0) * h0 / (f0 * Frob(h0))
    f0 = f0^f
    return f0
end

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

# return X + T, where T is a point of order 2
function CubicalTranslate(XP::T, ZP::T, XT::T, ZT::T) where T <: RingElem
    X = XP*XT - ZP*ZT
    Z = XP*ZT - ZP*XT
    TX == 0 && return -X, Z
    return X, Z
end

# return (num, den) s.t. num/den = g_{P, Q}, the biextension element above P, Q
function Monodromy(a24::T, e::Int, XP::T, XQinv::T, XPQ::T) where T <: RingElem
    F = parent(a24)
    XnP, ZnP, XnPQ, ZnPQ = CubicalLadderDbl(a24, e - 1, XPQ, F(1), XP, F(1), XQinv)
    num = XnPQ * ZnP - ZnPQ * XnP
    if XnP == 0
        den = ZnP^2
    else
        den = XnP^2 - ZnP^2
    end
    return num, den
end

# the 2^e-Weil pairing of P, Q, where XPQ is x(P - Q)
function Weil_pairing_2power(a24::T, XP::T, XPinv::T, XQ::T, XQinv::T, XPQ::T, e::Int) where T <: RingElem
    lamPn, lamPd = Monodromy(a24, e, XP, XQinv, XPQ)
    lamQn, lamQd = Monodromy(a24, e, XQ, XPinv, XPQ)
    return lamPd * lamQn, lamPn * lamQd
end