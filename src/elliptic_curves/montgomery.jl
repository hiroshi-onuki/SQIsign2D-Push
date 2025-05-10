export xDBL, xTPL, xADD, xDBLADD, xDBLe, xTPLe, ladder, ladder3pt, x_add_sub,
    linear_comb_2_e, random_point, random_point_order_l, random_point_order_l_power,
    Montgomery_coeff, A_to_a24, a24_to_A, a24_to_a24pm, jInvariant_a24, jInvariant_A,
    two_e_iso, three_iso, three_e_iso, Montgomery_normalize, basis_2e, basis_2e_from_hint, basis_3e, basis_3e_from_hint,
    three_isogenous_coeff_to_kernel, IsomorphismMontgomery

# random point on a Montgomery curve: y^2 = x^3 + Ax^2 + x
function random_point(A::T) where T <: RingElem
    F = parent(A)
    while true
        x = rand(F)
        is_square(x^3 + A*x^2 + x) && return Proj1(x)
    end
end

# random point on a Montgomery curve: y^2 = x^3 + Ax^2 + x
function random_point(A::Proj1{T}) where T <: RingElem
    F = parent(A.X)
    while true
        x = rand(F)
        is_square(A.Z^2*x^3 + A.X*A.Z*x^2 + A.Z^2*x) && return Proj1(x)
    end
end

# random point on a Montgomery curve with prime order l
function random_point_order_l(a24::Proj1{T}, curve_order::Integer, l::Integer) where T <: RingElem
    n = div(curve_order, l)
    A = a24_to_A(a24)
    while true
        P = random_point(A)
        P = ladder(n, P, a24)
        if !is_infinity(P)
            return P
        end
    end
end

# random point on a Montgomery curve with order l^e
function random_point_order_l_power(a24::Proj1{T}, curve_order::Integer, l::Integer, e::Integer) where T <: RingElem
    n = div(curve_order, BigInt(l)^e)
    A = a24_to_A(a24)
    le1 = BigInt(l)^(e-1)
    while true
        P = random_point(A)
        P = ladder(n, P, a24)
        if !is_infinity(ladder(le1, P, a24))
            return P
        end
    end
end

# random point on a Montgomery curve with order l^e
function random_point_order_l_power(A::T, curve_order::Integer, l::Integer, e::Integer) where T <: RingElem
    F = parent(A)
    a24 = Proj1(A + 2, F(4))
    n = div(curve_order, BigInt(l)^e)
    le1 = BigInt(l)^(e-1)
    while true
        P = random_point(A)
        P = ladder(n, P, a24)
        if !is_infinity(ladder(le1, P, a24))
            return P
        end
    end
end

# return [2]P on Mont_A with a24 = (A + 2)/4.
function xDBL(P::Proj1{T}, a24::Proj1{T}) where T <: RingElem
    t0 = P.X - P.Z
    t1 = P.X + P.Z
    t0 = t0^2
    t1 = t1^2
    Z = a24.Z*t0
    X = Z*t1
    t1 -= t0
    t0 = a24.X*t1
    Z += t0
    Z *= t1

    return Proj1(X, Z);
end

# return [3]P on Mont_A with a24pm = (A + 2 : A - 2)
function xTPL(P::Proj1{T}, a24pm::Proj1{T}) where T <: RingElem
    t0 = P.X - P.Z
    t2 = t0^2
    t1 = P.X + P.Z
    t3 = t1^2
    t4 = t1 + t0
    t0 = t1 - t0
    t1 = t4^2
    t1 -= t3
    t1 -= t2
    t5 = t3 * a24pm.X
    t3 *= t5
    t6 = t2 * a24pm.Z
    t2 *= t6
    t3 = t2 - t3
    t2 = t5 - t6
    t1 *= t2
    t2 = t3 + t1
    t2 *= t2
    X = t2 * t4
    t1 = t3 - t1
    t1 *= t1
    Z = t1 * t0
    return Proj1(X, Z)
end

# return [2^e]P on Mont_A with a24 = (A + 2)/4.
function xDBLe(P::Proj1{T}, a24::Proj1{T}, e::Int) where T <: RingElem
    outP = P
    for _ in 1:e
        outP = xDBL(outP, a24)
    end

    return outP
end

# return [3^e]P on Mont_A with a24pm = (A + 2 : A - 2)
function xTPLe(P::Proj1{T}, a24pm::Proj1{T}, e::Int) where T <: RingElem
    outP = P
    for _ in 1:e
        outP = xTPL(outP, a24pm)
    end

    return outP
end

# return P + Q from P, Q, Q-P
function xADD(P::Proj1{T}, Q::Proj1{T}, QmP::Proj1{T}) where T <: RingElem
    a = P.X + P.Z
    b = P.X - P.Z
    c = Q.X + Q.Z
    d = Q.X - Q.Z
    a *= d
    b *= c
    c = a + b
    d = a - b
    c = c^2
    d = d^2
    return Proj1(QmP.Z*c, QmP.X*d)
end

# return 2P and P + Q
function xDBLADD(P::Proj1{T}, Q::Proj1{T}, QmP::Proj1{T}, a24::Proj1{T}) where T <: RingElem
    t0 = P.X + P.Z;
    t1 = P.X - P.Z;
    tPX = t0^2;
    t2 = Q.X - Q.Z;
    PpQX = Q.X + Q.Z;
    t0 *= t2;
    tPZ = t1^2;
    t1 *= PpQX;
    t2 = tPX - tPZ;
    tPZ *= a24.Z
    tPX *= tPZ;
    PpQX = a24.X * t2;
    PpQZ = t0 - t1;
    tPZ = PpQX + tPZ;
    PpQX = t0 + t1;
    tPZ = tPZ * t2;
    PpQZ = PpQZ^2;
    PpQX = PpQX^2;
    PpQZ *= QmP.X;
    PpQX *= QmP.Z;

    return Proj1(tPX, tPZ), Proj1(PpQX, PpQZ);
end

# return x(P + Q) or x(P - Q)
function x_add_sub(P::Proj1{T}, Q::Proj1{T}, a24::Proj1{T}) where T <: RingElem
    is_infinity(P) && return Q
    is_infinity(Q) && return P

    A = a24.X + a24.X
    A -= a24.Z
    A += A
    C = a24.Z
    X1X2 = P.X * Q.X
    Z1Z2 = P.Z * Q.Z
    X1Z2 = P.X * Q.Z
    Z1X2 = P.Z * Q.X
    a = (X1Z2 - Z1X2)^2 * C
    b = (X1X2 + Z1Z2) * (X1Z2 + Z1X2) * C + (A + A) * X1X2 * Z1Z2
    c = (X1X2 - Z1Z2)^2 * C
    d = square_root(b^2 - a*c)
    return Proj1(b + d, a)
end

# return [m]P
function ladder(m::Integer, P::Proj1{T}, a24::Proj1{T}) where T <: RingElem
    m == 0 && return infinity_point(parent(P.X))
    m == 1 && return P
    m == 2 && return xDBL(P, a24)

    t = m >> 1
    b = BigInt(1)
    while t != 1
        t >>= 1
        b <<= 1 
    end

    P0, P1 = P, xDBL(P, a24)
    while b != 0
        if m & b == 0
            P0, P1 = xDBLADD(P0, P1, P, a24)
        else
            P1, P0 = xDBLADD(P1, P0, P, a24)
        end
        b >>= 1
    end
    return P0
end

# return x(P + [m]Q) from x(P), x(Q), x(Q-P)
function ladder3pt(m::Integer, P::Proj1{T}, Q::Proj1{T}, QmP::Proj1{T}, a24::Proj1{T}) where T <: RingElem
    m < 0 && error("m in Ladder3pt must be nonnegative")
    m == 0 && return P
    is_infinity(QmP) && error("Q == P is not allowed")

    P0 = Q;
    P1 = P;
    P2 = QmP;
    t = BigInt(m)
    while (t != 0)
        if (t & 1 == 1)
            P0, P1 = xDBLADD(P0, P1, P2, a24);
        else
            P0, P2 = xDBLADD(P0, P2, P1, a24);
        end
        t >>= 1;
    end
    return P1;
end

# return x([a]P + [b]Q) from x(P), x(Q), x(Q-P), where ord(P) = ord(Q) = 2^e
function linear_comb_2_e(a::Integer, b::Integer, xP::Proj1{T}, xQ::Proj1{T}, xQmP::Proj1{T}, a24::Proj1{T}, e::Int) where T <: RingElem
    a = a % (BigInt(2)^e)
    b = b % (BigInt(2)^e)
    a < 0 && (a += BigInt(2)^e)
    b < 0 && (b += BigInt(2)^e)
    a == 0 && return ladder(b, xQ, a24)
    b == 0 && return ladder(a, xP, a24)
    g = gcd(a, b)
    f = 0
    while g & 1 == 0
        g >>= 1
        f += 1
    end
    a >>= f
    b >>= f
    if a & 1 == 0
        c = invmod(b, BigInt(2)^e)
        a = (a * c) % (BigInt(2)^e)
        xR = ladder3pt(a, xQ, xP, xQmP, a24)
        xR = ladder(b, xR, a24)
    else
        c = invmod(a, BigInt(2)^e)
        b = (b * c) % (BigInt(2)^e)
        xR = ladder3pt(b, xP, xQ, xQmP, a24)
        xR = ladder(a, xR, a24)
    end
    return xDBLe(xR, a24, f)
end

# Montgomery coefficient of a24
function Montgomery_coeff(a24::Proj1)
    a = a24.X + a24.X
    a -= a24.Z
    a += a
    return a//a24.Z
end

function a24_to_A(a24::Proj1)
    a = a24.X + a24.X
    a -= a24.Z
    a += a
    return Proj1(a, a24.Z)
end

function a24_to_a24pm(a24::Proj1)
    return Proj1(a24.X, a24.X - a24.Z)
end

function A_to_a24(A::T) where T <: RingElem
    F = parent(A)
    return Proj1(A + 2, F(4))
end

function A_to_a24(A::Proj1)
    Z2 = A.Z + A.Z
    Z4 = Z2 + Z2
    return Proj1(A.X + Z2, Z4)
end

# the j-invariant of a24
function jInvariant_a24(a24::Proj1)
    j = a24.X + a24.X - a24.Z
    j += j
    j = j^2
    t1 = a24.Z^2
    t0 = t1 + t1
    t0 = j - t0
    t0 -= t1
    j = t0 - t1
    t1 = t1^2
    j *= t1
    t0 += t0
    t0 += t0
    t1 = t0^2
    t0 *= t1
    t0 += t0
    t0 += t0
    j = 1//j
    j *= t0

    return j
end

function jInvariant_A(A::Proj1)
    return jInvariant_a24(A_to_a24(A))
end

function jInvariant_A(A::T) where T <: RingElem
    return jInvariant_a24(A_to_a24(A))
end

function two_iso(a24::Proj1{T}, P::Proj1{T}) where T <: RingElem
    if P.X == 0
        a24, _ = two_iso_zero(a24, Proj1{T}[])
    else
        a24 = two_iso_curve(P)
    end
    return a24
end

# 2-isogey. return (A + 2)/4, where Mont_A = E/<P> with ord(P) = 2.
function two_iso_curve(P::Proj1)
    X = P.X^2;
    Z = P.Z^2;
    X = Z - X;

    return Proj1(X, Z);
end

# The image of 2-isogey. return f(Q), where f is an isogeny with kernel <P>.
function two_iso_eval(P::Proj1{T}, Q::Proj1{T}) where T <: RingElem
    t0 = P.X + P.Z;
    t1 = P.X - P.Z;
    t2 = Q.X + Q.Z;
    t3 = Q.X - Q.Z;
    t0 *= t3;
    t1 *= t2;
    t2 = t0 + t1;
    t3 = t0 - t1;
    X = Q.X * t2;
    Z = Q.Z * t3;

    return Proj1(X, Z);
end

# 2-isogeny with kernel (0, 0)
function two_iso_zero(a24::Proj1{T}, Qs::Vector{Proj1{T}}) where T <: RingElem
    a = a24.X + a24.X - a24.Z
    d = sqrt(a24.X*(a24.X - a24.Z))
    d += d
    d2 = d+d
    a24d = Proj1(-a + d, d2)
    a += a

    retQ = Proj1{T}[]
    for Q in Qs
        XZ = Q.X*Q.Z
        X = Q.X^2 + Q.Z^2
        X *= a24.Z
        X += a*XZ
        Z = d2*XZ
        push!(retQ, Proj1(X, Z))
    end

    return a24d, retQ
end

# 4-isogey. return (A + 2)/4 and (K1, K2, K3), where Mont_A = E/<P> with ord(P) = 4.
function four_iso_curve(P::Proj1)
    K2 = P.X - P.Z;
    K3 = P.X + P.Z;
    K1 = P.Z^2;
    K1 += K1;
    Z = K1^2;
    K1 += K1;
    X = P.X^2;
    X += X;
    X = X^2;

    return Proj1(X, Z), K1, K2, K3;
end

# The image of 4-isogey using an output (K1, K2, K3) of four_iso_curve().
function four_iso_eval(K1::T, K2::T, K3::T, Q::Proj1{T}) where T <: RingElem
    t0 = Q.X + Q.Z;
    t1 = Q.X - Q.Z;
    QX = t0 * K2;
    QZ = t1 * K3;
    t0 *= t1;
    t0 *= K1;
    t1 = QX + QZ;
    QZ = QX - QZ;
    t1 = t1^2;
    QZ = QZ^2;
    QX = t0 + t1;
    t0 = QZ - t0;
    X = QX * t1;
    Z = QZ * t0;

    return Proj1(X, Z);
end

# 4-isogeny with kernel <(1, -)>
four_iso_curve_one(a24::Proj1) = Proj1(a24.X, a24.X - a24.Z)

# 4-isogeny with kernel <(-1, -)>
four_iso_curve_neg_one(a24::Proj1) = Proj1(a24.Z, a24.X)

# evaluation under 4-isogeny with kernel <(1, -)>
function four_iso_eval_one(a24::Proj1{T}, P::Proj1{T}) where T <: RingElem
    t0 = (P.X - P.Z)^2
    t1 = P.X * P.Z
    t1 += t1
    t1 += t1
    X = (t0 + t1) * (a24.Z*t0 + a24.X*t1)
    Z = a24.Z - a24.X
    Z *= t0
    Z *= t1
    return Proj1(X, Z)
end

# evaluation under 4-isogeny with kernel <(-1, -)>
function four_iso_eval_neg_one(a24::Proj1{T}, P::Proj1{T}) where T <: RingElem
    Q = four_iso_eval_one(Proj1(a24.Z-a24.X, a24.Z), Proj1(-P.X, P.Z))
    return Proj1(-Q.X, Q.Z)
end

# 4-isogeny with kernel <ker>
function four_iso(a24::Proj1{T}, ker::Proj1{T}, Qs::Vector{Proj1{T}}) where T <: RingElem
    imQs = Vector{Proj1{T}}(undef, length(Qs))
    if ker.X == ker.Z
        for i in 1:length(Qs)
            imQs[i] = four_iso_eval_one(a24, Qs[i])
        end
        a24 = four_iso_curve_one(a24)
    elseif ker.X == -ker.Z
        for i in 1:length(Qs)
            imQs[i] = four_iso_eval_neg_one(a24, Qs[i])
        end
        a24 = four_iso_curve_neg_one(a24)
    else
        a24, K1, K2, K3 = four_iso_curve(ker)
        for i in 1:length(Qs)
            imQs[i] = four_iso_eval(K1, K2, K3, Qs[i])
        end
    end
    return a24, imQs
end

# 3-isogeny, return (A + 2 : A - 2) and (K1, K2), where Mont_A = E/<P> with ord(P) = 3.
function three_iso_curve(P::Proj1)
    K1 = P.X - P.Z
    t0 = K1^2
    K2 = P.X + P.Z
    t1 = K2^2
    t2 = t0 + t1
    t3 = K1 + K2
    t3 *= t3
    t3 -= t2
    t2 = t1 + t3
    t3 += t0
    t4 = t3 + t0
    t4 += t4
    t4 += t1
    a24m = t2 * t4
    t4 = t1 + t2
    t4 += t4
    t4 += t0
    a24p = t3 * t4
    return Proj1(a24p, a24m), K1, K2
end

# The image of 3-isogeny using an output (K1, K2) of three_iso_curve().
function three_iso_eval(K1::T, K2::T, Q::Proj1{T}) where T <: RingElem
    t0 = Q.X + Q.Z
    t1 = Q.X - Q.Z
    t0 *= K1
    t1 *= K2
    t2 = t0 + t1
    t0 = t1 - t0
    t2 *= t2
    t0 *= t0
    X = Q.X * t2
    Z = Q.Z * t0
    return Proj1(X, Z)
end

# 3-isogeny with kernel <P>
function three_iso(P::Proj1{T}, Qs::Vector{Proj1{T}}) where T <: RingElem
    a24pm, K1, K2 = three_iso_curve(P)
    imQs = Vector{Proj1{T}}(undef, length(Qs))
    for i in 1:length(Qs)
        imQs[i] = three_iso_eval(K1, K2, Qs[i])
    end
    return a24pm, imQs
end

# 2^e-isogeny with kernel <K>. A = (a + 2)/4.
function two_e_iso(a24::Proj1{T}, P::Proj1{T}, e::Int, Qs::Vector{Proj1{T}}) where T <: RingElem
    k = e-2
    while k >= 0
        ker = xDBLe(P, a24, k)
        if ker.X == ker.Z
            k != 0 && (P = four_iso_eval_one(a24, P))
            for i in 1:length(Qs)
                Qs[i] = four_iso_eval_one(a24, Qs[i])
            end
            a24 = four_iso_curve_one(a24)
        elseif ker.X == -ker.Z
            k != 0 && (P = four_iso_eval_neg_one(a24, P))
            for i in 1:length(Qs)
                Qs[i] = four_iso_eval_neg_one(a24, Qs[i])
            end
            a24 = four_iso_curve_neg_one(a24)
        else
            a24, K1, K2, K3 = four_iso_curve(ker)
            k != 0 && (P = four_iso_eval(K1, K2, K3, P))
            for i in 1:length(Qs)
                Qs[i] = four_iso_eval(K1, K2, K3, Qs[i])
            end
        end
        k -= 2
    end
    if k == -1
        if P.X == 0
            a24, Qs = two_iso_zero(a24, Qs)
        else
            a24 = two_iso_curve(P)
            for i in 1:length(Qs)
                Qs[i] = two_iso_eval(P, Qs[i])
            end
        end
    end

    return a24, Qs
end

# 2^e-isogeny using strategy. A = (a + 2)/4.
function two_e_iso(a24::Proj1{T}, P::Proj1{T}, e::Int, Qs::Vector{Proj1{T}}, strategy::Vector{Int}, out_put_neighbor=0) where T <: RingElem
    if out_put_neighbor == 1
        K = xDBLe(P, a24, e-1)
        a24_neighbor = two_iso(a24, K)
    end
    if e % 2 == 1
        K = xDBLe(P, a24, e-1)
        if K.X == 0
            a24, tmp = two_iso_zero(a24, vcat([P], Qs))
        else
            a24 = two_iso_curve(K)
            tmp = vcat([two_iso_eval(K, P)], [two_iso_eval(K, Q) for Q in Qs])
        end
        P = tmp[1]
        Qs = tmp[2:end]
        e -= 1
    end

    S = [div(e, 2)]
    Ps = vcat(Qs, [P])
    i = 1
    while length(S) > 0
        h = pop!(S)
        K = pop!(Ps)
        if h == 1
            if length(S) == 0 && out_put_neighbor == -1
                a24_neighbor = two_iso(a24, xDBL(K, a24))
            end
            a24, Ps = four_iso(a24, K, Ps)
            S = [h - 1 for h in S]
        else
            push!(S, h)
            push!(Ps, K)
            K = xDBLe(K, a24, 2*strategy[i])
            push!(S, h - strategy[i])
            push!(Ps, K)
            i += 1
        end
    end
    if out_put_neighbor == 0
        return a24, Ps
    else
        return a24, Ps, a24_neighbor
    end
end

# 3^e-isogeny with kernel <K>. A = (a + 2)/4.
function three_e_iso(a24::Proj1{T}, P::Proj1{T}, e::Int, Qs::Vector{Proj1{T}}) where T <: RingElem
    a24pm = Proj1(a24.X, a24.X - a24.Z)
    k = e-1
    while k >= 0
        ker = xTPLe(P, a24pm, k)
        a24pm, K1, K2 = three_iso_curve(ker)
        k != 0 && (P = three_iso_eval(K1, K2, P))
        for i in 1:length(Qs)
            Qs[i] = three_iso_eval(K1, K2, Qs[i])
        end
        k -= 1
    end
    a24 = Proj1(a24pm.X, a24pm.X - a24pm.Z)
    return a24, Qs
end

# 3^e-isogeny using strategy. A = (a + 2)/4.
function three_e_iso(a24::Proj1{T}, P::Proj1{T}, e::Int, Qs::Vector{Proj1{T}}, strategy::Vector{Int}, output_neighbor=0) where T <: RingElem
    a24pm = Proj1(a24.X, a24.X - a24.Z)
    S = [e]
    Ps = vcat(Qs, [P])
    i = 1
    a24_neighbor = a24
    while length(S) > 0
        h = pop!(S)
        K = pop!(Ps)
        if h == 1
            if length(S) == 0 && output_neighbor == -1
                a24_neighbor = Proj1(a24pm.X, a24pm.X - a24pm.Z)
            end
            a24pm, Ps = three_iso(K, Ps)
            S = [h - 1 for h in S]
        else
            push!(S, h)
            push!(Ps, K)
            K = xTPLe(K, a24pm, strategy[i])
            push!(S, h - strategy[i])
            push!(Ps, K)
            i += 1
        end
    end
    a24 = Proj1(a24pm.X, a24pm.X - a24pm.Z)
    if output_neighbor == 0
        return a24, Ps
    else
        return a24, Ps, a24_neighbor
    end
end

# compute lam, mu s.t. y - (lam * x + mu) is the tangent line at T on E_A
function compute_lam_mu(A::FqFieldElem, xT::Proj1{FqFieldElem})
    x3 = affine(xT)
    y3 = square_root(x3 * (x3^2 + A*x3 + 1))
    lam = (3*x3^2 + 2*A*x3 + 1) / (2*y3)
    mu = y3 - lam * x3
    return lam, mu
end

# return a point P in E(Fp^2) \ [3]E(Fp^2) and lam, mu for P
function point_full3power(A::FqFieldElem, cofactor::BigInt, full_exp::Int, global_data::GlobalData)
    hint = 1
    a24 = A_to_a24(A)
    a24pm = a24_to_a24pm(a24)
    u = global_data.Elligator2u
    N = length(global_data.Elligator2)
    x = parent(A)(1)
    lam, mu = 0, 0
    is_neg = 0
    while true
        is_neg = 0
        if hint < N
            x = global_data.Elligator2[hint]
        else
            r = hint^2
            x = -1/(1 + u*r)
        end
        x = A * x
        if !is_square(x * (x^2 + A * x + 1))
            x = -x - A
            is_neg = 1
        end

        if lam == 0
            xP = Proj1(x)
            xP = ladder(cofactor, xP, a24)
            if is_infinity(xP)
                hint += 1
                continue
            end
            xQ = xP
            e = 0
            while true
                e += 1
                tmp = xTPL(xQ, a24pm)
                if is_infinity(tmp)
                    break
                end
                xQ = tmp
            end
            xT = xQ # point of order 3
            lam, mu = compute_lam_mu(A, xT)
            e == full_exp && break
        else
            y = square_root(x * (x^2 + A * x + 1))
            t = y - (lam * x + mu)
            if !is_cube(t)
                xP = Proj1(x)
                xP = ladder(cofactor, xP, a24)
                xT = xTPLe(xP, a24pm, full_exp - 1)
                lam, mu = compute_lam_mu(A, xT)
                break
            end
        end
        hint += 1
    end
    hint -= 1 # hint starts from 0

    @assert hint < 1 << 7
    hint += is_neg << 7

    return x, lam, mu, hint
end

# return a point P in E(Fp^2) \ [3]E(Fp^2) s.t. P is not above a point of order 3 corresponding to lam, mu
function point_full3power_not_above(A::FqFieldElem, lam::FqFieldElem, mu::FqFieldElem, hint_start::Int, global_data::GlobalData)
    mask = 0x7F
    hint_start &= mask
    hint = hint_start + 2
    u = global_data.Elligator2u
    N = length(global_data.Elligator2)
    x = parent(A)(1)
    is_neg = 0

    while true
        is_neg = 0
        if hint < N
            x = global_data.Elligator2[hint]
        else
            r = hint^2
            x = -1/(1 + u*r)
        end
        x = A * x
        if !is_square(x * (x^2 + A * x + 1))
            x = -x - A
            is_neg = 1
        end
        
        y = square_root(x * (x^2 + A * x + 1))
        t = y - (lam * x + mu)
        !is_cube(t) && break
        hint += 1
    end
    hint -= hint_start + 2 # hint starts from 0

    @assert hint < 1 << 7
    hint += is_neg << 7

    return x, hint
end

# return a point P in E(Fp^2) \ [3]E(Fp^2) from hint
function point_full3power_from_hint(A::FqFieldElem, hint::Int, global_data::GlobalData)
    u = global_data.Elligator2u
    N = length(global_data.Elligator2)
    mask = 0x7F
    is_neg = hint >> 7
    hint &= mask
    hint += 1

    if hint < N
        x = global_data.Elligator2[hint]
    else
        r = hint^2
        x = -1/(1 + u*r)
    end
    x = A * x
    is_neg == 1 && (x = -x - A)

    return x
end

# return a point P in E(Fp^2) \ [3]E(Fp^2) from hint
function point_full3power_not_above_from_hint(A::FqFieldElem, hint1::Int, hint2::Int, global_data::GlobalData)
    u = global_data.Elligator2u
    N = length(global_data.Elligator2)
    mask = 0x7F
    is_neg = hint2 >> 7
    hint1 &= mask
    hint2 &= mask
    hint = hint1 + hint2 + 2

    if hint < N
        x = global_data.Elligator2[hint]
    else
        r = hint^2
        x = -1/(1 + u*r)
    end
    x = A * x
    is_neg == 1 && (x = -x - A)

    return x
end

# return a basis of E[2^e]
function basis_2e(A::FqFieldElem, cofactor::BigInt, global_data::GlobalData)
    Fp2 = global_data.Fp2
    i = gen(global_data.Fp2)
    a24 = A_to_a24(A)
    if is_square(A)
        hA = 1
    else
        hA = 0
    end
    h = 0
    x1 = Fp2(0)
    x2 = Fp2(0)
    if hA == 1
        while true
            h += 1
            x1 = -1/(1 + i * h) * A
            !is_square(base_field(Fp2)(1 + h^2)) && is_square(x1 * (x1^2 + A * x1 + 1)) && break
        end
    else
        while true
            h += 1
            x1 = h * A
            is_square(x1 * (x1^2 + A * x1 + 1)) && break
        end
    end
    x2 = -x1 - A
    xP = ladder(cofactor, Proj1(x1), a24)
    xPQ = ladder(cofactor, Proj1(x2), a24)
    xQ = x_add_sub(xP, xPQ, a24)

    if h >= 1 << 7
        hint = 0
    else
        hint = (h << 1) + hA
    end
    
    return xP, xQ, xPQ, hint
end

# return a basis of E[2^e] from hint
function basis_2e_from_hint(A::FqFieldElem, cofactor::BigInt, hint::Int, global_data::GlobalData)
    if hint == 0
        xP, xQ, xPQ, _ = basis_2e(A, cofactor, global_data)
        return xP, xQ, xPQ
    end

    Fp2 = global_data.Fp2
    i = gen(global_data.Fp2)
    a24 = A_to_a24(A)
    hA = hint & 1
    h = hint >> 1

    if hA == 1
        x1 = -1/(1 + i * h) * A
    else
        x1 = h * A
    end
    x2 = -x1 - A

    xP = ladder(cofactor, Proj1(x1), a24)
    xPQ = ladder(cofactor, Proj1(x2), a24)
    xQ = x_add_sub(xP, xPQ, a24)

    return xP, xQ, xPQ
end

# return a basis of E[3^e]
function basis_3e(A::FqFieldElem, cofactor::BigInt, full_exp::Int, global_data::GlobalData)
    a24 = A_to_a24(A)
    x1, lam, mu, hint1 = point_full3power(A, cofactor, full_exp, global_data)
    x2, hint2 = point_full3power_not_above(A, lam, mu, hint1, global_data)
    xP = ladder(cofactor, Proj1(x1), a24)
    xQ = ladder(cofactor, Proj1(x2), a24)
    xPQ = x_add_sub(xP, xQ, a24)

    return xP, xQ, xPQ, hint1, hint2
end

# return a basis of E[3^e] from hint
function basis_3e_from_hint(A::FqFieldElem, cofactor::BigInt, hint1::Int, hint2::Int, global_data::GlobalData)
    a24 = A_to_a24(A)
    x1 = point_full3power_from_hint(A, hint1, global_data)
    x2 = point_full3power_not_above_from_hint(A, hint1, hint2, global_data)

    xP = ladder(cofactor, Proj1(x1), a24)
    xQ = ladder(cofactor, Proj1(x2), a24)
    xPQ = x_add_sub(xP, xQ, a24)

    return xP, xQ, xPQ
end

# Algorithm 1 in SQIsign documentation
function Montgomery_normalize(a24::Proj1{T}, Ps::Vector{Proj1{T}}) where T <: RingElem
    A = a24_to_A(a24)
    A2 = A.X^2
    C2 = A.Z^2
    twoC2 = C2 + C2
    threeC2 = twoC2 + C2
    d = A2 - twoC2 - twoC2
    d = square_root(d)
    inv_2C2_d = 1/(twoC2 * d)
    Z0 = (A2 + A2) * inv_2C2_d * d
    t1 = (threeC2 + threeC2 + threeC2 - A2) * d
    t2 = (A2 - threeC2) * A.X
    Z1 = (t1 + t2) * inv_2C2_d
    Z2 = (t1 - t2) * inv_2C2_d

    Z = Z0
    lex_order(Z1, Z) && (Z = Z1)
    lex_order(Z2, Z) && (Z = Z2)

    Ad = Proj1(square_root(Z))

    if A == Ad
        R1, R2 = 0, 1
        U1, U2 = 1, 1
    elseif A == -Ad
        R1, R2 = 0, 1
        U1, U2 = -1, 1
    else
        Ad2 = Ad.X^2
        Cd2 = Ad.Z^2
        ACd2 = A2 * Cd2
        AdC2 = Ad2 * C2
        threeCCd2 = Cd2 * threeC2
        nineCCd2 = threeCCd2 + threeCCd2 + threeCCd2
        R1 = (ACd2 + AdC2 - threeCCd2 - threeCCd2) * A.X
        R2 = (ACd2 + AdC2 + AdC2 - nineCCd2) * A.Z
        U1 = Ad.X * A.Z * R2
        R1C = R1 * A.Z
        U2 = (A.X * R2 - R1C - R1C - R1C) * Ad.Z
    end

    images = Vector{Proj1{T}}(undef, length(Ps))
    for i in 1:length(Ps)
        P = Ps[i]
        X = P.X
        Z = P.Z
        images[i] = Proj1(U1*(X*R2 + Z*R1), U2*Z*R2)
    end

    return A_to_a24(Ad), images
end

# return a generator of the kernel of a 3-isogeny from a24 to a24d
function three_isogenous_coeff_to_kernel(a24::Proj1{T}, a24d::Proj1{T}) where T <: RingElem
    A = a24_to_A(a24)
    Ad = a24_to_A(a24d)

    X = A.X^3*Ad.Z^2 + 18*A.X^2*Ad.X*A.Z*Ad.Z - 3*A.X*Ad.X^2*A.Z^2 + 48*A.X*A.Z^2*Ad.Z^2 - 112*Ad.X*A.Z^3*Ad.Z
    Z = 4*A.X^3*Ad.X*Ad.Z + 114*A.X^2*A.Z*Ad.Z^2 + 12*A.X*Ad.X*A.Z^2*Ad.Z + 2*Ad.X^2*A.Z^3 - 576*A.Z^3*Ad.Z^2

    return Proj1(X, Z)
end

# compute the images under an isomorphism from a24 to a24d of points
# Algorithm 8.9 in SQIsign v 2.0 specification
function IsomorphismMontgomery(a24::Proj1{T}, a24d::Proj1{T}, points::Vector{Proj1{T}}) where T <: RingElem
    A = a24_to_A(a24)
    Ad = a24_to_A(a24d)
    
    lambda_x = (2*Ad.X^3 - 9*Ad.X*Ad.Z^2) * (3*A.Z^3 - A.X^2*A.Z)
    lambda_z = (2*A.X^3 - 9*A.X*A.Z^2) * (3*Ad.Z^3 - Ad.X^2*Ad.Z)
    @assert lambda_x != 0
    @assert lambda_z != 0

    ret = Vector{Proj1{T}}(undef, length(points))
    for i in 1:length(points)
        P = points[i]
        X = lambda_x * (3 * P.X * A.Z * Ad.Z + A.X * Ad.Z * P.Z) - lambda_z * Ad.X * A.Z * P.Z
        Z = 3 * lambda_z * A.Z * Ad.Z * P.Z
        ret[i] = Proj1(X, Z)
    end

    return ret
end