
# x^(2^e)
function square_e(x::FqFieldElem, e::Int)
    y = x
    for i in 1:e
        y = y^2
    end
    return y
end

# return n such that x = base^e
function fq_dlog_power_of_2(x::FqFieldElem, base::FqFieldElem, e::Integer)
    n = BigInt(0)
    t = x
    for i in 1:e
        if t^(BigInt(2)^(e-i)) == base^(BigInt(2)^(e-1))
            n += BigInt(2)^(i-1)
            t //= square_e(base, i-1)
        end
    end
    return n
end

function bi_dlog_odd_prime(A::T, P::Point{T}, R::Point{T}, S::Point{T}, l::Int) where T <: RingElem
    Pd = infinity_full_point(parent(A))
    for a in 0:(l-1)
        Pdd = Pd
        for b in 0:(l-1)
            if P == Pdd
                return a, b
            end
            Pdd = add(Pdd, S, Proj1(A))
        end
        Pd = add(Pd, R, Proj1(A))
    end
    @assert false "bi_dlog_odd_prime: no solution"
end

function ec_bi_dlog_odd_prime_power(A::T, P::Point{T}, R::Point{T}, S::Point{T}, l::Int, e::Int) where T <: RingElem
    e == 1 && return bi_dlog_odd_prime(A, P, R, S, l)
    f = div(e, 2)
    Pd = mult(BigInt(l)^(e - f), P, Proj1(A))
    Rd = mult(BigInt(l)^(e - f), R, Proj1(A))
    Sd = mult(BigInt(l)^(e - f), S, Proj1(A))
    a, b = ec_bi_dlog_odd_prime_power(A, Pd, Rd, Sd, l, f)
    aRbS = add(mult(a, R, Proj1(A)), mult(b, S, Proj1(A)), Proj1(A))
    P = add(P, -aRbS, Proj1(A))
    R = mult(BigInt(l)^f, R, Proj1(A))
    S = mult(BigInt(l)^f, S, Proj1(A))
    c, d = ec_bi_dlog_odd_prime_power(A, P, R, S, l, e - f)
    return a + c * BigInt(l)^f, b + d * BigInt(l)^f
end

function ec_bi_dlog_odd_prime_power(A::T, xP::Proj1{T}, xQ::Proj1{T}, xPQ::Proj1{T}, xR::Proj1{T}, xS::Proj1{T}, xRS::Proj1{T}, l::Int, e::Int) where T <: RingElem
    P = Point(A, xP)
    Q = Point(A, xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    R = Point(A, xR)
    S = Point(A, xS)
    RS = add(R, -S, Proj1(A))
    if !(xRS == Proj1(RS.X, RS.Z))
        S = -S
    end
    a, b = ec_bi_dlog_odd_prime_power(A, P, R, S, l, e)
    c, d = ec_bi_dlog_odd_prime_power(A, Q, R, S, l, e)
    return a, b, c, d
end

function ec_bi_dlog_odd_prime_power(A::T, xP::Proj1{T}, xR::Proj1{T}, xS::Proj1{T}, xRS::Proj1{T}, l::Int, e::Int) where T <: RingElem
    P = Point(A, xP)
    R = Point(A, xR)
    S = Point(A, xS)
    RS = add(R, -S, Proj1(A))
    if !(xRS == Proj1(RS.X, RS.Z))
        S = -S
    end
    a, b = ec_bi_dlog_odd_prime_power(A, P, R, S, l, e)
    return a, b
end
