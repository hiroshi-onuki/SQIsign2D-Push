export ec_bi_dlog_odd_prime_power, fp2_dlog, ec_bi_dlog

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
    P = Point(Proj1(A), xP)
    Q = Point(Proj1(A), xQ)
    PQ = add(P, -Q, Proj1(A))
    if !(xPQ == Proj1(PQ.X, PQ.Z))
        Q = -Q
    end
    R = Point(Proj1(A), xR)
    S = Point(Proj1(A), xS)
    RS = add(R, -S, Proj1(A))
    if !(xRS == Proj1(RS.X, RS.Z))
        S = -S
    end
    a, b = ec_bi_dlog_odd_prime_power(A, P, R, S, l, e)
    c, d = ec_bi_dlog_odd_prime_power(A, Q, R, S, l, e)
    return a, b, c, d
end

function ec_bi_dlog_odd_prime_power(A::T, xP::Proj1{T}, xR::Proj1{T}, xS::Proj1{T}, xRS::Proj1{T}, l::Int, e::Int) where T <: RingElem
    P = Point(Proj1(A), xP)
    R = Point(Proj1(A), xR)
    S = Point(Proj1(A), xS)
    RS = add(R, -S, Proj1(A))
    if !(xRS == Proj1(RS.X, RS.Z))
        S = -S
    end
    a, b = ec_bi_dlog_odd_prime_power(A, P, R, S, l, e)
    return a, b
end

# return n such that x = base^n where ord(base) = l^e
# the method is recursive
function fp2_dlog(x::FqFieldElem, base::FqFieldElem, l::Int, e::Int)
    if e == 0
        return 0
    elseif e == 1
        # Base case: when e == 1, we need to find n such that x = base^n
        for n in 0:l-1
            if base^n == x
                return n
            end
        end
        error("No discrete logarithm found")
    else
        # Recursive case: reduce the problem to a smaller instance
        ed = Int(ceil(e//2))
        x2 = x^(BigInt(l)^(e - ed))
        base2 = base^(BigInt(l)^(e - ed))
        n = fp2_dlog(x2, base2, l, ed)
        x = x * base^(-n)
        base = base2^(BigInt(l)^(2*ed - e))
        return n + BigInt(l)^ed * fp2_dlog(x, base, l, e - ed)
    end
end

function ec_bi_dlog(a24::Proj1{T}, b1::BasisData, b2::BasisData, l::Int, e::Int) where T <: RingElem
    A = a24_to_A(a24)
    P1, Q1 = Recover_y_from_basis(A, b1)
    P2, Q2 = Recover_y_from_basis(A, b2)
    P1 = Point(a24_to_A(a24), b1.xP)
    @assert P1 == Point(A, b1.xP) || P1 == -Point(A, b1.xP)
    @assert Q1 == Point(A, b1.xQ) || Q1 == -Point(A, b1.xQ)

    return 0, 0, 0, 0
end