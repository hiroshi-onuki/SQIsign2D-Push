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

# return (a, b, c, d) such that b1.P = [a]b2.P + [b]b2.Q and b1.Q = [c]b2.P + [d]b2.Q
function ec_bi_dlog(a24::Proj1{T}, b1::BasisData, b2::BasisData, l::Int, e::Int) where T <: RingElem

    if l == 2 && e == 1
        if b1.xP == b2.xP
            a, b = 1, 0
        elseif b1.xP == b2.xQ
            a, b = 0, 1
        elseif b1.xP == b2.xPQ
            a, b = 1, 1
        else
            a, b = 0, 0
        end
        if b1.xQ == b2.xP
            c, d = 1, 0
        elseif b1.xQ == b2.xQ
            c, d = 0, 1
        elseif b1.xQ == b2.xPQ
            c, d = 1, 1
        else
            c, d = 0, 0
        end
        return a, b, c, d
    end

    xP1, xQ1, xPQ1 = b1.xP, b1.xQ, b1.xPQ
    xP2, xQ2, xPQ2 = b2.xP, b2.xQ, b2.xPQ
    A = a24_to_A(a24)

    # compute x(P1 - P2), x(P1 - Q2), x(Q1 - P2), x(Q1 - Q2)
    P1, Q1 = Recover_y_from_basis(A, b1)
    P2, Q2 = Recover_y_from_basis(A, b2)
    skip_P1 = false
    skip_Q1 = false
    if P1 == P2
        a, b = 1, 0
        skip_P1 = true
    elseif P1 == Q2
        a, b = 0, 1
        skip_P1 = true
    end
    if Q1 == P2
        c, d = 1, 0
        skip_Q1 = true
    elseif Q1 == Q2
        c, d = 0, 1
        skip_Q1 = true
    end
    if skip_P1 && skip_Q1
        return a, b, c, d
    end
    !skip_P1 && (xP1P2 = add_xonly(P1, -P2, A))
    !skip_P1 && (xP1Q2 = add_xonly(P1, -Q2, A))
    !skip_Q1 && (xQ1P2 = add_xonly(Q1, -P2, A))
    !skip_Q1 && (xQ1Q2 = add_xonly(Q1, -Q2, A))

    # compute affine points
    elements_for_inv = [a24.Z]
    !skip_P1 && push!(elements_for_inv, xP1.X)
    !skip_P1 && push!(elements_for_inv, xP1.Z)
    !skip_Q1 && push!(elements_for_inv, xQ1.X)
    !skip_Q1 && push!(elements_for_inv, xQ1.Z)
    push!(elements_for_inv, xP2.X)
    push!(elements_for_inv, xP2.Z)
    push!(elements_for_inv, xQ2.X)
    push!(elements_for_inv, xQ2.Z)
    push!(elements_for_inv, xPQ2.Z)
    !skip_P1 && push!(elements_for_inv, xP1P2.Z)
    !skip_P1 && push!(elements_for_inv, xP1Q2.Z)
    !skip_Q1 && push!(elements_for_inv, xQ1P2.Z)
    !skip_Q1 && push!(elements_for_inv, xQ1Q2.Z)
    if l != 2
        push!(elements_for_inv, xPQ2.X)
        !skip_P1 && push!(elements_for_inv, xP1P2.X)
        !skip_P1 && push!(elements_for_inv, xP1Q2.X)
        !skip_Q1 && push!(elements_for_inv, xQ1P2.X)
        !skip_Q1 && push!(elements_for_inv, xQ1Q2.X)
    end
    inv_elements = batched_inversion(elements_for_inv)
    a24af = a24.X * inv_elements[1]
    idx = 2
    if !skip_P1
        xP1af = xP1.X * inv_elements[idx+1]
        xP1inv = xP1.Z * inv_elements[idx]
        idx += 2
    end
    if !skip_Q1
        xQ1af = xQ1.X * inv_elements[idx+1]
        xQ1inv = xQ1.Z * inv_elements[idx]
        idx += 2
    end
    xP2af = xP2.X * inv_elements[idx+1]
    xP2inv = xP2.Z * inv_elements[idx]
    xQ2af = xQ2.X * inv_elements[idx+3]
    xQ2inv = xQ2.Z * inv_elements[idx+2]
    xPQ2af = xPQ2.X * inv_elements[idx+4]
    idx += 5
    if !skip_P1
        xP1P2af = xP1P2.X * inv_elements[idx]
        xP1Q2af = xP1Q2.X * inv_elements[idx+1]
        idx += 2
    end
    if !skip_Q1
        xQ1P2af = xQ1P2.X * inv_elements[idx]
        xQ1Q2af = xQ1Q2.X * inv_elements[idx+1]
        idx += 2
    end
    if l != 2
        xPQ2inv = xPQ2.Z * inv_elements[idx]
        idx += 1
        if !skip_P1
            xP1P2inv = xP1P2.Z * inv_elements[idx]
            xP1Q2inv = xP1Q2.Z * inv_elements[idx+1]
            idx += 2
        end
        if !skip_Q1
            xQ1P2inv = xQ1P2.Z * inv_elements[idx]
            xQ1Q2inv = xQ1Q2.Z * inv_elements[idx+1]
        end
    end

    # compute Weil pairings
    n = BigInt(l)^e
    if l == 2
        w0n, w0d = Weil_pairing_2power(a24af, xP2af, xP2inv, xQ2af, xQ2inv, xPQ2af, e)
        if !skip_P1
            w1n, w1d = Weil_pairing_2power(a24af, xP1af, xP1inv, xP2af, xP2inv, xP1P2af, e)
            w2n, w2d = Weil_pairing_2power(a24af, xP1af, xP1inv, xQ2af, xQ2inv, xP1Q2af, e)
        end
        if !skip_Q1
            w3n, w3d = Weil_pairing_2power(a24af, xQ1af, xQ1inv, xP2af, xP2inv, xQ1P2af, e)
            w4n, w4d = Weil_pairing_2power(a24af, xQ1af, xQ1inv, xQ2af, xQ2inv, xQ1Q2af, e)
        end
    else
        w0n, w0d = Weil_pairing_odd(a24af, xP2af, xP2inv, xQ2af, xQ2inv, xPQ2af, xPQ2inv, n)
        if !skip_P1
            w1n, w1d = Weil_pairing_odd(a24af, xP1af, xP1inv, xP2af, xP2inv, xP1P2af, xP1P2inv, n)
            w2n, w2d = Weil_pairing_odd(a24af, xP1af, xP1inv, xQ2af, xQ2inv, xP1Q2af, xP1Q2inv, n)
        end
        if !skip_Q1
            w3n, w3d = Weil_pairing_odd(a24af, xQ1af, xQ1inv, xP2af, xP2inv, xQ1P2af, xQ1P2inv, n)
            w4n, w4d = Weil_pairing_odd(a24af, xQ1af, xQ1inv, xQ2af, xQ2inv, xQ1Q2af, xQ1Q2inv, n)
        end
    end
    elements_for_inv = [w0d]
    if !skip_P1
        push!(elements_for_inv, w1d)
        push!(elements_for_inv, w2d)
    end
    if !skip_Q1
        push!(elements_for_inv, w3d)
        push!(elements_for_inv, w4d)
    end
    inv_elements = batched_inversion(elements_for_inv)
    w0 = w0n * inv_elements[1]
    idx = 2
    if !skip_P1
        w1 = w1n * inv_elements[idx]
        w2 = w2n * inv_elements[idx+1]
        idx += 2
    end
    if !skip_Q1
        w3 = w3n * inv_elements[idx]
        w4 = w4n * inv_elements[idx+1]
    end

    # compute discrete logarithms
    if !skip_P1
        a = fp2_dlog(w1, w0, l, e)
        b = fp2_dlog(w2, w0, l, e)
    end
    if !skip_Q1
        c = fp2_dlog(w3, w0, l, e)
        d = fp2_dlog(w4, w0, l, e)
    end

    if skip_P1
        return a, b, d, n-c
    elseif skip_Q1
        return b, n-a, c, d
    end

    return b, n-a, d, n-c
end