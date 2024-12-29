export fp2_dlog, ec_bi_dlog, ec_bi_dlog_one_point

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

    xP1, xQ1 = b1.xP, b1.xQ
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

# return (1, a) (resp. (a, 1)) s.t. [c]P = basis.P + [a]basis.Q (resp. [c]Q = basis.P + [a]basis.Q) for some c
function ec_bi_dlog_one_point(a24::Proj1{T}, xP::Proj1{T}, basis::BasisData, l::Int, e::Int) where T <: RingElem
    A = a24_to_A(a24)

    # compute x(P - Pb), x(P - Qb)
    P = Point(A, xP)
    Pb, Qb = Recover_y_from_basis(A, basis)
    if P == Pb
        return 1, 0
    elseif P == Qb
        return 0, 1
    end
    xPPb = add_xonly(P, -Pb, A)
    xPQb = add_xonly(P, -Qb, A)

    # compute affine points
    elements_for_inv = [a24.Z, xP.X, xP.Z, basis.xP.X, basis.xP.Z, basis.xQ.X, basis.xQ.Z, xPPb.Z, xPQb.Z]
    if l != 2
        push!(elements_for_inv, xPPb.X)
        push!(elements_for_inv, xPQb.X)
    end
    inv_elements = batched_inversion(elements_for_inv)
    a24af = a24.X * inv_elements[1]
    xPaf = xP.X * inv_elements[3]
    xPinv = xP.Z * inv_elements[2]
    xPbaf = basis.xP.X * inv_elements[5]
    xPbinv = basis.xP.Z * inv_elements[4]
    xQbaf = basis.xQ.X * inv_elements[7]
    xQbinv = basis.xQ.Z * inv_elements[6]
    xPPbaf = xPPb.X * inv_elements[8]
    xPQbaf = xPQb.X * inv_elements[9]
    if l != 2
        xPPbinv = xPPb.Z * inv_elements[10]
        xPQbinv = xPQb.Z * inv_elements[11]
    end

    # compute Weil pairings
    n = BigInt(l)^e
    if l == 2
        wPn, wPd = Weil_pairing_2power(a24af, xPaf, xPinv, xPbaf, xPbinv, xPPbaf, e)
        wQn, wQd = Weil_pairing_2power(a24af, xPaf, xPinv, xQbaf, xQbinv, xPQbaf, e)
    else
        wPn, wPd = Weil_pairing_odd(a24af, xPaf, xPinv, xPbaf, xPbinv, xPPbaf, xPPbinv, n)
        wQn, wQd = Weil_pairing_odd(a24af, xPaf, xPinv, xQbaf, xQbinv, xPQbaf, xPQbinv, n)
    end
    wPd, wQn = batched_inversion([wPd, wQn])
    wP = wPn * wPd
    wQ = wQn * wQd

    if wP^div(n, l) == 1
        return 1, fp2_dlog(wP, wQ, l, e)
    else
        return fp2_dlog(wQ, wP, l, e), 1
    end

end