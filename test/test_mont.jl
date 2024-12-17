using Nemo
using SQIsign2D_Push

function check(num::Int)
    p = BigInt(2)^132 * BigInt(3)^80 * 7 - 1
    _, T = polynomial_ring(GF(p), "T")
    Fp2, _ = finite_field(T^2 + 1, "i")
    A0 = Fp2(0)
    a24_0 = Proj1(A0 + 2, Fp2(4))
    exp2 = 132
    exp3 = 80
    for i in 1:num
        A = rand(Fp2)
        C = rand(Fp2)
        a24 = Proj1(A + 2*C, 4*C)
        a24pm = Proj1(A + 2*C, A - 2*C)
        P = random_point(Proj1(A, C))
        e = rand(1:10)
        @assert ladder(3^e, P, a24) == xTPLe(P, a24pm, e)

        # make a random s.s. curve
        P = random_point_order_l_power(A0, p + 1, 2, exp2)
        a24, _ = two_e_iso(a24_0, P, exp2, Proj1{FqFieldElem}[])
        a24pm = Proj1(a24.X, a24.X - a24.Z)

        P = random_point_order_l(a24, p + 1, 3)
        @assert is_infinity(ladder(3, P, a24))
        Q = random_point(a24_to_A(a24))

        a24d, Qs = odd_isogeny(a24, P, 3, [Q])
        Qd = Qs[1]
        a24pm_d, K1, K2 = three_iso_curve(P)
        a24dd = Proj1(a24pm_d.X, a24pm_d.X - a24pm_d.Z)
        Qdd = three_iso_eval(K1, K2, Q)
        @assert a24d == a24dd
        @assert Qd == Qdd

        A = Montgomery_coeff(a24)
        P = random_point_order_l_power(A, p + 1, 3, 4)
        a24d, Qs = odd_isogeny(a24, P, 3^4, [Q])
        Qd = Qs[1]
        a24dd, Qs = three_e_iso(a24, P, 4, [Q])
        Qdd = Qs[1]
        @assert a24d == a24dd
        @assert Qd == Qdd

        strategy = compute_strategy(exp3 - 1, 1, 1)
        P = random_point_order_l_power(A, p + 1, 3, exp3)
        @time a24d, Qs = three_e_iso(a24, P, exp3, [Q])
        Qd = Qs[1]
        @time a24dd, Qs = three_e_iso(a24, P, exp3, [Q], strategy)
        Qdd = Qs[1]
        @assert a24d == a24dd
        @assert Qd == Qdd
    end
end

check(10)