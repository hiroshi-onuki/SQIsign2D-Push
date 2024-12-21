using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()

    two_to_e2 = param.two_to_e2
    for _ in 1:num
        q = 0
        while q % 3 == 0 || q % 2 == 0
            q = rand(1:two_to_e2-1)
        end
        a24m, a24, xK1, xK2, xP2m, xQ2m, xPQ2m, xP2, xQ2, xPQ2, J = param.FastDoublePath(false, global_data)

        w0 = global_data.E0_data.Weil_P2eQ2e
        w_m = Weil_pairing_2power(Montgomery_coeff(a24m), xP2m, xQ2m, xPQ2m, param.ExponentOfTwo)
        w = Weil_pairing_2power(Montgomery_coeff(a24), xP2, xQ2, xPQ2, param.ExponentOfTwo)
        @assert w_m == w0^param.three_to_e3
        @assert w == w_m^param.three_to_e3

        a24aux, xP2aux, xQ2aux, xPQ2aux = param.PushRandIsog(two_to_e2 - q, a24m, xK1, xK2, xP2m, xQ2m, xPQ2m, global_data)

        w = Weil_pairing_2power(Montgomery_coeff(a24), xP2, xQ2, xPQ2, param.ExponentOfTwo)
        w_aux = Weil_pairing_2power(Montgomery_coeff(a24aux), xP2aux, xQ2aux, xPQ2aux, param.ExponentOfTwo)

        @assert w_aux == w^(two_to_e2 - q)
    end
end

check(SQIsign2D_Push.Level1, 100)
