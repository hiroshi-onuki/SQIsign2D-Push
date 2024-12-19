using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()

    two_to_e2 = BigInt(2)^param.ExponentOfTwo
    for _ in 1:num
        q = 0
        while q % 3 == 0 || q % 2 == 0
            q = rand(1:two_to_e2-1)
        end
        param.ComposedRandIsog(two_to_e2 - q, global_data.E0_data.basis3e.xP, global_data)
    end
end

check(SQIsign2D_Push.Level1, 10)
