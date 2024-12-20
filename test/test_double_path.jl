using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()

    for _ in 1:num
        param.FastDoublePath(true, global_data)
    end
end

check(SQIsign2D_Push.Level1, 10)


