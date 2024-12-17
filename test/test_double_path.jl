using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()
end

check(SQIsign2D_Push.Level1, 10)


