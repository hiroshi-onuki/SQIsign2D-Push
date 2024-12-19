using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()

    param.ComposedRandIsog(BigInt(3214321531235125321), global_data.E0_data.basis3e.xP, global_data)
end

check(SQIsign2D_Push.Level1, 10)
