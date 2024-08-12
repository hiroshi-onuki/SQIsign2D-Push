using SQIsign2D_Push

function check(param::Module, num::Int, is_compact::Bool)
    global_data = param.make_precomputed_values()
    for i in 1:num
        pk, sk = param.key_gen(global_data)
        sign = param.signing(pk, sk, "message to sign", global_data, is_compact)
        if is_compact
             ver = param.verify_compact(pk, sign, "message to sign", global_data)
        else
            ver = param.verify(pk, sign, "message to sign", global_data)
        end
        println("ver: ", ver)
    end
end

check(SQIsign2D_Push.Level1, 10, false)
check(SQIsign2D_Push.Level1, 10, true)
