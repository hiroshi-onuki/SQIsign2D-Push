using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()
    for i in 1:num
        pk, sk = param.key_gen(global_data)
        m = "message to sign"
        param.signing(pk, sk, m, global_data)
        """
        sign, cnt = param.signing(pk, sk, m, global_data, is_compact)
        println("sign len: ", length(sign), " cnt: ", cnt)
        if is_compact
            @assert param.verify_compact(pk, sign, m, global_data)
        else
            @assert param.verify(pk, sign, m, global_data)
        end
        """
    end
end

check(SQIsign2D_Push.Level1, 100)
