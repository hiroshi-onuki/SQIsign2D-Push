using SQIsign2D_Push

function check(param::Module, num::Int, is_compact::Bool)
    global_data = param.make_precomputed_values()
    for i in 1:num
        pk, sk = param.key_gen(global_data)
        a24m, s0, s1, M0, M1, xPm, xQm, xPQm, xP, xQ, xPQ, I, nI = sk
        sign = param.signing(pk, sk, "message to sign", global_data, false)
        ver = param.verify(pk, sign, "message to sign", global_data)
        println("ver: ", ver)
        #=
        m = "hello"
        sign = param.signing(pk, sk, m, global_data, is_compact)
        i == 1 && println("sign len: ", length(sign))
        if !is_compact
            @assert param.verify(pk, sign, m, global_data)
        else
            @assert param.verify_compact(pk, sign, m, global_data)
        end
        =#
    end
end

check(SQIsign2D_Push.Level1, 10, false)
check(SQIsign2D_Push.Level1, 10, true)
