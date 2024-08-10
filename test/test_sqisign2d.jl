using SQIsign2D_Push

function check(param::Module, num::Int, is_compact::Bool)
    global_data = param.make_precomputed_values()
    for i in 1:num
        pk, (a24m, s0, s1, M0, M1, xPm, xQm, xPQm, xP, xQ, xPQ, I) = param.key_gen(global_data)
        param.PushRandIsog(BigInt(13123214321), a24m, pk, s0, s1, xPm, xQm, xPQm, xP, xQ, xPQ, M0, M1, global_data)
        println(i)
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
