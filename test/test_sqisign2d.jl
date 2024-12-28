using SQIsign2D_Push

function check(param::Module, num::Int)
    global_data = param.make_precomputed_values()
    for i in 1:num
        println("test $i start")
        @time pk, sk = param.key_gen(global_data)
        m = "message to sign"
        @time sign = param.signing(pk, sk, m, global_data)
        println("sign len: ", length(sign))
        @time verified = param.verify(pk, sign, m, global_data)
        @assert verified
    end
end

check(SQIsign2D_Push.Level1, 100)
