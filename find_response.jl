using Nemo
import Pkg
Pkg.activate(@__DIR__)
using SQIsign2D_Push

function benchmark_test(param::Module, num::Int, num_pk::Int)
    global_data = param.make_precomputed_values()
    
    println("\nLevel: $(param)")
    for i in 1:num_pk
        println("test $i start")
        pk, sk = param.key_gen(global_data)
        m = "message to sign"
        count = 0
        for k in 1:num
            found, bs, ideal_check = param.signing(pk, sk, m, global_data)
            if !found
                count += 1
            end
            #print("\r($k/$num) done. fail: $count")
        end
        println("fail response: $count/$num")
    end
end

@assert length(ARGS) == 3
level = parse(Int, ARGS[1])
num_pk = parse(Int, ARGS[2])
num = parse(Int, ARGS[3])

params = [SQIsign2D_Push.Level1, SQIsign2D_Push.Level3, SQIsign2D_Push.Level5]

benchmark_test(params[level], num, num_pk)
