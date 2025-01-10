using Nemo
import Pkg
Pkg.activate(@__DIR__)
using SQIsign2D_Push

function benchmark_test(param::Module, num::Int, num_pk::Int)
    global_data = param.make_precomputed_values()
    
    for i in 1:num_pk
        println("test $i start")
        pk, sk = param.key_gen(global_data)
        m = "message to sign"
        count = 0
        for k in 1:num
            found, bs, ideal_check = param.signing(pk, sk, m, global_data)
            if !found
                count += 1
                println("not found")
            end
            print("\r($k/$num) done. fail: $count")
        end
        println("\nfail response: $count/$num")
    end
end

num = 100
num_pk = 10
@time benchmark_test(SQIsign2D_Push.Level1, num, num_pk)
@time benchmark_test(SQIsign2D_Push.Level3, num, num_pk)
@time benchmark_test(SQIsign2D_Push.Level5, num, num_pk)