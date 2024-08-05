using Nemo
import Pkg
Pkg.activate(@__DIR__)
using SQIsign2D_Push

struct param
    mod::Module
    level::Int
    ds::Vector{Int}
end

params = [param(SQIsign2D_Push.Level1, 1, [2, 13, 15])]

for param in params
    println("Making order data for $(param.mod)")
    _, E0 = param.mod.make_E0_data()

    orders = []
    for d in param.ds
        println("Computing order data for d = $d")
        order = param.mod.compute_order_d(E0, d)
        push!(orders, order)
        println(order.j_inv)
    end

    open("src/parameters/level$(param.level)/precomputed_order_data.jl", "w") do file
        for order in orders
            println(file, "function order_data_$(order.d)()")
            println(file, "    d = $(order.d)")
            println(file, "    A = [$(coeff(order.A, 0)), $(coeff(order.A, 1))]")
            println(file, "    I = ", order.I)
            println(file, "    M = ", order.M)
            println(file, "    N = ", order.connecting_deg)
            println(file, "    M_sqrt_d = ", order.M_sqrt_d)
            println(file, "    return d, A, I, M, N, M_sqrt_d")
            println(file, "end\n")
        end
    end
end