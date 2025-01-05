export BasisData, E0Data, GlobalData

# x(P), x(Q), x(P-Q)
struct BasisData
    xP::Proj1{FqFieldElem}
    xQ::Proj1{FqFieldElem}
    xPQ::Proj1{FqFieldElem}
end

struct E0Data
    A0::FqFieldElem
    a24_0::Proj1{FqFieldElem}
    basis2e::BasisData
    basis3e::BasisData
    Matrices_2e::Vector{Matrix{BigInt}}
    Matrices_3e::Vector{Matrix{BigInt}}
    M44inv_chall::Matrix{BigInt}
end

# structure for precomputed values
struct GlobalData
    Fp2::FqField
    E0_data::E0Data
    NSQs::Vector{FqFieldElem}
    SQNSQs::Vector{FqFieldElem}
    Elligator2::Vector{FqFieldElem}
    Elligator2u::FqFieldElem
end