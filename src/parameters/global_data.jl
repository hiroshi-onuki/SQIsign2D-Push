struct DlogData
    e::Int
    window_size::Int
    T1::Vector{Vector{FqFieldElem}}
    T2::Vector{Vector{FqFieldElem}}
    strategy::Vector{Int}
end

struct OrderData
    d::Int
    A::FqFieldElem
    j_inv::FqFieldElem
    a24_0::Proj1{FqFieldElem}
    xP2e::Proj1{FqFieldElem}
    xQ2e::Proj1{FqFieldElem}
    xPQ2e::Proj1{FqFieldElem}
    xP2e_id2iso_d2::Proj1{FqFieldElem}
    xQ2e_id2iso_d2::Proj1{FqFieldElem}
    xPQ2e_id2iso_d2::Proj1{FqFieldElem}
    I::LeftIdeal
    M::Matrix{BigInt}
    connecting_deg::BigInt
    M_sqrt_d::Matrix{BigInt}
    tate_tableP::Vector{Vector{FqFieldElem}}
    tate_tableQ::Vector{Vector{FqFieldElem}}
    dlog_base::BigInt
end

struct BasisData
    xP::Proj1{FqFieldElem}
    xQ::Proj1{FqFieldElem}
    xPQ::Proj1{FqFieldElem}
end

struct E0Data
    A0::FqFieldElem
    A0d::FqFieldElem
    A0dd::FqFieldElem
    a24_0::Proj1{FqFieldElem}
    j0::FqFieldElem
    basis2e3e::BasisData
    basis2e::BasisData
    basis3e::BasisData
    Matrices_2e::Vector{Matrix{BigInt}}
    Matrices_3e::Vector{Matrix{BigInt}}
    Weil_P2eQ2e::FqFieldElem
    isomorphism_to_A0::Function
    dlog_data::DlogData
    tate_table::Vector{Vector{FqFieldElem}}
end

# structure for precomputed values
struct GlobalData
    Fp2::FqField
    E0_data::E0Data
end