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

struct E0Data
    A0::FqFieldElem
    A0d::FqFieldElem
    A0dd::FqFieldElem
    a24_0::Proj1{FqFieldElem}
    j0::FqFieldElem
    P2e::Point{FqFieldElem}
    Q2e::Point{FqFieldElem}
    xP2e::Proj1{FqFieldElem}
    xQ2e::Proj1{FqFieldElem}
    xPQ2e::Proj1{FqFieldElem}
    xP2e_id2iso_d2::Proj1{FqFieldElem}
    xQ2e_id2iso_d2::Proj1{FqFieldElem}
    xPQ2e_id2iso_d2::Proj1{FqFieldElem}
    DegreesOddTorsionBases::Vector{Int}
    ExponentsOddTorsionBases::Vector{Int}
    OddTorsionBases::Vector{Vector{Proj1{FqFieldElem}}}
    Matrices_2e::Vector{Matrix{BigInt}}
    Matrix_2ed_inv::Matrix{BigInt}
    Matrix_2ed2_inv::Matrix{BigInt}
    Matrices_odd::Vector{Vector{Matrix{Int}}}
    Weil_P2eQ2e::FqFieldElem
    isomorphism_to_A0::Function
    dlog_data_full::DlogData
    dlog_data_chall::DlogData
    dlog_data_chall2::DlogData
    dlog_data_res::DlogData
    tate_table::Vector{Vector{FqFieldElem}}
end

# structure for precomputed values
struct GlobalData
    Fp2::FqField
    E0_data::E0Data
    orders_data::Vector{OrderData}
end