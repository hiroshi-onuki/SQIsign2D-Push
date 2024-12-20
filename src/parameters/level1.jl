include("level1/prime.jl")
include("level1/constants.jl")
include("level1/precomputed_order_data.jl")

include("../quaternion/order.jl")
include("../quaternion/cornacchia.jl")
include("../quaternion/ideal.jl")
include("../quaternion/klpt.jl")

include("global_data.jl")
include("order_data.jl")

include("../elliptic_curves/dlog.jl")
include("../ideal_to_isogeny/ideal_to_isogeny.jl")
include("../rii/quat_action.jl")
include("../rii/d2isogeny.jl")
include("../rii/rii.jl")
include("../utilities/for_compression.jl")
include("../sqisign2d_push/sqisign2d_push.jl")

const StrategiesDim2 = Dict(
    ExponentOfTwo => compute_strategy(ExponentOfTwo-2, 2, 1),
)
const StrategiesDim1Two = Dict(
    ExponentOfTwo => compute_strategy(div(ExponentOfTwo,2) - 1, 1, 1),
)

const StrategiesDim1Three = Dict(
    ExponentOfThree => compute_strategy(ExponentOfThree - 1, 1, 1),
    ExponentOfThree - 1 => compute_strategy(ExponentOfThree - 2, 1, 1),
    ExponentOfThree - 2 => compute_strategy(ExponentOfThree - 3, 1, 1),
    ExponentOfThree - 3 => compute_strategy(ExponentOfThree - 4, 1, 1),
    ExponentOfThree - 4 => compute_strategy(ExponentOfThree - 5, 1, 1),
    ExponentOfThree - 5 => compute_strategy(ExponentOfThree - 6, 1, 1),
    ExponentOfThree - 6 => compute_strategy(ExponentOfThree - 7, 1, 1),
    ExponentOfThree - 7 => compute_strategy(ExponentOfThree - 8, 1, 1),
    ExponentOfThree - 8 => compute_strategy(ExponentOfThree - 9, 1, 1),
)

function make_E0_data()
    _, T = polynomial_ring(GF(p), "T")
    Fp2, Fp2_i = finite_field(T^2 + 1, "i")

    A0 = Fp2(0)

    # constants from precompute/level1torsion.txt
    P2e = Point(1531149781711917380367060239285238186300487199836080014663337348616798943170633*Fp2_i + 3110382937731504869536565537496875767584981042621809716732346748331993571065399, 4039804177053620030988880655691742858697099202524887514558580934455406914776902*Fp2_i + 3550721969574630064547234599815927349493838338141797270062684573900349635887548)
    Q2e = Point(4102084910679891093702283854639291337424569102586570711291205562199617354739638*Fp2_i + 2522851754660303604532778556427653756140075259800841009222196162484422726844872, 3550721969574630064547234599815927349493838338141797270062684573900349635887548*Fp2_i + 1593430515338188443080463438232786665027957099897763211395961976361009383133369)
    M_i_2e = [0 5444517870735015415413993718908291383295; 1 0]
    M_ij_2e = [4324312174203190724284295886362054813240 3334345937367886101996163442172158886848; 3334345937367886101996163442172158886849 1120205696531824691129697832546236570056]
    M_1k_2e = [2110171933367129313417830276736132496448 4324312174203190724284295886362054813240; 4324312174203190724284295886362054813240 3334345937367886101996163442172158886849]
    P3e = Point(2006982394376954054746282658989847061026521116048221434820315293094959912872476*Fp2_i + 108938614186280581715727671435891067310712878773562090392725294703051835860519, 3045087778386466394981949753874123890935402090926658244678695787342931849886897*Fp2_i + 4135746303091571843813910553603603847471653302956569747147568722468001408561092)
    Q3e = Point(3580470049332746741947130760416220554306664994686110901933585473854957312084444*Fp2_i + 4886745583818571840949688587415249425980637476684590448621209502512499302639836, 1058559647497099802500296356201468133140232567455848043656029939521670767143125*Fp2_i + 4833427449357231697459747797455252796818456485771877926638641051299787066793395)
    M_i_3e = [91191506070529126425020339914589708954 21744219888908283138058115059088881229; 29621950572876406765434768461894207096 56617323343816796891062870291793588647]
    M_ij_3e = [56165343702337901204160687363596405747 138446665261109147178718883603964753340; 113916734810988923526211326291292620635 91643485712008022111922522842786891854]
    M_1k_3e = [4554926750764503528794585725061784153 4672809189945585326802823747777729600; 12706980453292678961168823337516420164 143253902663581419787288624481321513449]

    a24_0 = A_to_a24(A0)

    P0 = add(P2e, P3e, Proj1(A0))
    Q0 = add(Q2e, Q3e, Proj1(A0))
    xP0 = Proj1(P0.X, P0.Z)
    xQ0 = Proj1(Q0.X, Q0.Z)
    PQ0 = add(P0, -Q0, Proj1(A0))
    xPQ0 = Proj1(PQ0.X, PQ0.Z)
    basis2e3e = BasisData(xP0, xQ0, xPQ0)

    xP2e = Proj1(P2e.X, P2e.Z)
    xQ2e = Proj1(Q2e.X, Q2e.Z)
    PQ2e = add(P2e, -Q2e, Proj1(A0))
    xPQ2e = Proj1(PQ2e.X, PQ2e.Z)
    basis2e = BasisData(xP2e, xQ2e, xPQ2e)

    xP3e = Proj1(P3e.X, P3e.Z)
    xQ3e = Proj1(Q3e.X, Q3e.Z)
    PQ3e = add(P3e, -Q3e, Proj1(A0))
    xPQ3e = Proj1(PQ3e.X, PQ3e.Z)
    basis3e = BasisData(xP3e, xQ3e, xPQ3e)

    Matrices_2e = [M_i_2e, M_ij_2e, M_1k_2e]
    Matrices_3e = [M_i_3e, M_ij_3e, M_1k_3e]

    # precomputed values for discrete logarithm
    tp_table = make_pairing_table(A0, P2e, ExponentOfTwo)
    tp_P2e_Q2e = Tate_pairing_P0(Q2e, tp_table, Cofactor)
    window_size = 3
    fq_dlog_table1, fq_dlog_table2 = make_dlog_table(tp_P2e_Q2e, ExponentOfTwo, window_size)
    strategy_dlog = compute_strategy(div(ExponentOfTwo, window_size) - 1, window_size, 1)
    dlog_data = DlogData(ExponentOfTwo, window_size, fq_dlog_table1, fq_dlog_table2, strategy_dlog)

    w = Weil_pairing_2power(A0, P2e, Q2e, ExponentOfTwo)

    # make constants for isomorphism to the curve E_A0
    _, T = polynomial_ring(Fp2, "T")
    As = roots((256 * (T^2 - 3)^3 - 1728 * (T^2 - 4))/T^2)
    A0d = As[1]
    beta = -A0d/3
    gamma = square_root(1 / (1 - 3*beta^2))
    A0dd = As[2]
    beta_d = -A0dd/3
    gamma_d = square_root(1 / (1 - 3*beta_d^2))
    function isomorphism_to_A0(A::Proj1{FqFieldElem}, Ps::Vector{Proj1{FqFieldElem}})
        if A == Proj1(A0)
            return Ps
        elseif A == Proj1(A0d)
            return [Proj1(gamma*(P.X - beta*P.Z), P.Z) for P in Ps]
        elseif A == Proj1(A0dd)
            return [Proj1(gamma_d*(P.X - beta_d*P.Z), P.Z) for P in Ps]
        else
            throw(ArgumentError("A is not A0d or A0dd"))
        end
    end

    return Fp2, E0Data(A0, A0d, A0dd, a24_0, jInvariant_A(A0), basis2e3e, basis2e, basis3e, Matrices_2e, Matrices_3e, w, isomorphism_to_A0, dlog_data, tp_table)
end

# Fp2 and values in Fp2
function make_precomputed_values()
    Fp2, E0 = make_E0_data()

    return GlobalData(Fp2, E0)
end