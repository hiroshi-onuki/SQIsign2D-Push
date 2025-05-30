module SQIsign2D_Push
using Nemo


include("utilities/integer.jl")
include("utilities/finite_field.jl")
include("utilities/batch_inv.jl")
include("utilities/lattice.jl")
include("utilities/strategy.jl")
include("utilities/matrix.jl")

include("elliptic_curves/proj1.jl")
include("parameters/global_data.jl")
include("elliptic_curves/full_point.jl")
include("elliptic_curves/pairing.jl")
include("elliptic_curves/montgomery.jl")
include("elliptic_curves/couple_point.jl")
include("elliptic_curves/dlog.jl")

include("theta/theta_structure_dim1.jl")
include("theta/theta_structure_dim2.jl")
include("theta/gluing.jl")
include("theta/theta_arithmetic.jl")
include("theta/splitting.jl")
include("theta/theta_isogeny.jl")

module Level1
using Nemo, SQIsign2D_Push
include("parameters/level1.jl")
end # module Level1

module Level3
using Nemo, SQIsign2D_Push
include("parameters/level3.jl")
end # module Level3

module Level5
using Nemo, SQIsign2D_Push
include("parameters/level5.jl")
end # module Level5

end # module SQIsign2D_Push
