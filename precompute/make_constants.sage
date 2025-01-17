import endomorphism as end
import torsion_points as tp

def matrix_to_str(M):
    return "[%s %s; %s %s]" % (M[0,0], M[0,1], M[1,0], M[1,1])

def matrix44_to_str(M):
    return "[%s %s %s %s; %s %s %s %s; %s %s %s %s; %s %s %s %s]" % (
        M[0,0], M[0,1], M[0,2], M[0,3],
        M[1,0], M[1,1], M[1,2], M[1,3],
        M[2,0], M[2,1], M[2,2], M[2,3],
        M[3,0], M[3,1], M[3,2], M[3,3]
    )

def make_constants(p, e2, e3, file_name):
    Fp4, Fp2, zeta4 = tp.calcFields(p)
    E0 = EllipticCurve(Fp4, [1, 0])
    Fp2d.<Fp2_i> = GF(p^2, modulus=x^2+1)

    str = ""

    # 2^e2-torsion in E(Fp2)
    P, Q = tp.basis_2e_special(E0, Fp2, zeta4, e2)
    Ms = end.action_matrices([P, Q], 2^e2, zeta4, Fp4)
    Px, Py = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in P.xy()]
    Qx, Qy = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in Q.xy()]
    str += "P2e = Point(%s, %s)\n" % (Px, Py)
    str += "Q2e = Point(%s, %s)\n" % (Qx, Qy)
    str += "M_i_2e = %s\n" % matrix_to_str(Ms[0])
    str += "M_ij_2e = %s\n" % matrix_to_str(Ms[1])
    str += "M_1k_2e = %s\n" % matrix_to_str(Ms[2])

    # 3^e3-torsion in E(Fp2)
    P, Q = tp.basis(E0, Fp2, False, 3, e3)
    Ms = end.action_matrices([P, Q], 3^e3, zeta4, Fp4)
    Msd = [[[1, 0], [0, 1]]] + Ms
    Z3e = quotient(ZZ, 3^e3)
    M44 = matrix(Z3e, [[Msd[i][j][k] for i in range(4)] for j, k in [(0, 0), (1, 0), (0, 1), (1, 1)]])
    Px, Py = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in P.xy()]
    Qx, Qy = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in Q.xy()]
    str += "P3e = Point(%s, %s)\n" % (Px, Py)
    str += "Q3e = Point(%s, %s)\n" % (Qx, Qy)
    str += "M_i_3e = %s\n" % matrix_to_str(Ms[0])
    str += "M_ij_3e = %s\n" % matrix_to_str(Ms[1])
    str += "M_1k_3e = %s\n" % matrix_to_str(Ms[2])
    str += "M44inv_chall = %s\n" % matrix44_to_str(M44^(-1))
    
    out_file = open(file_name, "w")
    out_file.write(str)
    out_file.close()

# new level1
set_random_seed(0)
e2 = 131
e3 = 78
p = 2^e2 * 3^e3 - 1
make_constants(p, e2, e3, "level1newtorsion.txt")

# level1
set_random_seed(0)
e2 = 132
e3 = 80
p = 2^e2 * 3^e3 * 7 - 1
make_constants(p, e2, e3, "level1torsion.txt")

# level3
e2 = 194
e3 = 121
p = 2^e2 * 3^e3 - 1
make_constants(p, e2, e3, "level3torsion.txt")

# level5
e2 = 261
e3 = 160
p = 2^e2 * 3^e3 * 31 - 1
make_constants(p, e2, e3, "level5torsion.txt")
