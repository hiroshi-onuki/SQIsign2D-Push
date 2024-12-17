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

    out_file = open(file_name, "w")

    # 2^e2-torsion in E(Fp2)
    P, Q = tp.basis_2e_special(E0, Fp2, zeta4, e2)
    Ms = end.action_matrices([P, Q], 2^e2, zeta4, Fp4)
    Px, Py = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in P.xy()]
    Qx, Qy = [tp.Fp2ToFp2d(v, zeta4, Fp2_i) for v in Q.xy()]
    out_file.write("P2e = Point(%s, %s)\n" % (Px, Py))
    out_file.write("Q2e = Point(%s, %s)\n" % (Qx, Qy))
    out_file.write("M_i_2e = %s\n" % matrix_to_str(Ms[0]))
    out_file.write("M_ij_2e = %s\n" % matrix_to_str(Ms[1]))
    out_file.write("M_1k_2e = %s\n" % matrix_to_str(Ms[2]))

    # odd torsion in E(Fp2)
    for l, e in [(3, e3)]:
        P, Q = tp.basis(E0, Fp2, False, l, e)
        Ms = end.action_matrices([P, Q], l^e, zeta4, Fp4)
        xP = tp.Fp2ToFp2d(P.xy()[0], zeta4, Fp2_i)
        xQ = tp.Fp2ToFp2d(Q.xy()[0], zeta4, Fp2_i)
        xPQ = tp.Fp2ToFp2d((P - Q).xy()[0], zeta4, Fp2_i)
        out_file.write("xP%d = Proj1(%s)\n" % (l, xP))
        out_file.write("xQ%d = Proj1(%s)\n" % (l, xQ))
        out_file.write("xPQ%d = Proj1(%s)\n" % (l, xPQ))
        out_file.write("M_i_%d = %s\n" % (l, matrix_to_str(Ms[0])))
        out_file.write("M_ij_%d = %s\n" % (l, matrix_to_str(Ms[1])))
        out_file.write("M_1k_%d = %s\n" % (l, matrix_to_str(Ms[2])))

    out_file.close()

# level1
set_random_seed(0)
e2 = 132
e3 = 80
p = 2^e2 * 3^e3 * 7 - 1
make_constants(p, e2, e3, "level1torsion.txt")

# level3
set_random_seed(0)
p = 2^389 * 12 - 1
e = 391
ed = 192
degs = 3
degs_d = 1
#make_constants(p, e, ed, degs, degs_d, "level3torsion.txt")

# level5
set_random_seed(0)
p = 2^517 * 16 - 1
e = 521
ed = 256
degs = 1
degs_d = 3 * 5^2 * 11
#make_constants(p, e, ed, degs, degs_d, "level5torsion.txt")