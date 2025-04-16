# basically the same as SQIsign reference implementation
const KLPT_repres_num_gamma_trial = 32768

const ChallengeDegree = three_to_e3
const ChallengeByteLength = Int(ceil(ceil(log(2, ChallengeDegree)) / 8))
const Is256Hash = ChallengeByteLength <= 32
const Dim2KernelCoeffByteLength = Int(ceil(ExponentOfTwo/8))
const Fp2ByteLength = Int(ceil(Log2p/8)) * 2
const DegreeExponentByteLength = Int(ceil(log(2, ExponentOfTwo)/8))
const PublicKeyByteLength = Fp2ByteLength + 2
const SignatureByteLength = Fp2ByteLength + 2*DegreeExponentByteLength + 4*Dim2KernelCoeffByteLength + ChallengeByteLength + 2

const SmallPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]

const NumOfElligator2 = 20