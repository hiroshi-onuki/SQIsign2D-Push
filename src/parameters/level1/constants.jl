# for FullRepresentInteger, the same as the round-1 SQIsign reference implementation
const KLPT_repres_num_gamma_trial = 16384

const ChallengeDegree = three_to_e3
const ChallengeByteLengh = Int(ceil(ceil(log(2, ChallengeDegree)) / 8))
const Is256Hash = ChallengeByteLengh <= 32

const SmallPrimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]
