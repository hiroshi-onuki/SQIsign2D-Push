const ExponentOfTwo = 194
const ExponentOfThree = 121
const two_to_e2 = BigInt(2)^ExponentOfTwo
const three_to_e3 = BigInt(3)^ExponentOfThree
const Cofactor = 1
const p = BigInt(2)^ExponentOfTwo * BigInt(3)^ExponentOfThree * Cofactor - 1
const Log2p = Int(ceil(log(2, p)))
