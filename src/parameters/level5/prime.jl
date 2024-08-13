const p = BigInt(2)^517 * 16 - 1
const Log2p = Int(ceil(log(2, p)))
const ExponentForDim2 = 261     # a
const ExponentForDim1 = 256     # b
const ExponentSum = ExponentForDim2 + ExponentForDim1

# for ideal-to-isogeny
const ExponentFull = 521
const ExponentForId2IsoDim2 = 273
const ExponentForId2IsoDim1 = 246
const Cofactor = 1
const ExtraDegree = 3 * 5^2 * 11
