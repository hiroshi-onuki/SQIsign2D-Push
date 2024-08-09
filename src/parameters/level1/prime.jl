const p = BigInt(2)^263 * 46 - 1
const Log2p = Int(ceil(log(2, p)))
const ExponentForDim2 = 135     # a
const ExponentForDim1 = 128     # b
const ExponentSum = ExponentForDim2 + ExponentForDim1

# for ideal-to-isogeny
const ExponentFull = 264
const ExponentForId2IsoDim2 = 142
const ExponentForId2IsoDim1 = 120
const Cofactor = 23
const ExtraDegree = 3 * 7 * 23
