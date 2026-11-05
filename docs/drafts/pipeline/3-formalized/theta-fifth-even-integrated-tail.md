# Complete fifth even theta tails

- **Stage:** 3-formalized
- **Wall:** Σ6
- **Statement:** The matrix
  `T₅(r)ᵢⱼ=∫_(s>r) thetaCuspNativeSignedJet(s/2,2(i+j)) ds`
  is positive definite for every `r≥0`.

Put `q=πexp(r)`, `E(q)=q^(3/2)exp(−2q)`, `A=M(0,1)>0`,
`b(q)=3/(8q)`, and `c(q)=3/(32q²)−3/(128q³)`.
The exponential substitution multiplies `T₅(r)` by the positive scalar
`π^(1/2)/4` and gives the literal complete radial matrix.

Its exact decomposition is the leading tail `(1,1),(1,2),(2,1)`,
five other doubled unequal pairs among atoms one through four, the
three remaining pure-atom tails, and the infinite omitted source.
Every comparison below holds for `q≥3`:

- The leading tail minus `E(b+c)A` is positive definite.
- The doubled pair `(1,3)` plus `EbA` is positive definite.
- Each doubled pair `(1,4),(2,3),(2,4),(3,4)` plus `EcA/8`
  is positive definite.
- The omitted source plus `EcA/2` is positive semidefinite.
- Pure-atom tails for atoms two, three, and four are positive definite.

Adding these inequalities cancels both reserves exactly and proves
strict positivity of the complete radial matrix. The source identity
retains every ordered pair; all entries are integrable, so its finite
sum integrates exactly. Since `r≥0` implies `q≥π>3`, the literal native
tail is positive definite.

Namespace `GaloisForLFunctions.ThetaCuspSections.FifthCompleteTail`:
`nativeTailMatrix_scaled`, `radialTailDecomposition_posDef`,
`radialNativeTailMatrix_eq_decomposition`,
`radialNativeTailMatrix_posDef`, `nativeTailMatrix_posDef`.

Module: `ThetaCuspSections/FifthEvenCompleteTail.lean`.
The capstones use only `propext`, `Classical.choice`, and `Quot.sound`.
