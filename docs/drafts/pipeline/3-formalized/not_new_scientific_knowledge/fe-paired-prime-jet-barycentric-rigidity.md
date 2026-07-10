# Barycentric nonlocality of FE-paired prime jets

- **ID:** fe-paired-prime-jet-barycentric-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** `fe-paired-prime-jet-rigidity`
- **Statement:** `[PROVED]` The unique reflected prime-log interpolation packet has an explicit
  barycentric coefficient formula.  Every coefficient is nonzero, and adjoining one new prime
  changes every old coefficient.

## Goal

Determine whether the unique finite FE-paired interpolant can be interpreted as a collection of
fixed local Euler contributions.  It cannot: each coefficient depends multiplicatively on the
entire chosen prime support.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, explicit Lagrange formula
- [x] 1 → 2 fully-proven: complete barycentric proof, no open dependency
- [x] 2 → 3 formalized: exact Lean target built and capstone axioms audited
- [ ] 3 → 4 publication-ready: integrate with the finite/all-orders boundary theorem

## Theorem

For distinct positive prime labels `p_i`, put

`r_i = log p_i`,  `x_i = r_i^2`.

The unique coefficients for which antisymmetric evaluation at the pairs `±r_i` matches the origin
derivation at odd degrees `1,3,...,2k-1` are

`a_i = (1/(2r_i)) * ∏_{j ≠ i} (-x_j)/(x_i-x_j)`.

Each `a_i` is nonzero.  If a new distinct positive prime is appended, then for every old index `i`
the barycentric numerator weight is multiplied by

`(-x_new)/(x_i-x_new)`.

This factor is not one: equality to one would imply `x_i=0`, contrary to `p_i>1`.  Since the
denominator `2r_i` is unchanged, every old coefficient changes.

If the appended prime is larger than an old prime, the multiplier is the positive real number
`x_new/(x_new-x_i)>1`; consequently that old coefficient strictly increases in norm.  The child
theorem [`prime-barycentric-coefficient-divergence.md`](prime-barycentric-coefficient-divergence.md)
iterates this mechanism quantitatively over canonical prime exhaustion and proves divergence.

## Proof

For any finite distinct nonzero node family `x`, define the origin interpolation weight

`b_i = ∏_j if j=i then 1 else (-x_j)/(x_i-x_j)`.

This is the Lagrange basis polynomial at node `x_i`, evaluated at zero.  Lagrange interpolation of
the monomial `X^m` therefore gives

`∑_i b_i x_i^m = δ_(m,0)` for `m<k`.

Setting `a_i=b_i/(2r_i)` and using

`a_i(r_i^(2m+1)-(-r_i)^(2m+1)) = b_i x_i^m`

gives the required odd moment constraints.  The existing Vandermonde uniqueness theorem identifies
this explicit packet with the unique abstract interpolant.

For support extension, splitting the product over `Fin (k+1)` into the old indices and the last
index gives the displayed multiplier exactly.  Nonzero nodes and pairwise distinctness make every
factor and coefficient nonzero; elementary field cancellation rules out multiplier one.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/FEPairedPrimeJetBarycentricRigidity.lean`

Capstones:

- `originInterpolationWeight_moments`
- `fePairedPrimeDerivationInterpolation_eq_barycentric`
- `fePairedOriginCoefficient_castSucc_ne`
- `fePairedPrimeBarycentricCoefficient_castSucc_ne`
- `fePairedOriginCoefficient_castSucc_eq`
- `fePairedPrimeBarycentricCoefficient_castSucc_norm_lt`

The module compiles directly and the exact target
`GaloisForLFunctions.RHTower.FEPairedPrimeJetBarycentricRigidity` builds successfully.  Each
capstone has axiom footprint `[propext, Classical.choice, Quot.sound]`.

## Novelty and significance

- **Novel:** the parent theorem proved uniqueness and ruled out a fully coefficient-preserving
  extension.  It did not compute the coefficients or show coordinatewise change.  The barycentric
  formula proves that every old coefficient changes.
- **Significant:** a finite exact packet is globally recomputed from its full support.  It therefore
  cannot be the restriction of fixed local Euler coefficients.  Treating successive packets as a
  source constructs a support-dependent flow in disguise.
- **RH status:** this is not an RH proof.  It forces the remaining Euler/Gamma interface to be a
  fixed, genuinely non-finite renormalized constraint; finite exact interpolation cannot supply it.
