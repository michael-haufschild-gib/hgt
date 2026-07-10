# Functional-equation-paired prime-jet rigidity

- **ID:** fe-paired-prime-jet-rigidity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** constraint-side continuation of `pinned-affine-prime-jet-rigidity`
- **Statement:** `[PROVED]` A packet supported on `k` reflected prime-log pairs `± log p_i`
  uniquely matches the origin derivation at every degree below `2k+1`; its degree-`2k+1`
  defect is exactly `-∏ i, (-(log p_i)^2)` and is nonzero.

## Goal

Decide whether functional-equation reflection removes the finite-carrier obstruction.  It does not:
reflection doubles the finite matching depth but leaves an exact first omitted odd defect and no
coefficient-preserving extension.

## Gates

- [x] 0 → 1 in-progress: well-posed, source-pure, attack idea
- [x] 1 → 2 fully-proven: complete fixed-polynomial proof, no open dependency
- [x] 2 → 3 formalized: exact Lean target built and capstone axioms audited
- [ ] 3 → 4 publication-ready: standalone paper theorem and RH-facing integration

## Definitions

For nodes `r_i` and coefficients `a_i`, the reflected antisymmetric moment is

`L_n = ∑ i, a_i (r_i^n - (-r_i)^n)`.

For prime labels, `r_i = log p_i > 0`.

## Theorem

Let `k > 0`, let `p : Fin k → ℕ` be injective, and suppose every `p_i > 1`.  There is a unique
coefficient vector `a : Fin k → ℂ` such that

`L_n = δ_(n,1)` for every `n < 2k+1`.

For that vector,

`L_(2k+1) - δ_(2k+1,1) = -∏ i, (-(log p_i)^2) ≠ 0`.

Distinctness is required only for existence and uniqueness of the square interpolation packet.  The
nonvanishing first omitted defect itself holds for every positive prime-labelled packet satisfying
the lower odd constraints.

There is also no coefficient-preserving support extension from `k` pairs to `k+1` pairs.  If the
old coefficients are retained, the degree-one equation forces the new coefficient to zero; the old
degree-`2k+1` defect then remains.

The child theorem
[`fe-paired-prime-jet-barycentric-rigidity.md`](fe-paired-prime-jet-barycentric-rigidity.md)
computes the unique packet explicitly and strengthens this statement: adjoining one prime changes
every old coefficient, not merely one unspecified coefficient.

## Proof

Antisymmetry gives `L_(2j) = 0`.  At an odd degree,

`L_(2j+1) = ∑ i, (2 a_i r_i) (r_i^2)^j`.

Thus the odd constraints for `j = 0, ..., k-1` form a square Vandermonde system at the nodes
`r_i^2`.  Positive distinct logarithms have positive distinct squares, and the weights `2r_i` are
nonzero, so the coefficient vector exists uniquely.  Together with automatic even vanishing, this
matches every degree below `2k+1`.

Let

`S(Y) = ∏ i, (Y - r_i^2)`.

It is monic of degree `k` and vanishes at all squared nodes.  Subtracting `Y^k` leaves a polynomial
of degree below `k`, on which the interpolating functional equals evaluation at zero.  Evaluation at
the nodes therefore gives

`L_(2k+1) = -S(0) = -∏ i, (-r_i^2)`.

Every `r_i` is nonzero, so the product cannot vanish.  This is equivalently the derivative at zero
of the odd reflected-node polynomial `X ∏ i, (X^2-r_i^2)`.

## Lean certificate

Module:
`formal/GaloisForLFunctions/RHTower/FEPairedPrimeJetRigidity.lean`

Capstones:

- `fePairedPrimeDerivationInterpolation_firstOmitted_eq_neg_prod`
- `existsUnique_fePairedPrimeDerivationInterpolation_through_double`
- `existsUnique_fePairedPrimeDerivationInterpolation_with_firstOmittedDefect`
- `no_fePairedPrimeDerivationInterpolation_coefficientPreserving_extension`

The module compiles directly and the exact target
`GaloisForLFunctions.RHTower.FEPairedPrimeJetRigidity` builds successfully.  Each capstone has axiom
footprint `[propext, Classical.choice, Quot.sound]`.

## Novelty and significance

- **Novel:** the prior tree contained one-sided prime-jet interpolation and abstract FE parity, but
  no reflected `±log p` interpolation theorem, exact squared-log defect, or nested-support no-go.
- **Significant:** the theorem eliminates the canonical FE-symmetric finite repair.  Reflection does
  not cure the carrier problem; it hides it for exactly twice as many degrees.
- **RH status:** this is not an RH proof.  The surviving interface must couple a fixed non-finite
  Euler source to the archimedean constraint without treating finite-support exhaustion as a source
  object or a propagated carrier.
