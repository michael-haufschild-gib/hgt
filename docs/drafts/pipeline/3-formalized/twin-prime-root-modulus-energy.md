# Finite energy for root-modulus averages

- **ID:** twin-prime-root-modulus-energy
- **Stage:** 3-formalized
- **Type:** THEOREM / BRIDGE
- **Source:** [partially consumed marks](../2-fully-proven/twin-prime-partially-consumed-mark-energy.md)
- **Lean:** `formal/GaloisForLFunctions/twin-prime/ModulusEnergy.lean`

## Exact theorem and paper proof

For `H` a natural number, arbitrary complex coefficients `a_k`,
and arbitrary weights `c_(q,k)` in the closed complex unit disk,
put

`R_q=sum_(1<=k<=H,q|k)c_(q,k)a_k`,
`T=sum_(1<=q<=H)|R_q|`,
`D=sum_(1<=k<=H)tau(k)`,
`E_j=sum_(1<=k<=H)tau(k)^j |a_k|^2`.

Then `T^2<=D E_1` and `T^4<=D^2 E_0 E_2`.
There is no arithmetic cancellation premise. The weight's unit-disk
type specifies the bounded multiplier itself; it does not stand in
for an unproved input about the coefficient sequence.

Triangle inequality gives `T<=sum_k tau(k)|a_k|`, since each
cofactor occurs once per positive divisor. Weighted
Cauchy--Schwarz gives `T^2<=D E_1`. A second Cauchy--Schwarz
gives `E_1^2<=E_0 E_2`, proving the fourth-power bound. The empty
case `H=0` is included. Zero weights encode subsets of moduli
and individual cofactor cutoffs without extra hypotheses.

## Lean surface

- `TwinPrime.sum_rootMultiples_eq`: exact divisor-incidence identity.
- `TwinPrime.rootModulusMass_le`: triangle bound with modulus-dependent weights.
- `TwinPrime.rootModulusMass_sq_le`: first energy estimate.
- `TwinPrime.cofactorEnergy_one_sq_le`: energy interpolation.
- `TwinPrime.rootModulusMass_pow_four_le`: unconditional fourth-power capstone.

The module imports mathlib only. It is wired into the twin-prime
umbrella. The finite statement is classical Cauchy--Schwarz, not
new scientific knowledge or a twin-prime theorem. Its role is to
verify that modulus-dependent bounded cofactor weights are allowed
in the analytic transfer. Estimates for the actual arithmetic
`E_0,E_2`, and the full marked theorem, remain separate obligations.

## Verification

- Leaf command passed:
  `lake --old env lean GaloisForLFunctions/twin-prime/ModulusEnergy.lean`.
- The incidence identity and fourth-power capstone depend only on
  `[propext, Classical.choice, Quot.sound]`.
- No new axioms, analytic premises, placeholders, computation
  certificates, or raised elaboration options.
- Umbrella wired without building it.

## Log

- 2026-10-23 — Paper proof and Lean proof complete. An incorrect
  initial mathlib import path was corrected using the corpus tool;
  the corrected leaf and axiom audit passed.
