# Dense prime-weld integral Lorentz descent

- **ID:** ULF-DALR-02
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Statement:** Literal integer prime formation has one rank-two integral orientation quotient on
  which all prime generators act by the certified horizontal Lorentz boosts.

## Big-picture law

Nonzero horizontal grade converts the gapless prime-log weld into a dense noncompact boost flow.
Exact integer occurrence should retain one common arithmetic lattice through formation, rather
than assign independent scalar reporters after a divisor is known. Dense continuous formation and
discrete finite-rank arithmetic descent are compatible only for the trivial boost.

## Corpus facts used

- `hurwitzBoost_mul` and `hurwitzBoost_lightCone`: multiplicative refinement is the Lorentz action
  with reciprocal reflected legs.
- `primeLogLattice_dense`: all prime rates generate a dense archimedean flow.
- Q8/FZZ/QCR facts: orientation lives in incidence and is erased by marginal or positive quotient.
- theta conormal socle: every Xi occurrence already has a faithful rank-two parity suspension and
  exact multiplicity current.
- integral Big-Witt descent: arithmetic integral structures exist, but current reporters fit
  individual light-cone ghosts and are exactly RH-equivalent.
- ULF-DALR-01: common integral trace descent of the dense boost flow forces zero grade.

## Exact RH closure

For each actual Xi divisor `rho`, source construction must give a prime-independent full lattice
`Lambda_rho` in its oriented rank-two conormal plane and prove

`B((2 Re(rho)-1) log p) Lambda_rho = Lambda_rho`

for every prime `p`. ULF-DALR-01 then gives `2 Re(rho)-1=0`. Universality over Xi divisor support is
RH.

## Current attack

Construct the quotient before divisor specialization from three existing integral objects:

1. the prime-exponent lattice `Z^(Primes)` and its formation action;
2. the Big-Witt Frobenius/ghost lattice, retaining both reflected orientations;
3. the theta conormal top-socle quotient, retaining multiplicity and the nonzero odd current.

Required fusion theorem: their common two-orientation quotient intertwines prime Frobenius with
`hurwitzBoost` in one fixed integral frame. It must be natural in prime label; a separately chosen
frame at each prime is rejected.

## Fresh source audit result

The obvious quotient does not exist in current corpus:

1. `rationalHurwitzFiberResponse` is a coefficient-one sum over `n` rational residue values, but
   division by `n*zeta(s+1)` compresses it to `n^s`; the Lorentz plane is visible only after this
   scalar normalization.
2. Literal finite prime formation has zero-sum kernel rank `r-1`, unbounded with packet size, while
   its coarse scalar cokernel is trivial. Integer coefficients therefore do not canonically yield
   a faithful rank-two quotient.
3. The Burnol theta quotient gives a nonzero two-prime vector but no multiplicative transport law.
4. Big-Witt Frobenius changes arithmetic base at fixed Xi fibre; its current reporter records the
   fibre label, not transport of the conormal vector.
5. Integral fixed/free Tate residue distinguishes reflection orbit type but does not show prime
   holonomy preserves the divisor multiplicity lattice.

Thus the candidate survives only in a sharper form: construct a rank-two **monoidal quotient**, not
a rank-two projection. It must quotient the unbounded zero-sum formation charge by a source-defined
prime-stable sublattice and prove that no horizontal information is discarded. Failure of such a
prime-stable quotient at neutral grade would retire the candidate.

## Projective correction

The full paired prime character contains a common unitary factor depending on zero height. A fixed
integral lattice for that full character would force the vertical phase to be trivial and is false
even on RH. The Lorentz action appears only after removing this common scalar. Therefore the source
object must be:

1. a projective two-orientation quotient removing the common phase without choosing it;
2. a determinant/volume trivialization fixing the remaining real homothety;
3. an integral lattice in the resulting unimodular radial plane.

Corpus already contains a one-prime irrational-rotation `K₀` integer-trace collision with an open
source-projective-module obligation. That result forbids treating projective vocabulary as the new
producer. New content here is the dense all-prime common-frame rigidity; missing content remains
the source-generated projective determinant normalization.

## Hostile tests

- Individual Pell boosts are allowed; one-prime integrality proves nothing.
- Infinite-rank lattice automorphism groups need not be discrete; finite rank is essential and
  must come from the rank-two conormal quotient, not truncation.
- Divisor-order equality and relative determinant cancellation are insufficient because
  exponential finite-part torsion survives.
- If the quotient is obtained only after inserting `rho` or choosing `a`, it is a receiver.
- If common phase is removed by a chosen scalar rather than a source-canonical projective quotient,
  the construction is post-divisor gauge fixing.
- If corpus source maps do not preserve any common finite-rank integral quotient even at neutral
  grade, candidate is mathematically false and must be retired.

## Gates

- [x] 0 -> 1: precise source object, hostile theorem, and RH closure specified
- [ ] 1 -> 2: construct coefficient-faithful common integral quotient
- [ ] 2 -> 3: formalize source construction and apply ULF-DALR-01
- [ ] 3 -> 4: publication-ready synthesis

## Log

- 2026-09-02 — opened after fresh Lean audit; abstract rigidity law proved separately.
