# Stieltjes–secular prime-log collision universality law

- **ID:** stieltjes-secular-prime-log-collision-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-first closure of the Stieltjes friable weight-one expansion and secular
  diagonal mode-frequency division
- **Statement:** A friable Stieltjes weight-one datum equals a secular combination-mode frequency
  up to a rational offset iff the offset is zero and every prime-lane coefficient agrees exactly.
  Consequently every nontrivial secular mode frequency, and the logarithm of its diagonal weight,
  is irrational.

## Gates

- [x] 0 → 1 in-progress: generated from verified Lean endpoints
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof literature audit found no exact collision

## Corpus inputs

- `friableC1_eq_sum_beta_log`
- `friableBeta_eq_zero_of_not_mem`
- `logPrime_rat_affine_relation_eq_zero`
- `modeFrequency`
- `log_diagonalWeightReal`

## Proof

`[PROVED HERE]` Put the friable prime support and the finite support of a secular exponent vector
`m` into one finite prime set `S`.  Expand

`friableC1 = ∑_{p∈S} β_p log p`

and extend the defining sum

`modeFrequency(m) = ∑_{p∈S} m_p log p`

by zero outside `support(m)`.  Then

`friableC1 = modeFrequency(m) + q`

is equivalent to the rational affine prime-log relation

`∑_{p∈S} (β_p-m_p) log p = q`.

Existing rational-affine prime-log independence forces `q=0` and `β_p=m_p` on `S`; both sides
vanish outside `S`, so lane equality is global.  The converse follows by substituting equal lanes.
Taking empty friable support shows that a rational nonzero mode frequency would force `m=0`.
Finally `log(diagonalWeightReal m)=-modeFrequency(m)`, and irrationality is preserved by negation.
No numerical computation is used.

## Strict gain over corpus endpoints

The Stieltjes endpoint classifies rationality only relative to the scalar rational line.  The
secular endpoint excludes only the zero resonance needed for mode division.  Their closure
classifies every rationally shifted collision between the two prime-log objects, recovers exact
prime coordinates from scalar equality, and strengthens nonresonance to irrationality.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.StieltjesSecularPrimeLogCollisionUniversalityLaw`
- Main theorem:
  `friableC1_eq_modeFrequency_add_rat_iff`
- Source:
  `formal/GaloisForLFunctions/RHTower/StieltjesSecularPrimeLogCollisionUniversalityLaw.lean`
- Exact-file check:
  `lake env lean GaloisForLFunctions/RHTower/StieltjesSecularPrimeLogCollisionUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty protocol

No literature search occurred before the dependency-closed proof.  Post-proof searches for
Stieltjes prime-log expansions, friable Dirichlet Taylor coefficients, rationally shifted secular
frequencies, and prime-lane collision classification found no exact collision.  Closest inspected
primary sources concern Stieltjes expansions without this prime-lane rigidity:

- S. Saad Eddin, *Applications of the Laurent-Stieltjes constants for Dirichlet L-series*,
  <https://arxiv.org/abs/1705.03596>, approximates Dirichlet `L`-functions near `s=1` by short
  Taylor polynomials, but does not classify collisions with finitely supported prime-log modes.
- M. W. Coffey, *Series representations for the Stieltjes constants*,
  <https://arxiv.org/abs/0905.1111>, develops series and addition formulas for Stieltjes constants,
  not rational-affine prime-lane recovery.
- M. W. Coffey, *Summatory relations and prime products for the Stieltjes constants, and other
  related results*, <https://arxiv.org/abs/1701.07064>, relates Stieltjes constants to prime
  products but does not prove the exact rational-offset collision law here.

## Log

- 2026-07-23 — Exact shared-symbol scan connected the secular nonresonance lane to the Stieltjes
  rational-affine prime-log theorem.
- 2026-07-23 — Dependency-closed global prime-lane collision classification completed.
- 2026-07-23 — Exact theorem checked warning-free and wired into the RHTower umbrella.
- 2026-07-23 — Post-proof collision audit found no exact literature match.
