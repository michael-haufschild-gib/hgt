# Xi apex-charge critical-half-strip confinement universality law

- **ID:** xi-apex-charge-critical-half-strip-confinement-universality
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean)
- **Source:** theorem-generated closure of `nontrivial_wCharge_ne_primeFlux_charge`,
  `xiDeckParity_ne_zero_imp_not_rh`, `xiDeckParity_eq_wCharge_two`, and
  `xi_ne_zero_of_one_lt_re`
- **Statement:** A nonzero level-one Xi apex charge right of the critical line is confined to
  `1/2 < Re ρ ≤ 1`, is unequal to every torsion reading of every prime-flux class, and refutes RH.

## Goal

Turn the local apex bit from an unlocalized obstruction into an exact critical-half-strip phase
law by closing it against Euler-product far-field zero-freeness.

## Gates

- [x] 0 → 1 in-progress: source-pure theorem-generated connector
- [x] 1 → 2 fully-proven: dependency-closed paper proof, `[PROVED HERE]`
- [x] 2 → 3 formalized: exact-file Lean check passed; final global axiom audit pending
- [x] 3 → 4 publication-ready: post-proof collision audit found no exact literature match

## Corpus inputs

- `nontrivial_wCharge_ne_primeFlux_charge`
- `xiDeckParity_ne_zero_imp_not_rh`
- `xiDeckParity_eq_wCharge_two`
- `xi_ne_zero_of_one_lt_re`
- `analyticOrderAt_eq_zero`
- `mem_rightHalf`

## Proof

**[PROVED HERE]** Let `ρ` lie in the Xi right half-plane and suppose its level-one additive
ladder charge `wCharge 2 (ordρ ξ)` is nonzero. Membership in the right half-plane gives
`1/2 < Re ρ`.

If instead `1 < Re ρ`, Euler-product far-field zero-freeness gives `ξ(ρ) ≠ 0`. Analyticity of Xi
then forces `ordρ ξ = 0`, so its additive charge is `wCharge 2(0)=0`, contradicting the
hypothesis. Therefore `Re ρ ≤ 1`.

Apex independence says every nonzero additive ladder charge differs from every homomorphic
torsion reading of every finitely supported prime-flux class. The deck-parity bridge identifies
this same charge with the Xi mod-two deck parity. Its nonvanishing at a right-half point triggers
the pointwise RH obstruction. Thus the charge is simultaneously confined, prime-flux invisible,
and fatal to RH. No computation is used. ∎

## Strict gain over corpus endpoints

Apex independence has no location information. The deck-parity RH obstruction only assumes the
right half-plane. Euler-product zero-freeness gives a far-field drain but does not identify the
surviving charge stratum or its prime-flux invisibility. Their closure localizes every possible
nonzero apex bit to the exact half-strip and attaches both arithmetic-independence and RH
consequences to the same pointwise certificate.

## Lean certificate

- Module:
  `GaloisForLFunctions.RHTower.XiApexChargeCriticalHalfStripConfinementUniversalityLaw`
- Main theorem:
  `xiApexCharge_criticalHalfStripConfinementUniversality`
- Exact-file command:
  `lake env lean GaloisForLFunctions/RHTower/XiApexChargeCriticalHalfStripConfinementUniversalityLaw.lean`
  passed warning-free on 2026-07-23.
- Umbrella:
  imported by `formal/GaloisForLFunctions/RHTower.lean`.

## Novelty audit

No literature search occurred before dependency-closed paper and Lean proofs. Post-proof searches
for Xi zero-free regions, odd zero multiplicity, parity/vorticity, and prime-flux readings found no
exact collision with the confined additive-charge certificate. Closest primary sources:

- T. Binder, S. Pauli, and F. Saidak, *Zeros of high derivatives of the Riemann Zeta function*,
  <https://arxiv.org/abs/1002.0362>, proves zero-free regions for zeta derivatives, not a
  mod-two Xi vanishing-order charge with prime-flux invisibility.
- A. LeClair, *An electrostatic depiction of the validity of the Riemann Hypothesis and a formula
  for the N-th zero at large N*, <https://arxiv.org/abs/1305.2613>, assigns local vorticity-like
  data near zeros, but gives neither the `1/2 < Re ≤ 1` additive-charge confinement certificate
  nor its cohomological separation from prime flux.
- M. Davis, A. Papp, D. S. Brown, and D. Haran, *A Relatively Small Turing Machine Whose Behavior
  Is Independent of Set Theory*, <https://arxiv.org/abs/1605.04343>, recalls the classical
  critical-strip formulation of RH in an encoding result, without multiplicity parity or
  prime-flux charge structure.

## Log

- 2026-07-23 — whole-corpus terminal scan paired the apex-charge stratum with far-field Xi
  zero-freeness and exposed a missing pointwise confinement law.
- 2026-07-23 — dependency-closed paper proof completed before literature search or Lean source.
- 2026-07-23 — exact Lean proof passed warning-free and module was wired into RHTower umbrella.
- 2026-07-23 — post-proof collision audit found no exact literature match.
