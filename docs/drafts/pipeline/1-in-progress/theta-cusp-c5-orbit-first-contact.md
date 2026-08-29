# Theta-Cusp C5 Physical-Orbit First Contact

- **ID:** CLG-TTF-C5-orbit-first-contact
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / OPEN GLOBAL ORBIT TRANSVERSALITY
- **Source:** `thetaCuspC5ExactCompletedSeamOrientation`, its exact slope theorem, the source-positive modular ODE, and the formal chamber-only slope no-go
- **Statement:** On the physical positive theta orbit, every zero of exact completed C5 orientation has strictly positive outgoing derivative.

## Goal and RH proof chain

Let `Ω` be `thetaCuspC5ExactCompletedSeamOrientation`. Prove

`∀ u > 0, Ω u = 0 → Ω' u > 0`.

Corpus already proves `Ω>0` immediately right of the modular centre. First-contact exclusion would
therefore give `Ω>0` on the full positive orbit. This closes the chain

`physical-orbit first-contact positivity`
→ `Ω>0` at every positive centre
→ punctured positivity of literal completed C5 compensation at every centre
→ local direct fixed-action Jacobian orientation
→ compact/far-tail assembly
→ fixed-action seam and reflection-odd rank-four/Ptolemy wall
→ cofinal no-escape
→ CLG/TTF or Weil-polarization positivity
→ RH.

Failure at one physical zero kills this direct-J seam route at that centre.

## Corpus-grounded conjecture

With source-log jets

`A=-L₂, B=-L₄, C=-L₆, E=-L₃, F=-L₅, G=-L₇`, define

`Ω=A²G-3ACE-2ABF+4B²E-18A³F+36A²BE`.

**[CONJECTURE C5-ORBIT-FIRST-CONTACT]** For every `u>0` on
`thetaCuspModularSourcePositiveState`, if `Ω(u)=0`, then the exact corpus slope

`A²D-5ABC+4B³-18A³C+36A²B²-AEG+6BEF-2AF²-3CE²-18A²EF+72ABE²`

is strictly positive.

## Hostile audit and attack

- [x] Chamber signs alone fail: exact corrected slope is negative at a strict source-positive
  chamber state.
- [ ] Test strongest replacement: completed C5 orientation is an invariant-region barrier for the
  exact source-positive polynomial vector field.
- [ ] If uniform barrier fails, formalize exact counterexample and strongest positive survivor.
- [ ] Attack remaining physical-incidence statement using exact orbit identities, not numerical
  computation.

Candidate falsifier for uniform barrier: algebraic seam `X=100`. Odd normalized source jets vanish,
so orientation is zero; corpus seam factorization makes corrected slope negative. The exact Lie-law
to prove is

`Q * Lie(Ω_clear) = slope_clear + 11 * (f₁ - (B/2)f₀) * Ω_clear`.

At `Ω_clear=0`, this identifies slope with the vector-field derivative up to positive factor `Q`.
If verified, the source-positive vector field points out of the proposed orientation region at this
seam, so physical initial-value/incidence data is logically indispensable.

## Open core

**[OPEN CORE]** After the uniform-flow audit, prove or refute
`C5-ORBIT-FIRST-CONTACT` on the actual modular theta trajectory. No chamber-only or arbitrary-flow
substitute closes the RH chain.

## Log

- 2026-08-29 — Extracted exact first-contact replacement after formal failure of global
  chamber-only slope positivity. RH passport and hostile uniform-flow falsifier fixed before Lean
  proof attempt.
