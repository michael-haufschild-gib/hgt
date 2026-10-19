# Arithmetic Criticality Theory: positive supersolutions for the odd-sector arithmetic jump form

- **ID:** act-2026-10-19
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for M1–M3 exact parts; CONJECTURE for M4–M5
- **Source:** docs/reports/review-1910/fable.md §4; receiver `riemannHypothesis_iff_odd_primeChain_poincare` (THIM) and `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare` (RHTower)
- **Statement:** RH ⟺ the odd-sector form `E_arch + E_prime − ∫ Θ cosh(x/2) v²` is not supercritical. A positive odd `ω` with `𝓛_N ω ≥ Θ cosh(x/2) ω` on `(0,∞)` implies RH through the folded ground-state representation; the shifted ground states `ω_a = (Θ(·−a) − Θ(·+a))/Θ` are exact `𝓛_D`-supersolutions with source `2 sinh(a/2) sinh(x/2) Θ` and fail the `𝓛_N` condition by the reflected collar mass.

## Goal
Replace the sign problem (a bound) by an existence problem (one positive function). The identities are
unconditional; RH content enters only through the equation of motion of Riemann's kernel
(`theta_harmonic_identity`). Not circular: no positivity is assumed; a supersolution is a hypothesis
of an implication whose other direction (M5) is the open research question.

## Gates
- [x] 0 → 1  in-progress: well-posed (Section 3 of the README), source-pure (Doob coordinates of the literal Weil form), attack idea (ground-state representation with the folded generator), Door passport: the receiver is the existing odd Poincaré criterion.
- [ ] 1 → 2  fully-proven: M3 asymptotic failure of `ω_a` (paper), M4 superposition extremal problem.
- [ ] 2 → 3  formalized: M1 modules (see Log), M2, M3 exact identities.
- [ ] 3 → 4  not applicable (no stage 4; RH only).

## Approach
1. Pointwise ground-state identities; finite jump form; finite Allegretto–Piepenbrink both directions
   (Rayleigh minimiser + absolute value).
2. Folded ground-state representation of `markovEnergy (Θ v)` for odd `v = ω u`: nonnegative
   remainder plus `2∫_{x>0} u² ω (𝓛_N ω − Θ cosh(x/2) ω)`.
3. Sufficiency: folded supersolution ⟹ `markovEnergy (Θ v) ≥ 0` ⟹ RH.
4. Shifted ground states: source equation via `oddProfile_harmonic_identity`; folded defect
   `2Θ(x)[sinh(a/2) sinh(x/2) − C_a(x)]`.
5. Paper: PNT asymptotics of `C_a(x)`; ratio `2∫_0^∞ e^{s/2}(Θ(s−a)−Θ(s+a)) ds / sinh(a/2) > 1`.
6. M4/M5 as in README §5.

## Lean modules (formal/GaloisForLFunctions/ArithmeticCriticalityTheory/)
- `GroundStateRepresentationAlgebra.lean` — pointwise identities, finite GSR, easy direction.
- `FiniteJumpFormAllegrettoPiepenbrink.lean` — Schrödinger matrix, Rayleigh form, hard direction, connectivity.
- `DoobJumpFoldedGroundStateRepresentation.lean` — folded shift GSR for the Doob forms.
- `OddSupersolutionCriterion.lean` — total GSR and the sufficiency theorem.
- `ShiftedGroundStateFoldedDefect.lean` — source equation and reflected collar defect of `ω_a`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** (open)
- **Strongest positive survivor:** (open)
- **New insight:** (open)
- **Status:** (open)

## Log
- 2026-10-19 — created in 1-in-progress from docs/reports/review-1910/fable.md §4; README written; module 1 drafted.
