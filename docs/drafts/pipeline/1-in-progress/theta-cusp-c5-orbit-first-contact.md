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
- [x] Test strongest replacement: completed C5 orientation is an invariant-region barrier for the
  exact source-positive polynomial vector field.
- [x] If uniform barrier fails, formalize exact counterexample and strongest positive survivor.
- [x] Close cofinal physical-incidence burden by exact spectral condensation, not numerical
  computation.
- [ ] Attack compact physical-incidence statement using exact orbit identities.

Candidate falsifier for uniform barrier: algebraic seam `X=100`. Odd normalized source jets vanish,
so orientation is zero; corpus seam factorization makes corrected slope negative. The exact Lie-law
to prove is

`Q * Lie(Ω_clear) = slope_clear + 11 * (f₁ - (B/2)f₀) * Ω_clear`.

At `Ω_clear=0`, this identifies slope with the vector-field derivative up to positive factor `Q`.
If verified, the source-positive vector field points out of the proposed orientation region at this
seam, so physical initial-value/incidence data is logically indispensable.

## Open core

**[OPEN CORE]** Prove or refute `C5-ORBIT-FIRST-CONTACT` on the remaining compact segment of the
actual modular theta trajectory. Cofinal positivity is unconditional: Lean proves
`Ω(x)/scale(x)^4 → 36864`, hence `Ω(x)>0` beyond some threshold. No chamber-only or arbitrary-flow
substitute closes the compact incidence gap.

## Log

- 2026-08-29 — Extracted exact first-contact replacement after formal failure of global
  chamber-only slope positivity. RH passport and hostile uniform-flow falsifier fixed before Lean
  proof attempt.
- 2026-08-29 — Uniform-flow replacement killed in Lean. Exact law
  `Q*Lie(Ωc)=Sc+11*(f₁-(B/2)f₀)*Ωc` reduces every orientation-boundary crossing to corrected-slope
  sign. At seam `X=100`, mass/gap are positive, `U',B'>0`, `Q'=0`, yet `Ωc=0` and `Lie(Ωc)<0`.
  Therefore physical theta-orbit incidence or a stronger orbit invariant is mandatory. See
  `../3-formalized/theta-cusp-c5-source-positive-flow-inward-barrier-no-go.md`.
- 2026-08-29 — Discharged entire far-tail burden in Lean. Fixed spectral-gap cooling gives
  super-polynomial extinction of normalized likelihood moments and cumulants through order seven;
  all likelihood log jets are `o(scale)`. First-atom normalized jets converge to
  `4,8,16,32,64,128`, forcing exact normalized C5 orientation limit `36864` and cofinal strict
  positivity. Remaining open core is compact actual-orbit incidence. See
  `../3-formalized/theta-cusp-c5-exact-completed-seam-far-tail.md`.
- 2026-08-29 — Killed static adapted thin-clock replacement. Physical identities
  `r=Rz`, `B=R(z-v)/3` translate the corpus clock cone `(2/5)z<v<(1/2)z` into
  `5B<r<6B`. Lean now constructs a strict source-positive, positive-gap state inside exactly this
  cone with negative corrected C5 slope. Therefore no implication from these pointwise orbit
  inequalities can prove first-contact orientation. Strongest survivor is genuinely dynamical:
  use centre initial data and an invariant/history law that excludes the negative component of the
  orientation boundary. See
  `../5-failed/theta-cusp-c5-static-thin-clock-first-contact.md`.

## Lowest-weight reduction attack

[CORPUS] `modularThetaSourcePositiveSl2R` and `modularThetaSourcePositiveSl2K` are annihilated by
the source lowering field; in adapted coordinates the lowering field is `-∂/∂b`. The physical
variables satisfy `r=Rz>0` and `k=R²(1-z²)/16>0`, while `k` decreases on the positive orbit.

[LITERATURE] Ramanujan--Serre theory supplies differential closure of modular and quasimodular
forms, but no real-orbit separator for this C5 covariant. Current order-moment/Hankel
total-positivity theorems require a positive moment representation in the varied order and do not
apply to this spatial log-cumulant derivative. The 2024 Ramanujan-vector-field invariant-curve
preprint was withdrawn and concerned positive-characteristic algebraic curves, not this real theta
orbit.

[CONJECTURE C5-LOWEST-WEIGHT-REDUCTION] The cleared exact completed C5 orientation polynomial is a
lowest-weight vector for the source `sl₂` action:

`Lie(sl2F, Ω_clear) = 0`.

Equivalently, after the exact adapted-coordinate automorphism, `Ω_clear` is independent of `b`.
Since it vanishes on the full algebraic seam `r=0`, it must factor as `r * P(r,k)`. If the remaining
two-variable factor is positive on the physical region `r>0`, `0<k≤k(0)`, this closes

`lowest-weight factorization`
→ `Ω>0` on full positive theta orbit
→ `completed C5 direct-J orientation at every centre`
→ `compact/far-tail assembly and rank-four/Ptolemy wall`
→ `CLG/TTF or Weil-polarization positivity`
→ `RH`.

[OPEN CORE] Prove or refute the exact lowering identity. If it survives, classify the resulting
two-variable factor and its sign on the centre-anchored monotone `(r,k)` trajectory.

## Lowest-weight attack result

**[FALSIFIED IN LEAN]** `C5-LOWEST-WEIGHT-REDUCTION` is false. At zero-scale seam
`U=B=0`, `Q=-3/8`, physical source field and `sl₂F` agree on every polynomial observable.
Orientation vanishes there, but exact covariant Lie law gives

`eval(sl₂F(Ω_clear)) = (-3/8)^5 * modularThetaC5FixedActionSeamPolynomial(0) > 0`.

Therefore adapted orientation genuinely depends on clock `b`; no factorization through `(r,k)` can
close compact incidence. Positive survivor is explicit lowest-weight anomaly: surviving proof must
retain `b` dynamics or construct invariant carrying same fixed-action C5 charge. See
`../3-formalized/theta-cusp-c5-lowest-weight-anomaly.md` and
`../5-failed/theta-cusp-c5-lowest-weight-reduction.md`.

Remaining RH proof chain is unchanged:

`compact centre-anchored C5 first-contact incidence`
→ `global Ω>0`
→ `completed C5 direct-J orientation`
→ `compact/far-tail and rank-four/Ptolemy assembly`
→ `CLG/TTF or Weil positivity`
→ `RH`.
