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

## Modular-center velocity attack

[CORPUS] `ThetaCuspFifthRootCurvatureStationaryLocus` proves every negative modular-center C5
failure has an interior witness where the literal numerator velocity vanishes.  The same corpus
gives the exact half-line factorization

`thetaCuspFullSource(t) = firstAtom(t) * LikelihoodPartition(B(t))`

and theta-specific support-gap cumulant inequalities, including strict positivity of the third
cumulant and `2 * normalizedMoment₂ < cumulant₃`.  Existing fixed-action likelihood reductions
require `t ≤ u` and therefore do not cover the modular centre `u=0<t`.

[LITERATURE] Planat--Solé's 2026 second-level concavity theorem controls a lower theta-kernel
Laguerre expression.  Corpus countermodels prove that second-level concavity and its Riccati
strengthening do not force fifth-root curvature.  No published fifth-root velocity law was found.

**[CONJECTURE C5-VP1]** For every `t>0`,

`0 < thetaCuspReflectedSourceFifthRootCurvatureVelocity 0 t`.

Exact proof chain:

`C5-VP1`
→ no negative stationary witness
→ modular-center source C5 at every radius
→ off-center/direct-J rank-four assembly
→ higher-packet no-escape
→ CLG/TTF or Weil positivity
→ RH.

Falsifier: one positive `t` with nonpositive literal velocity.  Current attack substitutes the
first-atom plus likelihood-cumulant log jets into the division-free velocity, then uses the sharp
spectral support edge rather than generic moment positivity.  If those inequalities do not force
the sign, classify the exact residual inequality and build an unconditional countermodel to kill
that proof architecture before returning to actual theta-orbit incidence.

## Modular-center velocity likelihood-reserve result

**[SIGNIFICANT PREMISE DISCHARGED IN LEAN]** The literal center velocity is exactly a positive
source-product square times an action three-jet core.  Its third likelihood channel is
`-10*(exp(action)-1)*t²*g₃`.  The theta-specific strict support-gap theorem
`6*g₂ < -g₃` proves that this channel pays strictly more than the reserve
`60*(exp(action)-1)*t²*g₂` for every `t>0`.

Consequently the entire third-cumulant burden has been removed from `C5-VP1`: nonnegativity of the
explicit `thetaCuspCenterFifthRootVelocityMasterReservedCore`, which contains no third likelihood
jet, implies strict positivity of the literal modular-center velocity.  The remaining open premise
uses only action, the first two center jets, and the explicit first-atom third jet.  Proving it for
all `t>0` closes `C5-VP1`; off-center/direct-J and downstream RH joins remain open.  See
`../3-formalized/theta-cusp-c5-center-velocity-likelihood-reserve.md`.

## Log

- 2026-08-29 — Formalized exact source-square normalization, center likelihood-jet decomposition,
  and strict six-curvature support-gap reserve.  Third likelihood cumulant is no longer an open
  `C5-VP1` premise.

## Modular-center second-likelihood reserve result

**[SIGNIFICANT PREMISE DISCHARGED IN LEAN]** Substitute the exact center identity
`q₂=2*(firstAtomCurvature-g₂)` into the master-reserved core.  Lean proves the exact decomposition

`masterReservedCore`
`= firstAtomCurvatureCore + 2t*g₂*(R*(30t+15t*q₁-1)+3t*q₁)`.

The coefficient is strictly positive for every `t>0`.  Mechanism is structural: positive theta
log-curvature makes center action convex and gives `0<A≤t*q₁`; if the displayed affine coefficient
is negative, that sign itself forces action velocity into the regime where
`exp(A)-1<3t*q₁`, reversing the adverse product and leaving a strict positive reserve.

Thus second likelihood curvature is strictly favorable.  Together with the preceding support-gap
theorem, all second and third likelihood cumulants have been removed from `C5-VP1`.  Exact remaining
premise is

`0 ≤ thetaCuspCenterFifthRootVelocityFirstAtomCurvatureCore(t)` for every `t>0`.

It involves only actual action, actual first jet, and explicit first-atom curvature/third jet.  See
`../3-formalized/theta-cusp-c5-center-velocity-second-likelihood-reserve.md`.

## Log

- 2026-08-29 — Formalized convex action--terminal-velocity law, universal exponential C5
  coefficient positivity, and exact strict second-likelihood reserve.  Second and third likelihood
  cumulants are no longer open `C5-VP1` premises.
