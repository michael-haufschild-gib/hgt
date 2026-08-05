# Co-moving mass cone for the literal Xi prime source

- **ID:** mass-xi-comoving-prime-cone
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** For every `σ > 1/2`, the legal depth-one von-Mangoldt source with mass `a(u) = |u| + 2` is uniformly bounded by `‖π i‖ xiPoissonTraceReal (σ - 1/2) + xiMassBottomArchUniformBound 2 σ`.

## Goal

Prove an unconditional, source-faithful bounded cone adjacent to the fixed-mass open core.  This
does not assert RH: mass changes with vertical time.  Its value is to isolate the missing theorem as
an aperture-recovery principle from a linearly widening Bessel mass cone to one fixed aperture.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem `norm_xiMassBottomPrimeIntegral_comoving_le`, targeted build green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact claim C12

Put `a(u) = |u| + 2`.  For `1/2 < σ` and every `u : ℝ`,

`‖xiMassBottomPrimeIntegral (a(u)) 1 (σ + u I)‖`

`≤ ‖(π : ℂ) * I‖ * xiPoissonTraceReal (σ - 1/2)`

`  + xiMassBottomArchUniformBound 2 σ`.

The contour is legal because `1/2 < 1 < a(u)`, and `a(u) ≥ 2 ≥ |u|`.

## Approach

1. Prove a universal co-moving trace lemma.  If an abstract spectral family has base at least
   `1/2`, `a ≥ 1/2`, `|u| ≤ a`, and `σ > 1/2`, then

   `‖(F.mass ha).traceC (σ + u I)‖ ≤ F.traceReal (σ - 1/2)`.

   For a point `p = R + iJ` and its mass image `M + iK`, the conserved law `MK = RJ`, the strict
   bounds `|J| < 1/2`, `M > R`, and the base hypothesis imply `a < M`.  Hence
   `uK ≤ |u||K| ≤ M|K| = R|J| ≤ R/2`.  Therefore
   `-σM + uK ≤ -(σ - 1/2)R`.  Sum the resulting termwise majorant.

2. Prove mass antitonicity of the complete archimedean bound.  For `1/2 < b ≤ a`, both
   `sqrt(x²+a²)` on the centered line and `sqrt(a²-1/4)` at the crossed pole increase with mass.
   Since `σ>0`, their exponential weights decrease; the logarithmic derivative is independent of
   mass.  Thus `xiMassBottomArchUniformBound a σ ≤ xiMassBottomArchUniformBound b σ`.

3. Use the exact source identity

   `prime = I * (π I * massTrace) + arch`

   at `a=a(u)`, `c=1`; apply the trace cone and the archimedean antitonicity with `b=2`.

## Complete paper proof `[PROVED HERE]`

Let `p=R+iJ` be one point of an admissible family with `1/2 ≤ base`, and write its mass image as
`M+iK`.  Then `R≥1/2` and `|J|<1/2`, so `R²-J²>0`.  The principal-root identity gives
`M² ≥ R²-J²+a²>a²`; because `a>0` and `M≥0`, this implies `a<M`.  Mass shifting also gives
`R<M` and conserves charge: `MK=RJ`.  Taking absolute values and using positivity of `M,R` yields
`M|K|=R|J|`.

If `|u|≤a`, then

`uK ≤ |u||K| ≤ a|K| ≤ M|K| = R|J| ≤ R/2`.

For `σ>1/2`, therefore,

`-σM+uK ≤ -σR+R/2 = -(σ-1/2)R`.

Exponentiation bounds the norm of each mass term by the original weight at real time
`σ-1/2`.  That weight is summable, so the norm of the mass trace is at most
`F.traceReal(σ-1/2)`.

Now let `1/2<b≤a`.  On the centered archimedean line, mass enters only through
`exp(-σ sqrt(x²+a²))`; the remaining logarithmic derivative is independent of mass.  Since
`sqrt(x²+a²)` increases with `a`, the norm integrand decreases pointwise and the integral does too.
The crossed-residue frequency `sqrt(a²-1/4)` also increases, so its exponential weight decreases.
Thus the entire bound satisfies `B(a,σ)≤B(b,σ)`.

Finally set `a(u)=|u|+2`, `b=2`, and `c=1`.  Then `|u|≤a(u)` and the contour is legal.  The exact
identity

`prime = I * (π I * massTrace) + arch`

plus the triangle inequality, the trace estimate, and `B(a(u),σ)≤B(2,σ)` gives C12 pointwise for
every real `u`.  No limit, truncation, zero-free hypothesis, or RH input occurs. ∎

## Lean certificate

| Role | Declaration | Module |
|---|---|---|
| shifted height exceeds aperture | `HTGeometry.AbstractSpectralFamily.lt_re_mass_of_base_half` | `HTGeometry.AbstractSpectralComovingMass` |
| termwise cone | `HTGeometry.AbstractSpectralFamily.norm_mass_term_le_comoving_weight` | same |
| universal trace cone | `HTGeometry.AbstractSpectralFamily.norm_mass_traceC_le_comoving` | same |
| complete Gamma antitonicity | `xiMassBottomArchUniformBound_antitone` | `RHTower.XiMassComovingPrimeCone` |
| Xi trace cone | `norm_xiMassTraceC_comoving_le` | same |
| literal prime-source capstone | `norm_xiMassBottomPrimeIntegral_comoving_le` | same |

Verification:

- `lake env lean GaloisForLFunctions/HTGeometry/AbstractSpectralComovingMass.lean` — PASS.
- `lake env lean GaloisForLFunctions/RHTower/XiMassComovingPrimeCone.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.XiMassComovingPrimeCone` — PASS (`9384/9384`).
- `#print axioms` on trace, Gamma, and prime capstones — only `propext`, `Classical.choice`,
  `Quot.sound`.
- Both new modules are wired into their umbrellas.

## Hostile audit

- **Generic-family gap found and repaired:** `mass height ≥ mass` is false for an arbitrary
  admissible family.  The proof needs `1/2 ≤ F.base`, which gives `R²-J²>0` and hence `a<M`.
  Xi satisfies the stronger base floor `R>3`.
- **No hidden RH input:** only admissibility, exact mass conservation, Xi source identity, and
  positive-real-time integrability occur.
- **No fixed-mass smuggling:** `a(u)` depends on `u`; vertical-line rigidity cannot be applied.
- **No auxiliary-channel growth:** the entire archimedean bound is antitone in `a`, not merely
  bounded separately for each mass.
- **No asymptotic or computation:** bound is pointwise in every real `u` with explicit constant.

## Door passport

- **Door 0:** exact moving-mass theorem, not RH and not a renamed fixed-mass criterion.
- **Door 1:** literal von-Mangoldt integral on a legal Euler line; no spectral surrogate in the
  conclusion.
- **Door 2:** stronger all-copy pointwise majorant is summed before source transfer.
- **Door 3:** no numerical evidence or finite truncation.
- **Door 4:** unconditional Lean target; only standard quotient/classical axioms permitted.

## Log

- 2026-08-05 — created in 1-in-progress after internal collision audit; C12 frozen.
- 2026-08-05 — hostile audit rejected the false generic assertion `mass height ≥ mass`; added the
  sharp base-floor hypothesis and upgraded target from trace-only to literal prime source.
- 2026-08-05 — paper proof dependency-closed; universal trace cone, full Gamma antitonicity, and
  literal source theorem formalized unconditionally. Targeted build and axiom audit pass.
