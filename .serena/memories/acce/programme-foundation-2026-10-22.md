# ACCE — Arithmetic Continuation and Critical Energy

New Lean programme: `formal/GaloisForLFunctions/ArithmeticContinuationAndCriticalEnergy`, umbrella
`GaloisForLFunctions.ArithmeticContinuationAndCriticalEnergy` (wired into `MainTheorems.lean`),
foundational README in the folder, pipeline card
`docs/drafts/pipeline/1-in-progress/arithmetic-continuation-and-critical-energy.md`.
Source: `docs/reports/review-2110/astra.md` § "New field - research programme".

## Central question
Which exact arithmetic relations prevent a complete signed critical energy from escaping as a
parameter (damping, coefficient cutoff, aperture) runs to its critical end? RH on the damped Möbius
lane is a transport question, not an inequality at one damping.

## Objects
- `Admits E ε := ∃ B, ∀ T, E ε T ≤ B` for `E : ℝ → ℕ → ℝ` (parameter × observation horizon);
  `CofinallyAdmits`, `UniformlyAdmitsOn`.
- `dampedMobiusEnergy = RHTower.pmPowerDampedDivisorDiscreteEnergy`.
- `signedDampingWork ε T = Σ_{n≤T} A_ε(n) E_ε(n)/(n(n+1))`, `E_ε = ∂_ε A_ε` the centred damped
  Chebyshev function from BVI's `DampedChebyshevTangentFormOfTheReceiver`.
- `LinearContinuation` / `OsgoodContinuation` budgets: one primitive `β` for all horizons.

## Theorems that matter
- `scaledEnergy_add_budget_le` — master monotonicity of `Ψ∘E + β`.
- `one_add_le_mul_exp_of_linear_work`, `Admits.of_linearContinuation`,
  `cofinallyAdmits_of_linearContinuation`; Osgood twins with `bddAbove_of_tendsto_atTop`.
- `hasDerivAt_dampedMobiusEnergy` : `∂_ε E_T = 2 W_T`;
  `two_mul_signedDampingWork_eq_markov` identifies it with BVI's flux − jump − forcing balance.
- `riemannHypothesis_of_dampingContinuation_endpoint` (any admitted endpoint),
  `riemannHypothesis_of_dampingContinuation_above_half_abscissa` (Littlewood endpoint shortens the
  obligation to `(0, Θ/2]`), `riemannHypothesis_of_superlinear_dampingContinuation`.
- `zetaZeroAbscissa_le_half_add_of_partial_dampingContinuation` — partial continuation above `a₀`
  gives the strip `Θ ≤ ½ + a₀`: the non-RH deliverable.
- `dampingContinuation_of_tangentNorm_le` — the owned tangent-norm receiver is the special case.
- `exists_vanishing_signed_work_with_large_tangent` — strictly weaker: a two-cell rotating row has
  constant energy, zero signed work, tangent norm `|K|`.
- `not_linearContinuation_escapeEnergy` — `exp(2(½−ε)log(T+1)) − 1` satisfies an exact per-horizon
  linear bound with the endpoint budget and escapes: the horizon quantifier placement is the theorem.
- `affineEnvelope`, `affineEnvelope_eq`, `affineEnvelope_le_of_contraction`,
  `affineEnvelope_one_one` — iterated sector compensation needs a contraction, not per-stage
  cancellation.
- `floor_le_of_relative_decay(_Ico)` — aperture mirror: bounded *relative* decay of a positive
  ground floor forbids crossing, with an explicit `μ(a)exp(−(β c − β a))` floor.
- `pronicNorm_add_sq`, `exists_sector_count_complete_energy_gt`,
  `exists_ratio_tendsto_zero_and_complete_unbounded` — cross-term discipline.

## Traps recorded
Horizon-dependent budgets transport nothing; the tangent norm is strictly stronger than the signed
pairing; ratio smallness is not a bound; sector energies may not be added; a non-coercive scale is
vacuous; recovery is not control (`RHTower.not_exists_uniform_lower_bound_primeGammaCauchyHorizonGrade`);
`A_ε(⌊x⌋)` vs the real-centred `𝒜_ε(x)` differ by a fractional-part term; an absolute dilation
estimate meets `Σ Λ(k)k^{−ε−1/2}` and cannot pass below half damping.

## Open
(C) the horizon-free bound on the negative part of `2W_T` on each compact damping interval; its
superlinear variant; a contracting complementary-sector recurrence; the compensated width floor (G);
the aperture instance; a stability theorem for a signed, origin-sensitive observation.

The shared-target section of all programme READMEs now says "Eight programmes" and carries
mechanism 6 (continuation), owned by this programme.
