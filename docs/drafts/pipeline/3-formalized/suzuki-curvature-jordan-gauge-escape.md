# Suzuki curvature Jordan-gauge escape

Status: `[FORMALIZED]` 2026-08-30; hostile corpus/literature/falsity audits and Lean audits passed.

## Exact RH proof chain

Exact signed Suzuki prime--archimedean curvature cells
→ floor-selected affine checkpoint current
→ bounded CCM-FU Suzuki checkpoint mixture
→ `riemannHypothesis_of_ccmFUSuzukiCheckpointAffineMixtureBound`
→ RH.

The result targets the shared CCM-FU/SP-E source representation. It does not assert the remaining
conditional cancellation. It asks whether that cancellation can live in any finite-variation,
Jordan-separated, or trace-class event measure after an equivalent positive diagonal change of
source coordinates.

## `[CORPUS]` exact input

For

`c_N = ∫_[log N, log(N+1)] screwRegularKernel(t) dt - Λ(N+1)/sqrt(N+1)`,

the corpus proves:

- `suzukiCheckpointAffineSlope_succ_sub_eq_signedCurvatureCell`: `c_N` is exactly the jump of the
  arithmetic affine checkpoint slope;
- `suzukiCheckpointSignedCurvatureCell_neg_iff_odd_primePower_endpoint`: `c_(k-1) < 0` exactly at
  odd prime-power endpoints;
- `suzukiCheckpointSignedCurvatureCell_pos_iff_not_odd_primePower_endpoint`: every other endpoint
  has positive curvature;
- `suzukiPsi_log_nat_eq_affine_add_signedCurvatureGreen_add_resets`: the endpoint source is the
  signed curvature Green potential modulo affine memory and an absolutely summable positive reset;
- `ccmFUCentralXiScrewPositiveMixtureBound_iff_checkpointAffineMixtureBound`: the checkpoint
  current retains the RH-bearing CCM-FU burden.

## `[CONJECTURE]` S-CURVATURE-JORDAN-GAUGE-ESCAPE

Define `c_N⁺ = max(c_N,0)` and `c_N⁻ = max(-c_N,0)`. For every positive diagonal gauge
`w : ℕ → ℝ` admitting one uniform lower bound `ε > 0`, neither series

`Σ_N w_N c_N⁺` nor `Σ_N w_N c_N⁻`

is summable.

Equivalently, no uniformly nondegenerate positive diagonal re-coordination turns the exact signed
curvature source into a finite signed measure. In particular, no finite-variation, trace-class, or
separately convergent Hahn--Jordan assembly can be the missing CCM-FU/SP-E producer.

## Hostile falsity and rediscovery audit

- Positive cells: endpoints `k = 6(m+1)` are never prime powers, so the atomic term vanishes. The
  regular-screw cell has a fixed positive multiple of `k^(-1/2)` as a lower bound.
- Negative cells: at every prime `p ≥ 5`, the atomic term is `log(p)/sqrt(p)`, while the smooth
  cell is at most `(27/25)/sqrt(p)`. Since `log 5 > 8/5`, the negative Jordan mass retains at least
  `(13/25)/sqrt(p)`.
- Both comparison series diverge: the first on the explicit `6(m+1)` lattice and the second over
  all primes after deleting the finite set `{2,3}`.
- Existing corpus no-gos cover absolute Suzuki wall masses, fixed positive channel rank, bounded
  scalar dressings, and a different centered Route-T source. Corpus search found no theorem for
  both Jordan components of this exact signed curvature source or invariance under every uniformly
  nondegenerate diagonal gauge.

Verdict: `SURVIVES PRELIMINARY ATTACK`.

## Dependency-closed paper proof

Write

`I_k = ∫_[log(k-1), log k] screwRegularKernel(t) dt`, so
`c_(k-1) = I_k - Λ(k)/sqrt(k)`.

### Positive Jordan sector

Fix `m ≥ 0` and put `k = 6(m+1)`. Since both `2` and `3` divide `k`, `k` is not a prime
power. Hence `Λ(k)=0`. The corpus checkpoint-cell estimate gives

`I_k ≥ (4/5)/sqrt(k)`.

Here `k ≥ 6`, so `sqrt(k) ≥ 2`; using `sqrt(k)^2=k` gives

`1/k ≤ (4/5)/sqrt(k) ≤ c_(k-1)^+`.

If `w_N ≥ ε > 0`, then

`ε/(6(m+1)) ≤ w_(6(m+1)-1) c_(6(m+1)-1)^+`.

The index map `m ↦ 6(m+1)-1` is injective. Summability of the weighted positive Jordan sector
would therefore imply summability of the shifted harmonic series after multiplication by `6/ε`,
a contradiction.

### Negative Jordan sector

Fix a prime `p ≥ 5`. Then `Λ(p)=log p`. The corpus upper cell estimate and scaled square-root
gap bound give

`I_p sqrt(p) ≤ 27/25`.

Monotonicity of `log`, together with the corpus theorem `log 5 > 8/5`, gives
`log p > 8/5`. Therefore

`(-c_(p-1)) sqrt(p) = log p - I_p sqrt(p) ≥ 13/25`.

In particular `c_(p-1)<0`. Also `sqrt(p) ≥ 2`, hence `25 ≤ 13 sqrt(p)` and

`1/p ≤ (13/25)/sqrt(p) ≤ c_(p-1)^-`.

Thus every uniformly nondegenerate gauge satisfies

`ε/p ≤ w_(p-1)c_(p-1)^-`.

The map `p ↦ p-1` is injective. Summability of the weighted negative Jordan sector would imply
summability of `1/p` over all primes `p ≥ 5`. The omitted primes `{2,3}` form a finite set, so this
contradicts Euler divergence of the prime harmonic series.

Both contradictions are unconditional. They prove the stated two-sided Jordan-gauge escape and
the closed existential class no-go.

## Hostile proof audit

- No sign classification is inferred from asymptotics: positive endpoints have exactly zero atomic
  term, while negative endpoints are primes and use the exact von Mangoldt value.
- Lower bounds are pointwise and uniform on infinite injective subsequences; no density claim is
  used.
- The gauge is allowed to be unbounded and otherwise arbitrary. Only the necessary
  nondegeneracy condition `w_N ≥ ε > 0` is used.
- The negative comparison discards only `{2,3}`. This is a finite alteration of the prime harmonic
  series, not an unproved statement about prime distribution.
- No numerical experiment, RH consequence, or conditional analytic estimate enters the proof.

Verdict: `DEPENDENCY-CLOSED PAPER PROOF`.

## Lean realization

Module:
`GaloisForLFunctions.RHTower.Suzuki.SuzukiCurvatureJordanGaugeEscape`

Public conclusions:

- `suzukiCheckpointSignedCurvaturePositiveMass_ge_sixthHarmonic`;
- `suzukiCheckpointSignedCurvatureNegativeMass_ge_primeHarmonic`;
- `not_summable_suzukiCheckpointSignedCurvaturePositiveMass_mul_of_uniformLowerBound`;
- `not_summable_suzukiCheckpointSignedCurvatureNegativeMass_mul_of_uniformLowerBound`;
- `no_uniformlyNondegenerate_summable_suzukiCheckpointCurvatureJordanGauge`.

The formal negative-sector proof uses the cofinite prime tail `p ≥ 11` and the already imported
certificate `log 3 > 0.9`; this removes only `{2,3,5,7}` and proves the same class no-go with a
smaller dependency cone.

Audit:

- direct `lake env lean` check passed;
- targeted `lake build GaloisForLFunctions.RHTower.Suzuki.SuzukiCurvatureJordanGaugeEscape` passed;
- `#print axioms` reports only `propext`, `Classical.choice`, and `Quot.sound`;
- module is wired into `GaloisForLFunctions.RHTower`;
- repository lint recognizes this module as reachable. Global lint remains red only on unrelated
  pre-existing/concurrent unreachable modules elsewhere in both theorem-area umbrellas.

## Literature audit (2026-08-30)

Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096v2, proves finite-aperture
operator results but explicitly identifies cofinal arithmetic prime control as beyond its argument.
Suzuki's 2022 screw-function and screw-line papers give RH equivalences and unconditional local
identities, not the discrete event-curvature Hahn--Jordan classification above. The 2026 numerical
operator paper reports experiments and explicitly does not prove RH. Searches of these primary
sources and arXiv records found no bounded-diagonal-gauge or two-sided Jordan-escape theorem for
this curvature measure.

Primary records:

- https://arxiv.org/abs/2606.09096
- https://arxiv.org/abs/2206.03682
- https://arxiv.org/abs/2209.04658
- https://arxiv.org/abs/2607.24830

## Proposed positive survivor

The signed curvature measure is not merely non-summable: its positive and negative sectors each
carry invariant infinite mass in every equivalent diagonal source gauge. Therefore any viable
CCM-FU/SP-E proof must retain the unsplit conditional Green potential before Jordan decomposition,
or use a genuinely singular/non-invertible damping together with an exact inverse landing. Ordinary
finite signed measures, trace-class event operators, and boundedly invertible diagonal changes of
source norm are excluded.
