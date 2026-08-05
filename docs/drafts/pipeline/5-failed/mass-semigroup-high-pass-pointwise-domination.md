# Pointwise domination cannot bound the mass-semigroup prime high-pass

- **ID:** mass-semigroup-high-pass-pointwise-domination
- **Stage:** 5-failed
- **Type:** FALSIFIED
- **Source:** ../../../reports/mass-shifted-spectral-trace-route.md · §9.3 Exact open core
- **Statement:** The canonical fixed-minus-co-moving mass high-pass admits a height-uniform
  pointwise or almost-everywhere majorant on the common Euler line.

## Goal

Test whether the bounded co-moving arm makes the canonical aperture gap small before integration,
so that modulus estimates, dominated convergence, or a uniform `L¹` kernel bound could close the
prime-source open core.

## Gates

- [x] 0 → 1 in-progress: exact common-line kernel already formalized
- [ ] 1 → 2 fully-proven: conjecture falsified instead
- [x] no-go closure: positive-measure divergence cone and strongest positive survivor Lean-proved

## Failed conjecture C16

For fixed `σ>0`, the kernel

`Kσ(u,x) = xiMassBottomTest 1 (3/4) (σ+iu) x`

`           - xiMassBottomTest (|u|+2) (3/4) (σ+iu) x`

has a finite height-uniform pointwise majorant, at least almost everywhere in `x`.  An integrable
such majorant would permit absolute-value control of the factored von-Mangoldt integral.

This conjecture is false in the strongest elementary sense: no finite real-valued majorant exists
even without requiring measurability or integrability.

## Exact killing theorem/mechanism

Put `z_x=x-3i/4` and write

`sqrt(z_x²+a²)=M_a(x)+i K_a(x)`

for the principal mass root.  Lean proves the exact charge law

`M_a(x) K_a(x) = -3x/4`.

For every `x<-3/4` and every `a>3/4`, one has `M_a(x)>a` and `K_a(x)>0`.  Hence the fixed arm has
exact modulus

`exp(-σ M_1(x) + u K_1(x)) → ∞`.

For the co-moving aperture `A(u)=u+2` on `u≥0`, charge conservation and `M_A(x)>A(u)>u` give

`u K_A(x) ≤ M_A(x)K_A(x) = -3x/4`.

Therefore

`‖test_A(u)(σ+iu,x)‖ ≤ exp(-σ(u+2)-3x/4) → 0`.

The reverse triangle inequality now yields

`‖Kσ(u,x)‖ → ∞`

for every `x<-3/4`, an entire positive-measure half-line.  Applying the result along integer
heights and intersecting the countably many almost-everywhere domination statements on
`[-2,-1]` proves that no finite function `g(x)` can dominate `‖Kσ(u,x)‖` for every real height even
almost everywhere.

## No-go closure

- **Exact killing theorem/mechanism:**
  `tendsto_norm_xiMassSemigroupHighPassKernel_negative_frequency_atTop` proves pointwise
  divergence on every `x<-3/4`.
- **Strongest positive survivor:**
  `not_exists_ae_uniform_majorant_xiMassSemigroupHighPassKernel` proves absence of any finite
  uniform almost-everywhere majorant.  Thus no uniform `L¹` majorant exists.
- **New insight:** the mass-semigroup subtraction is an integrated high-pass, not a pointwise
  smoothing operation.  The co-moving arm vanishes on the negative-frequency cone while the
  fixed arm grows.  Any proof of bounded integrated source must retain cancellation between
  frequency regions and the complex von-Mangoldt factor; pointwise modulus, dominated
  convergence, and fixed-frequency estimates are structurally incapable of closing the route.
- **Status:** paper proof dependency-closed and formalized in
  `RHTower.XiMassPrimeSemigroupHighPassPointwiseNoGo`.

## Lean certificate

- `RHTower.xiMassAnalyticSqrt_re_mul_im`
- `RHTower.xiMassHighPassBottomRoot_charge`
- `RHTower.xiMassHighPassBottomRoot_re_gt_mass`
- `RHTower.norm_xiMassBottomTest_comoving_negative_frequency_le`
- `RHTower.tendsto_norm_xiMassBottomTest_comoving_negative_frequency_zero`
- `RHTower.tendsto_norm_xiMassBottomTest_fixed_negative_frequency_atTop`
- `RHTower.tendsto_norm_xiMassSemigroupHighPassKernel_negative_frequency_atTop`
- `RHTower.not_exists_ae_uniform_majorant_xiMassSemigroupHighPassKernel`

Verification:

- `lake env lean GaloisForLFunctions/RHTower/XiMassPrimeSemigroupHighPassPointwiseNoGo.lean` — PASS.
- `lake build GaloisForLFunctions.RHTower.XiMassPrimeSemigroupHighPassPointwiseNoGo` — PASS
  (`[9391/9391]`).
- Axiom audit of the charge law, negative-frequency divergence, and no-majorant capstone contains
  only `propext`, `Classical.choice`, and `Quot.sound`.
