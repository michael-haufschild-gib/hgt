# FDNLS quasi-Riesz paper (arXiv:2407.12441) — CLOSED at stage 3

Zhong–Malomed–Yan, *Dynamics of discrete solitons in the fractional discrete NLS equation with the
quasi-Riesz derivative*.  Every analytical (non-numerical) statement of the paper is now an
unconditional Lean theorem.

Card: `docs/drafts/pipeline/3-formalized/fdnls-quasi-riesz-zhong-malomed-yan.md`
Code: `formal/GaloisForLFunctions/HTGeometry/FDNLS/` (13 modules, ~3550 lines, all wired into the
`GaloisForLFunctions.HTGeometry` umbrella).

## Module map

| module | paper equations |
|---|---|
| `CouplingCoefficient` | (10), (10') IBP form, closed forms at α = 1, 2 |
| `CouplingDecay` | uniform decay bound, absolute summability of `D_·^{(α)}` |
| `DispersionRelation` | (32)(33)(34)(35)(38)(39) — the exact `ω(k) = C|k|^α` |
| `Operator` | (9) Fourier multiplier, (11) and (14) written out |
| `Conservation` | (16)(17)(18) power and Hamiltonian conservation |
| `AntiContinuum` | (40)(41) |
| `Bogoliubov` | (28)(29)(30) |
| `ShortRangeComparison` | (23)(24) non-commutativity, (42)(43) PN barrier |
| `SineSeries` | (36)(37) |
| `Symmetries` | (21) staggering, (26)(27) scaling |
| `MellinSine` | `∫_0^∞ x^{α-1} sin x dx = Γ(α)sin(πα/2)` (mathlib gap) |
| `CouplingAsymptotics` | (12)(13) |
| `DipolarRealization` | (31) |

## Corpus assets that made it cheap — search for these before rebuilding

* `HTGeometry.ComplexScaledGammaIntegral.gammaScaledIntegral_eq` :
  `∫_0^∞ t^{a-1} e^{-ct} dt = Γ(a)/c^a` for **complex** `c` with `Re c > 0` (mathlib only has real
  `c`).  Import closure: 2 modules.  This is the single input that turns the Mellin sine transform
  from a contour-integration project into a regularisation argument.
* `RHTower.SawtoothFourierSeries.tendsto_sum_sawtoothSine` : `∑ sin(nθ)/n = (π-θ)/2` on `(0,2π)`.
  Import closure: 5 project modules.  Equation (37) is the half-period shift `θ ↦ θ + π` of it.
* `RHTower.FresnelIntegral` : the α = 1/2 case of the same Mellin transform, proved by the same
  ε-regularisation + uniform-tail template.  Read it before attempting any other conditionally
  convergent oscillatory integral.

## New reusable layers

* **Pointwise Fourier inversion for a non-`C¹` symbol.**  `CouplingDecay.abs_integral_sin_rpow`
  bounds `∫_0^π sin(ℓk)k^{α-1}dk` by `(2π+3)ℓ^{-min(α,1)}` by splitting at `k = 1/ℓ`: crude
  `|sin x| ≤ x` below, one integration by parts above (the singular endpoint has been excised).
  That gives absolute summability, which is exactly what `hasSum_fourier_series_of_summable`
  needs.  The corpus previously had this only for `C²` symbols
  (`RHTower.PeriodicFourierDecay`).
* **Discrete-NLS conservation.**  `Conservation.rePair`/`imPair` + `sum_sum_antisymm`: both
  conservation laws are antisymmetric double sums against a symmetric kernel.  Works for an
  arbitrary finite index type and an arbitrary real symmetric coupling; the FDNLS lattice is the
  instance `quasiRieszKernel`.
* **Exact Bogoliubov linearization.**  `Bogoliubov.hasDerivAt_stationaryResidual` states equation
  (30) as a genuine `HasDerivAt` in the perturbation amplitude, not a formal `O(δ)` truncation; the
  polarisation identity `2 Re⟨v,w⟩ v = |v|²w + v²w̄` (`two_rePair_mul`) is what makes `|v|²v`
  differentiable in the real direction.

## Traps hit

* `Real.hasDerivAt_rpow_const` needs `x ≠ 0`, so any integration by parts against `k^{α-1}` on
  `[0, π]` must either excise the origin (split at `1/ℓ`) or use
  `intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`, which only asks for the derivative on
  the *open* interval.
* `HasDerivAt.mul`, `.pow`, `.sum`, `.neg` all return Pi-typed functions
  (`f * g`, `f ^ n`, `∑ i, A i`).  `simp only [Pi.mul_def]` / `Pi.pow_apply` / a `funext` rewrite is
  needed before the statement matches; and `simpa` frequently fails on the instance path where
  plain `exact` succeeds (`Complex.reCLM.hasFDerivAt.comp_hasDerivAt`).
* `MeasureTheory.integral_union` is now `setIntegral_union`; `Finset.erase_eq_of_not_mem` is
  `erase_eq_of_notMem`; `intervalIntegral.integral_finset_sum` is deprecated in favour of
  `integral_finsetSum`.
