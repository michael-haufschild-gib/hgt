# Mass-shifted factorial positive-carrier orientation no-go

- **ID:** `mass-shifted-factorial-positive-carrier-orientation-no-go`
- **Status:** Formalized in Lean 4
- **Route:** mass-shifted spectral face, §9.3 exact open core
- **Novelty:** `[NOVELTY UNVERIFIED]`

## Failed conjecture

### F1 — A positive heat/source carrier orients the first surviving factorial rung

Let `μ` be a strictly positive finite measure on `(0,∞)` and set

`s_k = (1/k!) ∫ t^k dμ(t)`.

Because every raw moment Gram of `μ` is positive, one might expect a singular Hankel face of the
factorially normalized sequence `s` to have positive Krein crossing. This would turn positivity of
the Xi heat carrier or a positive Euler--Gamma source Gram into the missing sign theorem.

**Falsified exactly.** Take

`μ₊ = (16/17) δ_(3/4) + (1/17) δ_5`,

`μ₋ = (4/5) δ_(1/2) + (1/5) δ_3`.

Every weight and node is strictly positive. Both normalized sequences satisfy

`s_0 = s_1 = s_2 = 1`.

Hence both have the same positive size-one head, the same singular size-two face, and the same null
polynomial `P=X-1`. Their third normalized moments are

`s_3⁺=31/24`, `s_3⁻=11/12`,

so their affine/Krein crossings are

`[P,XP]₊ = s_3⁺-s_2 = 7/24 > 0`,

`[P,XP]₋ = s_3⁻-s_2 = -1/12 < 0`.

Thus strict positivity of the pre-normalized carrier does not orient the factorially normalized
extension class, even at the smallest nontrivial singular face.

## Positive survivor

For the actual shifted Xi face, put

`F_r(t)=Σ_j c_j t^(r+j)/(r+j)!`.

The singular-face equations are exactly

`∫ F_i(t) exp(-yt) H_Xi(t) dt = 0`, `0≤i≤n`,

while the Krein crossing is

`[P_c,XP_c]_y = c_n⁻¹ ∫ F_(n+1)(t) exp(-yt) H_Xi(t) dt`.

Therefore the missing theorem is not positivity of a carrier. It is orientation of the first
surviving factorial-Volterra rung, conditional on annihilation of the whole visible flag and on
global completed Euler--Gamma incidence. This exact survivor is formalized by
`RHTower.xiShiftedHankelBoundary_kreinVolterraFlag`.

## Corpus audit

- `VonMangoldtGammaStrictHankelLaw` proves strict positivity for a different bivariate Hausdorff
  moment row; it is not the shifted-Xi factorial row.
- `VonMangoldtGammaFactorialNormalizationNoGo` already proves that literal factorial normalization
  can destroy positivity of the cofinal raw Euler source. The new two-carrier theorem strengthens
  this to opposite orientations on one identical singular face.
- `VonMangoldtSuccessorDiracKreinEdge` controls successor differences of additive logarithmic
  moments. No theorem identifies that exchange form with multiplication-by-`X` crossing in the
  negative-binomial shifted reciprocal-Xi sequence.
- `GammaJacobiArtanhTransportCoupling` reconstructs the logarithmic coordinate but explicitly
  leaves completed Euler cyclic reading and fibre orientation open.
- aperture-relative Krein modules concern an aperture derivative and require an RH-strength
  half-plane input for their positive direction; they do not orient this Volterra crossing.

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/FactorialPositiveCarrierOrientationNoGo.lean`
  - `HTGeometry.factorialPositiveCarrierOrientationNoGo`
  - exact positive nodes and weights, common face and kernel, crossings `7/24` and `-1/12`
- `formal/GaloisForLFunctions/RHTower/XiShiftedHankelBoundaryKreinCrossing.lean`
  - `RHTower.xiShiftedHankelBoundaryHeatKernel_eq_factorialVolterraHeatKernel`
  - `RHTower.xiShiftedHankelBoundaryNullCrossingForm_eq_inv_mul_nextVolterraIntegral`
  - `RHTower.xiShiftedHankelBoundary_kreinVolterraFlag`

All statements are unconditional and contain no new axioms. RH remains open: the positive survivor
requires a completed-source conditional variation/orientation theorem not present in the corpus.
