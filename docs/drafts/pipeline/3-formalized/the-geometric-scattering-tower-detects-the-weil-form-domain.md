# The geometric scattering tower detects the Weil form domain

- **ID:** the-geometric-scattering-tower-detects-the-weil-form-domain
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Obstacle:** B133: the intrinsic primitive-pair diagonal on the complete Weil form domain.
- **Statement:** The finite raw geometric scattering energies extend continuously to aperture L². They have a finite limit exactly on the complete Weil form domain, recover its literal diagonal there, and diverge to positive infinity elsewhere.

## Exact finite-height kernel

Write `ω(t)=exp(−t/2)/(1−exp(−2t))` for `t>0`. At every integer height `N≥0`,

`κ_N(t)=(1−exp(−Nt))ω(t)`
`=exp(−t/2)/(1+exp(−t)) Σ_{j<N} exp(−jt)`.

The second expression removes the singularity at zero and gives
`0≤κ_N(t)≤N exp(−t/2)` on the positive half-line. For `Re s>0`,

`∫₀∞ κ_N(t)exp(−(s−½)t)dt = (Γℝ′/Γℝ)(s+N)−(Γℝ′/Γℝ)(s)`.

For `f∈C²_c(ℝ,ℂ)` and `k=f⋆f̃`, the energy of the actual raw primitive-pair
scattering fields equals

`2 robinCounterterm(N+3/2) k(0)+H_k(0)+H_k(1)`
`−∫₀∞ κ_N(t)(k(t)+k(−t))dt`
`−Σ_n Λ(n)(1−n^(−N))/√n ·(k(log n)+k(−log n))`.

Both poles and the geometric Robin normalization are retained exactly.

## Complete physical domain

On aperture `a`, let `U_t` be logarithmic translation and let `P_N` be the
finite prime transport operator with coefficients `Λ(n)(1−n^(−N))`.
Set

`b_N=2 Re robinCounterterm(N+3/2)−2∫₀∞κ_N(t)dt`,

`E_N(f)=∫₀∞κ_N(t)‖U_t f−f‖²dt+b_N‖f‖²`
`+Re⟨P_polar f,f⟩−Re⟨P_N f,f⟩`.

Each `E_N` is continuous on physical aperture L². On every complex smooth
interior source, the full complex raw energy equals `ofReal(E_N(f))`.
For every aperture L² state `f`,

`(∃L∈ℝ, E_N(f)→L) ↔ f∈range(ccmArchimedeanFormToAperture a)`.

For `f=Ju`, the limit is `Re(ccmRestrictedWeilForm a u u)`. Outside this
range, `E_N(f)→+∞`.

## Proof [PROVED HERE]

Expand the factor `(1−exp(−2t))⁻¹` into finite geometric sums. Their
Laplace integrals are differences of reciprocal sums; subtraction of the
two Gauss digamma limits identifies the Gamma difference. The bound
`N exp(−Re(s)t)` justifies dominated convergence, including odd heights.
Tilted Fourier inversion and Fubini convert this difference to the literal
jump kernel. The Euler-series telescope supplies the exact prime weights;
the two contour poles supply the two polar moments.

On smooth sources, translation coefficients are autocorrelations, their
symmetric sum is `2‖f‖²−‖U_t f−f‖²`, and aperture support truncates the
prime series exactly. Translation adjoints and self-adjointness prove
reality before the tower limit. The integrable finite-height kernel gives
L² continuity by dominated convergence.

The kernels increase to `ω`; monotone convergence therefore identifies
their extended limit with `criticalGreenEnergy`, including infinity.
Its finite domain is the previously established complete Weil form range.
The mass coefficient tends to `2 gammaHardyPhaseRate 0` by the Gamma–Robin
estimate, and the finite prime operators converge in norm. Adding this
convergent bounded remainder gives both the literal Weil diagonal and
divergence outside its domain.

## Lean declarations

Namespace `GaloisForLFunctions.HyperbolicArakelovTheory.ScatteringTower`.

- `TheFiniteScatteringTowerHasAnExactArithmeticJumpKernel.lean`:
  `laplace_scatteringCutoffKernel`, `rawEnergy_eq_cutoff`.
- `TheGeometricScatteringTowerDetectsTheWeilFormDomain.lean`:
  `continuous_scatteringWeilEnergy`,
  `rawEnergy_smooth_eq_ofReal_scatteringWeilEnergy`,
  `tendsto_scatteringJumpEnergy_extended`,
  `tendsto_scatteringWeilEnergy_form`,
  `tendsto_scatteringWeilEnergy_atTop`,
  `finite_scatteringWeil_limit_iff_form_range`.

Validation: both production modules pass plain `lake --old env lean`;
the six principal declarations have only `[propext, Classical.choice, Quot.sound]`.

## Boundary

This closes the passage from the raw primitive-pair scattering diagonal
to its complete physical form domain. The construction retains its
arithmetic scattering data and separate polar channel. It does not assert
an invariant torus-glued Green realization or unshifted Weil positivity.
