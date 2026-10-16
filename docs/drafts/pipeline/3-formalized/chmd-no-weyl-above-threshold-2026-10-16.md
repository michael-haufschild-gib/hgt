# CHMD: no Weyl sequences of the arithmetic resolvent above the threshold 1/2

- **ID:** chmd-no-weyl-above-threshold-2026-10-16
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** CHMD route; continuation of chmd-far-field-energy-localization-2026-10-16 (confinement above `1/2`) and chmd-pointwise-generator-threshold-weyl-2026-10-16 (`1/2 ∈ σ_ess(R)`); closes the item "local compactness ⇒ σ_ess(R) ⊆ [0,1/2]" that the operator-core cards listed as the next hard obstacle
- **Statement:** For `μ > 1/2` there is no weakly null sequence of unit vectors `e_n` in `L²(Θcosh(x/2)dx)` with `‖Re_n − μe_n‖ → 0` (`R` the bounded arithmetic resolvent). Every Weyl value of `R` is `≤ 1/2`; eigenvalues above `1/2` carry no infinite orthonormal eigenfamily. Ingredients proved on the way: logarithmic growth of the archimedean Lévy symbol, Lévy–Khintchine + Plancherel tail bound for compact `C²` functions, and the localization `Q(χ_R v) ≤ C_R(J_arch(v) + ‖v‖²_μ)` of the Doob energy.
- **Status:** STATUS MUST-1547, MUST-1548. Four leaves (`CHMDLevySymbolLowerBound`, `CHMDWindowFourierTail`, `CHMDWindowLocalization`, `CHMDNoWeylAboveThreshold`; 70 declarations), all axioms propext/Classical.choice/Quot.sound; plain `lake env lean` audits clean; `lake build --old` green for each; wired once each into `GaloisForLFunctions/RHTower.lean`; index refreshed; global lint clean of proof debt.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below = the Lean development)
- [x] 2 → 3  formalized: `levySymbol_ge_log`, `fourier_tail_le`, `exists_window_levyForm_bound`, `no_weakly_null_weyl_above_half`, `weyl_value_le_half`, `no_orthonormal_eigenfamily_above_half`
- [ ] 3 → 4  publication-ready

## Obstacle addressed
In the CHMD dictionary RH ⟺ `R ≤ 1/2` on even primitives. The previous cards established that
`1/2` is essential spectrum (cusp escape) and that approximate eigenvectors above `1/2` are confined
to a window. What was missing was compactness: that confined approximate eigenvectors cannot be
weakly null, i.e. that the spectrum above `1/2` is discrete in the Weyl sense. The other CHMD cards
tried to reach this through an operator core of the singular archimedean generator (half-density
`aAa + V`), which is still open. This card bypasses the core entirely: the arithmetic Doob form on
a window controls the flat archimedean Lévy form, whose symbol grows logarithmically (digamma), so
graph-bounded families have uniform Fourier tails; weak nullness kills the low frequencies by
dominated convergence; Plancherel closes.

## Paper proof
*Symbol.* `γ(r) = Re ψ(1/4 + ir/2) − log π` (corpus), `γ(r) − γ(0) = 2∫_0^∞ ω(x)(1 − cos rx)dx ≥ 0`
(corpus Lévy–Khintchine form). For `z = 1/4 + ir/2`, `|r| ≥ 4`: `‖z‖ ≥ |r|/2 ≥ 2`, so
`Re ψ(z) ≥ log‖z‖ − 3/‖z‖ ≥ log(|r|/2) − 3/2` (corpus `norm_digamma_sub_log_le_of_re_pos`).
Hence `γ(r) − γ(0) ≥ log(|r|/2) − c₀`.

*Tail.* For compactly supported `C²` real `g`: `|ĝ(r)|² ≤ N²/(1+|r|)⁴` and `|γ(r)| ≤ A + log(2+|r|)`
(corpus), so the Fourier side of the corpus identity
`(1/2π)∫|ĝ|²γ = γ(0)∫g² + Q(g)` is integrable; with Plancherel `∫|ĝ|² = 2π∫g²` (corpus) this gives
`(1/2π)∫|ĝ|²(γ − γ(0)) = Q(g)`. Since `γ − γ(0) ≥ 0` everywhere and `≥ log(T/2) − c₀` on `|r| ≥ T`,
`(log(T/2) − c₀)∫_{|r|≥T}|ĝ|² ≤ 2πQ(g)`.

*Localization.* `χ_R` = smooth bump (`ContDiffBump`) with `rIn = R+1`, `rOut = R+2`; `m = min_{|y|≤R+3}Θ`,
`m' = min_{|y|≤R+3}(Θcosh)`, `L` a Lipschitz constant of `χ_R`. For a compact `C²` test `v` and
`g = χ_R v`: `(g(u) − g(u+t))² = (χ(u)(v(u) − v(u+t)) + (χ(u) − χ(u+t))v(u+t))² ≤ 2χ(u)²(Δ_t v)² + 2L²t²v(u+t)²`
on the relevant set; for `t ≤ 1`, `χ(u) ≠ 0` forces `|u|,|u+t| ≤ R+3` so `χ(u)²(Δ_t v)² ≤ Θ(u)Θ(u+t)(Δ_t v)²/m²`,
and the commutator term is supported in `|u+t| ≤ R+3`; for `t > 1`, `(g − τ_t g)² ≤ 2g² + 2(τ_t g)²`
and `∫g² ≤ ∫_{|y|≤R+3}v² ≤ ‖v‖²_μ/m'`. Hence `ω(t)∫(g − τ_t g)² ≤ ω(t)[2J_t(v)/m² + t²(2L²+4)‖v‖²_μ/m']`
for all `t > 0`, and integrating, `Q(χ_R v) ≤ (2/m²)J_arch(v) + (∫_0^∞ω t²)(2L²+4)‖v‖²_μ/m'`.

*Main theorem.* Let `e_n` be weakly null unit vectors with `‖Re_n − μe_n‖ → 0`, `μ > 1/2`. By
confinement (`exists_window_mass_resolvent`) there are `R, θ, η` with `‖1_R Re_n‖² ≥ θ` once
`‖Re_n − μe_n‖ ≤ η`. Choose compact tests `p_n = compactLift v_n` with `‖p_n − Riesz(e_n)‖ < 1/(n+1)`
(density of compact tests). Since `‖Riesz(w)‖² = ⟪w, Rw⟫ ≤ 1`, `‖p_n‖ ≤ 2`, so
`J_arch(v_n) + ‖v_n‖²_μ ≤ ‖p_n‖² ≤ 4` (edge energy = arch + prime jump energies, both `≥ 0`).
Thus `Q(g_n) ≤ 4C_R` for `g_n = χ_R v_n`, and `∫_{|r|≥T}|ĝ_n|² ≤ 8πC_R/(log(T/2) − c₀)` uniformly.
Weak nullness: `Re ĝ_n(r) = ∫ g_n cos(ru) = ⟪p_n.fst, k_r⟫_μ` with `k_r = χ_R cos(r·)/(Θcosh) ∈ L²(μ)`,
and `⟪p_n.fst, k⟫ = ⟪Re_n, k⟫ + O(‖p_n − Riesz e_n‖) = ⟪e_n, Rk⟫ + O(1/n) → 0` (`R` symmetric); same
for the imaginary part. Uniform bound `|ĝ_n(r)| ≤ ∫|g_n| ≤ (R+2) + 2/m'` (`|g| ≤ (1+g²)/2` on the window).
Dominated convergence on `|r| < T` gives `∫_{|r|<T}|ĝ_n|² → 0`; Plancherel gives
`∫g_n² = (1/2π)(∫_{|r|≥T} + ∫_{|r|<T})|ĝ_n|² ≤ 4C_R/(log(T/2) − c₀) + o(1)`, so `∫g_n² → 0`.
But on `|x| ≤ R`, `g_n = v_n` and `Θcosh ≤ M`, so `θ/4 ≤ (√θ − 1/(n+1))² ≤ ‖1_R p_n.fst‖²_μ ≤ M∫g_n²`
for large `n`: contradiction.

*Corollaries.* Orthonormal sequences are weakly null (Bessel), so an eigenvalue `μ > 1/2` has no
infinite orthonormal eigenfamily; every Weyl value is `≤ 1/2`.

## Lean modules (namespace `RHTower.CHMDPolar`)
1. `RHTower/CHMDLevySymbolLowerBound.lean` — `levySymbol`, `levySymbol_eq_integral`, `levySymbol_nonneg`,
   `gammaBracket_ge_log`, `levyConst`, `levySymbol_ge_log`, `levySymbol_ge_log_of_le`, `tendsto_log_half_sub_atTop`.
2. `RHTower/CHMDWindowFourierTail.lean` — `levyForm`, `fourierSq`, `continuous_fourierSq`, `exists_fourierSq_le`,
   `integrable_one_add_abs_pow_three`, `integrable_fourierSq_mul_gammaBracket`, `integrable_fourierSq`,
   `integrable_fourierSq_mul_levySymbol`, `exists_support_radius`, `tsupport_ofReal_subset`, `integral_fourierSq_eq`,
   `levyForm_eq_fourier`, `levyForm_nonneg`, `highFreq`, `measurableSet_highFreq`, `fourier_tail_le`.
3. `RHTower/CHMDWindowLocalization.lean` — `windowBump` (+ algebra), `windowTest`, `exists_theta_window_lower`,
   `exists_mass_window_lower`, `hasCompactSupport_sq`, `integrable_sq_of_compact`, `flatWindowMass`, `flatWindowMass_le`,
   `windowSq` (+ lemmas), `windowTest_sq_le_windowSq`, `sq_add_le_two`, `exists_window_levyForm_bound`.
4. `RHTower/CHMDNoWeylAboveThreshold.lean` — `WeaklyNull`, `weaklyNull_of_orthonormal`, `norm_sub_fst_le`,
   `tendsto_inner_source_zero`, `massVecFun`, `massVec`, `inner_compactLift_massVec`, `paperFT_ofReal_re_im`,
   `norm_paperFT_ofReal_le`, `abs_le_half_add_sq`, `integral_abs_windowTest_le`, `fourierSq_windowTest_le`,
   `tendsto_fourierSq_windowTest`, `no_weakly_null_weyl_above_half`, `weyl_value_le_half`,
   `no_orthonormal_eigenfamily_above_half`.

## Big picture
- Combined with the cusp-escape sharpness (MUST-1546): the Weyl spectrum of the arithmetic resolvent
  is exactly contained in `[0, 1/2]` with `1/2` attained. All spectrum of `R` above `1/2`, i.e. the
  CHMD image of off-line Xi zeros, is Weyl-discrete: it can only consist of eigenvalues without
  infinite orthonormal eigenfamilies.
- The mechanism is purely arithmetic-analytic: harmonic identity + Chebyshev shells (confinement) and
  digamma asymptotics (log Sobolev control). No operator core, no Fourier analysis of the Doob
  weights, no positivity assumption.
- What remains to turn this into a counting statement: isolation and finite multiplicity of the
  eigenvalues above `1/2` (standard from the no-Weyl-sequence property plus selfadjointness; needs
  the approximate-eigenvector characterization of the real spectrum in Lean), and the identification
  of these eigenvalues with the nonreal Xi orbits (Birman–Schwinger).

## Next conjectures
1. `spectrum ℝ R ∩ (1/2 + ε, 1]` is finite for every `ε > 0` (from `no_weakly_null_weyl_above_half`
   via a Weyl-sequence construction from the spectral theorem / approximate point spectrum).
2. Eigenvalues of `R` above `1/2` ↔ nonreal zeros of `Xi` (Birman–Schwinger / the signed divisor pairing).
3. The even-sector restriction: the same statements on even primitives, where RH ⟺ no spectrum above `1/2`.
