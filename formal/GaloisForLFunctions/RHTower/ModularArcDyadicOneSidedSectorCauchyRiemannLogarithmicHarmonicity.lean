import GaloisForLFunctions.RHTower.ModularArcDyadicLogarithmicSubharmonicityWronskianJacobian

/-!
# One-Sided Origin and Infinity Sector Cauchy–Riemann Equations, Five-Point Harmonicity, Liouville–Gauss Logarithmic Harmonicity of One-Sided Sector Moduli, and Brahmagupta–Fibonacci Sector Norm Calculus

This module advances the `ModularArcDyadic*` producer series (Cycle 55) from the full-strip
Liouville–Gauss logarithmic harmonicity of `|F_k(l, τ)|²` and `|Δ_k(l, τ)|²` and the Jacobian
determinant of `(H_k, W_k)` in `ModularArcDyadicLogarithmicSubharmonicityWronskianJacobian` to the
complete holomorphic, harmonic, and logarithmic-subharmonic calculus of the **one-sided infinity and
origin sector Mellin transforms**:
`F_k^+(l, τ) = (C_k^+(l, τ), S_k^+(l, τ)) =
  (∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx, ∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx)`
and
`F_k^-(l, τ) = (C_k^-(l, τ), S_k^-(l, τ)) =
  (∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx, ∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx)`.

## Main Results

1. **Section 1: Universal Half-Sum / Half-Difference Linear-Combination Calculus for First-Order
   Difference Quotients, Five-Point Laplacians, and Brahmagupta–Fibonacci Sector Norm Identities**
   - `tendsto_div_sector_pos_nhdsWithin_zero` / `tendsto_div_sector_neg_nhdsWithin_zero`:
     Universal punctured-neighborhood (`nhdsWithin 0 {0}ᶜ`) difference-quotient limit theorems
     recovering `(c_pos(h) − c_pos₀) / h → (u' + x') / 2` and
     `(c_neg(h) − c_neg₀) / h → (u' − x') / 2` from the sum `u = c_pos + c_neg` and difference
     `c_pos − c_neg`.
   - `tendsto_div_sq_fivePoint_sector_pos_harmonic_nhdsWithin_zero` /
     `tendsto_div_sq_fivePoint_sector_neg_harmonic_nhdsWithin_zero`:
     Universal punctured-neighborhood five-point Laplacian vanishing theorems for the half-sum
     `c_pos` and half-difference `c_neg`.
   - `sector_inner_polarization_identity`, `sector_brahmagupta_fibonacci_identity`,
     `derivative_sector_parallelogram_identity`:
     Universal polynomial identities relating the full-to-imbalance and origin-to-infinity pairings.

2. **Section 2: Full-Strip Partial Derivatives, Global Cauchy–Riemann Equations, and Five-Point
   Harmonicity of the One-Sided Sector Components `C_k^±(l, τ)` and `S_k^±(l, τ)`**
   - `tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero`,
     `tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero`:
     Exact horizontal and vertical partial derivatives of the infinity-sector Mellin components
     `C_k^+(l, τ)` and `S_k^+(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ`.
   - `tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero`,
     `tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero`:
     Exact horizontal and vertical partial derivatives of the origin-sector Mellin components
     `C_k^-(l, τ)` and `S_k^-(l, τ)` across `|l| < 1/8`, `τ ∈ ℝ`.
   - `tendsto_div_sector_Ioi_one_cauchyRiemann_first_nhds_zero`,
     `tendsto_div_sector_Ioi_one_cauchyRiemann_second_nhds_zero`,
     `tendsto_div_sector_Ioc_zero_one_cauchyRiemann_first_nhds_zero`,
     `tendsto_div_sector_Ioc_zero_one_cauchyRiemann_second_nhds_zero`:
     Global Cauchy–Riemann equations `∂_l C_k^± = ∂_τ S_k^±` and `∂_l S_k^± = −∂_τ C_k^±` across
     `|l| < 1/8`, `τ ∈ ℝ`.
   - `tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero`,
     `tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero`,
     `tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero`,
     `tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero`:
     Global five-point harmonicity for all four one-sided sector components across `|l| < 1/8`, `τ ∈ ℝ`.

3. **Section 3: Partial Derivatives, Critical-Line Anti-Symmetry, and Division-Free Liouville–Gauss
   Logarithmic Harmonicity of One-Sided Sector Moduli Squared `|F_k^+(l, τ)|²` and `|F_k^-(l, τ)|²`**
   - `tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorModulusSq_Ioi_one_vert_shift_nhds_zero`,
     `tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_nhds_zero`,
     `tendsto_div_sectorModulusSq_Ioc_zero_one_vert_shift_nhds_zero`:
     Full-strip horizontal and vertical partial derivatives of `|F_k^+(l, τ)|²` and `|F_k^-(l, τ)|²`
     across `|l| < 1/8`, `τ ∈ ℝ`.
   - `tendsto_sectorModulusSq_Ioi_one_liouville_gauss_nhds_zero`,
     `tendsto_sectorModulusSq_Ioc_zero_one_liouville_gauss_nhds_zero`:
     Unconditional division-free Liouville–Gauss logarithmic harmonicity
     `|F_k^±(l, τ)|² · Δ(|F_k^±(l, τ)|²) − ((∂_l |F_k^±(l, τ)|²)² + (∂_τ |F_k^±(l, τ)|²)²) → 0`
     across `|l| < 1/8`, `τ ∈ ℝ`.
   - `tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_nhds_zero`,
     `tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_at_criticalLine_nhds_zero`,
     `tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_zero`:
     Critical-line (`l = 0`) opposite-sign transverse derivatives
     `∂_l |F_k^+(0, τ)|² = −∂_l |F_k^-(0, τ)|² = (1/2) ∂_l H_k(0, τ)` and critical-line zero-locus
     specialization `∂_l |F_k^+(0, τ₀)|² = −(1/2) ∂_τ W_k(0, τ₀)`.

4. **Section 4: Brahmagupta–Fibonacci Sector Norm Identities, Subharmonicity and Liouville–Gauss
   Logarithmic Harmonicity of `H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² |Δ_k(l, τ)|²`, and Master
   Witness Theorem**
   - `hermitianPairing_sq_add_sectorWronskian_sq_eq`:
     `H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² · |Δ_k(l, τ)|²` across `|l| < 1/2`, `τ ∈ ℝ`.
   - `complexModulusSq_sub_imbalanceModulusSq_sq_add_four_mul_sectorWronskian_sq_eq`:
     `(|F_k(l, τ)|² − |Δ_k(l, τ)|²)² + 4 W_k(l, τ)² = 16 |F_k^+(l, τ)|² · |F_k^-(l, τ)|²`
     across `|l| < 1/2`, `τ ∈ ℝ`.
   - `tendsto_div_sq_hermitianWronskianNormSq_fivePoint_laplacian_nhds_zero` and
     `tendsto_hermitianWronskianNormSq_liouville_gauss_nhds_zero`:
     Global five-point subharmonicity and division-free Liouville–Gauss logarithmic harmonicity of
     `H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² |Δ_k(l, τ)|²` across `|l| < 1/8`, `τ ∈ ℝ`.
   - `exists_dyadic_oneSidedSector_cauchyRiemann_logarithmicHarmonicity_arcWitness`:
     Master unconditional existential witness theorem bundling the entire one-sided sector
     Cauchy–Riemann, harmonic, Liouville–Gauss, and Brahmagupta–Fibonacci package.
-/

open scoped Real Topology
open MeasureTheory Set Filter

namespace RHTower

noncomputable section

/-! ## Section 1: Universal Half-Sum / Half-Difference Linear-Combination Calculus for First-Order Difference Quotients, Five-Point Laplacians, and Brahmagupta–Fibonacci Sector Norm Identities -/

/-- **Universal punctured-neighborhood half-sum difference-quotient limit theorem:**
If `u h = c_pos h + c_neg h` on `Ioo (-1/8) (1/8)`, `u₀ = c_pos₀ + c_neg₀`,
`(u h − u₀) / h → u'`, and `((c_pos h − c_neg h) − (c_pos₀ − c_neg₀)) / h → x'` as
`h → 0` (`h ≠ 0`), then `(c_pos h − c_pos₀) / h → (u' + x') / 2`. -/
theorem tendsto_div_sector_pos_nhdsWithin_zero
    {u c_pos c_neg : ℝ → ℝ} {u₀ c_pos₀ c_neg₀ u' x' : ℝ}
    (hu_eq : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u h = c_pos h + c_neg h)
    (hu₀ : u₀ = c_pos₀ + c_neg₀)
    (hu : Tendsto (fun h : ℝ => (u h - u₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds u'))
    (hx : Tendsto (fun h : ℝ => ((c_pos h - c_neg h) - (c_pos₀ - c_neg₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds x')) :
    Tendsto (fun h : ℝ => (c_pos h - c_pos₀) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((u' + x') / 2)) := by
  have hcomb := (hu.add hx).div_const (2 : ℝ)
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh
  rw [hu_eq h hh, hu₀]
  ring

/-- **Universal punctured-neighborhood half-difference difference-quotient limit theorem:**
If `u h = c_pos h + c_neg h` on `Ioo (-1/8) (1/8)`, `u₀ = c_pos₀ + c_neg₀`,
`(u h − u₀) / h → u'`, and `((c_pos h − c_neg h) − (c_pos₀ − c_neg₀)) / h → x'` as
`h → 0` (`h ≠ 0`), then `(c_neg h − c_neg₀) / h → (u' − x') / 2`. -/
theorem tendsto_div_sector_neg_nhdsWithin_zero
    {u c_pos c_neg : ℝ → ℝ} {u₀ c_pos₀ c_neg₀ u' x' : ℝ}
    (hu_eq : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u h = c_pos h + c_neg h)
    (hu₀ : u₀ = c_pos₀ + c_neg₀)
    (hu : Tendsto (fun h : ℝ => (u h - u₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds u'))
    (hx : Tendsto (fun h : ℝ => ((c_pos h - c_neg h) - (c_pos₀ - c_neg₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds x')) :
    Tendsto (fun h : ℝ => (c_neg h - c_neg₀) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds ((u' - x') / 2)) := by
  have hcomb := (hu.sub hx).div_const (2 : ℝ)
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh
  rw [hu_eq h hh, hu₀]
  ring

/-- **Universal punctured-neighborhood Cauchy–Riemann first equation `∂_l c = ∂_τ s`:**
If `(c₁ h − c₀) / h → u'` and `(s₂ h − s₀) / h → u'` as `h → 0` (`h ≠ 0`), then
`((c₁ h − c₀) − (s₂ h − s₀)) / h → 0`. -/
theorem tendsto_div_cauchyRiemann_first_of_eq_nhdsWithin_zero
    {c₁ s₂ : ℝ → ℝ} {c₀ s₀ u' : ℝ}
    (hc : Tendsto (fun h : ℝ => (c₁ h - c₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds u'))
    (hs : Tendsto (fun h : ℝ => (s₂ h - s₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds u')) :
    Tendsto (fun h : ℝ => ((c₁ h - c₀) - (s₂ h - s₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hsub := hc.sub hs
  rw [sub_self] at hsub
  exact hsub.congr (fun h => by ring)

/-- **Universal punctured-neighborhood Cauchy–Riemann second equation `∂_l s + ∂_τ c = 0`:**
If `(s₁ h − s₀) / h → v'` and `(c₂ h − c₀) / h → -v'` as `h → 0` (`h ≠ 0`), then
`((s₁ h − s₀) + (c₂ h − c₀)) / h → 0`. -/
theorem tendsto_div_cauchyRiemann_second_of_eq_nhdsWithin_zero
    {s₁ c₂ : ℝ → ℝ} {s₀ c₀ v' : ℝ}
    (hs : Tendsto (fun h : ℝ => (s₁ h - s₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds v'))
    (hc : Tendsto (fun h : ℝ => (c₂ h - c₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (-v'))) :
    Tendsto (fun h : ℝ => ((s₁ h - s₀) + (c₂ h - c₀)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hadd := hs.add hc
  rw [add_neg_cancel] at hadd
  exact hadd.congr (fun h => by ring)

/-- **Universal punctured-neighborhood five-point harmonicity for the half-sum `c_pos`:**
If `u_i h = c_pos_i h + c_neg_i h` (`i = 1, 2, 3, 4`) on `Ioo (-1/8) (1/8)`, `u₀ = c_pos₀ + c_neg₀`,
and the five-point Laplacians of `u` and `c_pos − c_neg` both converge to `0` as `h → 0` (`h ≠ 0`),
then the five-point Laplacian of `c_pos` converges to `0`. -/
theorem tendsto_div_sq_fivePoint_sector_pos_harmonic_nhdsWithin_zero
    {u₁ u₂ u₃ u₄ c_pos₁ c_pos₂ c_pos₃ c_pos₄ c_neg₁ c_neg₂ c_neg₃ c_neg₄ : ℝ → ℝ}
    {u₀ c_pos₀ c_neg₀ : ℝ}
    (hu₁ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₁ h = c_pos₁ h + c_neg₁ h)
    (hu₂ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₂ h = c_pos₂ h + c_neg₂ h)
    (hu₃ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₃ h = c_pos₃ h + c_neg₃ h)
    (hu₄ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₄ h = c_pos₄ h + c_neg₄ h)
    (hu₀ : u₀ = c_pos₀ + c_neg₀)
    (hu : Tendsto
      (fun h : ℝ => (((u₁ h + u₂ h - 2 * u₀) + (u₃ h + u₄ h - 2 * u₀)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hx : Tendsto
      (fun h : ℝ =>
        ((((c_pos₁ h - c_neg₁ h) + (c_pos₂ h - c_neg₂ h) - 2 * (c_pos₀ - c_neg₀)) +
          ((c_pos₃ h - c_neg₃ h) + (c_pos₄ h - c_neg₄ h) - 2 * (c_pos₀ - c_neg₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        (((c_pos₁ h + c_pos₂ h - 2 * c_pos₀) + (c_pos₃ h + c_pos₄ h - 2 * c_pos₀)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hcomb := (hu.add hx).div_const (2 : ℝ)
  have hlim : ((0 : ℝ) + 0) / 2 = 0 := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh
  rw [hu₁ h hh, hu₂ h hh, hu₃ h hh, hu₄ h hh, hu₀]
  ring

/-- **Universal punctured-neighborhood five-point harmonicity for the half-difference `c_neg`:**
If `u_i h = c_pos_i h + c_neg_i h` (`i = 1, 2, 3, 4`) on `Ioo (-1/8) (1/8)`, `u₀ = c_pos₀ + c_neg₀`,
and the five-point Laplacians of `u` and `c_pos − c_neg` both converge to `0` as `h → 0` (`h ≠ 0`),
then the five-point Laplacian of `c_neg` converges to `0`. -/
theorem tendsto_div_sq_fivePoint_sector_neg_harmonic_nhdsWithin_zero
    {u₁ u₂ u₃ u₄ c_pos₁ c_pos₂ c_pos₃ c_pos₄ c_neg₁ c_neg₂ c_neg₃ c_neg₄ : ℝ → ℝ}
    {u₀ c_pos₀ c_neg₀ : ℝ}
    (hu₁ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₁ h = c_pos₁ h + c_neg₁ h)
    (hu₂ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₂ h = c_pos₂ h + c_neg₂ h)
    (hu₃ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₃ h = c_pos₃ h + c_neg₃ h)
    (hu₄ : ∀ h ∈ Ioo (-(1 / 8 : ℝ)) (1 / 8), u₄ h = c_pos₄ h + c_neg₄ h)
    (hu₀ : u₀ = c_pos₀ + c_neg₀)
    (hu : Tendsto
      (fun h : ℝ => (((u₁ h + u₂ h - 2 * u₀) + (u₃ h + u₄ h - 2 * u₀)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0))
    (hx : Tendsto
      (fun h : ℝ =>
        ((((c_pos₁ h - c_neg₁ h) + (c_pos₂ h - c_neg₂ h) - 2 * (c_pos₀ - c_neg₀)) +
          ((c_pos₃ h - c_neg₃ h) + (c_pos₄ h - c_neg₄ h) - 2 * (c_pos₀ - c_neg₀))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) :
    Tendsto
      (fun h : ℝ =>
        (((c_neg₁ h + c_neg₂ h - 2 * c_neg₀) + (c_neg₃ h + c_neg₄ h - 2 * c_neg₀)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hcomb := (hu.sub hx).div_const (2 : ℝ)
  have hlim : ((0 : ℝ) - 0) / 2 = 0 := by ring
  rw [hlim] at hcomb
  refine hcomb.congr' ?_
  have hmem : Ioo (-(1 / 8 : ℝ)) (1 / 8 : ℝ) ∈ nhdsWithin (0 : ℝ) {(0 : ℝ)}ᶜ :=
    mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds (by norm_num) (by norm_num))
  filter_upwards [hmem] with h hh
  rw [hu₁ h hh, hu₂ h hh, hu₃ h hh, hu₄ h hh, hu₀]
  ring

/-- **Universal sector inner-product polarization identity:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`((c_pos + c_neg)² + (s_pos + s_neg)²) − ((c_pos − c_neg)² + (s_pos − s_neg)²) =
  4 * (c_pos * c_neg + s_pos * s_neg)`. -/
theorem sector_inner_polarization_identity (c_pos s_pos c_neg s_neg : ℝ) :
    ((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) -
      ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2) =
    4 * (c_pos * c_neg + s_pos * s_neg) := by
  ring

/-- **Universal Brahmagupta–Fibonacci identity for the origin-to-infinity sector product:**
For all `c_pos, s_pos, c_neg, s_neg : ℝ`,
`(((c_pos + c_neg)² + (s_pos + s_neg)²) − ((c_pos − c_neg)² + (s_pos − s_neg)²))² +
  4 * ((c_pos + c_neg) * (s_pos − s_neg) − (s_pos + s_neg) * (c_pos − c_neg))² =
  16 * (c_pos² + s_pos²) * (c_neg² + s_neg²)`. -/
theorem origin_infinity_sector_brahmagupta_fibonacci_identity (c_pos s_pos c_neg s_neg : ℝ) :
    (((c_pos + c_neg) ^ 2 + (s_pos + s_neg) ^ 2) -
        ((c_pos - c_neg) ^ 2 + (s_pos - s_neg) ^ 2)) ^ 2 +
      4 * ((c_pos + c_neg) * (s_pos - s_neg) - (s_pos + s_neg) * (c_pos - c_neg)) ^ 2 =
    16 * (c_pos ^ 2 + s_pos ^ 2) * (c_neg ^ 2 + s_neg ^ 2) := by
  ring

/-- **Universal derivative sector parallelogram law:**
For all `u', v', x', y' : ℝ`,
`2 * (((u' + x') / 2)² + ((v' + y') / 2)² + ((u' − x') / 2)² + ((v' − y') / 2)²) =
  (u'² + v'²) + (x'² + y'²)`. -/
theorem derivative_sector_parallelogram_identity (u' v' x' y' : ℝ) :
    2 * (((u' + x') / 2) ^ 2 + ((v' + y') / 2) ^ 2 +
         ((u' - x') / 2) ^ 2 + ((v' - y') / 2) ^ 2) =
      (u' ^ 2 + v' ^ 2) + (x' ^ 2 + y' ^ 2) := by
  ring

/-- **Universal 2D five-point bilinear product Laplacian limit theorem for general functions:**
If `(U_l h − U₀) / h → D_Ul`, `(U_t h − U₀) / h → D_Ut`,
`(V_l h − V₀) / h → D_Vl`, `(V_t h − V₀) / h → D_Vt`, and the five-point Laplacians satisfy
`((U_l h + U_l (−h) − 2 U₀) + (U_t h + U_t (−h) − 2 U₀)) / h² → L_U` and
`((V_l h + V_l (−h) − 2 V₀) + (V_t h + V_t (−h) − 2 V₀)) / h² → L_V` as `h → 0` (`h ≠ 0`), then
`((U_l h * V_l h + U_l (−h) * V_l (−h) − 2 * U₀ * V₀) +
  (U_t h * V_t h + U_t (−h) * V_t (−h) − 2 * U₀ * V₀)) / h² →
  U₀ * L_V + V₀ * L_U + 2 * (D_Ul * D_Vl + D_Ut * D_Vt)`. -/
theorem tendsto_div_sq_fivePoint_mul_general_nhdsWithin_zero
    {U_l U_t V_l V_t : ℝ → ℝ} {U₀ V₀ D_Ul D_Ut D_Vl D_Vt L_U L_V : ℝ}
    (hUl : Tendsto (fun h : ℝ => (U_l h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul))
    (hUt : Tendsto (fun h : ℝ => (U_t h - U₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ut))
    (hVl : Tendsto (fun h : ℝ => (V_l h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl))
    (hVt : Tendsto (fun h : ℝ => (V_t h - V₀) / h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vt))
    (hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_U))
    (hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds L_V)) :
    Tendsto
      (fun h : ℝ =>
        ((U_l h * V_l h + U_l (-h) * V_l (-h) - 2 * U₀ * V₀) +
          (U_t h * V_t h + U_t (-h) * V_t (-h) - 2 * U₀ * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds (U₀ * L_V + V₀ * L_U + 2 * (D_Ul * D_Vl + D_Ut * D_Vt))) := by
  have hneg : Tendsto (fun h : ℝ => -h) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhdsWithin 0 {(0 : ℝ)}ᶜ) :=
    tendsto_neg_nhdsWithin_zero
  have hUlm : Tendsto (fun h : ℝ => (U_l (-h) - U₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ul) :=
    hUl.comp hneg
  have hUtm : Tendsto (fun h : ℝ => (U_t (-h) - U₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Ut) :=
    hUt.comp hneg
  have hVlm : Tendsto (fun h : ℝ => (V_l (-h) - V₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vl) :=
    hVl.comp hneg
  have hVtm : Tendsto (fun h : ℝ => (V_t (-h) - V₀) / (-h)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds D_Vt) :=
    hVt.comp hneg
  have hcomb :=
    (((hVlap.const_mul U₀).add (hUlap.const_mul V₀)).add
      ((hUl.mul hVl).add (hUlm.mul hVlm))).add
      ((hUt.mul hVt).add (hUtm.mul hVtm))
  have hlim :
      U₀ * L_V + V₀ * L_U + (D_Ul * D_Vl + D_Ul * D_Vl) + (D_Ut * D_Vt + D_Ut * D_Vt) =
        U₀ * L_V + V₀ * L_U + 2 * (D_Ul * D_Vl + D_Ut * D_Vt) := by
    ring
  rw [hlim] at hcomb
  exact hcomb.congr (fun h =>
    (fivePoint_mul_div_sq_eq
      (U_l h) (U_l (-h)) (U_t h) (U_t (-h)) U₀
      (V_l h) (V_l (-h)) (V_t h) (V_t (-h)) V₀ h).symm)


/-! ## Section 2: Full-Strip Partial Derivatives, Global Cauchy–Riemann Equations, and Five-Point Harmonicity of the One-Sided Sector Components `C_k^±(l, τ)` and `S_k^±(l, τ)` -/

/-- **Horizontal Partial Derivative of the Infinity-Sector Cosine Mellin Component
`C_k^+(l, τ) = ∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(C_k^+(l + h, τ) − C_k^+(l, τ)) / h →
  ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv) + (∫_{v > 0} 2v cosh(lv) cos(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_pos_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Infinity-Sector Cosine Mellin Component
`C_k^+(l, τ) = ∫_{x > 1} x^{l − 1/2} cos(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(C_k^+(l, τ + h) − C_k^+(l, τ)) / h →
  −(((∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv) + (∫_{v > 0} 2v sinh(lv) sin(τv) Φ_k(v) dv)) / 2)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) := by
  have hl_half : |l| < 1 / 2 := by linarith
  have h := tendsto_div_sector_pos_nhdsWithin_zero
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ + h))
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
  have hlim :
      ((-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) / 2 =
      -(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) := by
    ring
  rw [hlim] at h
  exact h

/-- **Horizontal Partial Derivative of the Infinity-Sector Sine Mellin Component
`S_k^+(l, τ) = ∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(S_k^+(l + h, τ) − S_k^+(l, τ)) / h →
  ((∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv) + (∫_{v > 0} 2v sinh(lv) sin(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_pos_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Infinity-Sector Sine Mellin Component
`S_k^+(l, τ) = ∫_{x > 1} x^{l − 1/2} sin(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(S_k^+(l, τ + h) − S_k^+(l, τ)) / h →
  ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv) + (∫_{v > 0} 2v cosh(lv) cos(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_pos_nhdsWithin_zero
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ + h))
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)

/-- **Horizontal Partial Derivative of the Origin-Sector Cosine Mellin Component
`C_k^-(l, τ) = ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(C_k^-(l + h, τ) − C_k^-(l, τ)) / h →
  ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv) − (∫_{v > 0} 2v cosh(lv) cos(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_neg_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_oscillatoryMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_left_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Origin-Sector Cosine Mellin Component
`C_k^-(l, τ) = ∫_{x ∈ (0, 1]} x^{l − 1/2} cos(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(C_k^-(l, τ + h) − C_k^-(l, τ)) / h →
  −(((∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv) − (∫_{v > 0} 2v sinh(lv) sin(τv) Φ_k(v) dv)) / 2)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) := by
  have hl_half : |l| < 1 / 2 := by linarith
  have h := tendsto_div_sector_neg_nhdsWithin_zero
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ + h))
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_oscillatoryMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceCos_sub_right_nhds_zero hk hν hl τ)
  have hlim :
      ((-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) -
        (-(∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) / 2 =
      -(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) := by
    ring
  rw [hlim] at h
  exact h

/-- **Horizontal Partial Derivative of the Origin-Sector Sine Mellin Component
`S_k^-(l, τ) = ∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(S_k^-(l + h, τ) − S_k^-(l, τ)) / h →
  ((∫_ℝ v cosh(lv) sin(τv) Φ_k(v) dv) − (∫_{v > 0} 2v sinh(lv) sin(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_neg_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sineMellin_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_left_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Origin-Sector Sine Mellin Component
`S_k^-(l, τ) = ∫_{x ∈ (0, 1]} x^{l − 1/2} sin(τ log x) V_k(x) dx` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`(S_k^-(l, τ + h) − S_k^-(l, τ)) / h →
  ((∫_ℝ v sinh(lv) cos(τv) Φ_k(v) dv) − (∫_{v > 0} 2v cosh(lv) cos(τv) Φ_k(v) dv)) / 2`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sector_neg_nhdsWithin_zero
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ + h))
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sineMellin_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceSin_sub_right_nhds_zero hk hν hl τ)

/-- **First Cauchy–Riemann Equation `∂_l C_k^+(l, τ) = ∂_τ S_k^+(l, τ)` for the Infinity Sector
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((C_k^+(l + h, τ) − C_k^+(l, τ)) − (S_k^+(l, τ + h) − S_k^+(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sector_Ioi_one_cauchyRiemann_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_cauchyRiemann_first_of_eq_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Second Cauchy–Riemann Equation `∂_l S_k^+(l, τ) + ∂_τ C_k^+(l, τ) = 0` for the Infinity Sector
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((S_k^+(l + h, τ) − S_k^+(l, τ)) + (C_k^+(l, τ + h) − C_k^+(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sector_Ioi_one_cauchyRiemann_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_cauchyRiemann_second_of_eq_nhdsWithin_zero
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)

/-- **First Cauchy–Riemann Equation `∂_l C_k^-(l, τ) = ∂_τ S_k^-(l, τ)` for the Origin Sector
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((C_k^-(l + h, τ) − C_k^-(l, τ)) − (S_k^-(l, τ + h) − S_k^-(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sector_Ioc_zero_one_cauchyRiemann_first_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_cauchyRiemann_first_of_eq_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Second Cauchy–Riemann Equation `∂_l S_k^-(l, τ) + ∂_τ C_k^-(l, τ) = 0` for the Origin Sector
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((S_k^-(l + h, τ) − S_k^-(l, τ)) + (C_k^-(l, τ + h) − C_k^-(l, τ))) / h → 0` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sector_Ioc_zero_one_cauchyRiemann_second_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) :=
  tendsto_div_cauchyRiemann_second_of_eq_nhdsWithin_zero
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Five-Point Harmonicity (`Δ C_k^+(l, τ) = 0`) of the Infinity-Sector Cosine Mellin
Component across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):** -/
theorem tendsto_div_sq_sectorCos_Ioi_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sq_fivePoint_sector_pos_harmonic_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_sub l h, abs_lt.mpr hh] : |l - h| < 1 / 2) τ)
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ + h))
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ - h))
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Global Five-Point Harmonicity (`Δ S_k^+(l, τ) = 0`) of the Infinity-Sector Sine Mellin
Component across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):** -/
theorem tendsto_div_sq_sectorSin_Ioi_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sq_fivePoint_sector_pos_harmonic_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_sub l h, abs_lt.mpr hh] : |l - h| < 1 / 2) τ)
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ + h))
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ - h))
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Global Five-Point Harmonicity (`Δ C_k^-(l, τ) = 0`) of the Origin-Sector Cosine Mellin
Component across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):** -/
theorem tendsto_div_sq_sectorCos_Ioc_zero_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sq_fivePoint_sector_neg_harmonic_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (fun h hh => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν
      (by linarith [abs_sub l h, abs_lt.mpr hh] : |l - h| < 1 / 2) τ)
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ + h))
    (fun h _ => setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half (τ - h))
    (setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sq_oscillatoryMellin_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceCos_fivePoint_laplacian_nhds_zero hk hν hl τ)

/-- **Global Five-Point Harmonicity (`Δ S_k^-(l, τ) = 0`) of the Origin-Sector Sine Mellin
Component across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):** -/
theorem tendsto_div_sq_sectorSin_Ioc_zero_one_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            2 * ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hl_half : |l| < 1 / 2 := by linarith
  refine tendsto_div_sq_fivePoint_sector_neg_harmonic_nhdsWithin_zero
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_add_le l h, abs_lt.mpr hh] : |l + h| < 1 / 2) τ)
    (fun h hh => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν
      (by linarith [abs_sub l h, abs_lt.mpr hh] : |l - h| < 1 / 2) τ)
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ + h))
    (fun h _ => setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half (τ - h))
    (setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl_half τ)
    (tendsto_div_sq_sineMellin_fivePoint_laplacian_nhds_zero hk hν hl τ)
    (tendsto_div_sq_imbalanceSin_fivePoint_laplacian_nhds_zero hk hν hl τ)


/-! ## Section 3: Partial Derivatives, Critical-Line Anti-Symmetry, and Division-Free Liouville–Gauss Logarithmic Harmonicity of One-Sided Sector Moduli Squared `|F_k^+(l, τ)|²` and `|F_k^-(l, τ)|²` -/

/-- **Horizontal Partial Derivative of the Infinity-Sector Modulus Squared
`|F_k^+(l, τ)|² = C_k^+(l, τ)² + S_k^+(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((|F_k^+(l + h, τ)|² − |F_k^+(l, τ)|²) / h) → 2 (C_k^+ ∂_l C_k^+ + S_k^+ ∂_l S_k^+)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Infinity-Sector Modulus Squared
`|F_k^+(l, τ)|² = C_k^+(l, τ)² + S_k^+(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((|F_k^+(l, τ + h)|² − |F_k^+(l, τ)|²) / h) → 2 (C_k^+ ∂_τ C_k^+ + S_k^+ ∂_τ S_k^+)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Horizontal Partial Derivative of the Origin-Sector Modulus Squared
`|F_k^-(l, τ)|² = C_k^-(l, τ)² + S_k^-(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((|F_k^-(l + h, τ)|² − |F_k^-(l, τ)|²) / h) → 2 (C_k^- ∂_l C_k^- + S_k^- ∂_l S_k^-)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
            (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)

/-- **Vertical Partial Derivative of the Origin-Sector Modulus Squared
`|F_k^-(l, τ)|² = C_k^-(l, τ)² + S_k^-(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((|F_k^-(l, τ + h)|² − |F_k^-(l, τ)|²) / h) → 2 (C_k^- ∂_τ C_k^- + S_k^- ∂_τ S_k^-)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioc_zero_one_vert_shift_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (2 * ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
            (∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)))) :=
  tendsto_div_modulusSq_sub_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity of the Infinity-Sector Modulus
Squared `|F_k^+(l, τ)|² = C_k^+(l, τ)² + S_k^+(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`|F_k^+(l, τ)|² · ((Δ_l² |F_k^+|² + Δ_τ² |F_k^+|²) / h²) −
  (((|F_k^+(l + h, τ)|² − |F_k^+(l, τ)|²) / h)² + ((|F_k^+(l, τ + h)|² − |F_k^+(l, τ)|²) / h)²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_sectorModulusSq_Ioi_one_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (((((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
        (((((∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
          ((((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hLap := tendsto_div_sq_sectorModulusSq_Ioi_one_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hLap_eq :
      (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
        ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2) =
      4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) ^ 2 +
          (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) ^ 2) := by
    ring
  rw [hLap_eq] at hLap
  exact tendsto_liouville_gauss_modulusSq_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioi_one_vert_shift_nhds_zero hk hν hl τ)
    hLap

/-- **Global Division-Free Liouville–Gauss Logarithmic Harmonicity of the Origin-Sector Modulus
Squared `|F_k^-(l, τ)|² = C_k^-(l, τ)² + S_k^-(l, τ)²` across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`|F_k^-(l, τ)|² · ((Δ_l² |F_k^-|² + Δ_τ² |F_k^-|²) / h²) −
  (((|F_k^-(l + h, τ)|² − |F_k^-(l, τ)|²) / h)² + ((|F_k^-(l, τ + h)|² − |F_k^-(l, τ)|²) / h)²) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_sectorModulusSq_Ioc_zero_one_liouville_gauss_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          (((((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                2 * ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
        (((((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
          ((((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 0) := by
  have hLap := tendsto_div_sq_sectorModulusSq_Ioc_zero_one_fivePoint_laplacian_nhds_zero hk hν hl τ
  have hLap_eq :
      (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2 +
        ((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) ^ 2) =
      4 * ((((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) ^ 2 +
          (((∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) ^ 2) := by
    ring
  rw [hLap_eq] at hLap
  exact tendsto_liouville_gauss_modulusSq_nhdsWithin_zero
    (tendsto_div_sectorCos_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorCos_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_sectorSin_Ioc_zero_one_vert_shift_nhds_zero hk hν hl τ)
    hLap

/-- **Critical-Line Horizontal Stationarity of the Sum of Sector Moduli Squared
`|F_k^+(h, τ)|² + |F_k^-(h, τ)|²` (`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`(((|F_k^+(h, τ)|² + |F_k^-(h, τ)|²) − (|F_k^+(0, τ)|² + |F_k^-(0, τ)|²)) / h) → 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_add_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((∫ x in Ioi (1 : ℝ),
                x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (1 : ℝ),
                x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
          (((∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
            ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) := by
  have hk1 : 1 ≤ k := by omega
  have hl0 : (0 : ℝ) - 1 / 2 = -(1 / 2 : ℝ) := by ring
  have hpos := tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hneg := tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_nhds_zero
    hk hν (by norm_num : |(0 : ℝ)| < 1 / 8) τ
  have hsum := hpos.add hneg
  have hsinh_full :
      (∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hsinh_half :
      (∫ v in Ioi (0 : ℝ),
        2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0 := by
    have h0 :
        (fun v : ℝ => 2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) =
        fun _ => 0 := by
      ext v; rw [zero_mul, Real.sinh_zero, mul_zero, zero_mul, zero_mul]
    rw [h0, integral_zero]
  have hC_eq := setIntegral_Ioi_one_sub_Ioc_zero_one_rpow_zero_mul_cos_log hk1 ν τ
  have hS_eq := setIntegral_Ioc_zero_one_rpow_neg_half_mul_sin_log_eq_neg_Ioi_one hk1 ν τ
  have hlim :
      2 * ((∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
          (∫ x in Ioi (1 : ℝ),
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (((∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) +
      2 * ((∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (((∫ v : ℝ, v * Real.sinh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
          (∫ x in Ioc (0 : ℝ) 1,
              x ^ ((0 : ℝ) - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (((∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) -
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) =
      0 := by
    rw [hsinh_full, hsinh_half, hl0]
    have hC :
        (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) =
        ∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x := by
      linarith [hC_eq]
    have hS :
        (∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
        (∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 := by
      linarith [hS_eq]
    linarith [
      (by ring :
        2 * ((∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((0 + (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
            (∫ x in Ioi (1 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) + 0) / 2)) +
        2 * ((∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              ((0 - (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) +
            (∫ x in Ioc (0 : ℝ) 1,
                x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (((∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) - 0) / 2)) =
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
          (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)),
      (by rw [hC, sub_self, zero_mul, hS, zero_mul, add_zero] :
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
          (∫ v in Ioi (0 : ℝ),
            2 * v * Real.cosh ((0 : ℝ) * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) *
          (∫ v : ℝ, v * Real.cosh ((0 : ℝ) * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) = 0)]
  rw [hlim] at hsum
  refine hsum.congr (fun h => ?_)
  have h0h : (0 : ℝ) + h - 1 / 2 = h - 1 / 2 := by ring
  rw [h0h, hl0]
  ring

/-- **Critical-Line Transverse Derivative of the Infinity-Sector Modulus Squared
`|F_k^+(l, τ)|²` (`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`((|F_k^+(h, τ)|² − |F_k^+(0, τ)|²) / h) → (1/2) ∂_l H_k(0, τ)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (((∫ x in Ioi (0 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
            (2 * ∫ v in Ioi (0 : ℝ),
              v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
          (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
            (2 * ∫ v in Ioi (0 : ℝ),
              Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2)) := by
  have hk1 : 1 ≤ k := by omega
  have hsum := tendsto_div_sectorModulusSq_add_at_criticalLine_nhds_zero hk hν τ
  have hdiff := tendsto_div_sectorModulusSq_sub_nhds_zero hk hν τ
  have heq := sectorModulusSq_Ioi_one_eq_Ioc_zero_one_at_criticalLine hk1 ν τ
  have hcomb := (hsum.add hdiff).div_const (2 : ℝ)
  rw [zero_add] at hcomb
  refine hcomb.congr (fun h => ?_)
  rw [← heq]
  ring

/-- **Critical-Line Transverse Derivative of the Origin-Sector Modulus Squared
`|F_k^-(l, τ)|²` (`l = 0`, `k ≥ 2`, `τ ∈ ℝ`):**
`((|F_k^-(h, τ)|² − |F_k^-(0, τ)|²) / h) → −(1/2) ∂_l H_k(0, τ)` as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioc_zero_one_horiz_shift_at_criticalLine_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioc (0 : ℝ) 1,
              x ^ (h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioc (0 : ℝ) 1,
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (-(((∫ x in Ioi (0 : ℝ),
                x ^ (-(1 / 2 : ℝ)) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (2 * ∫ v in Ioi (0 : ℝ),
                v * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ v : ℝ, v * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) *
              (2 * ∫ v in Ioi (0 : ℝ),
                Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2))) := by
  have hk1 : 1 ≤ k := by omega
  have hsum := tendsto_div_sectorModulusSq_add_at_criticalLine_nhds_zero hk hν τ
  have hdiff := tendsto_div_sectorModulusSq_sub_nhds_zero hk hν τ
  have heq := sectorModulusSq_Ioi_one_eq_Ioc_zero_one_at_criticalLine hk1 ν τ
  have hcomb := (hsum.sub hdiff).div_const (2 : ℝ)
  rw [zero_sub, neg_div] at hcomb
  refine hcomb.congr (fun h => ?_)
  rw [heq]
  ring

/-- **Critical-Line Zero-Locus Transverse Derivative of the Infinity-Sector Modulus Squared
(`l = 0`, `k ≥ 2`, `τ₀ ∈ ℝ`, `M_k(0, τ₀) = 0`):**
At any critical-line zero `M_k(0, τ₀) = 0`,
`((|F_k^+(h, τ₀)|² − |F_k^+(0, τ₀)|²) / h) →
  (∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_ℝ v sin(τ₀ v) Φ_k(v) dv) = −(1/2) ∂_τ W_k(0, τ₀)`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {τ₀ : ℝ}
    (hzero :
      (∫ x in Ioi (0 : ℝ),
        x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0) :
    Tendsto
      (fun h : ℝ =>
        (((∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (h - 1 / 2) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
          ((∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (1 : ℝ),
              x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
  have h := tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_nhds_zero hk hν τ₀
  have hlim :
      ((0 * (2 * ∫ v in Ioi (0 : ℝ),
            v * Real.cos (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) +
        (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
          (2 * ∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)) / 2) =
      (∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
        (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) := by
    ring
  rw [hzero, hlim] at h
  exact h


/-! ## Section 4: Brahmagupta–Fibonacci Sector Norm Identities, Subharmonicity and Liouville–Gauss Logarithmic Harmonicity of `H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² |Δ_k(l, τ)|²`, and Master Witness Theorem -/

/-- **Full-to-Imbalance Brahmagupta–Fibonacci Norm Identity (`k ∈ ℕ`, `l, τ ∈ ℝ`):**
`H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² · |Δ_k(l, τ)|²`. -/
theorem hermitianPairing_sq_add_sectorWronskian_sq_eq
    (k : ℕ) (ν : Measure ArcParam) (l τ : ℝ) :
    ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2 +
    ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2 =
    ((∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        (∫ x in Ioi (0 : ℝ),
          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
      (((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
        ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
          ∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  ring

/-- **Origin-to-Infinity Sector Brahmagupta–Fibonacci Identity (`k ≥ 2`, `|l| < 1/2`, `τ ∈ ℝ`):**
`(|F_k(l, τ)|² − |Δ_k(l, τ)|²)² + 4 W_k(l, τ)² = 16 |F_k^+(l, τ)|² · |F_k^-(l, τ)|²`. -/
theorem complexModulusSq_sub_imbalanceModulusSq_sq_add_four_mul_sectorWronskian_sq_eq
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 2) (τ : ℝ) :
    (((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
        (((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ^ 2 +
      4 * ((∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
        (∫ x in Ioi (0 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
          ((∫ x in Ioi (1 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
            ∫ x in Ioc (0 : ℝ) 1,
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2 =
    16 * ((∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioi (1 : ℝ),
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
        ((∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
          (∫ x in Ioc (0 : ℝ) 1,
            x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) := by
  rw [setIntegral_Ioi_rpow_mul_cos_log_eq_add_sectors hk hν hl τ,
    setIntegral_Ioi_rpow_mul_sin_log_eq_add_sectors hk hν hl τ]
  exact origin_infinity_sector_brahmagupta_fibonacci_identity _ _ _ _

/-- **Global Five-Point Subharmonicity of the Holomorphic Product Modulus Squared
`|F_k(l, τ)|² · |Δ_k(l, τ)|² = H_k(l, τ)² + W_k(l, τ)² = P_k(l, τ)² + Q_k(l, τ)²`
across `|l| < 1/8`, `τ ∈ ℝ` (`k ≥ 2`):**
`((Δ_l² (|F_k|² |Δ_k|²) + Δ_τ² (|F_k|² |Δ_k|²)) / h²) →
  4 ((∂_l P_k(l, τ))² + (∂_l Q_k(l, τ))²) ≥ 0`
as `h → 0` (`h ≠ 0`). -/
theorem tendsto_div_sq_hermitianWronskianNormSq_fivePoint_laplacian_nhds_zero
    {k : ℕ} (hk : 2 ≤ k) {ν : Measure ArcParam} [IsFiniteMeasure ν]
    (hν : ν.map arcNeg = ν) {l : ℝ} (hl : |l| < 1 / 8) (τ : ℝ) :
    Tendsto
      (fun h : ℝ =>
        ((((((∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) +
            ((((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
              (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) -
              2 * (((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  ((∫ x in Ioi (1 : ℝ),
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                       x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)))) / h ^ 2))
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) *
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
          ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
              (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
            ((∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
        8 * (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
          ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
            (((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (-(∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
              ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))))) := by
  set U_l : ℝ → ℝ := fun h =>
    (∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U_t : ℝ → ℝ := fun h =>
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set U₀ : ℝ :=
    (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
      (∫ x in Ioi (0 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_l : ℝ → ℝ := fun h =>
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V_t : ℝ → ℝ := fun h =>
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  set V₀ : ℝ :=
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
    ((∫ x in Ioi (1 : ℝ),
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
      ∫ x in Ioc (0 : ℝ) 1,
        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2
  have hUlap : Tendsto
      (fun h : ℝ => ((U_l h + U_l (-h) - 2 * U₀) + (U_t h + U_t (-h) - 2 * U₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
    refine (tendsto_div_sq_complexModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [U_l, U_t, U₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have hVlap : Tendsto
      (fun h : ℝ => ((V_l h + V_l (-h) - 2 * V₀) + (V_t h + V_t (-h) - 2 * V₀)) / h ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds
        (4 * ((∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2))) := by
    refine (tendsto_div_sq_imbalanceModulusSq_fivePoint_laplacian_nhds_zero hk hν hl τ).congr (fun h => ?_)
    dsimp [V_l, V_t, V₀]
    have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
    have ht_sub : τ + -h = τ - h := by ring
    rw [hl_sub, ht_sub]
  have h := tendsto_div_sq_fivePoint_mul_general_nhdsWithin_zero
    (tendsto_div_complexModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_complexModulusSq_vert_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_horiz_shift_nhds_zero hk hν hl τ)
    (tendsto_div_imbalanceModulusSq_vert_shift_nhds_zero hk hν hl τ)
    hUlap hVlap
  have hlim :
      U₀ * (4 * ((∫ v in Ioi (0 : ℝ),
                  2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v in Ioi (0 : ℝ),
                  2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
      V₀ * (4 * ((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
                (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
      2 * ((2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) *
            (2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v))) +
          (2 * ((∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
                (∫ x in Ioi (0 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) *
            (2 * (((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (-(∫ v in Ioi (0 : ℝ),
                    2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
                ((∫ x in Ioi (1 : ℝ),
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                    ∫ x in Ioc (0 : ℝ) 1,
                      x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                  (∫ v in Ioi (0 : ℝ),
                    2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)))) =
      4 * (((∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2) *
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
        ((∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
            (∫ x in Ioi (0 : ℝ),
              x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
          ((∫ v in Ioi (0 : ℝ),
              2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2 +
            (∫ v in Ioi (0 : ℝ),
              2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v) ^ 2)) +
      8 * (((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
        ((∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(∫ v : ℝ, v * Real.cosh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
            (∫ x in Ioi (0 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v : ℝ, v * Real.sinh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v)) *
          (((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (-(∫ v in Ioi (0 : ℝ),
                2 * v * Real.sinh (l * v) * Real.sin (τ * v) * arcLineInfiniteDyadicProfile k ν v)) +
            ((∫ x in Ioi (1 : ℝ),
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              ∫ x in Ioc (0 : ℝ) 1,
                x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
              (∫ v in Ioi (0 : ℝ),
                2 * v * Real.cosh (l * v) * Real.cos (τ * v) * arcLineInfiniteDyadicProfile k ν v))) := by
    dsimp [U₀, V₀]; ring
  rw [hlim] at h
  refine h.congr (fun h => ?_)
  dsimp [U_l, U_t, U₀, V_l, V_t, V₀]
  have hl_sub : l + -h - 1 / 2 = l - h - 1 / 2 := by ring
  have ht_sub : τ + -h = τ - h := by ring
  rw [hl_sub, ht_sub]
  ring

/-- **Master Witness Theorem for One-Sided Sector Cauchy–Riemann Equations, Five-Point Harmonicity,
Division-Free Liouville–Gauss Logarithmic Harmonicity of One-Sided Sector Moduli, and
Brahmagupta–Fibonacci Sector Norm Identities:**
There exists an explicit symmetric non-zero finite arc measure `ν` on `ArcParam` such that for all
`k ≥ 2`:
1. Across `|l| < 1/8` and `τ ∈ ℝ`, the infinity-sector Mellin pair `(C_k^+(l, τ), S_k^+(l, τ))` and
   origin-sector Mellin pair `(C_k^-(l, τ), S_k^-(l, τ))` satisfy the global Cauchy–Riemann
   equations `∂_l C_k^± = ∂_τ S_k^±` and `∂_l S_k^± = −∂_τ C_k^±` and have vanishing five-point
   Laplacians;
2. Across `|l| < 1/8` and `τ ∈ ℝ`, both one-sided sector moduli squared `|F_k^+(l, τ)|²` and
   `|F_k^-(l, τ)|²` satisfy the division-free Liouville–Gauss logarithmic harmonicity laws
   `|F_k^±|² · Δ(|F_k^±|²) − ((∂_l |F_k^±|²)² + (∂_τ |F_k^±|²)²) → 0`;
3. Across `|l| < 1/2` and `τ ∈ ℝ`, the Brahmagupta–Fibonacci sector norm identities
   `H_k(l, τ)² + W_k(l, τ)² = |F_k(l, τ)|² · |Δ_k(l, τ)|²` and
   `(|F_k(l, τ)|² − |Δ_k(l, τ)|²)² + 4 W_k(l, τ)² = 16 |F_k^+(l, τ)|² · |F_k^-(l, τ)|²` hold;
4. On the critical line `l = 0`, the sum of sector moduli squared is horizontally stationary
   (`∂_l(|F_k^+|² + |F_k^-|²)(0, τ) = 0`), the individual sector moduli have opposite transverse
   derivatives `∂_l |F_k^+(0, τ)|² = −∂_l |F_k^-(0, τ)|² = (1/2) ∂_l H_k(0, τ)`, and at any
   critical-line zero `M_k(0, τ₀) = 0` satisfy
   `∂_l |F_k^+(0, τ₀)|² = (∫_{v > 0} sin(τ₀ v) Φ_k(v) dv) · (∫_ℝ v sin(τ₀ v) Φ_k(v) dv)`. -/
theorem exists_dyadic_oneSidedSector_cauchyRiemann_logarithmicHarmonicity_arcWitness :
    ∃ ν : Measure ArcParam,
      IsFiniteMeasure ν ∧
      ν.map arcNeg = ν ∧
      ν ≠ 0 ∧
      ∀ ⦃k : ℕ⦄, 2 ≤ k →
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) +
                ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 8 → ∀ τ : ℝ,
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((((∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    (((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioi (1 : ℝ),
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
              (((((∫ x in Ioi (1 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
                ((((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    ((∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioi (1 : ℝ),
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0) ∧
          Tendsto
            (fun h : ℝ =>
              ((∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
                (((((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) +
                    (((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) +
                      ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin ((τ - h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                      2 * ((∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                        (∫ x in Ioc (0 : ℝ) 1,
                          x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2))) / h ^ 2) -
              (((((∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l + h - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l + h - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    ((∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2 +
                ((((∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin ((τ + h) * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                    ((∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                      (∫ x in Ioc (0 : ℝ) 1,
                        x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h) ^ 2))
            (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 0)) ∧
        (∀ ⦃l : ℝ⦄, |l| < 1 / 2 → ∀ τ : ℝ,
          (((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ^ 2 +
            4 * ((∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
              (∫ x in Ioi (0 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) *
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) -
                  ∫ x in Ioc (0 : ℝ) 1,
                    x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x)) ^ 2 =
          16 * ((∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioi (1 : ℝ),
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) *
              ((∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.cos (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                (∫ x in Ioc (0 : ℝ) 1,
                  x ^ (l - 1 / 2) * Real.sin (τ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) ∧
        (∀ τ₀ : ℝ,
          (∫ x in Ioi (0 : ℝ),
            x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) = 0 →
          Tendsto
            (fun h : ℝ =>
              (((∫ x in Ioi (1 : ℝ),
                    x ^ (h - 1 / 2) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (h - 1 / 2) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2) -
                ((∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.cos (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2 +
                  (∫ x in Ioi (1 : ℝ),
                    x ^ (-(1 / 2 : ℝ)) * Real.sin (τ₀ * Real.log x) * arcLineInfiniteDyadicVector k ν x) ^ 2)) / h)
            (nhdsWithin 0 {(0 : ℝ)}ᶜ)
            (nhds
              ((∫ v in Ioi (0 : ℝ), Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v) *
                (∫ v : ℝ, v * Real.sin (τ₀ * v) * arcLineInfiniteDyadicProfile k ν v)))) := by
  obtain ⟨ν, hfin, hne, hν, _, _⟩ := exists_arcWitness
  refine ⟨ν, hfin, hν, hne, fun k hk => ?_⟩
  refine ⟨fun l hl τ =>
      ⟨tendsto_div_sector_Ioi_one_cauchyRiemann_first_nhds_zero hk hν hl τ,
       tendsto_div_sector_Ioi_one_cauchyRiemann_second_nhds_zero hk hν hl τ,
       tendsto_div_sector_Ioc_zero_one_cauchyRiemann_first_nhds_zero hk hν hl τ,
       tendsto_div_sector_Ioc_zero_one_cauchyRiemann_second_nhds_zero hk hν hl τ⟩,
    fun l hl τ =>
      ⟨tendsto_sectorModulusSq_Ioi_one_liouville_gauss_nhds_zero hk hν hl τ,
       tendsto_sectorModulusSq_Ioc_zero_one_liouville_gauss_nhds_zero hk hν hl τ⟩,
    fun l hl τ =>
      complexModulusSq_sub_imbalanceModulusSq_sq_add_four_mul_sectorWronskian_sq_eq hk hν hl τ,
    fun τ₀ hzero =>
      tendsto_div_sectorModulusSq_Ioi_one_horiz_shift_at_criticalLine_zero hk hν hzero⟩

end

end RHTower
