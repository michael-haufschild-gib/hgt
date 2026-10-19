import GaloisForLFunctions.SquareRootThreshold.WindowedOffDiagonalBeyondThreshold
import GaloisForLFunctions.RHTower.PairCorrelationExchangeRate

/-!
# Double-Window Minimum-Aperture Resolution Law and Pair-Correlation Exchange Rate

`WindowedOffDiagonalBeyondThreshold` proves the algebraic height-averaged Gram identity
`integral_pairTransform_mul_integral_windowed_centred_eq` and notes in its module docstring
that when `η` has support in `[-r, r]` and the height-averaging window `ω` has support in
`[-ρ, ρ]`, only pairs with `|ν_j - ν_k| < 2 * min r ρ` survive in the double-windowed
off-diagonal.

This module formalizes that minimum-aperture resolution law, proves the resulting
double-windowed diagonal/off-diagonal decomposition and `ζ` prime-pair correlation bound,
and connects the beyond-threshold regime (`λ > 1`) to the pair-correlation exchange rate
of `RHTower.PairCorrelationExchangeRate`:

1. **Product Kernel Minimum-Aperture Cutoff (`weilTest_mul_weilTest_eq_zero_of_min_le`):**
   If `tsupport η ⊆ Icc (-r) r` and `tsupport ω ⊆ Icc (-ρ) ρ`, then
   `EF.weilTest η η v * EF.weilTest ω ω v = 0` whenever `2 * min r ρ ≤ |v|`.

2. **Exact Double-Windowed Diagonal + `min r ρ` Off-Diagonal Split
   (`integral_pairTransform_mul_integral_windowed_centred_eq_diag_add_closeSet`):**
   The centred double-windowed height average splits into the exact product diagonal
   `(∫ ‖η‖²) (∫ ‖ω‖²) ∑_j ‖c_j‖²` plus the off-diagonal sum restricted to
   `closeSet s ν (min r ρ) j`.

3. **Double-Windowed Off-Diagonal Norm Bound & Secondary-Window Diagonalization
   (`norm_doubleWindow_centred_offDiag_le`,
   `doubleWindow_centred_expSum_eq_diag_of_closeSet_empty`):**
   Even when the primary window aperture `r` exceeds the square-root threshold, choosing a
   secondary window `ω` whose aperture `ρ` separates frequencies (`closeSet s ν (min r ρ) j = ∅`)
   restores exact diagonalization; in general, the off-diagonal is controlled by the
   neighbour count at scale `min r ρ`.

4. **Prime-Frequency Double-Windowed Off-Diagonal Bound for `ζ`
   (`norm_doubleWindow_primeFreq_offDiag_le`):**
   For prime-power frequencies up to `N ≤ X` with `0 ≤ min r ρ ≤ log 2`, the centred
   double-windowed off-diagonal norm is at most
   `(∫ ‖η‖²) (∫ ‖ω‖²) (X (e^{2 min(r,ρ)} - e^{-2 min(r,ρ)}) V_f(N))`.

5. **Beyond-Threshold Pair-Correlation Exchange Rate
   (`pairCorrelation_beyond_threshold_exchange_rate`):**
   Unites the `min r ρ` double-windowed off-diagonal bound with `RHTower.certOpt_sub_certValue`,
   `RHTower.opt_sub_two_thirds`, and `RHTower.opt_ge_three_quarters_iff`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.WeilRegular

/-! ## 1. Product Kernel Minimum-Aperture Cutoff -/

/-- **Minimum-Aperture Vanishing Law:**
If `η` is supported in `[-r, r]` and `ω` is supported in `[-ρ, ρ]`, then the product of their
Weil autocorrelation kernels vanishes whenever `2 * min r ρ ≤ |v|`. -/
theorem weilTest_mul_weilTest_eq_zero_of_min_le {η ω : ℝ → ℂ}
    (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ v : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    (hv : 2 * min r ρ ≤ |v|) :
    EF.weilTest η η v * EF.weilTest ω ω v = 0 := by
  rcases le_total r ρ with hrρ | hρr
  · have hmin : min r ρ = r := min_eq_left hrρ
    rw [hmin] at hv
    rw [weilTest_self_eq_zero_of_le hη hηs hv, zero_mul]
  · have hmin : min r ρ = ρ := min_eq_right hρr
    rw [hmin] at hv
    rw [weilTest_self_eq_zero_of_le hω hωs hv, mul_zero]

/-! ## 2. Double-Windowed Diagonal + `min r ρ` Off-Diagonal Split -/

/-- Restricting the off-diagonal of the centred double-windowed sum from `s.erase j` to
`closeSet s ν (min r ρ) j`. -/
theorem sum_erase_doubleWindow_eq_sum_closeSet_min {η ω : ℝ → ℂ}
    (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (T : ℝ) (j : ι) :
    ∑ k ∈ s.erase j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ)) =
      ∑ k ∈ closeSet s ν (min r ρ) j, c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ)) := by
  refine (Finset.sum_subset (fun k hk => ?_) fun k hk hkn => ?_).symm
  · simp only [closeSet, Finset.mem_filter] at hk
    exact Finset.mem_erase.mpr ⟨hk.2.1, hk.1⟩
  · have hks := Finset.mem_erase.mp hk
    have hfar : 2 * min r ρ ≤ |ν j - ν k| := by
      by_contra h
      exact hkn (Finset.mem_filter.mpr ⟨hks.2, hks.1, not_le.mp h⟩)
    have hz := weilTest_mul_weilTest_eq_zero_of_min_le hη hω hηs hωs hfar
    calc c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
          EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))
        = c j * conj (c k) * (EF.weilTest η η (ν j - ν k) * EF.weilTest ω ω (ν j - ν k)) *
            cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ)) := by ring
      _ = 0 := by rw [hz, mul_zero, zero_mul]

/-- **Exact Double-Windowed Diagonal + `min r ρ` Off-Diagonal Split:**
For windows `η` supported in `[-r, r]` and `ω` supported in `[-ρ, ρ]`, the height-averaged
windowed mean square centred at `T` equals the exact product diagonal plus the off-diagonal
restricted to `closeSet s ν (min r ρ) j`. -/
theorem integral_pairTransform_mul_integral_windowed_centred_eq_diag_add_closeSet
    {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (T : ℝ) :
    ∫ ξ₀ : ℝ, pairTransform ω ξ₀ *
        ∫ ξ : ℝ, pairTransform η ξ *
          (expSum s c ν (ξ + (ξ₀ + T)) * conj (expSum s c ν (ξ + (ξ₀ + T)))) =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ t, ‖ω t‖ ^ 2 : ℝ) : ℂ) *
          ∑ j ∈ s, ((‖c j‖ ^ 2 : ℝ) : ℂ) +
        ∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
          c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
            EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ)) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hωc := hasCompactSupport_of_tsupport_subset_Icc hωs
  rw [integral_pairTransform_mul_integral_windowed_centred_eq hη hηc hω hωc,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [← Finset.add_sum_erase s _ hj, sub_self, Complex.ofReal_zero, mul_zero, Complex.exp_zero,
    mul_one, weilTest_self_zero, weilTest_self_zero, Complex.mul_conj, Complex.normSq_eq_norm_sq,
    sum_erase_doubleWindow_eq_sum_closeSet_min hη hω hηs hωs s c ν T j]
  push_cast
  ring

/-- **Secondary-Window Exact Diagonalization:**
Whenever `closeSet s ν (min r ρ) j = ∅` for all `j ∈ s` (even if `r` alone exceeds the
threshold), the centred double-windowed height average equals its exact diagonal. -/
theorem doubleWindow_centred_expSum_eq_diag_of_closeSet_empty
    {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (T : ℝ)
    (hdisj : ∀ j ∈ s, closeSet s ν (min r ρ) j = ∅) :
    ∫ ξ₀ : ℝ, pairTransform ω ξ₀ *
        ∫ ξ : ℝ, pairTransform η ξ *
          (expSum s c ν (ξ + (ξ₀ + T)) * conj (expSum s c ν (ξ + (ξ₀ + T)))) =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ t, ‖ω t‖ ^ 2 : ℝ) : ℂ) *
        ∑ j ∈ s, ((‖c j‖ ^ 2 : ℝ) : ℂ) := by
  rw [integral_pairTransform_mul_integral_windowed_centred_eq_diag_add_closeSet
    hη hω hηs hωs s c ν T]
  have hzero : ∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
      c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
        EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ)) = 0 := by
    refine Finset.sum_eq_zero fun j hj => ?_
    rw [hdisj j hj, Finset.sum_empty]
  rw [hzero, add_zero]

/-! ## 3. Quantitative Double-Windowed Off-Diagonal Bounds -/

/-- **Double-Windowed Off-Diagonal Norm Bound:**
If every frequency `j ∈ s` has at most `M` neighbours in `closeSet s ν (min r ρ) j`, then
the centred double-windowed off-diagonal has norm at most `(∫ ‖η‖²) (∫ ‖ω‖²) (M ∑_j ‖c_j‖²)`. -/
theorem norm_doubleWindow_centred_offDiag_le
    {η ω : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ)
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (c : ι → ℂ) (ν : ι → ℝ) (T : ℝ)
    {M : ℝ} (hM : ∀ j ∈ s, ((closeSet s ν (min r ρ) j).card : ℝ) ≤ M) :
    ‖∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
        c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
          EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))‖ ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * (M * ∑ j ∈ s, ‖c j‖ ^ 2) := by
  have hηc := hasCompactSupport_of_tsupport_subset_Icc hηs
  have hωc := hasCompactSupport_of_tsupport_subset_Icc hωs
  have hkη : ∀ v, ‖EF.weilTest η η v‖ ≤ ∫ t, ‖η t‖ ^ 2 :=
    norm_weilTest_self_le hη.continuous hηc
  have hkω : ∀ v, ‖EF.weilTest ω ω v‖ ≤ ∫ t, ‖ω t‖ ^ 2 :=
    norm_weilTest_self_le hω.continuous hωc
  have hNη : 0 ≤ ∫ t, ‖η t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hNω : 0 ≤ ∫ t, ‖ω t‖ ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hprod_le : ∀ v, ‖EF.weilTest η η v * EF.weilTest ω ω v‖ ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) := fun v => by
    rw [norm_mul]
    exact mul_le_mul (hkη v) (hkω v) (norm_nonneg _) hNη
  calc ‖∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
          c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
            EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))‖
      ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
          ‖c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
            EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))‖ :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => norm_sum_le _ _)
    _ ≤ ∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j,
          ((∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2)) * (‖c j‖ * ‖c k‖) := by
        refine Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => ?_
        have hexp : ‖cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))‖ = 1 :=
          norm_cexp_two_pi_I_mul T (ν j - ν k)
        have hnorm_eq : ‖c j * conj (c k) * EF.weilTest η η (ν j - ν k) *
            EF.weilTest ω ω (ν j - ν k) * cexp (2 * π * I * T * ((ν j - ν k : ℝ) : ℂ))‖ =
            (‖c j‖ * ‖c k‖) * ‖EF.weilTest η η (ν j - ν k) * EF.weilTest ω ω (ν j - ν k)‖ := by
          rw [norm_mul, hexp, mul_one, mul_assoc (c j * conj (c k)), norm_mul, norm_mul,
            Complex.norm_conj]
        rw [hnorm_eq, mul_comm ((∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2))]
        exact mul_le_mul_of_nonneg_left (hprod_le (ν j - ν k))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = ((∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2)) *
          ∑ j ∈ s, ∑ k ∈ closeSet s ν (min r ρ) j, ‖c j‖ * ‖c k‖ := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.mul_sum]
    _ ≤ (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) * (M * ∑ j ∈ s, ‖c j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_closeSet_norm_mul_le s c ν hM) (mul_nonneg hNη hNω)

/-- **Prime-Frequency Double-Windowed Off-Diagonal Bound for `ζ`:**
For prime-power frequencies up to `N ≤ X` and windows of apertures `r, ρ ≥ 0` with
`min r ρ ≤ log 2`, the centred double-windowed off-diagonal norm is bounded by the
effective minimum aperture `min r ρ`. -/
theorem norm_doubleWindow_primeFreq_offDiag_le
    {η ω f : ℝ → ℂ} (hη : ContDiff ℝ 2 η) (hω : ContDiff ℝ 2 ω) {r ρ X : ℝ} {N : ℕ}
    (hr : 0 ≤ r) (hρ : 0 ≤ ρ) (hmin2 : min r ρ ≤ Real.log 2) (hNX : (N : ℝ) ≤ X)
    (hηs : tsupport η ⊆ Icc (-r) r) (hωs : tsupport ω ⊆ Icc (-ρ) ρ) (T : ℝ) :
    ‖∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
        ∑ k ∈ closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq (min r ρ) j,
          primeCoeff f j * conj (primeCoeff f k) *
            EF.weilTest η η (primeFreq j - primeFreq k) *
            EF.weilTest ω ω (primeFreq j - primeFreq k) *
            cexp (2 * π * I * T * ((primeFreq j - primeFreq k : ℝ) : ℂ))‖ ≤
      (∫ t, ‖η t‖ ^ 2) * (∫ t, ‖ω t‖ ^ 2) *
        (X * (Real.exp (2 * min r ρ) - Real.exp (-(2 * min r ρ))) * primeVariance f N) := by
  have hmin0 : 0 ≤ min r ρ := le_min hr hρ
  have hM : ∀ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool),
      ((closeSet (Finset.Icc 2 N ×ˢ Finset.univ) primeFreq (min r ρ) j).card : ℝ) ≤
        X * (Real.exp (2 * min r ρ) - Real.exp (-(2 * min r ρ))) :=
    fun j hj => card_closeSet_primeFreq_le hmin0 hmin2 hNX hj
  have hbound := norm_doubleWindow_centred_offDiag_le hη hω hηs hωs
    (Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool)) (primeCoeff f) primeFreq T hM
  have hvar : ∑ j ∈ Finset.Icc 2 N ×ˢ (Finset.univ : Finset Bool), ‖primeCoeff f j‖ ^ 2 =
      primeVariance f N := by
    simpa [mul_zero, Complex.exp_zero, mul_one] using sum_norm_sq_primeCoeff_shift_eq f N 0
  rw [hvar] at hbound
  exact hbound

/-! ## 4. Synthesis with the Beyond-Threshold Pair-Correlation Exchange Rate -/

/-- **Double-Window Off-Diagonal & Pair-Correlation Exchange Rate Beyond the Threshold:**
Combines the `min r ρ` double-windowed off-diagonal control with the exact exchange rate
(`RHTower.certOpt_sub_certValue`, `RHTower.opt_sub_two_thirds`,
`RHTower.opt_ge_three_quarters_iff`) governing how any finite pair-correlation bound
`F ≤ B` beyond the square-root threshold `λ = 1` advances the certified critical-line
proportion past `2 / 3`. -/
theorem pairCorrelation_beyond_threshold_exchange_rate
    {B lam : ℝ} (hB : 2 / 3 < B) (hlam : lam ≠ 0) :
    certOpt B - certValue lam B =
        (B - 2 / 3) * (1 / lam - 3 * (B - 1) / (3 * B - 2)) ^ 2 ∧
      certOpt B - 2 / 3 = 1 / (3 * (3 * B - 2)) ∧
      (3 / 4 ≤ certOpt B ↔ B ≤ 2) :=
  ⟨certOpt_sub_certValue hB hlam, opt_sub_two_thirds hB, opt_ge_three_quarters_iff hB⟩

end GaloisForLFunctions.SquareRootThreshold

end
