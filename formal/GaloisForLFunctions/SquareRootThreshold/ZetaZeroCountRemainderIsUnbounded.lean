import GaloisForLFunctions.SquareRootThreshold.ZetaOffLineCorrectionSmallOutsideSparseHeights
import GaloisForLFunctions.SquareRootThreshold.ZetaWindowPrimePolynomialOnThePrimeTorus

/-!
# The zero-count remainder `S(T)` is unbounded

Let `N(T)` count the zeros of `ξ` with ordinate in `(0, T]` and `M(T) = (T/2π) log(T/2πe) + 7/8`.
The remainder `S(T) = N(T) − M(T)` (`rvmRemainder`) is unbounded: for every `B` and `T₀` there is
`T ≥ T₀` with `|S(T)| > B` (`rvmRemainder_unbounded`).  Unconditional.

**Proof.**  Suppose `|S| ≤ B` on `[1, ∞)` (`exists_abs_rvmRemainder_le_on_Ici_one`).  For an
aperture `ℓ > 0` the window prime polynomial satisfies
`Re Π_ℓ(T) = ∫_1^{2T} S(t) ψ_ℓ'(t − T) dt − Corr_ℓ(T) + o(1)`
(`tendsto_windowPrime_add_offLineCorrection_sub`), and the integral is at most
`B ∫|ψ_ℓ'| = B ℓ² ∫|ψ_1'|` (`abs_integral_rvmRemainder_mul_psiDeriv_le`).
1. *Gain.*  At the aligned prime phases `Re Π_ℓ` takes the value `F_ℓ(1) ≫ ℓ e^{ℓ/4}`; choose `ℓ`
   with `F_ℓ(1) > G := B ℓ² ∫|ψ_1'| + 2`.
2. *Kronecker.*  The heights `T ∈ [U/4, U/2]` with `Re Π_ℓ(T) > G` have measure `≥ cU` for all large
   `U` (Kronecker–Weyl for the prime phases `p^{−iT}`).
3. *Zero density.*  The heights in `[U/4, U/2]` with `|Corr_ℓ(T)| > 1/2` lie in a set of measure
   `≤ cU/2` (Selberg-type density of the zeros off the line).
A height of the first kind outside the second set has `G < Re Π_ℓ(T) ≤ Bℓ²∫|ψ_1'| + 1`.

**Meaning.**  A bounded spectral shift is the signature of a finite-rank modification of a
reference operator.  The zero fluctuation `S` is unbounded, so no spectral model of the zeros is a
finite-rank perturbation of an archimedean reference with counting function `M`; together with the
non-integrability of `S`, trace-class perturbations are excluded as well.
-/

open Complex MeasureTheory Real Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower _root_.RHTower.Littlewood

/-- A bound for `|S|` at large heights extends to `[1, ∞)`: on `[1, T₀]` the count is monotone and
the smooth term continuous. -/
theorem exists_abs_rvmRemainder_le_on_Ici_one {B T₀ : ℝ} (h : ∀ T, T₀ ≤ T → |rvmRemainder T| ≤ B) :
    ∃ B' : ℝ, 0 ≤ B' ∧ ∀ t, 1 ≤ t → |rvmRemainder t| ≤ B' := by
  set T₁ := max T₀ 1 with hT₁
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (continuousOn_routeKSmoothRVMCount.mono fun t (ht : t ∈ Icc 1 T₁) =>
      (show (0 : ℝ) < t by linarith [ht.1]))
  refine ⟨max (max B 0) (zeroCountReal T₁ + K), le_max_of_le_left (le_max_right _ _),
    fun t ht => ?_⟩
  rcases le_or_gt T₁ t with htT | htT
  · exact (h t (le_trans (le_max_left _ _) htT)).trans (le_max_of_le_left (le_max_left _ _))
  · refine le_max_of_le_right ?_
    have hN0 : 0 ≤ zeroCountReal t := by
      unfold zeroCountReal; exact_mod_cast xiZeroCount_nonneg t
    have hN1 : zeroCountReal t ≤ zeroCountReal T₁ := zeroCountReal_mono htT.le
    have hM := hK t ⟨ht, htT.le⟩
    rw [Real.norm_eq_abs] at hM
    calc |rvmRemainder t| = |zeroCountReal t - routeKSmoothRVMCount t| := rfl
      _ ≤ |zeroCountReal t| + |routeKSmoothRVMCount t| := abs_sub _ _
      _ ≤ zeroCountReal T₁ + K := by rw [abs_of_nonneg hN0]; linarith

section Window

variable {ℓ : ℝ} (hℓ : 0 < ℓ)
include hℓ

theorem integrable_psiDeriv : Integrable (psiDeriv ℓ) := by
  obtain ⟨C, hC, hd⟩ := exists_psi_decay hℓ
  refine (integrable_inv_one_add_sq.const_mul C).mono'
    (continuous_psiDeriv hℓ).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (hd y).2.trans ?_
  rw [div_eq_mul_one_div]
  exact mul_le_mul_of_nonneg_left
    ((one_div_pow_four_le_pow_three y).trans (one_div_pow_three_le_inv_one_add_sq y)) hC

/-- A bound `|S| ≤ B` on `[1, ∞)` caps the smoothed remainder by `B ∫|ψ_ℓ'| = B ℓ² ∫|ψ_1'|`. -/
theorem abs_integral_rvmRemainder_mul_psiDeriv_le {B T : ℝ} (hB : ∀ t, 1 ≤ t → |rvmRemainder t| ≤ B)
    (hT : 1 ≤ T) :
    |∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T)| ≤
      B * (ℓ ^ 2 * ∫ y, |psiDeriv 1 y|) := by
  have h12 : (1 : ℝ) ≤ 2 * T := by linarith
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 1 le_rfl)
  have hint : Integrable fun t => |psiDeriv ℓ (t - T)| :=
    ((integrable_psiDeriv hℓ).comp_sub_right T).abs
  have h1 := intervalIntegral.norm_integral_le_of_norm_le h12
    (g := fun t => B * |psiDeriv ℓ (t - T)|)
    (Eventually.of_forall fun t ht => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul_of_nonneg_right (hB t ht.1.le) (abs_nonneg _))
    ((hint.const_mul B).intervalIntegrable)
  rw [Real.norm_eq_abs] at h1
  refine h1.trans ?_
  rw [intervalIntegral.integral_const_mul, ← integral_abs_psiDeriv_eq hℓ]
  refine mul_le_mul_of_nonneg_left ?_ hB0
  rw [intervalIntegral.integral_of_le h12,
    ← integral_sub_right_eq_self (fun y => |psiDeriv ℓ y|) T]
  exact setIntegral_le_integral hint (Eventually.of_forall fun _ => abs_nonneg _)

end Window

/-- **`S(T)` is unbounded.**  For every `B` and `T₀` there is `T ≥ T₀` with `|S(T)| > B`. -/
theorem rvmRemainder_unbounded (B T₀ : ℝ) : ∃ T, T₀ ≤ T ∧ B < |rvmRemainder T| := by
  by_contra hcon
  push Not at hcon
  obtain ⟨B', hB'0, hB'⟩ := exists_abs_rvmRemainder_le_on_Ici_one hcon
  set X := ∫ y, |psiDeriv 1 y| with hX
  have hX0 : 0 ≤ X := integral_nonneg fun _ => abs_nonneg _
  -- the aperture
  obtain ⟨ℓ, hgain, hℓ1⟩ := ((eventually_mul_sq_lt_windowPhaseObservable_one (B' * X + 3)).and
    (eventually_gt_atTop 1)).exists
  have hℓ : 0 < ℓ := by linarith
  set G := B' * (ℓ ^ 2 * X) + 2 with hG
  have hGlt : G < windowPhaseObservable ℓ 1 := by
    have : 2 < 3 * ℓ ^ 2 := by nlinarith
    calc G = B' * X * ℓ ^ 2 + 2 := by rw [hG]; ring
      _ < (B' * X + 3) * ℓ ^ 2 := by nlinarith
      _ < windowPhaseObservable ℓ 1 := hgain
  -- Kronecker visits, sparse bad heights, and the asymptotic identity
  obtain ⟨c, hc, hvis⟩ := exists_eventually_volume_windowPrime_gt hGlt
  have hsparse := eventually_exists_sparse_windowExcludedHeights hℓ (ε := c / 2) (η := 1 / 2)
    (by positivity) (by norm_num)
  obtain ⟨T₂, hT₂⟩ := eventually_atTop.mp ((tendsto_windowPrime_add_offLineCorrection_sub hℓ).eventually
    (Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)))
  obtain ⟨U, hUvis, ⟨Bad, hBadm, hBadvol, hBad⟩, hUT, hU0⟩ := (hvis.and (hsparse.and
    ((eventually_ge_atTop (4 * max T₂ 1)).and (eventually_gt_atTop 0)))).exists
  -- a Kronecker height outside the bad set
  obtain ⟨T, ⟨hTV, hTI⟩, hTB⟩ : ∃ T, T ∈ {T | G < windowPrime ℓ T} ∩ Icc (U / 4) (U / 2) ∧
      T ∉ Bad := by
    by_contra hall
    push Not at hall
    have hsub : {T | G < windowPrime ℓ T} ∩ Icc (U / 4) (U / 2) ⊆ Bad := fun T hT => hall T hT
    have hlt : ENNReal.ofReal (c / 2 * U) < ENNReal.ofReal (c * U) :=
      (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr (by nlinarith)
    exact absurd ((hUvis.trans (measure_mono hsub)).trans hBadvol) (not_le.mpr hlt)
  have hTU : max T₂ 1 ≤ T := by linarith [hTI.1]
  have hT1 : 1 ≤ T := le_trans (le_max_right _ _) hTU
  have hid := (hT₂ T (le_trans (le_max_left _ _) hTU)).2
  have hcorr := hBad T hTI hTB
  have hint := abs_integral_rvmRemainder_mul_psiDeriv_le hℓ hB' hT1
  have hTV' : G < windowPrime ℓ T := hTV
  have h1 := le_abs_self (∫ t in (1 : ℝ)..(2 * T), rvmRemainder t * psiDeriv ℓ (t - T))
  have h2 := neg_abs_le (offLineCorrection ℓ T)
  linarith

/-- `|S(T)|` is not bounded at infinity. -/
theorem not_isBoundedUnder_abs_rvmRemainder :
    ¬ IsBoundedUnder (· ≤ ·) atTop (fun T => |rvmRemainder T|) := by
  rintro ⟨B, hB⟩
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hB
  obtain ⟨T, hT, hlt⟩ := rvmRemainder_unbounded B T₀
  exact absurd (hT₀ T hT) (not_le.mpr hlt)

end GaloisForLFunctions.SquareRootThreshold
