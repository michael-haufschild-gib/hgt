import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaKernelHasAFourteenthOrderPolynomialLowerBound
import GaloisForLFunctions.WindowTowerOfSpecZ.TheGammaRemainderRetainsHigherLagsThroughRadiusTwo
import GaloisForLFunctions.LatticeSectionTheory.WindowJumpCounts.TheQuarticLagDeficitRetainsAMassReserve
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheTrivialApertureAndTheExceptionalSquare

/-!
# The Gamma reserve from the full quartic lag deficit

The degree-fourteen reciprocal bounds retain larger cubic and quartic weights
through radius `11/10`. The disjoint half-windows pay the cubic weight;
the first five Legendre moments pay the quartic weight on the entire window.
-/

noncomputable section
open Real MeasureTheory Set Filter Topology
open _root_.RHTower _root_.RHTower.ArchimedeanAnomaly
open _root_.RHTower.WeilLevyPoleGauss _root_.RHTower.WeilMarkovPole
namespace GaloisForLFunctions.WindowTowerOfSpecZ
open ArithmeticCriticalityTheory BiScaleUncertainty LatticeSectionTheory

private theorem sharper_hyperbolic_lower {z : ℝ} (h0 : 0 < z) (h1 : z ≤ 11 / 20) :
    1 - z ^ 2 / 6 + z ^ 4 / 54 ≤ z / Real.sinh z ∧
      1 - z ^ 2 / 2 + (2 / 11) * z ^ 4 ≤ 1 / Real.cosh z := by
  have hL := gamma_reciprocal_polynomials14_lower h0 (by linarith only [h1])
  have hp (n : ℕ) : z ^ n ≤ (11 / 20 : ℝ) ^ n := pow_le_pow_left₀ h0.le h1 n
  have hs : 0 ≤ 7 / 360 - 1 / 54 - (31 / 15120) * z ^ 2 +
      (127 / 604800) * z ^ 4 - (73 / 3421440) * z ^ 6 +
        (1414477 / 653837184000) * z ^ 8 - (8191 / 37362124800) * z ^ 10 := by
    linarith only [hp 2, hp 6, hp 10, pow_nonneg h0.le 4, pow_nonneg h0.le 8]
  have hc : 0 ≤ 5 / 24 - 2 / 11 - (61 / 720) * z ^ 2 +
      (1385 / 40320) * z ^ 4 - (50521 / 3628800) * z ^ 6 +
        (2702765 / 479001600) * z ^ 8 - (199360981 / 87178291200) * z ^ 10 := by
    linarith only [hp 2, hp 6, hp 10, pow_nonneg h0.le 4, pow_nonneg h0.le 8]
  constructor
  · apply le_trans _ hL.1
    have h := mul_nonneg (pow_nonneg h0.le 4) hs
    dsimp only [gammaSinhPolynomial14]
    nlinarith only [h]
  · apply le_trans _ hL.2
    have h := mul_nonneg (pow_nonneg h0.le 4) hc
    dsimp only [gammaCoshPolynomial14]
    nlinarith only [h]

/-- Near the prime-three boundary the Gamma remainder retains larger positive lag weights. -/
theorem retainedGammaRemainderWeight_ge_sharper_lags {t : ℝ}
    (ht : t ∈ Ioc (0 : ℝ) (11 / 10)) :
    t ^ 3 / 864 + t ^ 4 / 176 ≤ retainedGammaRemainderWeight t := by
  obtain ⟨hs, hc⟩ := sharper_hyperbolic_lower
    (z := t / 2) (by linarith only [ht.1]) (by linarith only [ht.2])
  have hden : Real.sinh (t / 2) ≠ 0 :=
    (Real.sinh_pos_iff.mpr (by linarith only [ht.1])).ne'
  have he : archLevySinhWeight t =
      1 / (2 * Real.sinh (t / 2)) + 1 / (2 * Real.cosh (t / 2)) := by
    rw [archLevySinhWeight, exp_half_div_sinh_eq ht.1,
      archLevyDensity_eq_inv_sinh_add_inv_cosh ht.1]
    ring
  have hm := mul_le_mul_of_nonneg_left hs (le_of_lt (one_div_pos.mpr ht.1))
  have heq : 1 / t * ((t / 2) / Real.sinh (t / 2)) = 1 / (2 * Real.sinh (t / 2)) := by
    field_simp [ht.1.ne', hden]
  rw [heq] at hm
  unfold retainedGammaRemainderWeight
  rw [he]
  have hp : 1 / t * (1 - (t / 2) ^ 2 / 6 + (t / 2) ^ 4 / 54) +
      (1 - (t / 2) ^ 2 / 2 + (2 / 11) * (t / 2) ^ 4) / 2 =
      1 / t + 1 / 2 - t / 24 - t ^ 2 / 16 + t ^ 3 / 864 + t ^ 4 / 176 := by
    field_simp [ht.1.ne']
    ring
  have hcHalf := mul_le_mul_of_nonneg_left hc (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hcEq : (1 / 2 : ℝ) * (1 / Real.cosh (t / 2)) = 1 / (2 * Real.cosh (t / 2)) := by ring
  rw [hcEq] at hcHalf
  linarith only [hm, hcHalf, hp]

private theorem cubic_lag_deficit_ge_half_window {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {a : ℝ} (ha : 0 < a)
    (hs : tsupport F ⊆ Icc (-a) a) :
    (15 / 8) * a ^ 4 * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), t ^ 3 * (autocorr F 0 - autocorr F t) := by
  let M := ∫ x, F x ^ 2
  let D := fun t => autocorr F 0 - autocorr F t
  have hM : 0 ≤ M := integral_nonneg fun x => sq_nonneg (F x)
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hD : Continuous D := continuous_const.sub hc
  have hnonneg (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hi {l u : ℝ} : IntegrableOn (fun t : ℝ => t ^ 3 * D t) (Ioc l u) :=
    ((continuous_pow 3).mul hD).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hn : 0 ≤ ∫ t in Ioc (0 : ℝ) a, t ^ 3 * D t := by
    apply setIntegral_nonneg measurableSet_Ioc
    intro t ht
    exact mul_nonneg (pow_nonneg ht.1.le 3) (hnonneg t)
  have hhalf (t : ℝ) (ht : a < t) : M / 2 ≤ D t := by
    have h := AbsoluteGeometryOfSpecZ.two_mul_abs_packetAutocorr_le_of_aperture
      hF.continuous hcs (c := 0) ht.le (fun x hx => by
        apply image_eq_zero_of_notMem_tsupport
        intro hxs
        have hb := hs hxs
        simp only [sub_zero] at hx
        exact (not_lt_of_ge (abs_le.mpr hb)) hx)
    change 2 * |autocorr F t| ≤ M at h
    dsimp only [D]
    rw [LatticeSectionTheory.autocorr_zero_eq]
    linarith only [h, le_abs_self (autocorr F t)]
  have hp : IntegrableOn (fun t : ℝ => t ^ 3 * (M / 2)) (Ioc a (2 * a)) :=
    ((continuous_pow 3).mul continuous_const).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbound : (∫ t in Ioc a (2 * a), t ^ 3 * (M / 2)) ≤
      ∫ t in Ioc a (2 * a), t ^ 3 * D t := by
    apply setIntegral_mono_on hp hi measurableSet_Ioc
    intro t ht
    exact mul_le_mul_of_nonneg_left (hhalf t ht.1) (pow_nonneg (ha.trans ht.1).le 3)
  have he : (∫ t in Ioc a (2 * a), t ^ 3 * (M / 2)) =
      (15 / 8) * a ^ 4 * M := by
    rw [← intervalIntegral.integral_of_le (by linarith only [ha] : a ≤ 2 * a),
      intervalIntegral.integral_mul_const, integral_pow]
    norm_num
    ring
  rw [he] at hbound
  have hu : Ioc (0 : ℝ) a ∪ Ioc a (2 * a) = Ioc (0 : ℝ) (2 * a) := by
    ext t
    simp only [mem_union, mem_Ioc]
    constructor
    · rintro (⟨ht0, hta⟩ | ⟨hta, ht2⟩)
      · exact ⟨ht0, by linarith only [hta, ha]⟩
      · exact ⟨ha.trans hta, ht2⟩
    · rintro ⟨ht0, ht2⟩
      rcases le_or_gt t a with ht | ht
      · exact Or.inl ⟨ht0, ht⟩
      · exact Or.inr ⟨ht, ht2⟩
  have hadd := setIntegral_union
    (s := Ioc (0 : ℝ) a) (t := Ioc a (2 * a))
    (Set.disjoint_left.mpr (fun t ht ht' => not_lt_of_ge ht.2 ht'.1))
    measurableSet_Ioc hi hi
  rw [hu] at hadd
  change (15 / 8) * a ^ 4 * M ≤ ∫ t in Ioc (0 : ℝ) (2 * a), t ^ 3 * D t
  linarith only [hn, hbound, hadd]

private theorem local_gamma_remainder_ge_cubic_and_quartic {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) (hcs : HasCompactSupport F) {a : ℝ}
    (ha : 2 * a ≤ 11 / 10) :
    (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 3 * (autocorr F 0 - autocorr F t)) / 864 +
      (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * (autocorr F 0 - autocorr F t)) / 176 ≤
        ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t *
          (autocorr F 0 - autocorr F t) := by
  let D := fun t => autocorr F 0 - autocorr F t
  have hc := _root_.RHTower.ArchimedeanExactForm.continuous_autocorr hF hcs
  have hD : Continuous D := continuous_const.sub hc
  have hnonneg (t : ℝ) : 0 ≤ D t := sub_nonneg.mpr
    ((le_abs_self _).trans (abs_autocorr_le_zero hcs hF.continuous t))
  have hiR := (local_gamma_terms_integrable_to_two hF hcs).2.mono_set
    (show Ioc (0 : ℝ) (2 * a) ⊆ Ioc (0 : ℝ) 2 from
      fun t ht => ⟨ht.1, by linarith only [ht.2, ha]⟩)
  have hi3 : IntegrableOn (fun t : ℝ => t ^ 3 * D t / 864) (Ioc 0 (2 * a)) :=
    (((continuous_pow 3).mul hD).div_const _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi4 : IntegrableOn (fun t : ℝ => t ^ 4 * D t / 176) (Ioc 0 (2 * a)) :=
    (((continuous_pow 4).mul hD).div_const _).integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hbound : (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 3 * D t / 864 + t ^ 4 * D t / 176) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t * D t := by
    apply setIntegral_mono_on (hi3.add hi4) hiR measurableSet_Ioc
    intro t ht
    change t ^ 3 * D t / 864 + t ^ 4 * D t / 176 ≤
      retainedGammaRemainderWeight t * D t
    have h := mul_le_mul_of_nonneg_right
      (retainedGammaRemainderWeight_ge_sharper_lags ⟨ht.1, ht.2.trans ha⟩) (hnonneg t)
    convert h using 1 <;> ring
  rw [integral_add hi3 hi4, integral_div, integral_div] at hbound
  exact hbound

/-- Retaining the full quartic deficit preserves its exact low-moment charges. -/
theorem local_gamma_remainder_ge_fourth_deficit {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) {a : ℝ} (ha : 0 < a) (ha1 : 2 * a ≤ 11 / 10)
    (hs : tsupport F ⊆ Icc (-a) a) :
    (5 * a ^ 4 / 2304) * (∫ x, F x ^ 2) +
      (∫ t in Ioc (0 : ℝ) (2 * a), t ^ 4 * (autocorr F 0 - autocorr F t)) / 176 ≤
        ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t *
          (autocorr F 0 - autocorr F t) := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have h3 := cubic_lag_deficit_ge_half_window hF hcs ha hs
  have hR := local_gamma_remainder_ge_cubic_and_quartic hF hcs ha1
  linarith only [h3, hR]

/-- The cubic half-window reserve and full quartic reserve combine into an explicit Gamma floor. -/
theorem local_gamma_remainder_ge_quartic_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) {a : ℝ} (ha : 0 < a) (ha1 : 2 * a ≤ 11 / 10)
    (hs : tsupport F ⊆ Icc (-a) a) :
    (5 * a ^ 4 / 2304 + 47 * a ^ 5 / 1760) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t) := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have h3 := cubic_lag_deficit_ge_half_window hF hcs ha hs
  have h4 := quartic_lag_deficit_ge_mass hF ha hs
  have hR := local_gamma_remainder_ge_cubic_and_quartic hF hcs ha1
  linarith only [h3, h4, hR]

/-- Odd sources retain the stronger quartic reserve in the Gamma comparison. -/
theorem local_gamma_remainder_ge_odd_quartic_reserve {F : ℝ → ℝ}
    (hF : ContDiff ℝ 2 F) {a : ℝ} (ha : 0 < a) (ha1 : 2 * a ≤ 11 / 10)
    (hs : tsupport F ⊆ Icc (-a) a) (ho : ∀ x, F (-x) = -F x) :
    (5 * a ^ 4 / 2304 + 63 * a ^ 5 / 1760) * (∫ x, F x ^ 2) ≤
      ∫ t in Ioc (0 : ℝ) (2 * a), retainedGammaRemainderWeight t *
        (autocorr F 0 - autocorr F t) := by
  have hcs : HasCompactSupport F :=
    isCompact_Icc.of_isClosed_subset (isClosed_tsupport F) hs
  have h3 := cubic_lag_deficit_ge_half_window hF hcs ha hs
  have h4 := odd_quartic_lag_deficit_ge_mass hF ha hs ho
  have hR := local_gamma_remainder_ge_cubic_and_quartic hF hcs ha1
  linarith only [h3, h4, hR]

end GaloisForLFunctions.WindowTowerOfSpecZ

#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.retainedGammaRemainderWeight_ge_sharper_lags
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_ge_fourth_deficit
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_ge_quartic_reserve
#print axioms GaloisForLFunctions.WindowTowerOfSpecZ.local_gamma_remainder_ge_odd_quartic_reserve
