import GaloisForLFunctions.TransThresholdPairCorrelation.GridFourierMultiplier
import GaloisForLFunctions.RHTower.CauchyBetaIntegral
import Mathlib.Analysis.Fourier.Inversion

/-!
# The totient lower bound for every positivity test

A nonnegative integrable test whose Fourier transform is nonpositive outside
the unit band has positivity cost at least `1+3/π²`. The positive grid laws
supply this bound before taking their origin-mass limit. Thus the obstruction
applies to the full Fourier positivity class, not only squared-sinc tests.
-/

open Real Set MeasureTheory Filter Topology FourierTransform
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.TransThresholdPairCorrelation

private theorem fourier_zero_real (f : ℝ → ℝ) :
    𝓕 (fun x => (f x : ℂ)) 0 = ((∫ x : ℝ, f x : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul,
    integral_complex_ofReal]

private theorem fourier_real_norm_le (f : ℝ → ℝ) (ξ : ℝ) :
    ‖𝓕 (fun x => (f x : ℂ)) ξ‖ ≤ ∫ x : ℝ, ‖f x‖ := by
  have he (x : ℝ) : ‖Complex.exp ((-2 * π * x * ξ : ℝ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp
  rw [Real.fourier_real_eq_integral_exp_smul]
  simpa only [smul_eq_mul, norm_mul, he, one_mul, Complex.norm_real] using
    norm_integral_le_integral_norm (fun x : ℝ =>
      Complex.exp ((-2 * π * x * ξ : ℝ) * Complex.I) * (f x : ℂ))

private theorem fourier_real_pair_inversion {g h : ℝ → ℝ}
    (hgc : Continuous g) (hgi : Integrable g) (hhi : Integrable h)
    (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ)) (x : ℝ) :
    𝓕 (fun ξ => (h ξ : ℂ)) (-x) = (g x : ℂ) := by
  have he : 𝓕 (fun x => (g x : ℂ)) = fun ξ => (h ξ : ℂ) := funext hFT
  have hFi : Integrable (𝓕 (fun x => (g x : ℂ))) := by rw [he]; exact hhi.ofReal
  have hi := congrFun ((Complex.continuous_ofReal.comp hgc).fourierInv_fourier_eq hgi.ofReal hFi) x
  change 𝓕⁻ (𝓕 (fun x => (g x : ℂ))) x = (g x : ℂ) at hi
  rw [he, Real.fourierInv_eq_fourier_neg] at hi
  exact hi

private theorem integrable_mul_grid {h : ℝ → ℝ} (hhi : Integrable h)
    {m : ℕ} (hm : 0 < m) (L : ℕ) :
    Integrable (fun α => h α * gridPeriodicTriangle L m α) := by
  have hi : Integrable (fun α => gridPeriodicTriangle L m α * h α) := by
    apply hhi.bdd_mul (c := (L : ℝ))
    · exact (continuous_gridPeriodicTriangle hm L).aestronglyMeasurable
    · filter_upwards with α
      rw [Real.norm_eq_abs, abs_of_nonneg (gridPeriodicTriangle_nonneg L m α),
        gridPeriodicTriangle_eq_interpolation hm]
      have hcoeff (k : ℤ) : (if (m : ℤ) ∣ k then (1 : ℝ) else 0) ≤ 1 := by split_ifs <;> norm_num
      have hu := mul_le_mul_of_nonneg_left (integerHatInterpolation_le hcoeff ((L : ℝ) * α))
        (Nat.cast_nonneg (α := ℝ) L)
      simpa only [mul_one] using hu
  simpa only [mul_comm] using hi

/-- A nonnegative test sees at least the constant mode of each cyclic grid. -/
theorem grid_constant_mode_le_positive_test {g h : ℝ → ℝ}
    (hgc : Continuous g) (hgi : Integrable g) (hhi : Integrable h)
    (hg : ∀ x, 0 ≤ g x) (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ))
    {m : ℕ} (hm : 0 < m) (L : ℕ) :
    ((L : ℝ) / m) * g 0 ≤ ∫ α : ℝ, h α * gridPeriodicTriangle L m α := by
  let t : ℤ → ℝ := fun r => (L : ℝ) * gridSincWeight m r * g (gridFourierFrequency L m r)
  have ht (r : ℤ) : 0 ≤ t r :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg L) (gridSincWeight_nonneg m r)) (hg _)
  have hbound (x : ℝ) : g x ≤ ∫ ξ : ℝ, ‖h ξ‖ := by
    have hb := fourier_real_norm_le h (-x)
    rw [fourier_real_pair_inversion hgc hgi hhi hFT, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (hg x)] at hb
    exact hb
  have hs : Summable t := by
    apply Summable.of_nonneg_of_le ht (fun r => ?_)
      (((summable_gridSincWeight hm).mul_left (L : ℝ)).mul_right (∫ ξ : ℝ, ‖h ξ‖))
    exact mul_le_mul_of_nonneg_left (hbound _) (mul_nonneg (Nat.cast_nonneg L) (gridSincWeight_nonneg m r))
  have he : (∫ α : ℝ, h α * gridPeriodicTriangle L m α) = ∑' r : ℤ, t r := by
    apply Complex.ofReal_injective
    calc
      ((∫ α : ℝ, h α * gridPeriodicTriangle L m α : ℝ) : ℂ) =
          𝓕 (fun α => (gridPeriodicTriangle L m α : ℂ) * (h α : ℂ)) 0 := by
        rw [Real.fourier_real_eq_integral_exp_smul]
        simp only [mul_zero, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_smul]
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        filter_upwards with α
        push_cast
        ring
      _ = _ := by
        rw [fourier_mul_gridPeriodicTriangle (f := fun α => (h α : ℂ)) hm L hhi.ofReal,
          Complex.ofReal_tsum]
        apply tsum_congr
        intro r
        rw [zero_sub, fourier_real_pair_inversion hgc hgi hhi hFT]
        dsimp only [t]
        push_cast
        ring
  rw [he]
  have hz : t 0 = ((L : ℝ) / m) * g 0 := by
    simp only [t, gridSincWeight_zero, gridFourierFrequency, Int.cast_zero, mul_zero]
    ring
  rw [← hz]
  exact hs.le_tsum 0 (fun r _ => ht r)

/-- The removed central triangle costs no more than the test's total mass. -/
theorem central_triangle_test_le_mass {g h : ℝ → ℝ}
    (hgi : Integrable g) (hg : ∀ x, 0 ≤ g x)
    (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ))
    {L : ℕ} (hL : 0 < L) :
    (∫ α : ℝ, h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α))) ≤ h 0 := by
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  let C : ℝ → ℂ := fun α => (((L : ℝ) * triangleFn 1 ((L : ℝ) * α) : ℝ) : ℂ)
  have hC : C = fun α => (L : ℂ) * (triangleFn (1 / (L : ℝ)) α : ℂ) := by
    funext α
    simp only [C, triangleFn_one_mul hLR, Complex.ofReal_mul, Complex.ofReal_natCast]
  have hCi : Integrable C := by
    have ht : Integrable (triangleFn (1 / (L : ℝ))) := by
      simpa only [sub_zero] using integrable_triangleFn_sub (one_div_pos.mpr hLR) 0
    rw [hC]
    exact ht.ofReal.const_mul _
  have hCF (x : ℝ) : 𝓕 C x = ((sinc (π * (1 / (L : ℝ)) * x) ^ 2 : ℝ) : ℂ) := by
    rw [hC, fourierIntegral_const_mul, fourier_triangleFn (one_div_pos.mpr hLR)]
    simp only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
    have hLC : (L : ℂ) ≠ 0 := by exact_mod_cast hL.ne'
    field_simp
  have hp := GaloisForLFunctions.RHTower.Kuznetsov.integral_fourier_mul_eq
    (fun x => (g x : ℂ)) C hgi.ofReal hCi
  have hpair : (∫ α : ℝ, h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α))) =
      ∫ x : ℝ, g x * sinc (π * (1 / (L : ℝ)) * x) ^ 2 := by
    apply Complex.ofReal_injective
    calc
      ((∫ α : ℝ, h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) : ℝ) : ℂ) =
          ∫ α : ℝ, 𝓕 (fun x => (g x : ℂ)) α * C α := by
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        filter_upwards with α
        rw [hFT]
        simp only [C, Complex.ofReal_mul]
      _ = ∫ x : ℝ, (g x : ℂ) * 𝓕 C x := hp
      _ = _ := by
        rw [← integral_complex_ofReal]
        apply integral_congr_ae
        filter_upwards with x
        rw [hCF, Complex.ofReal_mul]
  have hpi : Integrable (fun x => g x * sinc (π * (1 / (L : ℝ)) * x) ^ 2) := by
    have hi : Integrable (fun x => sinc (π * (1 / (L : ℝ)) * x) ^ 2 * g x) := by
      apply hgi.bdd_mul (c := 1)
      · exact (by fun_prop : Continuous (fun x : ℝ => sinc (π * (1 / (L : ℝ)) * x) ^ 2)).aestronglyMeasurable
      · filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact (sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one _)
    simpa only [mul_comm] using hi
  have hm : (∫ x : ℝ, g x) = h 0 := by
    have h := hFT 0
    rw [fourier_zero_real] at h
    exact Complex.ofReal_injective h
  rw [hpair, ← hm]
  apply integral_mono hpi hgi
  intro x
  have hb := mul_le_mul_of_nonneg_left
    ((sq_le_one_iff_abs_le_one _).mpr (abs_sinc_le_one (π * (1 / (L : ℝ)) * x))) (hg x)
  simpa only [mul_one] using hb

private theorem integrable_mul_totientGridFormFactor {h : ℝ → ℝ} (hhi : Integrable h)
    {L : ℕ} (hL : 1 ≤ L) : Integrable (fun α => h α * totientGridFormFactor L α) := by
  have hi : Integrable (fun α => totientGridFormFactor L α * h α) := by
    apply hhi.bdd_mul (c := (L : ℝ))
    · exact (continuous_totientGridFormFactor L).aestronglyMeasurable
    · filter_upwards with α
      rw [Real.norm_eq_abs, abs_of_nonneg (totientGridFormFactor_nonneg hL α)]
      exact totientGridFormFactor_le hL α
  simpa only [mul_comm] using hi

/-- The exact grid law gives a lower bound for any nonnegative Fourier test. -/
theorem totientGridOriginMass_mul_le_test {g h : ℝ → ℝ}
    (hgc : Continuous g) (hgi : Integrable g) (hhi : Integrable h)
    (hg : ∀ x, 0 ≤ g x) (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ))
    {L : ℕ} (hL : 1 ≤ L) :
    totientGridOriginMass L * g 0 ≤ h 0 + ∫ α : ℝ, h α * totientGridFormFactor L α := by
  have hLpos : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hL
  have hLR : (0 : ℝ) < L := by exact_mod_cast hLpos
  have hi (m : ℕ) (hm : m ∈ Finset.Icc 1 L) :
      Integrable (fun α => totientGridWeight L m * (h α * gridPeriodicTriangle L m α)) :=
    (integrable_mul_grid hhi (Finset.mem_Icc.mp hm).1 L).const_mul _
  have hn : Integrable (fun α => totientGridRemainder L * (h α * gridPeriodicTriangle L (L + 1) α)) :=
    (integrable_mul_grid hhi (Nat.succ_pos L) L).const_mul _
  have hci : Integrable (fun α => h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α))) := by
    have hi : Integrable (fun α => ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) * h α) := by
      apply hhi.bdd_mul (c := (L : ℝ))
      · exact (continuous_const.mul ((continuous_triangleFn 1).comp
          (continuous_const.mul continuous_id))).aestronglyMeasurable
      · filter_upwards with α
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hLR.le (triangleFn_nonneg 1 _))]
        exact (mul_le_mul_of_nonneg_left (triangleFn_le_one one_pos _) hLR.le).trans_eq (mul_one _)
    simpa only [mul_comm] using hi
  have hsi := integrable_finsetSum (Finset.Icc 1 L) hi
  have hfun : (fun α => h α * totientGridFormFactor L α) = fun α =>
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * (h α * gridPeriodicTriangle L m α)) +
        totientGridRemainder L * (h α * gridPeriodicTriangle L (L + 1) α) -
        h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) := by
    funext α
    rw [totientGridFormFactor_eq_mixture, mul_sub, mul_add, Finset.mul_sum]
    congr 2
    · apply Finset.sum_congr rfl
      intro m hm
      ring
    · ring
  have hdecomp : (∫ α : ℝ, h α * totientGridFormFactor L α) =
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * ∫ α : ℝ, h α * gridPeriodicTriangle L m α) +
        totientGridRemainder L * (∫ α : ℝ, h α * gridPeriodicTriangle L (L + 1) α) -
        ∫ α : ℝ, h α * ((L : ℝ) * triangleFn 1 ((L : ℝ) * α)) := by
    rw [hfun]
    have hai : Integrable (fun α =>
        (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * (h α * gridPeriodicTriangle L m α)) +
        totientGridRemainder L * (h α * gridPeriodicTriangle L (L + 1) α)) := hsi.add hn
    rw [integral_sub hai hci, integral_add hsi hn, integral_finsetSum (Finset.Icc 1 L) hi]
    simp only [integral_const_mul]
  have hmain : totientGridOriginMass L * g 0 ≤
      (∑ m ∈ Finset.Icc 1 L, totientGridWeight L m * ∫ α : ℝ, h α * gridPeriodicTriangle L m α) +
        totientGridRemainder L * (∫ α : ℝ, h α * gridPeriodicTriangle L (L + 1) α) := by
    have hs := Finset.sum_le_sum (s := Finset.Icc 1 L) (fun m hm =>
      mul_le_mul_of_nonneg_left
        (grid_constant_mode_le_positive_test hgc hgi hhi hg hFT (Finset.mem_Icc.mp hm).1 L)
        (totientGridWeight_nonneg L m))
    have hn := mul_le_mul_of_nonneg_left
      (grid_constant_mode_le_positive_test hgc hgi hhi hg hFT (Nat.succ_pos L) L)
      (totientGridRemainder_nonneg hL)
    rw [totientGridOriginMass_eq_weighted_modes hLpos, add_mul, Finset.sum_mul]
    simpa only [Nat.cast_succ, Nat.succ_eq_add_one, mul_assoc, mul_left_comm, mul_comm] using add_le_add hs hn
  have hc := central_triangle_test_le_mass hgi hg hFT hLpos
  linarith only [hmain, hdecomp, hc]

/-- A nonpositive Fourier tail discards all contributions beyond the prescribed unit band. -/
theorem totientGrid_test_le_unit_band {h : ℝ → ℝ} (hhi : Integrable h)
    (htail : ∀ α, 1 ≤ |α| → h α ≤ 0) {L : ℕ} (hL : 1 ≤ L) :
    (∫ α : ℝ, h α * totientGridFormFactor L α) ≤
      ∫ α in Icc (-1 : ℝ) 1, h α * |α| := by
  have hi := integrable_mul_totientGridFormFactor hhi hL
  have hineq : (∫ α : ℝ, h α * totientGridFormFactor L α) ≤
      ∫ α : ℝ, (Icc (-1 : ℝ) 1).indicator (fun α => h α * totientGridFormFactor L α) α := by
    apply integral_mono hi (hi.indicator measurableSet_Icc)
    intro α
    by_cases ha : α ∈ Icc (-1 : ℝ) 1
    · rw [Set.indicator_of_mem ha]
    · rw [Set.indicator_of_notMem ha]
      have habs : 1 ≤ |α| := by
        by_contra hn
        have hh := abs_le.mp (le_of_lt (lt_of_not_ge hn))
        exact ha hh
      exact mul_nonpos_of_nonpos_of_nonneg (htail α habs) (totientGridFormFactor_nonneg hL α)
  rw [integral_indicator measurableSet_Icc] at hineq
  have he : (∫ α in Icc (-1 : ℝ) 1, h α * totientGridFormFactor L α) =
      ∫ α in Icc (-1 : ℝ) 1, h α * |α| := by
    apply setIntegral_congr_fun measurableSet_Icc
    intro α hα
    change h α * totientGridFormFactor L α = h α * |α|
    rw [totientGridFormFactor_eq_abs hL (abs_le.mpr hα)]
  exact hineq.trans_eq he

/-- Every admissible positivity test costs at least the limiting totient origin mass. -/
theorem positivity_test_cost_ge_totient_limit {g h : ℝ → ℝ}
    (hgc : Continuous g) (hgi : Integrable g) (hhi : Integrable h)
    (hg : ∀ x, 0 ≤ g x) (hg0 : 0 < g 0)
    (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ))
    (htail : ∀ α, 1 ≤ |α| → h α ≤ 0) :
    1 + 3 / π ^ 2 ≤ (h 0 + ∫ α in Icc (-1 : ℝ) 1, h α * |α|) / g 0 := by
  apply (le_div_iff₀ hg0).mpr
  have hlim := tendsto_totientGridOriginMass.mul_const (g 0)
  apply le_of_tendsto hlim
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with L hL
  exact (totientGridOriginMass_mul_le_test hgc hgi hhi hg hFT hL).trans
    (add_le_add (le_refl (h 0)) (totientGrid_test_le_unit_band hhi htail hL))

/-- The full Fourier positivity class cannot certify seventy percent. -/
theorem positivity_test_cost_gt_thirteen_tenths {g h : ℝ → ℝ}
    (hgc : Continuous g) (hgi : Integrable g) (hhi : Integrable h)
    (hg : ∀ x, 0 ≤ g x) (hg0 : 0 < g 0)
    (hFT : ∀ ξ, 𝓕 (fun x => (g x : ℂ)) ξ = (h ξ : ℂ))
    (htail : ∀ α, 1 ≤ |α| → h α ≤ 0) :
    (13 : ℝ) / 10 < (h 0 + ∫ α in Icc (-1 : ℝ) 1, h α * |α|) / g 0 := by
  have hπ : π ^ 2 < 10 := by nlinarith only [pi_lt_d2, pi_pos]
  have hπ0 : 0 < π ^ 2 := sq_pos_of_pos pi_pos
  have hfrac : (3 : ℝ) / 10 < 3 / π ^ 2 := by
    apply (lt_div_iff₀ hπ0).mpr
    nlinarith only [hπ]
  have hbound := positivity_test_cost_ge_totient_limit hgc hgi hhi hg hg0 hFT htail
  linarith only [hfrac, hbound]

end GaloisForLFunctions.TransThresholdPairCorrelation
