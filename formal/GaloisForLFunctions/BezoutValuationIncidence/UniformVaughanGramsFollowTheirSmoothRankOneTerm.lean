import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicRemaindersInAllVaughanRows
import GaloisForLFunctions.BezoutValuationIncidence.PronicGramErrorsAroundASmoothRankOneTerm

/-!
The centered Vaughan Gram has a uniform smooth rank-one asymptotic below half
damping. Logarithmic row bounds control the mixed pairings for arbitrary cutoffs;
independently diverging horizons and cutoff products give zero normalized Gram.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

private theorem abs_vaughan_smooth_coefficient_le (ε : ℝ) (U V : ℕ) (i : Fin 5) :
    |subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      pmPronicVaughanSmoothSigns i| ≤ |subHalfZetaCoeff ε| := by
  have hs : |pmPronicVaughanSmoothSigns i| ≤ 1 := by
    fin_cases i <;> norm_num [pmPronicVaughanSmoothSigns]
  have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
    rw [abs_mul]
    simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
      (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
  have hK : |subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤
      |subHalfZetaCoeff ε| := by
    rw [mul_assoc, abs_mul]
    exact mul_le_of_le_one_right (abs_nonneg _) hcoeff
  rw [abs_mul]
  exact (mul_le_of_le_one_right (abs_nonneg _) hs).trans hK

/-- The complete centered Vaughan Gram follows its smooth rank-one term with every uniform logarithmic rate. -/
theorem exists_uniform_pmPronicVaughanCentredGram_smooth_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram ε U V T i j -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j *
            (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)| ≤
        C * (T : ℝ) ^ (1 - 2 * ε) / Real.log (T : ℝ) ^ q := by
  let β : ℝ := 1 - 2 * ε
  let c : ℝ := |subHalfZetaCoeff ε|
  let H : ℝ := Real.sqrt (1 + 1 / β)
  have hβ : 0 < β := by dsimp only [β]; linarith only [hε2]
  have hc : 0 ≤ c := abs_nonneg _
  have hH : 0 ≤ H := Real.sqrt_nonneg _
  obtain ⟨B, hB, hR⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_log_rate hε hε2 q
  obtain ⟨D, hD, herror⟩ := exists_smooth_power_pronicEnergy_bounded_error hε hε2
  have hloglim : Tendsto (fun T : ℕ => Real.log (T : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨2 * c * H * B + B ^ 2 + c ^ 2 * D, by positivity, ?_⟩
  filter_upwards [hR, eventually_log_pow_le_sqrt_rpow q hβ,
    hloglim.eventually_ge_atTop 1, eventually_ge_atTop 1] with T hRT hlogP hlog hT U V i j
  let P : ℝ := (T : ℝ) ^ β
  let L : ℝ := Real.log (T : ℝ) ^ q
  let h : ℕ → ℝ := fun n => (n : ℝ) ^ (1 - ε)
  let r : Fin 5 → ℕ → ℝ := fun k n => pmPronicVaughanSmoothRemainder ε U V n k
  let a : Fin 5 → ℝ := fun k =>
    subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      pmPronicVaughanSmoothSigns k
  have hP1 : 1 ≤ P := Real.one_le_rpow (by exact_mod_cast hT) hβ.le
  have hP : 0 ≤ P := zero_le_one.trans hP1
  have hL1 : 1 ≤ L := one_le_pow₀ hlog
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hsqrt : Real.sqrt P ^ 2 = P := Real.sq_sqrt hP
  have hLP : L ≤ P := hlogP.trans (Real.sqrt_le_iff.mpr ⟨hP, by
    simpa only [mul_one, pow_two] using mul_le_mul_of_nonneg_left hP1 hP⟩)
  have ha (k : Fin 5) : |a k| ≤ c := abs_vaughan_smooth_coefficient_le ε U V k
  have hnorm : pronicNorm h T ≤ H * Real.sqrt P := pronicNorm_smooth_power_le hε hε2 hT
  have hr (k : Fin 5) : pronicNorm (r k) T ≤ B * Real.sqrt P / L := hRT U V k
  have hr' (k : Fin 5) : pronicNorm (r k) T ≤ B * Real.sqrt P :=
    (hr k).trans (div_le_self (by positivity) hL1)
  have hGram : pmPronicVaughanCentredGram ε U V T i j =
      ∑ n ∈ Icc 1 T, (a i * h n + r i n) * (a j * h n + r j n) /
        ((n : ℝ) * ((n : ℝ) + 1)) := by
    unfold pmPronicVaughanCentredGram
    apply sum_congr rfl
    intro n _hn
    simp only [a, h, r, pmPronicVaughanSmoothRemainder, pronicSeq, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    ring
  have hpair := abs_pronicGram_sub_rankOne_le (a i) (a j) h (r i) (r j) T
  rw [← hGram] at hpair
  have hmixed (k l : Fin 5) :
      |a k| * pronicNorm h T * pronicNorm (r l) T ≤ c * H * B * P / L := by
    calc
      _ ≤ (c * (H * Real.sqrt P)) * (B * Real.sqrt P / L) :=
        mul_le_mul (mul_le_mul (ha k) hnorm (pronicNorm_nonneg _ _) hc)
          (hr l) (pronicNorm_nonneg _ _) (by positivity)
      _ = _ := by
        rw [show (c * (H * Real.sqrt P)) * (B * Real.sqrt P / L) =
          c * H * B * Real.sqrt P ^ 2 / L by ring, hsqrt]
  have hres : pronicNorm (r i) T * pronicNorm (r j) T ≤ B ^ 2 * P / L := by
    calc
      _ ≤ (B * Real.sqrt P) * (B * Real.sqrt P / L) :=
        mul_le_mul (hr' i) (hr j) (pronicNorm_nonneg _ _) (by positivity)
      _ = _ := by
        rw [show (B * Real.sqrt P) * (B * Real.sqrt P / L) = B ^ 2 * Real.sqrt P ^ 2 / L by ring,
          hsqrt]
  have hmass : |a i * a j| ≤ c ^ 2 := by
    rw [abs_mul, pow_two]
    exact mul_le_mul (ha i) (ha j) (abs_nonneg _) hc
  have hsmooth : |a i * a j * (pronicNorm h T ^ 2 - P / β)| ≤ c ^ 2 * D * P / L := by
    rw [abs_mul]
    calc
      _ ≤ c ^ 2 * D := mul_le_mul hmass (herror T hT) (abs_nonneg _) (sq_nonneg c)
      _ ≤ _ := (le_div_iff₀ hL).mpr (mul_le_mul_of_nonneg_left hLP (by positivity))
  have heq : pmPronicVaughanCentredGram ε U V T i j - a i * a j * P / β =
      (pmPronicVaughanCentredGram ε U V T i j - a i * a j * pronicNorm h T ^ 2) +
        a i * a j * (pronicNorm h T ^ 2 - P / β) := by ring
  have hfinal : |pmPronicVaughanCentredGram ε U V T i j - a i * a j * P / β| ≤
      (2 * c * H * B + B ^ 2 + c ^ 2 * D) * P / L := by
    rw [heq]
    exact (abs_add_le _ _).trans ((add_le_add
      (hpair.trans (add_le_add (add_le_add (hmixed i j) (hmixed j i)) hres))
      hsmooth).trans_eq (by ring))
  have haa : a i * a j =
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j := by
    dsimp only [a]
    ring
  rw [haa] at hfinal
  exact hfinal

/-- Normalizing by the trivial power leaves a common logarithmic error for every Gram entry. -/
theorem exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε)| ≤
        C / Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, h⟩ := exists_uniform_pmPronicVaughanCentredGram_smooth_log_rate hε hε2 q
  refine ⟨C, hC, ?_⟩
  filter_upwards [h, eventually_ge_atTop 1] with T hT hT1 U V i j
  have hP : 0 < (T : ℝ) ^ (1 - 2 * ε) :=
    Real.rpow_pos_of_pos (by exact_mod_cast hT1) _
  have heq : pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε) =
      (pmPronicVaughanCentredGram ε U V T i j -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j *
            (T : ℝ) ^ (1 - 2 * ε) / (1 - 2 * ε)) / (T : ℝ) ^ (1 - 2 * ε) := by
    field_simp
  rw [heq, abs_div, abs_of_pos hP]
  exact (div_le_div_of_nonneg_right (hT U V i j) hP.le).trans_eq (by field_simp)

/-- Arbitrarily moving cutoffs retain the same smooth Gram asymptotic at a common horizon. -/
theorem tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (i j : Fin 5) :
    Tendsto (fun T : ℕ =>
      pmPronicVaughanCentredGram ε (U T) (V T) (H T) i j / (H T : ℝ) ^ (1 - 2 * ε) -
        (subHalfZetaCoeff ε * deningerHarmonicPartial (U T) * deningerHarmonicPartial (V T)) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε))
      atTop (𝓝 0) := by
  obtain ⟨C, _hC, h⟩ := exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate hε hε2 1
  have hlim : Tendsto (fun T : ℕ => C / Real.log (H T : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      ((Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).comp hH)
  apply squeeze_zero_norm' ?_ hlim
  filter_upwards [hH.eventually h] with T hT
  simpa only [Real.norm_eq_abs, pow_one] using hT (U T) (V T) i j

/-- Divergence of the horizon and cutoff product separately suffices for zero normalized centered Gram. -/
theorem tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hUV : Tendsto (fun T => U T * V T) atTop atTop)
    (i j : Fin 5) :
    Tendsto (fun T : ℕ => pmPronicVaughanCentredGram ε (U T) (V T) (H T) i j /
      (H T : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0) := by
  have hHzero : Tendsto deningerHarmonicPartial atTop (𝓝 0) := by
    simpa only [pow_zero, one_mul] using Sieve.tendsto_log_pow_mul_deningerHarmonicPartial_zero 0
  have hproduct := tendsto_mul_of_product_indices_atTop zero_le_one
    abs_deningerHarmonicPartial_le_one hHzero U V hUV
  have hsmooth : Tendsto (fun T : ℕ =>
      (subHalfZetaCoeff ε * deningerHarmonicPartial (U T) * deningerHarmonicPartial (V T)) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j / (1 - 2 * ε))
      atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0),
      zero_mul, zero_div] using
      ((((hproduct.const_mul (subHalfZetaCoeff ε)).pow 2).mul_const
        (pmPronicVaughanSmoothSigns i)).mul_const (pmPronicVaughanSmoothSigns j)).div_const
          (1 - 2 * ε)
  have h := (tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term hε hε2 H U V hH i j).add hsmooth
  simpa only [sub_add_cancel, zero_add] using h

#print axioms exists_uniform_pmPronicVaughanCentredGram_smooth_log_rate
#print axioms exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate
#print axioms tendsto_pmPronicVaughanCentredGram_sub_moving_smooth_term
#print axioms tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product
end GaloisForLFunctions.BezoutValuationIncidence
