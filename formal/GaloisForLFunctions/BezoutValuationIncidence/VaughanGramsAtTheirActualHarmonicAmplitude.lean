import GaloisForLFunctions.BezoutValuationIncidence.UniformVaughanGramsFollowTheirSmoothRankOneTerm
import GaloisForLFunctions.BezoutValuationIncidence.TheRanksOfSubcriticalVaughanLimits
import GaloisForLFunctions.RHTower.FiniteMobiusHarmonicSumsHaveExplicitLowerBounds

/-!
Factorial denominator bounds control the relative error in the smooth Vaughan
Gram. Every positive cutoff schedule admits horizons paying that denominator
cost, even when its ordinary normalized Gram tends to zero.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- Finite harmonic nonvanishing has an explicit factorial separation from zero. -/
theorem one_div_factorial_le_abs_deningerHarmonicPartial {N : ℕ} (hN : 1 ≤ N) :
    1 / (N.factorial : ℝ) ≤ |deningerHarmonicPartial N| := by
  rw [deningerHarmonicPartial_eq_sum_Icc]
  exact one_div_factorial_le_abs_sum_moebius_div hN

/-- Positive cutoff amplitudes have a positive lower bound and a controlled reciprocal. -/
theorem pmVaughanSmoothAmplitude_pos_and_inv_le_factorial
    {U V : ℕ} (hU : 1 ≤ U) (hV : 1 ≤ V) :
    0 < deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2 ∧
      1 / (deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2) ≤
        ((U.factorial : ℝ) * V.factorial) ^ 2 := by
  have hF : 0 < (U.factorial : ℝ) * V.factorial := by
    exact mul_pos (by exact_mod_cast Nat.factorial_pos U)
      (by exact_mod_cast Nat.factorial_pos V)
  have hprod : 1 / ((U.factorial : ℝ) * V.factorial) ≤
      |deningerHarmonicPartial U| * |deningerHarmonicPartial V| := by
    simpa only [one_div, mul_inv] using mul_le_mul
      (one_div_factorial_le_abs_deningerHarmonicPartial hU)
      (one_div_factorial_le_abs_deningerHarmonicPartial hV) (by positivity) (abs_nonneg _)
  have hsq := pow_le_pow_left₀ (by positivity) hprod 2
  rw [mul_pow, sq_abs, sq_abs] at hsq
  have ha : 0 < deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2 :=
    (sq_pos_of_pos (one_div_pos.mpr hF)).trans_le hsq
  refine ⟨ha, ?_⟩
  have hinv := one_div_le_one_div_of_le (sq_pos_of_pos (one_div_pos.mpr hF)) hsq
  simpa only [div_pow, one_pow, one_div_one_div] using hinv

/-- The common absolute Gram bound becomes a relative bound with an explicit denominator cost. -/
theorem exists_uniform_pmPronicVaughanCentredGram_relative_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ,
      1 ≤ U → 1 ≤ V → ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram ε U V T i j /
          ((T : ℝ) ^ (1 - 2 * ε) * (deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2)) -
        subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j| ≤
        C * ((U.factorial : ℝ) * V.factorial) ^ 2 / Real.log (T : ℝ) ^ q := by
  obtain ⟨C, hC, hG⟩ := exists_uniform_pmPronicVaughanCentredGram_normalized_log_rate hε hε2 q
  refine ⟨C, hC, ?_⟩
  filter_upwards [hG, eventually_ge_atTop 1] with T hT hT1 U V hU hV i j
  obtain ⟨ha, hinv⟩ := pmVaughanSmoothAmplitude_pos_and_inv_le_factorial hU hV
  let a := deningerHarmonicPartial U ^ 2 * deningerHarmonicPartial V ^ 2
  let k := subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) *
    pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j
  have herror : |pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) - a * k| ≤
      C / Real.log (T : ℝ) ^ q := by
    convert hT U V i j using 1
    congr 1
    dsimp only [a, k]
    ring
  have heq : pmPronicVaughanCentredGram ε U V T i j /
      ((T : ℝ) ^ (1 - 2 * ε) * a) - k =
        (pmPronicVaughanCentredGram ε U V T i j / (T : ℝ) ^ (1 - 2 * ε) - a * k) / a := by
    rw [div_mul_eq_div_div, sub_div, mul_div_cancel_left₀ _ ha.ne']
  change |pmPronicVaughanCentredGram ε U V T i j / ((T : ℝ) ^ (1 - 2 * ε) * a) - k| ≤ _
  rw [heq, abs_div, abs_of_pos ha]
  calc
    _ ≤ (C / Real.log (T : ℝ) ^ q) / a := div_le_div_of_nonneg_right herror ha.le
    _ = (C / Real.log (T : ℝ) ^ q) * (1 / a) := by ring
    _ ≤ (C / Real.log (T : ℝ) ^ q) * ((U.factorial : ℝ) * V.factorial) ^ 2 :=
      mul_le_mul_of_nonneg_left hinv (div_nonneg hC
        (pow_nonneg (Real.log_nonneg (by exact_mod_cast hT1)) q))
    _ = _ := by ring

/-- A vanishing explicit factorial error gives a universal relative Gram limit. -/
theorem tendsto_pmPronicVaughanCentredGram_relative_of_factorial_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (H U V : ℕ → ℕ)
    (hH : Tendsto H atTop atTop) (hU : ∀ n, 1 ≤ U n) (hV : ∀ n, 1 ≤ V n)
    (q : ℕ) (hrate : Tendsto (fun n =>
      (((U n).factorial : ℝ) * (V n).factorial) ^ 2 / Real.log (H n : ℝ) ^ q) atTop (𝓝 0))
    (i j : Fin 5) :
    Tendsto (fun n => pmPronicVaughanCentredGram ε (U n) (V n) (H n) i j /
      ((H n : ℝ) ^ (1 - 2 * ε) *
        (deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)))
      atTop (𝓝 (subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j)) := by
  obtain ⟨C, _hC, hG⟩ := exists_uniform_pmPronicVaughanCentredGram_relative_log_rate hε hε2 q
  apply (tendsto_sub_nhds_zero_iff).mp
  apply squeeze_zero_norm' ?_ (by simpa only [mul_zero] using hrate.const_mul C)
  filter_upwards [hH.eventually hG] with n hn
  simpa only [Real.norm_eq_abs, mul_div_assoc] using hn (U n) (V n) (hU n) (hV n) i j

/-- Every pair of cutoff schedules admits divergent horizons paying its factorial denominator cost. -/
theorem exists_horizon_pmVaughan_factorial_log_rate (U V : ℕ → ℕ) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      Tendsto (fun n => (((U n).factorial : ℝ) * (V n).factorial) ^ 2 /
        Real.log (H n : ℝ)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hex (n : ℕ) : ∃ m : ℕ, n + 1 ≤ m ∧
      ((n : ℝ) + 1) * (((U n).factorial : ℝ) * (V n).factorial) ^ 2 ≤ Real.log (m : ℝ) :=
    ((eventually_ge_atTop (n + 1)).and (hlog.eventually_ge_atTop _)).exists
  choose H hH hcal using hex
  have hHlim : Tendsto H atTop atTop := by
    apply tendsto_atTop.2
    intro B
    filter_upwards [eventually_ge_atTop B] with n hn
    exact hn.trans ((Nat.le_succ n).trans (hH n))
  refine ⟨H, hHlim, ?_⟩
  have hbound (n : ℕ) :
      (((U n).factorial : ℝ) * (V n).factorial) ^ 2 / Real.log (H n : ℝ) ≤
        1 / ((n : ℝ) + 1) := by
    have hA : 0 < (((U n).factorial : ℝ) * (V n).factorial) ^ 2 := by
      have hU : (0 : ℝ) < (U n).factorial := by exact_mod_cast Nat.factorial_pos (U n)
      have hV : (0 : ℝ) < (V n).factorial := by exact_mod_cast Nat.factorial_pos (V n)
      positivity
    have hlogH : 0 < Real.log (H n : ℝ) := (mul_pos (by positivity) hA).trans_le (hcal n)
    apply (div_le_iff₀ hlogH).mpr
    have h := (le_div_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      (by simpa only [mul_comm] using hcal n)
    simpa only [div_eq_mul_inv, one_mul, mul_comm] using h
  have hden : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [(tendsto_natCast_atTop_atTop :
      Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).eventually_ge_atTop b] with n hn
    exact hn.trans (le_add_of_nonneg_right zero_le_one)
  have hzero : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  apply squeeze_zero' (Eventually.of_forall ?_) (Eventually.of_forall hbound) hzero
  intro n
  have hH1 : 1 ≤ H n := (by omega : 1 ≤ n + 1).trans (hH n)
  exact div_nonneg (sq_nonneg _) (Real.log_nonneg (by exact_mod_cast hH1))

/-- Positive cutoffs always admit horizons on which their relative Gram has the same nonzero smooth limit. -/
theorem exists_horizon_pmPronicVaughanCentredGram_relative_limit
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (U V : ℕ → ℕ)
    (hU : ∀ n, 1 ≤ U n) (hV : ∀ n, 1 ≤ V n) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧ ∀ i j : Fin 5,
      Tendsto (fun n => pmPronicVaughanCentredGram ε (U n) (V n) (H n) i j /
        ((H n : ℝ) ^ (1 - 2 * ε) *
          (deningerHarmonicPartial (U n) ^ 2 * deningerHarmonicPartial (V n) ^ 2)))
        atTop (𝓝 (subHalfZetaCoeff ε ^ 2 / (1 - 2 * ε) *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j)) := by
  obtain ⟨H, hH, hrate⟩ := exists_horizon_pmVaughan_factorial_log_rate U V
  exact ⟨H, hH, fun i j => tendsto_pmPronicVaughanCentredGram_relative_of_factorial_log_rate
    hε hε2 H U V hH hU hV 1 (by simpa only [pow_one] using hrate) i j⟩

/-- The same moving arithmetic rows realize zero at the trivial scale and rank one at their harmonic scale. -/
theorem exists_horizon_vaughan_zero_and_relative_rank_one_limits
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) :
    ∃ H : ℕ → ℕ, Tendsto H atTop atTop ∧
      (∀ i j : Fin 5, Tendsto (fun n =>
        pmPronicVaughanCentredGram ε (n + 1) (n + 1) (H n) i j /
          (H n : ℝ) ^ (1 - 2 * ε)) atTop (𝓝 0)) ∧
      (∀ i j : Fin 5, Tendsto (fun n =>
        pmPronicVaughanCentredGram ε (n + 1) (n + 1) (H n) i j /
          ((H n : ℝ) ^ (1 - 2 * ε) *
            (deningerHarmonicPartial (n + 1) ^ 2 * deningerHarmonicPartial (n + 1) ^ 2)))
          atTop (𝓝 (pmVaughanSmoothLimitMatrix ε 1 i j))) ∧
      Matrix.rank (pmVaughanSmoothLimitMatrix ε 1) = 1 := by
  obtain ⟨H, hH, hrelative⟩ := exists_horizon_pmPronicVaughanCentredGram_relative_limit
    hε hε2 (fun n => n + 1) (fun n => n + 1) (fun n => by omega) (fun n => by omega)
  have hproduct : Tendsto (fun n : ℕ => (n + 1) * (n + 1)) atTop atTop := by
    apply tendsto_atTop.2
    intro N
    filter_upwards [eventually_ge_atTop N] with n hn
    simpa only [mul_one] using Nat.mul_le_mul (by omega : N ≤ n + 1) (by omega : 1 ≤ n + 1)
  refine ⟨H, hH, ?_, ?_, rank_pmVaughanSmoothLimitMatrix_of_pos hε hε2 zero_lt_one⟩
  · exact fun i j => tendsto_pmPronicVaughanCentredGram_div_of_horizon_and_product
      hε hε2 H (fun n => n + 1) (fun n => n + 1) hH hproduct i j
  · intro i j
    simpa only [pmVaughanSmoothLimitMatrix, mul_one] using hrelative i j

#print axioms one_div_factorial_le_abs_deningerHarmonicPartial
#print axioms pmVaughanSmoothAmplitude_pos_and_inv_le_factorial
#print axioms exists_uniform_pmPronicVaughanCentredGram_relative_log_rate
#print axioms tendsto_pmPronicVaughanCentredGram_relative_of_factorial_log_rate
#print axioms exists_horizon_pmVaughan_factorial_log_rate
#print axioms exists_horizon_pmPronicVaughanCentredGram_relative_limit
#print axioms exists_horizon_vaughan_zero_and_relative_rank_one_limits
end GaloisForLFunctions.BezoutValuationIncidence
