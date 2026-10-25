import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicEnergyInTheVaughanConvolution
import GaloisForLFunctions.BezoutValuationIncidence.LogarithmicEnergySavingsForTheMobiusInterior

/-! Removing the common smooth-power direction gives logarithmic pronic norm savings
for every Vaughan row, uniformly in both cutoffs. The exact five-row identity
transfers the estimates to the both-large row. -/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- The undilated smooth-power remainder has bounded pronic norm. -/
theorem pronicNorm_subHalfRemainder_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) (T : ℕ) :
    pronicNorm (subHalfRemainder ε) T ≤
      Real.sqrt (1 + 1 / ε) *
        (floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|) := by
  have h := pronicNorm_subHalfDilationRemainder_le hε hε1 (j := 1) (by norm_num) T
  have heq : pronicNorm (subHalfRemainder ε) T =
      pronicNorm (fun n => if 1 ≤ n then subHalfDilationRemainder ε n 1 else 0) T := by
    apply pronicNorm_congr
    intro n hn
    simp only [if_pos (mem_Icc.mp hn).1, subHalfDilationRemainder, Nat.div_one,
      Nat.cast_one, Real.one_rpow, mul_one, sub_self, mul_zero, sub_zero]
  rw [heq]
  simpa only [Nat.cast_one, Real.one_rpow, mul_one] using h

/-- The five centered Vaughan rows after removing their explicit common smooth-power direction. -/
def pmPronicVaughanSmoothRemainder (ε : ℝ) (U V n : ℕ) (i : Fin 5) : ℝ :=
  pmPronicVaughanCentredPiece ε U V n i -
    (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V *
      pmPronicVaughanSmoothSigns i) * (n : ℝ) ^ (1 - ε)

/-- The convolution remainder separates into a bounded unit-pattern correction and the actual fluctuation. -/
theorem pmPronicVaughanSmoothRemainder_smallSmall_eq {ε : ℝ} (hε : 0 < ε) (U V n : ℕ) :
    pmPronicVaughanSmoothRemainder ε U V n 2 =
      -(deningerHarmonicPartial U * deningerHarmonicPartial V) * subHalfRemainder ε n -
        pmVaughanConvolutionFluctuationPrefix ε U V n := by
  rw [pmPronicVaughanSmoothRemainder,
    pmPronicVaughanCentredPiece_smallSmall_eq_unit_add_fluctuation hε]
  change -(deningerHarmonicPartial U * deningerHarmonicPartial V) * patternPrefix ε unitSign n -
    pmVaughanConvolutionFluctuationPrefix ε U V n -
      (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * (-1)) *
        (n : ℝ) ^ (1 - ε) = _
  rw [subHalfRemainder, patternPrefix]
  ring

/-- The convolution row has every uniform logarithmic norm saving after removing its smooth term. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_smallSmall_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ,
      pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) T ≤
        C * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  have hε1 : ε < 1 := by linarith only [hε2]
  let K : ℝ := Real.sqrt (1 + 1 / ε) *
    (floorSumRate ((1 - ε : ℝ) : ℂ) + |subHalfZetaCoeff ε|)
  have hK : 0 ≤ K :=
    (pronicNorm_nonneg (subHalfRemainder ε) 0).trans (pronicNorm_subHalfRemainder_le hε hε1 0)
  let f : ℕ × ℕ → ℕ → ℝ := fun a n =>
    -(deningerHarmonicPartial a.1 * deningerHarmonicPartial a.2) * subHalfRemainder ε n
  have hbounded (a : ℕ × ℕ) (T : ℕ) : pronicNorm (f a) T ≤ K := by
    have hcoeff : |deningerHarmonicPartial a.1 * deningerHarmonicPartial a.2| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one a.1)
        (abs_deningerHarmonicPartial_le_one a.2) (abs_nonneg _) zero_le_one
    dsimp only [f]
    rw [pronicNorm_smul, abs_neg]
    calc
      _ ≤ 1 * K := mul_le_mul hcoeff (pronicNorm_subHalfRemainder_le hε hε1 T)
        (pronicNorm_nonneg _ _) zero_le_one
      _ = _ := one_mul _
  have hunit := eventually_pronicNorm_log_rate_of_uniform_bound
    (by linarith only [hε2] : 0 < 1 - 2 * ε) hK hbounded q
  obtain ⟨B, hB, hfluct⟩ := exists_uniform_pmVaughanConvolutionFluctuation_pronicNorm_log_rate hε hε2 q
  refine ⟨K + B, add_nonneg hK hB, ?_⟩
  filter_upwards [hunit, hfluct] with T hunitT hfluctT U V
  have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) =
      fun n => f (U, V) n + (-1) * pmVaughanConvolutionFluctuationPrefix ε U V n := by
    funext n
    rw [pmPronicVaughanSmoothRemainder_smallSmall_eq hε]
    dsimp only [f]
    ring
  rw [heq]
  calc
    _ ≤ pronicNorm (f (U, V)) T +
        pronicNorm (fun n => (-1) * pmVaughanConvolutionFluctuationPrefix ε U V n) T :=
      pronicNorm_add_le _ _ T
    _ = pronicNorm (f (U, V)) T + pronicNorm (pmVaughanConvolutionFluctuationPrefix ε U V) T := by
      congr 1
      rw [pronicNorm_smul, abs_neg, abs_one, one_mul]
    _ ≤ K * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q +
        B * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q :=
      add_le_add (hunitT (U, V)) (hfluctT U V)
    _ = _ := by ring

/-- Removing the opposite smooth terms leaves the exact interior identity unchanged. -/
theorem sum_pmPronicVaughanSmoothRemainder (ε : ℝ) (U V n : ℕ) :
    (∑ i : Fin 5, pmPronicVaughanSmoothRemainder ε U V n i) = pmBezoutInteriorPrefix ε n := by
  have hs : (∑ i : Fin 5, pmPronicVaughanSmoothSigns i) = 0 := by
    norm_num [pmPronicVaughanSmoothSigns, Fin.sum_univ_succ]
  have hcent : (∑ i : Fin 5, pmPronicVaughanCentredPiece ε U V n i) =
      pmBezoutInteriorPrefix ε n := by
    simp only [pmPronicVaughanCentredPiece, sum_sub_distrib, ← sum_mul,
      sum_pmPronicVaughanPiece, sum_pmPronicVaughanMean, zero_mul, sub_zero]
  simp only [pmPronicVaughanSmoothRemainder, sum_sub_distrib]
  rw [hcent, ← sum_mul, ← mul_sum, hs, mul_zero, zero_mul, sub_zero]

/-- The smooth remainder of the both-large row is bounded by the other four rows and the interior. -/
theorem pronicNorm_pmPronicVaughanSmoothRemainder_large_le (ε : ℝ) (U V T : ℕ) :
    pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 3) T ≤
      pronicNorm (pmBezoutInteriorPrefix ε) T +
        (pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 0) T +
          (pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 1) T +
            (pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) T +
              pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 4) T))) := by
  let r : Fin 5 → ℕ → ℝ := fun i n => pmPronicVaughanSmoothRemainder ε U V n i
  have heq : r 3 = fun n => pmBezoutInteriorPrefix ε n +
      (-1 : ℝ) * (r 0 n + (r 1 n + (r 2 n + r 4 n))) := by
    funext n
    have hs := sum_pmPronicVaughanSmoothRemainder ε U V n
    simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hs
    change r 0 n + (r 1 n + (r 2 n + (r 3 n + r 4 n))) = _ at hs
    linarith only [hs]
  change pronicNorm (r 3) T ≤ _
  rw [heq]
  have h := pronicNorm_add_le (pmBezoutInteriorPrefix ε)
    (fun n => (-1 : ℝ) * (r 0 n + (r 1 n + (r 2 n + r 4 n)))) T
  rw [pronicNorm_smul, abs_neg, abs_one, one_mul] at h
  exact h.trans (add_le_add le_rfl
    ((pronicNorm_add_le (r 0) _ T).trans (add_le_add le_rfl
      ((pronicNorm_add_le (r 1) _ T).trans (add_le_add le_rfl
        (pronicNorm_add_le (r 2) (r 4) T))))))

/-- All five smooth remainders share every logarithmic norm saving, independently of both cutoffs. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_log_rate
    {ε : ℝ} (hε : 0 < ε) (hε2 : ε < 1 / 2) (q : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ T : ℕ in atTop, ∀ U V : ℕ, ∀ i : Fin 5,
      pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n i) T ≤
        C * Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q := by
  obtain ⟨A, hA, hI⟩ := exists_pmBezoutInteriorPrefix_pronicNorm_log_rate hε hε2 q
  obtain ⟨B, hB, hsmall⟩ := exists_uniform_patternPrefix_truncatedMoebius_pronicNorm_log_rate hε hε2 q
  obtain ⟨D, hD, hconv⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_smallSmall_log_rate hε hε2 q
  have hpole := eventually_pronicNorm_log_rate_of_uniform_bound
    (f := fun a : ℕ × ℕ => fun n => pmPronicVaughanSmoothRemainder ε a.1 a.2 n 4)
    (by linarith only [hε2] : 0 < 1 - 2 * ε) (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (fun a T => pronicNorm_le_of_abs_le (by norm_num) (fun n => by
      change |pmPronicVaughanCentredPiece ε a.1 a.2 n 4 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial a.1 * deningerHarmonicPartial a.2 * 0) *
          (n : ℝ) ^ (1 - ε)| ≤ 1 / 2
      simpa only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece] using
        abs_pmPronicVaughanPiece_pole_sub_mean_le hε.le a.1 a.2 n) T) q
  refine ⟨A + (B + (B + (D + 1 / 2))), by positivity, ?_⟩
  filter_upwards [hI, hsmall, hconv, hpole, eventually_ge_atTop 1] with T hIT hsmallT hconvT hpoleT hT U V i
  let S : ℝ := Real.sqrt ((T : ℝ) ^ (1 - 2 * ε)) / Real.log (T : ℝ) ^ q
  have hS : 0 ≤ S := div_nonneg (Real.sqrt_nonneg _)
    (pow_nonneg (Real.log_nonneg (by exact_mod_cast hT)) _)
  have h0 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 0) T ≤ B * S := by
    have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 0) =
        patternPrefix ε (Sieve.truncatedMoebius U) := by
      funext n
      change pmPronicVaughanCentredPiece ε U V n 0 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
          (n : ℝ) ^ (1 - ε) = _
      simp only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
        pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε]
    rw [heq]
    simpa only [S, mul_div_assoc] using hsmallT U
  have h1 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 1) T ≤ B * S := by
    have heq : (fun n => pmPronicVaughanSmoothRemainder ε U V n 1) =
        patternPrefix ε (Sieve.truncatedMoebius V) := by
      funext n
      change pmPronicVaughanCentredPiece ε V U n 0 -
        (subHalfZetaCoeff ε * deningerHarmonicPartial U * deningerHarmonicPartial V * 0) *
          (n : ℝ) ^ (1 - ε) = _
      simp only [mul_zero, zero_mul, sub_zero, pmPronicVaughanCentredPiece,
        pmPronicVaughanPiece_small_sub_mean_eq_patternPrefix hε]
    rw [heq]
    simpa only [S, mul_div_assoc] using hsmallT V
  have h2 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 2) T ≤ D * S := by
    simpa only [S, mul_div_assoc] using hconvT U V
  have h4 : pronicNorm (fun n => pmPronicVaughanSmoothRemainder ε U V n 4) T ≤ (1 / 2) * S := by
    simpa only [S, mul_div_assoc] using hpoleT (U, V)
  have hI' : pronicNorm (pmBezoutInteriorPrefix ε) T ≤ A * S := by
    simpa only [S, mul_div_assoc] using hIT
  rw [mul_div_assoc]
  change _ ≤ (A + (B + (B + (D + 1 / 2)))) * S
  fin_cases i
  · exact h0.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hD]) hS)
  · exact h1.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hD]) hS)
  · exact h2.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hD]) hS)
  · exact (pronicNorm_pmPronicVaughanSmoothRemainder_large_le ε U V T).trans
      ((add_le_add hI' (add_le_add h0 (add_le_add h1 (add_le_add h2 h4)))).trans_eq (by ring))
  · exact h4.trans (mul_le_mul_of_nonneg_right (by linarith only [hA, hB, hD]) hS)

#print axioms pronicNorm_subHalfRemainder_le
#print axioms pmPronicVaughanSmoothRemainder_smallSmall_eq
#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_smallSmall_log_rate
#print axioms sum_pmPronicVaughanSmoothRemainder
#print axioms pronicNorm_pmPronicVaughanSmoothRemainder_large_le
#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_log_rate
end GaloisForLFunctions.BezoutValuationIncidence
