import GaloisForLFunctions.BezoutValuationIncidence.UniformLogarithmicPrefixRemaindersInAllVaughanRows
import GaloisForLFunctions.BezoutValuationIncidence.UniformCriticalPronicPairingsFromLogarithmicCancellation

/-!
At half damping the smooth Gram term is a shifted harmonic sum. Summable
mixed-and-square envelopes give a common bounded error for every cutoff pair
and every entry of the actual centered Vaughan Gram.
-/

open Finset Filter RHTower
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators Topology
noncomputable section
namespace GaloisForLFunctions.BezoutValuationIncidence
set_option autoImplicit false

/-- All actual half-damping remainders share one summable mixed-and-square cell envelope. -/
theorem exists_summable_pmPronicVaughanSmoothRemainder_half_envelope :
    ∃ g : ℕ → ℝ, Summable g ∧ (∀ n, 0 ≤ g n) ∧ ∀ U V n : ℕ, ∀ i : Fin 5,
      (Real.sqrt (n : ℝ) * |pmPronicVaughanSmoothRemainder (1 / 2) U V n i| +
        pmPronicVaughanSmoothRemainder (1 / 2) U V n i ^ 2) /
          ((n : ℝ) * ((n : ℝ) + 1)) ≤ g n := by
  obtain ⟨A, hA, hlinear⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_linear_bound
    (ε := (1 / 2 : ℝ)) (by norm_num) le_rfl
  obtain ⟨B, hB, hlog⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_prefix_log_rate
    (ε := (1 / 2 : ℝ)) (by norm_num) le_rfl 2
  let f : (ℕ × ℕ) × Fin 5 → ℕ → ℝ := fun a n =>
    pmPronicVaughanSmoothRemainder (1 / 2) a.1.1 a.1.2 n a.2
  have hlog' : ∀ᶠ n : ℕ in atTop, ∀ a,
      |f a n| ≤ B * Real.sqrt (n : ℝ) / Real.log (n : ℝ) ^ 2 := by
    filter_upwards [hlog] with n hn a
    simpa only [f, show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow] using
      hn a.1.1 a.1.2 a.2
  obtain ⟨g, hg, hg0, hgf⟩ := exists_summable_critical_pronic_envelope hA hB
    (f := f) (fun a n hn => hlinear a.1.1 a.1.2 n hn a.2) hlog'
  exact ⟨g, hg, hg0, fun U V n i => hgf ((U, V), i) n⟩

/-- The half-damping actual remainders have uniform energy and absolutely bounded smooth pairings. -/
theorem exists_uniform_pmPronicVaughanSmoothRemainder_half_mixed_and_energy_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, ∀ i : Fin 5,
      (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * |pmPronicVaughanSmoothRemainder (1 / 2) U V n i| /
        ((n : ℝ) * ((n : ℝ) + 1))) ≤ C ∧
      pronicNorm (fun n => pmPronicVaughanSmoothRemainder (1 / 2) U V n i) T ^ 2 ≤ C := by
  obtain ⟨g, hg, hg0, hbound⟩ := exists_summable_pmPronicVaughanSmoothRemainder_half_envelope
  refine ⟨∑' n : ℕ, g n, tsum_nonneg hg0, fun U V T i => ?_⟩
  have hsum : (∑ n ∈ Icc 1 T,
      (Real.sqrt (n : ℝ) * |pmPronicVaughanSmoothRemainder (1 / 2) U V n i| +
        pmPronicVaughanSmoothRemainder (1 / 2) U V n i ^ 2) /
          ((n : ℝ) * ((n : ℝ) + 1))) ≤ ∑' n : ℕ, g n :=
    (sum_le_sum fun n _ => hbound U V n i).trans (hg.sum_le_tsum _ (fun n _ => hg0 n))
  constructor
  · refine (sum_le_sum fun n _ => ?_).trans hsum
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_right (sq_nonneg _)) (by positivity)
  · rw [pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity)]
    refine (sum_le_sum fun n _ => ?_).trans hsum
    exact div_le_div_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (by positivity)

private theorem abs_pronic_pair_le_common_energy (r s : ℕ → ℝ) (T : ℕ) {C : ℝ}
    (hr : pronicNorm r T ^ 2 ≤ C) (hs : pronicNorm s T ^ 2 ≤ C) :
    |∑ n ∈ Icc 1 T, r n * s n / ((n : ℝ) * ((n : ℝ) + 1))| ≤ C := by
  have hpoint (n : ℕ) : |r n * s n| ≤ (r n ^ 2 + s n ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith only [sq_nonneg (|r n| - |s n|), sq_abs (r n), sq_abs (s n)]
  calc
    _ ≤ ∑ n ∈ Icc 1 T, |r n * s n / ((n : ℝ) * ((n : ℝ) + 1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Icc 1 T, (r n ^ 2 + s n ^ 2) / 2 / ((n : ℝ) * ((n : ℝ) + 1)) := by
      apply sum_le_sum
      intro n _
      rw [abs_div, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]
      exact div_le_div_of_nonneg_right (hpoint n) (by positivity)
    _ = (pronicNorm r T ^ 2 + pronicNorm s T ^ 2) / 2 := by
      rw [pronicNorm, pronicNorm, Real.sq_sqrt (sum_nonneg fun n _ => by positivity),
        Real.sq_sqrt (sum_nonneg fun n _ => by positivity), ← sum_add_distrib, sum_div]
      exact sum_congr rfl fun n _ => by ring
    _ ≤ C := by linarith only [hr, hs]

private theorem abs_smooth_pronic_pair_le (r : ℕ → ℝ) (T : ℕ) :
    |∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r n / ((n : ℝ) * ((n : ℝ) + 1))| ≤
      ∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * |r n| / ((n : ℝ) * ((n : ℝ) + 1)) := by
  refine (abs_sum_le_sum_abs _ _).trans_eq ?_
  apply sum_congr rfl
  intro n _
  rw [abs_div, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n : ℝ) * ((n : ℝ) + 1))]

/-- The half-damping centered Vaughan Gram has a cutoff-uniform bounded error after its harmonic rank-one term. -/
theorem exists_uniform_pmPronicVaughanCentredGram_half_harmonic_error_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ U V T : ℕ, ∀ i j : Fin 5,
      |pmPronicVaughanCentredGram (1 / 2) U V T i j -
        (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
          pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j *
            (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1))| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_uniform_pmPronicVaughanSmoothRemainder_half_mixed_and_energy_bound
  let c := |subHalfZetaCoeff (1 / 2)|
  have hc : 0 ≤ c := abs_nonneg _
  refine ⟨(2 * c + 1) * C, by positivity, fun U V T i j => ?_⟩
  let a : Fin 5 → ℝ := fun k => subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U *
    deningerHarmonicPartial V * pmPronicVaughanSmoothSigns k
  let r : Fin 5 → ℕ → ℝ := fun k n => pmPronicVaughanSmoothRemainder (1 / 2) U V n k
  have ha (k : Fin 5) : |a k| ≤ c := by
    have hsign : |pmPronicVaughanSmoothSigns k| ≤ 1 := by
      fin_cases k <;> norm_num [pmPronicVaughanSmoothSigns]
    have hcoeff : |deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ 1 := by
      rw [abs_mul]
      simpa only [one_mul] using mul_le_mul (abs_deningerHarmonicPartial_le_one U)
        (abs_deningerHarmonicPartial_le_one V) (abs_nonneg _) zero_le_one
    have hfirst : |subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V| ≤ c := by
      rw [mul_assoc, abs_mul]
      exact mul_le_of_le_one_right hc hcoeff
    dsimp only [a]
    rw [abs_mul]
    exact (mul_le_of_le_one_right (abs_nonneg _) hsign).trans hfirst
  have hmixed (k : Fin 5) :
      |∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r k n / ((n : ℝ) * ((n : ℝ) + 1))| ≤ C :=
    (abs_smooth_pronic_pair_le (r k) T).trans (hbound U V T k).1
  have hres : |∑ n ∈ Icc 1 T, r i n * r j n / ((n : ℝ) * ((n : ℝ) + 1))| ≤ C :=
    abs_pronic_pair_le_common_energy (r i) (r j) T (hbound U V T i).2 (hbound U V T j).2
  have heq : pmPronicVaughanCentredGram (1 / 2) U V T i j -
      a i * a j * (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1)) =
        a i * (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r j n / ((n : ℝ) * ((n : ℝ) + 1))) +
          a j * (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r i n / ((n : ℝ) * ((n : ℝ) + 1))) +
            ∑ n ∈ Icc 1 T, r i n * r j n / ((n : ℝ) * ((n : ℝ) + 1)) := by
    have hrow (k : Fin 5) (n : ℕ) : pmPronicVaughanCentredPiece (1 / 2) U V n k =
        a k * Real.sqrt (n : ℝ) + r k n := by
      dsimp only [a, r, pmPronicVaughanSmoothRemainder]
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by ring, ← Real.sqrt_eq_rpow]
      ring
    simp only [pmPronicVaughanCentredGram, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    apply sum_congr rfl
    intro n hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast (mem_Icc.mp hn).1
    simp only [hrow, pronicSeq, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
    have hsq := Real.sq_sqrt hn0.le
    have hprod : (a i * Real.sqrt (n : ℝ) + r i n) *
        (a j * Real.sqrt (n : ℝ) + r j n) =
          a i * a j * n + a i * Real.sqrt (n : ℝ) * r j n +
            a j * Real.sqrt (n : ℝ) * r i n + r i n * r j n := by
      calc
        _ = a i * a j * Real.sqrt (n : ℝ) ^ 2 +
            a i * Real.sqrt (n : ℝ) * r j n +
              a j * Real.sqrt (n : ℝ) * r i n + r i n * r j n := by ring
        _ = _ := by rw [hsq]
    rw [hprod]
    field_simp [hn0.ne', (show (n : ℝ) + 1 ≠ 0 by positivity)]
    ring
  have herror : |pmPronicVaughanCentredGram (1 / 2) U V T i j -
      a i * a j * (∑ n ∈ Icc 1 T, 1 / ((n : ℝ) + 1))| ≤ (2 * c + 1) * C := by
    rw [heq]
    calc
      _ ≤ |a i * (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r j n / ((n : ℝ) * ((n : ℝ) + 1)))| +
          |a j * (∑ n ∈ Icc 1 T, Real.sqrt (n : ℝ) * r i n / ((n : ℝ) * ((n : ℝ) + 1)))| +
            |∑ n ∈ Icc 1 T, r i n * r j n / ((n : ℝ) * ((n : ℝ) + 1))| :=
        (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
      _ ≤ c * C + c * C + C := by
        exact add_le_add (add_le_add
          ((abs_mul (a i) _).trans_le
            (mul_le_mul (ha i) (hmixed j) (abs_nonneg _) hc))
          ((abs_mul (a j) _).trans_le
            (mul_le_mul (ha j) (hmixed i) (abs_nonneg _) hc))) hres
      _ = _ := by ring
  have haa : a i * a j =
      (subHalfZetaCoeff (1 / 2) * deningerHarmonicPartial U * deningerHarmonicPartial V) ^ 2 *
        pmPronicVaughanSmoothSigns i * pmPronicVaughanSmoothSigns j := by
    dsimp only [a]
    ring
  rw [haa] at herror
  exact herror

#print axioms exists_summable_pmPronicVaughanSmoothRemainder_half_envelope
#print axioms exists_uniform_pmPronicVaughanSmoothRemainder_half_mixed_and_energy_bound
#print axioms exists_uniform_pmPronicVaughanCentredGram_half_harmonic_error_bound
end GaloisForLFunctions.BezoutValuationIncidence
