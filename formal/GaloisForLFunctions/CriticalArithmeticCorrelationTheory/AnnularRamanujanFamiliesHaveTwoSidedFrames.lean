import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.GrowingRamanujanFamiliesHaveASquareRootHorizon
import GaloisForLFunctions.BezoutValuationIncidence.OscillatoryPronicTailSummationByPartsAndSecondOrderVonMangoldtError

/-!
# Two-sided annular frames for growing Ramanujan families

The actual large-sieve window discrepancy is uniform in its starting point.
Summation by parts costs only the first harmonic weight, so an annulus beyond
the quadratic conductor scale has two frame bounds independent of its size.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory

open BezoutValuationIncidence RenormalizedArithmeticPotentialTheory ArithmeticEffectivityTheory

private theorem sum_window_eq_range (f : ℕ → ℝ) (A N : ℕ) :
    (∑ n ∈ Icc (A + 1) (A + N), f n) = ∑ i ∈ range N, f (A + i + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [show A + (N + 1) = (A + N) + 1 by omega,
      sum_Icc_succ_top (by omega : A + 1 ≤ (A + N) + 1), ih, Finset.sum_range_succ]

/-- Every real coefficient vector has the same harmonic annular discrepancy,
with the exact cost `Q(Q-1)/(A+1)` from the first weight. -/
theorem abs_ramanujanPoleProfile_annular_gram_discrepancy_le {Q : ℕ} (hQ : 2 ≤ Q)
    (a : ℕ → ℝ) (A N : ℕ) :
    |(∑ n ∈ Icc (A + 1) (A + N),
        (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2) -
      (∑ n ∈ Icc (A + 1) (A + N), 1 / (n : ℝ)) * (∑ m ∈ Icc 1 Q, a m ^ 2)| ≤
      ((Q : ℝ) * ((Q : ℝ) - 1)) / ((A : ℝ) + 1) * (∑ m ∈ Icc 1 Q, a m ^ 2) := by
  let C := ∑ m ∈ Icc 1 Q, a m ^ 2
  let D : ℝ := (Q : ℝ) * ((Q : ℝ) - 1)
  let f : ℕ → ℝ := fun i =>
    (∑ m ∈ Icc 1 Q, a m * normalizedRamanujanMode m (A + i + 1)) ^ 2 - C
  let w : ℕ → ℝ := fun i => 1 / ((A + i + 1 : ℕ) : ℝ)
  have hC : 0 ≤ C := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := mul_nonneg (Nat.cast_nonneg _) (by
    have h : (1 : ℝ) ≤ Q := by exact_mod_cast (show 1 ≤ Q by omega)
    exact sub_nonneg.mpr h)
  have hp (K : ℕ) : |∑ i ∈ range K, f i| ≤ D * C := by
    have h := abs_ramanujanPacket_window_discrepancy_le hQ a A K
    rw [sum_window_eq_range] at h
    simpa only [f, C, D, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul] using h
  have hb := abs_sum_range_mul_antitone_le f w N (mul_nonneg hD hC)
    (fun i => by dsimp only [w]; positivity)
    (fun i j hij => one_div_le_one_div_of_le (by positivity)
      (by exact_mod_cast (show A + i + 1 ≤ A + j + 1 by omega)))
    (fun K _ => hp K)
  have he : (∑ i ∈ range N, w i * f i) =
      (∑ n ∈ Icc (A + 1) (A + N),
        (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2) -
      (∑ n ∈ Icc (A + 1) (A + N), 1 / (n : ℝ)) * C := by
    rw [sum_window_eq_range, sum_window_eq_range, sum_mul, ← sum_sub_distrib]
    apply sum_congr rfl
    intro i hi
    simp only [ramanujanPoleProfile, ← mul_div_assoc, ← sum_div, div_pow,
      Real.sq_sqrt (Nat.cast_nonneg (A + i + 1)), w, f]
    ring
  rw [he] at hb
  simpa only [w, Nat.add_zero, Nat.cast_add, Nat.cast_zero, Nat.cast_one, add_zero, C, D, mul_one_div,
    div_mul_eq_mul_div] using hb

private theorem dyadic_harmonic_bounds {A : ℕ} (hA : 0 < A) :
    (1 : ℝ) / 2 ≤ ∑ n ∈ Icc (A + 1) (A + A), 1 / (n : ℝ) ∧
      (∑ n ∈ Icc (A + 1) (A + A), 1 / (n : ℝ)) ≤ 1 := by
  have hA0 : (0 : ℝ) < A := by exact_mod_cast hA
  rw [sum_window_eq_range]
  have hlo : ∀ i ∈ range A, 1 / (2 * (A : ℝ)) ≤ 1 / ((A + i + 1 : ℕ) : ℝ) := by
    intro i hi
    apply one_div_le_one_div_of_le (by positivity)
    have hiA : i < A := mem_range.mp hi
    have h : A + i + 1 ≤ 2 * A := by omega
    exact_mod_cast h
  have hup : ∀ i ∈ range A, 1 / ((A + i + 1 : ℕ) : ℝ) ≤ 1 / (A : ℝ) := by
    intro i hi
    exact one_div_le_one_div_of_le hA0 (by exact_mod_cast (show A ≤ A + i + 1 by omega))
  have hl := sum_le_sum hlo
  have hu := sum_le_sum hup
  simp only [sum_const, card_range, nsmul_eq_mul] at hl hu
  have he1 : (A : ℝ) * (1 / (2 * A)) = 1 / 2 := by field_simp [hA0.ne']
  have he2 : (A : ℝ) * (1 / A) = 1 := by field_simp [hA0.ne']
  rw [he1] at hl
  rw [he2] at hu
  exact ⟨hl, hu⟩

/-- Beyond four times the quadratic conductor scale, every actual annular
Ramanujan packet has frame constants `1/4` and `5/4`, simultaneously. -/
theorem ramanujanPoleProfile_dyadic_twoSided_frame {Q A : ℕ}
    (hQ : 2 ≤ Q) (hA : 4 * (Q * (Q - 1)) ≤ A) (a : ℕ → ℝ) :
    (1 / 4 : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) ≤
        ∑ n ∈ Icc (A + 1) (2 * A),
          (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2 ∧
      (∑ n ∈ Icc (A + 1) (2 * A),
          (∑ m ∈ Icc 1 Q, a m * ramanujanPoleProfile m n) ^ 2) ≤
        (5 / 4 : ℝ) * (∑ m ∈ Icc 1 Q, a m ^ 2) := by
  have hDnat : 0 < Q * (Q - 1) := Nat.mul_pos (by omega) (by omega)
  have hA0 : 0 < A := by omega
  have hAr : (4 : ℝ) * ((Q : ℝ) * ((Q : ℝ) - 1)) ≤ A := by
    have h : (4 : ℝ) * ((Q * (Q - 1) : ℕ) : ℝ) ≤ A := by exact_mod_cast hA
    simpa only [Nat.cast_mul, Nat.cast_sub (show 1 ≤ Q by omega), Nat.cast_one] using h
  have hcost : ((Q : ℝ) * ((Q : ℝ) - 1)) / ((A : ℝ) + 1) ≤ 1 / 4 := by
    rw [div_le_iff₀ (by positivity)]
    linarith only [hAr]
  have hC : 0 ≤ ∑ m ∈ Icc 1 Q, a m ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hb := (abs_ramanujanPoleProfile_annular_gram_discrepancy_le hQ a A A).trans
    (mul_le_mul_of_nonneg_right hcost hC)
  obtain ⟨hl, hu⟩ := dyadic_harmonic_bounds hA0
  have hlC := mul_le_mul_of_nonneg_right hl hC
  have huC := mul_le_mul_of_nonneg_right hu hC
  rw [← two_mul A] at hb hlC huC
  obtain ⟨hlo, hup⟩ := abs_le.mp hb
  constructor <;> linarith only [hlo, hup, hlC, huC]

/-- One open dyadic annulus has no proper divisibility edge. Its frame geometry
therefore does not retain the prime transport between scales. -/
theorem weilPrimeKernel_eq_zero_on_dyadic_annulus {A m n : ℕ}
    (hm : m ∈ Icc (A + 1) (2 * A)) (hn : n ∈ Icc (A + 1) (2 * A)) :
    weilPrimeKernel m n = 0 := by
  have hdiv : ∀ u ∈ Icc (A + 1) (2 * A), ∀ v ∈ Icc (A + 1) (2 * A),
      ¬ (u ∣ v ∧ u ≠ v) := by
    intro u hu v hv
    rintro ⟨⟨k, rfl⟩, hne⟩
    have hu' := mem_Icc.mp hu
    have hv' := mem_Icc.mp hv
    have hk : 2 ≤ k := by
      by_contra h
      rcases (show k = 0 ∨ k = 1 by omega) with hk | hk
      · subst k
        simp only [mul_zero] at hv'
        omega
      · subst k
        exact hne (mul_one u).symm
    have hmul := Nat.mul_le_mul_left u hk
    nlinarith only [hu'.1, hv'.2, hmul]
  simp only [weilPrimeKernel, if_neg (hdiv m hm n hn), if_neg (hdiv n hn m hm)]

/-- The literal prime compression to one dyadic annulus is zero for every
signed coefficient vector; any prime energy transfer must cross its boundary. -/
theorem dyadic_annulus_prime_quadratic_eq_zero (A : ℕ) (x : ℕ → ℝ) :
    (∑ n ∈ Icc (A + 1) (2 * A), ∑ j ∈ Icc (A + 1) (2 * A),
      x n * x j * weilPrimeKernel n j) = 0 := by
  exact sum_eq_zero fun n hn => sum_eq_zero fun j hj => by
    rw [weilPrimeKernel_eq_zero_on_dyadic_annulus hn hj, mul_zero]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.abs_ramanujanPoleProfile_annular_gram_discrepancy_le
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ramanujanPoleProfile_dyadic_twoSided_frame
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.dyadic_annulus_prime_quadratic_eq_zero
