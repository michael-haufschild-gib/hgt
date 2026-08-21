import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Prod
import GaloisForLFunctions.RHTower.Sieve.IntegerRowSum
import GaloisForLFunctions.HTGeometry.IntervalMeanSquareMoment

/-!
# Fixed-ambient spatial Mellin L² estimate for Maynard cells

Maynard's prime-gap argument keeps selected Dirichlet-polynomial cells fixed while physical base
varies. This module proves missing spatial estimate in that coherent geometry. Positive-ray Mellin
Gram kernel decays harmonically in frequency separation; unit-cell reparameterization and Jensen
reduce continuous cells to integer-separated discrete packets.

Final theorem gives explicit `R log N` bound for any finite selected cell family with uniform
coefficient envelope. No coefficient or support data may depend on physical base.
-/

open Complex intervalIntegral MeasureTheory

noncomputable section

namespace RHTower.Sieve

theorem integral_maynardMellinGramKernel_eq
    {x c t u : ℝ} (hc : 0 ≤ c) :
    (∫ y : ℝ in x..(2 * x),
      (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I)) =
      ((((2 * x : ℝ) : ℂ) ^
          ((((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) + 1)) -
        ((x : ℂ) ^
          ((((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) + 1))) /
        ((((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) + 1) := by
  rw [integral_cpow]
  left
  simp only [add_re, ofReal_re, ofReal_im, mul_re, I_re, I_im, mul_zero, mul_one]
  linarith

/-- Exact positive-ray Mellin Gram kernel has reciprocal frequency decay. -/
theorem norm_maynardMellinGramKernel_le
    {x c t u : ℝ} (hx : 0 < x) (hc : 0 ≤ c) :
    ‖∫ y : ℝ in x..(2 * x),
      (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I)‖ ≤
      4 * (2 * x) ^ (2 * c + 1) / (1 + |t - u|) := by
  rw [integral_maynardMellinGramKernel_eq hc, norm_div]
  let z : ℂ := (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) + 1
  have hzre : z.re = 2 * c + 1 := by
    dsimp only [z]
    simp
  have hzim : z.im = t - u := by
    dsimp only [z]
    simp
  have h2x : 0 < 2 * x := by positivity
  have hpowx : ‖((x : ℂ) ^ z)‖ = x ^ (2 * c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hzre]
  have hpow2x : ‖(((2 * x : ℝ) : ℂ) ^ z)‖ = (2 * x) ^ (2 * c + 1) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos h2x, hzre]
  have hpowmono : x ^ (2 * c + 1) ≤ (2 * x) ^ (2 * c + 1) := by
    exact Real.rpow_le_rpow hx.le (by linarith) (by linarith)
  have hnum : ‖(((2 * x : ℝ) : ℂ) ^ z) - ((x : ℂ) ^ z)‖ ≤
      2 * (2 * x) ^ (2 * c + 1) := by
    calc
      ‖(((2 * x : ℝ) : ℂ) ^ z) - ((x : ℂ) ^ z)‖ ≤
          ‖(((2 * x : ℝ) : ℂ) ^ z)‖ + ‖((x : ℂ) ^ z)‖ := norm_sub_le _ _
      _ = (2 * x) ^ (2 * c + 1) + x ^ (2 * c + 1) := by rw [hpow2x, hpowx]
      _ ≤ 2 * (2 * x) ^ (2 * c + 1) := by linarith
  have hzabs : |t - u| ≤ ‖z‖ := by
    rw [← hzim]
    exact Complex.abs_im_le_norm z
  have hzone : 1 ≤ ‖z‖ := by
    have := Complex.abs_re_le_norm z
    rw [hzre, abs_of_nonneg (by linarith : 0 ≤ 2 * c + 1)] at this
    linarith
  have hzsum : 1 + |t - u| ≤ 2 * ‖z‖ := by linarith
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hzone
  have hdenpos : 0 < 1 + |t - u| := by positivity
  have hpow0 : 0 ≤ (2 * x) ^ (2 * c + 1) := Real.rpow_nonneg h2x.le _
  calc
    ‖(((2 * x : ℝ) : ℂ) ^ z) - ((x : ℂ) ^ z)‖ / ‖z‖ ≤
        (2 * (2 * x) ^ (2 * c + 1)) / ‖z‖ :=
      div_le_div_of_nonneg_right hnum hzpos.le
    _ ≤ 4 * (2 * x) ^ (2 * c + 1) / (1 + |t - u|) := by
      rw [div_le_div_iff₀ hzpos hdenpos]
      nlinarith

theorem cpow_mul_conj_cpow_eq_maynardMellinKernel
    {y c t u : ℝ} (hy : 0 < y) :
    ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) *
        star ((y : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)) =
      (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) := by
  have harg : ((y : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hy.le]
    exact ne_of_lt Real.pi_pos
  have hconj :
      star ((y : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)) =
        (y : ℂ) ^ (star ((c : ℂ) + (u : ℂ) * I)) := by
    simpa using
      (Complex.cpow_conj (y : ℂ) ((c : ℂ) + (u : ℂ) * I) harg).symm
  have hexp :
      ((c : ℂ) + (t : ℂ) * I) + star ((c : ℂ) + (u : ℂ) * I) =
        ((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp <;> ring
  calc
    ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) *
        star ((y : ℂ) ^ ((c : ℂ) + (u : ℂ) * I)) =
      ((y : ℂ) ^ ((c : ℂ) + (t : ℂ) * I)) *
        ((y : ℂ) ^ star ((c : ℂ) + (u : ℂ) * I)) := by rw [hconj]
    _ = (y : ℂ) ^ (((c : ℂ) + (t : ℂ) * I) +
        star ((c : ℂ) + (u : ℂ) * I)) :=
      (Complex.cpow_add _ _ (ofReal_ne_zero.mpr hy.ne')).symm
    _ = (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I) := by rw [hexp]

/-- Fixed-frequency Mellin packet used before restoring continuous unit cells. -/
def maynardDiscreteMellinPacket
    (S : Finset ℕ) (a : ℕ → ℂ) (c y : ℝ) : ℂ :=
  ∑ m ∈ S, a m * (y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I)

theorem maynardDiscreteMellinPacket_mul_star_eq
    {y c : ℝ} (hy : 0 < y) (S : Finset ℕ) (a : ℕ → ℂ) :
    maynardDiscreteMellinPacket S a c y * star (maynardDiscreteMellinPacket S a c y) =
      ∑ m ∈ S, ∑ n ∈ S,
        (a m * star (a n)) *
          (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((m : ℝ) - n : ℝ) : ℂ) * I) := by
  classical
  simp only [maynardDiscreteMellinPacket, star_sum, star_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hkernel :
      (y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I) *
          star ((y : ℂ) ^ ((c : ℂ) + (n : ℂ) * I)) =
        (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((m : ℝ) - n : ℝ) : ℂ) * I) := by
    simpa using
      (cpow_mul_conj_cpow_eq_maynardMellinKernel
        (y := y) (c := c) (t := (m : ℝ)) (u := (n : ℝ)) hy)
  calc
    a m * (y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I) *
        (star ((y : ℂ) ^ ((c : ℂ) + (n : ℂ) * I)) * star (a n)) =
      (a m * star (a n)) *
        ((y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I) *
          star ((y : ℂ) ^ ((c : ℂ) + (n : ℂ) * I))) := by ring
    _ = (a m * star (a n)) *
        (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((m : ℝ) - n : ℝ) : ℂ) * I) := by
      rw [hkernel]

theorem continuousOn_maynardDiscreteMellinPacket
    {x c : ℝ} (hx : 0 < x) (S : Finset ℕ) (a : ℕ → ℂ) :
    ContinuousOn (maynardDiscreteMellinPacket S a c) (Set.uIcc x (2 * x)) := by
  classical
  rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)]
  apply continuousOn_finsetSum S
  intro m hm
  apply continuousOn_const.mul
  apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
  intro y hy
  left
  have hypos : 0 < y := lt_of_lt_of_le hx hy.1
  simpa using hypos

theorem intervalIntegrable_maynardDiscreteMellinPacket_mul_star
    {x c : ℝ} (hx : 0 < x) (S : Finset ℕ) (a : ℕ → ℂ) :
    IntervalIntegrable
      (fun y => maynardDiscreteMellinPacket S a c y *
        star (maynardDiscreteMellinPacket S a c y)) volume x (2 * x) := by
  exact ((continuousOn_maynardDiscreteMellinPacket hx S a).mul
    (continuousOn_maynardDiscreteMellinPacket hx S a).star).intervalIntegrable

theorem intervalIntegrable_maynardMellinGramKernel
    {x c t u : ℝ} (hx : 0 < x) :
    IntervalIntegrable
      (fun y : ℝ =>
        (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + ((t - u : ℝ) : ℂ) * I))
      volume x (2 * x) := by
  apply ContinuousOn.intervalIntegrable
  rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)]
  apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
  intro y hy
  left
  have hypos : 0 < y := lt_of_lt_of_le hx hy.1
  simpa using hypos

theorem integral_maynardDiscreteMellinPacket_mul_star_eq
    {x c : ℝ} (hx : 0 < x) (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ y : ℝ in x..(2 * x),
      maynardDiscreteMellinPacket S a c y *
        star (maynardDiscreteMellinPacket S a c y)) =
      ∑ m ∈ S, ∑ n ∈ S,
        (a m * star (a n)) *
          (∫ y : ℝ in x..(2 * x),
            (y : ℂ) ^ (((2 * c : ℝ) : ℂ) + (((m : ℝ) - n : ℝ) : ℂ) * I)) := by
  classical
  rw [intervalIntegral.integral_congr]
  · rw [intervalIntegral.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro m hm
      rw [intervalIntegral.integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro n hn
        rw [intervalIntegral.integral_const_mul]
      · intro n hn
        exact (intervalIntegrable_maynardMellinGramKernel
          (x := x) (c := c) (t := (m : ℝ)) (u := (n : ℝ)) hx).const_mul _
    · intro m hm
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_finsetSum S
      intro n hn
      exact (continuousOn_const.mul
        (by
          rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)]
          apply ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
          intro y hy
          left
          have hypos : 0 < y := lt_of_lt_of_le hx hy.1
          simpa using hypos))
  · intro y hy
    apply maynardDiscreteMellinPacket_mul_star_eq
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
    exact lt_of_lt_of_le hx hy.1

theorem integral_norm_sq_maynardDiscreteMellinPacket_le_gram
    {x c : ℝ} (hx : 0 < x) (hc : 0 ≤ c)
    (S : Finset ℕ) (a : ℕ → ℂ) :
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
      ∑ m ∈ S, ∑ n ∈ S,
        ‖a m‖ * ‖a n‖ *
          (4 * (2 * x) ^ (2 * c + 1) /
            (1 + |(m : ℝ) - (n : ℝ)|)) := by
  classical
  let P : ℝ → ℂ := maynardDiscreteMellinPacket S a c
  have hnonneg : 0 ≤ ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    positivity
  have hcoe :
      (((∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2) : ℝ) : ℂ) =
        ∫ y : ℝ in x..(2 * x), P y * star (P y) := by
    rw [← intervalIntegral.integral_ofReal]
    apply intervalIntegral.integral_congr
    intro y hy
    change ((‖P y‖ ^ 2 : ℝ) : ℂ) = P y * star (P y)
    rw [Complex.ofReal_pow]
    simpa only [RCLike.star_def] using (Complex.mul_conj' (P y)).symm
  have hexpand :
      (∫ y : ℝ in x..(2 * x), P y * star (P y)) =
        ∑ m ∈ S, ∑ n ∈ S,
          (a m * star (a n)) *
            (∫ y : ℝ in x..(2 * x),
              (y : ℂ) ^ (((2 * c : ℝ) : ℂ) +
                (((m : ℝ) - n : ℝ) : ℂ) * I)) := by
    exact integral_maynardDiscreteMellinPacket_mul_star_eq hx S a
  calc
    (∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2) =
        |∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2| := (abs_of_nonneg hnonneg).symm
    _ = ‖(((∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2) : ℝ) : ℂ)‖ := by simp
    _ = ‖∫ y : ℝ in x..(2 * x), P y * star (P y)‖ := by rw [hcoe]
    _ = ‖∑ m ∈ S, ∑ n ∈ S,
          (a m * star (a n)) *
            (∫ y : ℝ in x..(2 * x),
              (y : ℂ) ^ (((2 * c : ℝ) : ℂ) +
                (((m : ℝ) - n : ℝ) : ℂ) * I))‖ := by rw [hexpand]
    _ ≤ ∑ m ∈ S, ‖∑ n ∈ S,
          (a m * star (a n)) *
            (∫ y : ℝ in x..(2 * x),
              (y : ℂ) ^ (((2 * c : ℝ) : ℂ) +
                (((m : ℝ) - n : ℝ) : ℂ) * I))‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          ‖(a m * star (a n)) *
            (∫ y : ℝ in x..(2 * x),
              (y : ℂ) ^ (((2 * c : ℝ) : ℂ) +
                (((m : ℝ) - n : ℝ) : ℂ) * I))‖ := by
      apply Finset.sum_le_sum
      intro m hm
      exact norm_sum_le _ _
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
        ‖a m‖ * ‖a n‖ *
          (4 * (2 * x) ^ (2 * c + 1) /
            (1 + |(m : ℝ) - (n : ℝ)|)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_mul, norm_mul, norm_star]
      have hk := norm_maynardMellinGramKernel_le
        (x := x) (c := c) (t := (m : ℝ)) (u := (n : ℝ)) hx hc
      exact mul_le_mul_of_nonneg_left hk (mul_nonneg (norm_nonneg _) (norm_nonneg _))

theorem sum_one_div_one_add_abs_int_dist_le
    {N m : ℕ} (hm : m < N) :
    ∑ n ∈ Finset.range N, 1 / (1 + |(n : ℝ) - (m : ℝ)|) ≤
      1 + 2 * (1 + Real.log N) := by
  classical
  have hmem : m ∈ Finset.range N := Finset.mem_range.mpr hm
  have hsplit : insert m ((Finset.range N).erase m) = Finset.range N :=
    Finset.insert_erase hmem
  rw [← hsplit, Finset.sum_insert (by simp)]
  simp only [sub_self, abs_zero, add_zero, div_one]
  have hoff :
      ∑ n ∈ (Finset.range N).erase m,
          1 / (1 + |(n : ℝ) - (m : ℝ)|) ≤
        ∑ n ∈ (Finset.range N).erase m,
          1 / |(n : ℝ) - (m : ℝ)| := by
    apply Finset.sum_le_sum
    intro n hn
    have hne : n ≠ m := (Finset.mem_erase.mp hn).1
    have hdiff : 0 < |(n : ℝ) - (m : ℝ)| := by
      rw [abs_pos, sub_ne_zero]
      exact_mod_cast hne
    exact one_div_le_one_div_of_le hdiff (by linarith)
  have hrow := RHTower.Sieve.sum_inv_abs_int_dist_le hm
  linarith

theorem sum_subset_one_div_one_add_abs_int_dist_le
    {N m : ℕ} {S : Finset ℕ}
    (hS : S ⊆ Finset.range N) (hm : m ∈ S) :
    ∑ n ∈ S, 1 / (1 + |(n : ℝ) - (m : ℝ)|) ≤
      1 + 2 * (1 + Real.log N) := by
  have hsub :
      ∑ n ∈ S, 1 / (1 + |(n : ℝ) - (m : ℝ)|) ≤
        ∑ n ∈ Finset.range N, 1 / (1 + |(n : ℝ) - (m : ℝ)|) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hS
    intro n hn hnS
    positivity
  exact hsub.trans (sum_one_div_one_add_abs_int_dist_le
    (Finset.mem_range.mp (hS hm)))

theorem integral_norm_sq_maynardDiscreteMellinPacket_le_card
    {x c A : ℝ} {N : ℕ} (hx : 0 < x) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (a : ℕ → ℂ)
    (ha : ∀ m ∈ S, ‖a m‖ ≤ A) :
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * c + 1) * A ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log N)) := by
  classical
  let K : ℝ := 4 * (2 * x) ^ (2 * c + 1)
  let H : ℝ := 1 + 2 * (1 + Real.log N)
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hbase := integral_norm_sq_maynardDiscreteMellinPacket_le_gram hx hc S a
  calc
    (∫ y : ℝ in x..(2 * x), ‖maynardDiscreteMellinPacket S a c y‖ ^ 2) ≤
        ∑ m ∈ S, ∑ n ∈ S,
          ‖a m‖ * ‖a n‖ *
            (K / (1 + |(m : ℝ) - (n : ℝ)|)) := by
      simpa only [K] using hbase
    _ ≤ ∑ m ∈ S, ∑ n ∈ S,
          A ^ 2 * K * (1 / (1 + |(n : ℝ) - (m : ℝ)|)) := by
      apply Finset.sum_le_sum
      intro m hm
      apply Finset.sum_le_sum
      intro n hn
      have hprod : ‖a m‖ * ‖a n‖ ≤ A * A :=
        mul_le_mul (ha m hm) (ha n hn) (norm_nonneg _) hA
      have hden : 0 ≤ K / (1 + |(m : ℝ) - (n : ℝ)|) := by positivity
      calc
        ‖a m‖ * ‖a n‖ * (K / (1 + |(m : ℝ) - (n : ℝ)|)) ≤
            (A * A) * (K / (1 + |(m : ℝ) - (n : ℝ)|)) :=
          mul_le_mul_of_nonneg_right hprod hden
        _ = A ^ 2 * K * (1 / (1 + |(n : ℝ) - (m : ℝ)|)) := by
          rw [abs_sub_comm]
          ring
    _ = ∑ m ∈ S,
          A ^ 2 * K *
            (∑ n ∈ S, 1 / (1 + |(n : ℝ) - (m : ℝ)|)) := by
      apply Finset.sum_congr rfl
      intro m hm
      rw [Finset.mul_sum]
    _ ≤ ∑ _m ∈ S, A ^ 2 * K * H := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (sum_subset_one_div_one_add_abs_int_dist_le hS hm)
        (mul_nonneg (sq_nonneg A) hK)
    _ = 4 * (2 * x) ^ (2 * c + 1) * A ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log N)) := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      dsimp only [K, H]
      ring

/-- Continuous selected-cell integrand after writing `t = m + v`, `0 ≤ v ≤ 1`. -/
def maynardUnitCellMellinIntegrand
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c v y : ℝ) : ℂ :=
  ∑ m ∈ S, b m v *
    (y : ℂ) ^ ((c : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I)

/-- Fixed-ambient sum of selected unit-cell Mellin integrals. -/
def maynardUnitCellMellinPacket
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c y : ℝ) : ℂ :=
  ∫ v : ℝ in (0 : ℝ)..1, maynardUnitCellMellinIntegrand S b c v y

def maynardUnitCellMellinIntegrandPosExtension
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c v y : ℝ) : ℂ :=
  ∑ m ∈ S, b m v *
    ((max 1 y : ℝ) : ℂ) ^
      ((c : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I)

def maynardUnitCellMellinPacketPosExtension
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c y : ℝ) : ℂ :=
  ∫ v : ℝ in (0 : ℝ)..1,
    maynardUnitCellMellinIntegrandPosExtension S b c v y

theorem continuous_maynardUnitCellMellinIntegrandPosExtension
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c : ℝ)
    (hb : ∀ m ∈ S, Continuous (b m)) :
    Continuous fun p : ℝ × ℝ =>
      maynardUnitCellMellinIntegrandPosExtension S b c p.1 p.2 := by
  classical
  apply continuous_finsetSum S
  intro m hm
  apply (hb m hm).comp continuous_fst |>.mul
  have hbase : Continuous fun p : ℝ × ℝ => ((max 1 p.2 : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (continuous_const.max continuous_snd)
  have hexp : Continuous fun p : ℝ × ℝ =>
      (c : ℂ) + ((((m : ℝ) + p.1 : ℝ) : ℂ) * I) := by fun_prop
  apply hbase.cpow hexp
  intro p
  left
  have hp : (0 : ℝ) < max 1 p.2 := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  simp [hp]

theorem continuous_maynardUnitCellMellinPacketPosExtension
    (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c : ℝ)
    (hb : ∀ m ∈ S, Continuous (b m)) :
    Continuous (maynardUnitCellMellinPacketPosExtension S b c) := by
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  · have h := continuous_maynardUnitCellMellinIntegrandPosExtension S b c hb
    exact h.comp (continuous_snd.prodMk continuous_fst)

theorem maynardUnitCellMellinIntegrandPosExtension_eq
    {y : ℝ} (hy : 1 ≤ y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c v : ℝ) :
    maynardUnitCellMellinIntegrandPosExtension S b c v y =
      maynardUnitCellMellinIntegrand S b c v y := by
  simp only [maynardUnitCellMellinIntegrandPosExtension,
    maynardUnitCellMellinIntegrand, max_eq_right hy]

theorem maynardUnitCellMellinPacketPosExtension_eq
    {y : ℝ} (hy : 1 ≤ y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c : ℝ) :
    maynardUnitCellMellinPacketPosExtension S b c y =
      maynardUnitCellMellinPacket S b c y := by
  apply intervalIntegral.integral_congr
  intro v hv
  exact maynardUnitCellMellinIntegrandPosExtension_eq hy S b c v

theorem maynardUnitCellMellinIntegrand_eq_phase_mul_discrete
    {y : ℝ} (hy : 0 < y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c v : ℝ) :
    maynardUnitCellMellinIntegrand S b c v y =
      (y : ℂ) ^ ((v : ℂ) * I) *
        maynardDiscreteMellinPacket S (fun m => b m v) c y := by
  classical
  rw [maynardUnitCellMellinIntegrand, maynardDiscreteMellinPacket,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hexp :
      (v : ℂ) * I + ((c : ℂ) + (m : ℂ) * I) =
        (c : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I := by
    apply Complex.ext
    · simp
    · simp
      ring
  calc
    b m v * (y : ℂ) ^ ((c : ℂ) + (((m : ℝ) + v : ℝ) : ℂ) * I) =
        b m v * (y : ℂ) ^
          ((v : ℂ) * I + ((c : ℂ) + (m : ℂ) * I)) := by rw [hexp]
    _ = b m v *
        ((y : ℂ) ^ ((v : ℂ) * I) *
          (y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I)) := by
      rw [Complex.cpow_add _ _ (ofReal_ne_zero.mpr hy.ne')]
    _ = (y : ℂ) ^ ((v : ℂ) * I) *
        (b m v * (y : ℂ) ^ ((c : ℂ) + (m : ℂ) * I)) := by ring

theorem norm_maynardUnitCellMellinIntegrand_eq_discrete
    {y : ℝ} (hy : 0 < y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c v : ℝ) :
    ‖maynardUnitCellMellinIntegrand S b c v y‖ =
      ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ := by
  rw [maynardUnitCellMellinIntegrand_eq_phase_mul_discrete hy,
    norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hy]
  have hre : (((v : ℂ) * I).re) = 0 := by simp
  rw [hre, Real.rpow_zero, one_mul]

theorem continuous_maynardUnitCellMellinIntegrand_fixed_base
    {y : ℝ} (hy : 1 ≤ y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c : ℝ)
    (hb : ∀ m ∈ S, Continuous (b m)) :
    Continuous fun v : ℝ => maynardUnitCellMellinIntegrand S b c v y := by
  have hpos := continuous_maynardUnitCellMellinIntegrandPosExtension S b c hb
  have hslice : Continuous fun v : ℝ =>
      maynardUnitCellMellinIntegrandPosExtension S b c v y :=
    hpos.comp (continuous_id.prodMk continuous_const)
  have heq : (fun v : ℝ => maynardUnitCellMellinIntegrandPosExtension S b c v y) =
      fun v : ℝ => maynardUnitCellMellinIntegrand S b c v y := by
    funext v
    exact maynardUnitCellMellinIntegrandPosExtension_eq hy S b c v
  rwa [heq] at hslice

theorem norm_sq_maynardUnitCellMellinPacket_le_integral_discrete
    {y : ℝ} (hy : 1 ≤ y) (S : Finset ℕ) (b : ℕ → ℝ → ℂ) (c : ℝ)
    (hb : ∀ m ∈ S, Continuous (b m)) :
    ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 ≤
      ∫ v : ℝ in (0 : ℝ)..1,
        ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := by
  let D : ℝ → ℂ := fun v => maynardUnitCellMellinIntegrand S b c v y
  have hD : Continuous D := continuous_maynardUnitCellMellinIntegrand_fixed_base hy S b c hb
  have hnorm : ‖maynardUnitCellMellinPacket S b c y‖ ≤
      ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ := by
    exact intervalIntegral.norm_integral_le_integral_norm zero_le_one
  have hcs :=
    GaloisForLFunctions.HTGeometry.integral_norm_le_sqrt_length_mul_sqrt_meanSquare
      hD (a := (0 : ℝ)) (b := 1) zero_le_one
  simp only [sub_zero, Real.sqrt_one, one_mul] at hcs
  have hI2nonneg : 0 ≤ ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 2 := by
    apply intervalIntegral.integral_nonneg zero_le_one
    intro v hv
    positivity
  have hsqrt := Real.sq_sqrt hI2nonneg
  have hbound : ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 ≤
      ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 2 := by
    nlinarith [norm_nonneg (maynardUnitCellMellinPacket S b c y),
      Real.sqrt_nonneg (∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 2)]
  calc
    ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 ≤
        ∫ v : ℝ in (0 : ℝ)..1, ‖D v‖ ^ 2 := hbound
    _ = ∫ v : ℝ in (0 : ℝ)..1,
        ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro v hv
      change ‖maynardUnitCellMellinIntegrand S b c v y‖ ^ 2 =
        ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2
      rw [norm_maynardUnitCellMellinIntegrand_eq_discrete (lt_of_lt_of_le zero_lt_one hy)]

theorem intervalIntegral_swap_of_continuous_maynard
    {F : ℝ → ℝ → ℝ} (hF : Continuous fun p : ℝ × ℝ => F p.1 p.2)
    (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, F x y) =
      ∫ y in c..d, ∫ x in a..b, F x y := by
  apply MeasureTheory.intervalIntegral_intervalIntegral_swap
  have hcompact : IsCompact (Set.uIcc a b ×ˢ Set.uIcc c d) :=
    isCompact_uIcc.prod isCompact_uIcc
  have hint : IntegrableOn (Function.uncurry F)
      (Set.uIcc a b ×ˢ Set.uIcc c d) :=
    hF.continuousOn.integrableOn_compact hcompact
  exact hint.mono_set
    (Set.prod_mono Set.uIoc_subset_uIcc Set.uIoc_subset_uIcc)

/-- **Maynard spatial L² bound for fixed selected unit cells.** Uniform cell envelope `A` and
`R = S.card` selected integer cells below `N` give explicit `A² R log N` spatial mean square.
Coefficient functions depend on cell coordinate `v`, but not physical base `y`. -/
theorem integral_norm_sq_maynardUnitCellMellinPacket_le_card
    {x c A : ℝ} {N : ℕ} (hx : 1 ≤ x) (hc : 0 ≤ c) (hA : 0 ≤ A)
    (S : Finset ℕ) (hS : S ⊆ Finset.range N) (b : ℕ → ℝ → ℂ)
    (hb : ∀ m ∈ S, Continuous (b m))
    (hbnd : ∀ m ∈ S, ∀ v ∈ Set.Icc (0 : ℝ) 1, ‖b m v‖ ≤ A) :
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) ≤
      4 * (2 * x) ^ (2 * c + 1) * A ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log N)) := by
  classical
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  let Q : ℝ → ℝ → ℂ := fun v y =>
    maynardUnitCellMellinIntegrandPosExtension S b c v y
  let P : ℝ → ℂ := maynardUnitCellMellinPacketPosExtension S b c
  let F : ℝ → ℝ → ℝ := fun y v => ‖Q v y‖ ^ 2
  let C : ℝ := 4 * (2 * x) ^ (2 * c + 1) * A ^ 2 * (S.card : ℝ) *
    (1 + 2 * (1 + Real.log N))
  have hQ : Continuous fun p : ℝ × ℝ => Q p.1 p.2 := by
    exact continuous_maynardUnitCellMellinIntegrandPosExtension S b c hb
  have hP : Continuous P := by
    exact continuous_maynardUnitCellMellinPacketPosExtension S b c hb
  have hF : Continuous fun p : ℝ × ℝ => F p.1 p.2 := by
    dsimp only [F]
    exact (hQ.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2
  have hleft :
      (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    change ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 =
      ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 2
    rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
  have hpoint : ∀ y ∈ Set.Icc x (2 * x),
      ‖P y‖ ^ 2 ≤ ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    intro y hy
    have hy1 : 1 ≤ y := hx.trans hy.1
    have hj := norm_sq_maynardUnitCellMellinPacket_le_integral_discrete
      hy1 S b c hb
    calc
      ‖P y‖ ^ 2 = ‖maynardUnitCellMellinPacket S b c y‖ ^ 2 := by
        change ‖maynardUnitCellMellinPacketPosExtension S b c y‖ ^ 2 = _
        rw [maynardUnitCellMellinPacketPosExtension_eq hy1]
      _ ≤ ∫ v : ℝ in (0 : ℝ)..1,
          ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := hj
      _ = ∫ v : ℝ in (0 : ℝ)..1, F y v := by
        apply intervalIntegral.integral_congr
        intro v hv
        dsimp only [F, Q]
        rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
          norm_maynardUnitCellMellinIntegrand_eq_discrete
            (lt_of_lt_of_le zero_lt_one hy1)]
  have hinnerContinuous : Continuous fun y => ∫ v : ℝ in (0 : ℝ)..1, F y v :=
    intervalIntegral.continuous_parametric_intervalIntegral_of_continuous' hF 0 1
  have hmono :
      (∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2) ≤
        ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := by
    have hleftContinuous : Continuous fun y => ‖P y‖ ^ 2 := hP.norm.pow 2
    exact intervalIntegral.integral_mono_on (by linarith)
      (hleftContinuous.intervalIntegrable x (2 * x))
      (hinnerContinuous.intervalIntegrable x (2 * x)) hpoint
  have hswap :
      (∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v) =
        ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v :=
    intervalIntegral_swap_of_continuous_maynard hF x (2 * x) 0 1
  have houterContinuous : Continuous fun v => ∫ y : ℝ in x..(2 * x), F y v := by
    change Continuous fun v => ∫ y : ℝ in x..(2 * x), ‖Q v y‖ ^ 2
    have hFswap : Continuous fun p : ℝ × ℝ => ‖Q p.1 p.2‖ ^ 2 := hQ.norm.pow 2
    exact intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      hFswap x (2 * x)
  have houterPoint : ∀ v ∈ Set.Icc (0 : ℝ) 1,
      (∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    intro v hv
    have heq :
        (∫ y : ℝ in x..(2 * x), F y v) =
          ∫ y : ℝ in x..(2 * x),
            ‖maynardDiscreteMellinPacket S (fun m => b m v) c y‖ ^ 2 := by
      apply intervalIntegral.integral_congr
      intro y hy
      rw [Set.uIcc_of_le (by linarith : x ≤ 2 * x)] at hy
      have hy1 : 1 ≤ y := hx.trans hy.1
      dsimp only [F, Q]
      rw [maynardUnitCellMellinIntegrandPosExtension_eq hy1,
        norm_maynardUnitCellMellinIntegrand_eq_discrete
          (lt_of_lt_of_le zero_lt_one hy1)]
    rw [heq]
    have hd := integral_norm_sq_maynardDiscreteMellinPacket_le_card
      hxpos hc hA S hS (fun m => b m v) (fun m hm => hbnd m hm v hv)
    simpa only [C] using hd
  have houter :
      (∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v) ≤ C := by
    have hcst : IntervalIntegrable (fun _v : ℝ => C) volume 0 1 :=
      continuous_const.intervalIntegrable 0 1
    have hle := intervalIntegral.integral_mono_on zero_le_one
      (houterContinuous.intervalIntegrable 0 1) hcst houterPoint
    simpa using hle
  calc
    (∫ y : ℝ in x..(2 * x), ‖maynardUnitCellMellinPacket S b c y‖ ^ 2) =
        ∫ y : ℝ in x..(2 * x), ‖P y‖ ^ 2 := hleft
    _ ≤ ∫ y : ℝ in x..(2 * x), ∫ v : ℝ in (0 : ℝ)..1, F y v := hmono
    _ = ∫ v : ℝ in (0 : ℝ)..1, ∫ y : ℝ in x..(2 * x), F y v := hswap
    _ ≤ C := houter
    _ = 4 * (2 * x) ^ (2 * c + 1) * A ^ 2 * (S.card : ℝ) *
        (1 + 2 * (1 + Real.log N)) := rfl

end RHTower.Sieve

end
