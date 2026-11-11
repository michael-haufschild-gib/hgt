import GaloisForLFunctions.HTGeometry.IntegerPowerSeriesBounds
import Mathlib.Analysis.MeanInequalities

/-!
# Power moments from dyadic mass bounds

A nonnegative sequence with mass `O(T^a)` on dyadic blocks has a finite
inverse-power moment at every exponent greater than `a`. The proof sums
the geometric majorants of the blocks, without a pointwise bound.
-/

open Finset Filter

namespace GaloisForLFunctions.HTGeometry

/-- Dyadic mass growth gives all strictly higher inverse-power moments. -/
theorem summable_div_rpow_of_dyadic_mass_bound {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) {a σ B : ℝ} (ha : 0 ≤ a) (haσ : a < σ)
    {j₀ : ℕ}
    (hblock : ∀ j, j₀ ≤ j →
      ∑ n ∈ Ioc (2 ^ j) (2 ^ (j + 1)), f n ≤ B * ((2 : ℝ) ^ j) ^ a) :
    Summable (fun n : ℕ => f n / (n : ℝ) ^ σ) := by
  classical
  let r : ℝ := (2 : ℝ) ^ (a - σ)
  have hr0 : 0 ≤ r := Real.rpow_nonneg (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (sub_neg.mpr haσ)
  let g : ℕ → ℝ := fun n => f n / (n : ℝ) ^ σ
  have hg : ∀ n, 0 ≤ g n := fun n => div_nonneg (hf n) (Real.rpow_nonneg (Nat.cast_nonneg n) σ)
  let b : ℕ → ℝ := fun j => ∑ n ∈ Ioc (2 ^ j) (2 ^ (j + 1)), g n
  have hb : ∀ j, 0 ≤ b j := fun j => sum_nonneg fun n _ => hg n
  have hbs : Summable b := by
    refine ((summable_geometric_of_lt_one hr0 hr1).mul_left |B|).of_norm_bounded_eventually ?_
    rw [eventually_cofinite]
    refine (Set.finite_lt_nat j₀).subset fun j hj => ?_
    simp only [Set.mem_setOf_eq, not_le] at hj ⊢
    by_contra hj0
    have hj₀ : j₀ ≤ j := le_of_not_gt hj0
    apply (not_lt.mpr ?_) hj
    rw [Real.norm_eq_abs, abs_of_nonneg (hb j)]
    have hpow : ((2 : ℝ) ^ j) ^ a / ((2 : ℝ) ^ j) ^ σ = r ^ j := by
      rw [← Real.rpow_sub (by positivity), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
        ← Real.rpow_mul (by norm_num)]
      congr 1
      ring
    calc
      b j ≤ ∑ n ∈ Ioc (2 ^ j) (2 ^ (j + 1)), f n / ((2 : ℝ) ^ j) ^ σ := by
        apply sum_le_sum
        intro n hn
        apply div_le_div_of_nonneg_left (hf n) (Real.rpow_pos_of_pos (by positivity) _)
        apply Real.rpow_le_rpow (by positivity) _ (ha.trans haσ.le)
        exact_mod_cast (mem_Ioc.mp hn).1.le
      _ = (∑ n ∈ Ioc (2 ^ j) (2 ^ (j + 1)), f n) / ((2 : ℝ) ^ j) ^ σ := by
        rw [sum_div]
      _ ≤ B * ((2 : ℝ) ^ j) ^ a / ((2 : ℝ) ^ j) ^ σ :=
        div_le_div_of_nonneg_right (hblock j hj₀) (by positivity)
      _ = B * r ^ j := by rw [mul_div_assoc, hpow]
      _ ≤ |B| * r ^ j := mul_le_mul_of_nonneg_right (le_abs_self B) (pow_nonneg hr0 _)
  have hdyad : ∀ J : ℕ, ∑ n ∈ Ioc 1 (2 ^ J), g n ≤ ∑ j ∈ range J, b j := by
    intro J
    induction J with
    | zero => simp
    | succ J ih =>
      rw [← sum_Ioc_consecutive g Nat.one_le_two_pow
        (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ J)), sum_range_succ]
      exact add_le_add ih le_rfl
  apply summable_of_sum_range_le (c := g 0 + g 1 + ∑' j, b j) hg
  intro T
  have hsplit : range (2 ^ T + 1) = ({0, 1} : Finset ℕ) ∪ Ioc 1 (2 ^ T) := by
    ext n
    simp only [mem_range, mem_union, mem_insert, mem_singleton, mem_Ioc]
    have := Nat.one_le_two_pow (n := T)
    omega
  have hdisj : Disjoint ({0, 1} : Finset ℕ) (Ioc 1 (2 ^ T)) := by
    apply disjoint_left.mpr
    intro n hn hn'
    simp only [mem_insert, mem_singleton] at hn
    have := (mem_Ioc.mp hn').1
    omega
  calc
    ∑ n ∈ range T, g n ≤ ∑ n ∈ range (2 ^ T + 1), g n :=
      sum_le_sum_of_subset_of_nonneg (range_subset_range.mpr (by
        have := Nat.lt_two_pow_self (n := T)
        omega)) (fun n _ _ => hg n)
    _ = g 0 + g 1 + ∑ n ∈ Ioc 1 (2 ^ T), g n := by
      rw [hsplit, sum_union hdisj, sum_pair (by decide)]
    _ ≤ g 0 + g 1 + ∑' j, b j :=
      add_le_add le_rfl ((hdyad T).trans (hbs.sum_le_tsum _ fun j _ => hb j))

/-- A weighted square moment gives lower moments of the normalized square
root. The inequality on exponents is precisely the summable Hölder tail. -/
theorem summable_sqrt_div_sq_rpow_of_weighted_moment {f : ℕ → ℝ}
    (hf : ∀ n, 0 ≤ f n) {a q : ℝ} (ha : 0 < a) (hq : 0 < q) (hq2 : q < 2)
    (haq : (a - 4) * q < q - 2)
    (hsum : Summable (fun n : ℕ => f n / (n : ℝ) ^ a)) :
    Summable (fun n : ℕ => (Real.sqrt (f n) / (n : ℝ) ^ 2) ^ q) := by
  let P := 2 / q
  let Q := Real.conjExponent P
  have hP : 1 < P := (lt_div_iff₀ hq).mpr (by simpa only [one_mul] using hq2)
  have hPQ : P.HolderConjugate Q := Real.HolderConjugate.conjExponent hP
  have hQeq : Q = 2 / (2 - q) := by
    rw [hPQ.conjugate_eq]
    dsimp [P]
    field_simp [hq.ne', (sub_pos.mpr hq2).ne']
  let x : ℕ → ℝ := fun n => (f n / (n : ℝ) ^ a) ^ (q / 2)
  let y : ℕ → ℝ := fun n => (n : ℝ) ^ ((a / 2 - 2) * q)
  have hx0 : ∀ n, 0 ≤ x n := fun n => Real.rpow_nonneg (by positivity [hf n]) _
  have hy0 : ∀ n, 0 ≤ y n := fun n => Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hx : Summable (fun n => x n ^ P) := by
    refine hsum.congr fun n => ?_
    dsimp [x, P]
    rw [← Real.rpow_mul (by positivity [hf n]),
      show q / 2 * (2 / q) = 1 by field_simp [hq.ne'], Real.rpow_one]
  have hexp : ((a / 2 - 2) * q) * Q < -1 := by
    rw [hQeq, show ((a / 2 - 2) * q) * (2 / (2 - q)) =
      (a - 4) * q / (2 - q) by ring]
    apply (div_lt_iff₀ (sub_pos.mpr hq2)).mpr
    linarith only [haq]
  have hy : Summable (fun n => y n ^ Q) := by
    refine (Real.summable_nat_rpow.mpr hexp).congr fun n => ?_
    exact Real.rpow_mul (Nat.cast_nonneg n) _ _
  refine (Real.summable_mul_of_Lp_Lq_of_nonneg hPQ hx0 hy0 hx hy).congr fun n => ?_
  by_cases hn : n = 0
  · subst n
    simp only [x, y, Nat.cast_zero, Real.zero_rpow ha.ne', div_zero,
      Real.zero_rpow (div_pos hq (by norm_num : (0 : ℝ) < 2)).ne', zero_mul,
      zero_pow (by decide : (2 : ℕ) ≠ 0), Real.zero_rpow hq.ne']
  have hn0 : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
  dsimp [x, y]
  rw [Real.div_rpow (hf n) (Real.rpow_nonneg hn0.le _),
    ← Real.rpow_mul hn0.le, Real.sqrt_eq_rpow,
    Real.div_rpow (Real.rpow_nonneg (hf n) _) (by positivity),
    ← Real.rpow_mul (hf n), ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
  have he : (n : ℝ) ^ ((a / 2 - 2) * q) * (n : ℝ) ^ (2 * q) =
      (n : ℝ) ^ (a * (q / 2)) := by
    rw [← Real.rpow_add hn0]
    congr 1
    ring
  have h1 : (n : ℝ) ^ (a * (q / 2)) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
  have h2 : (n : ℝ) ^ (2 * q) ≠ 0 := (Real.rpow_pos_of_pos hn0 _).ne'
  apply (eq_div_iff h2).mpr
  calc
    _ = f n ^ (q / 2) *
        ((n : ℝ) ^ ((a / 2 - 2) * q) * (n : ℝ) ^ (2 * q)) /
          (n : ℝ) ^ (a * (q / 2)) := by ring
    _ = f n ^ (q / 2) := by rw [he, mul_div_cancel_right₀ _ h1]
    _ = f n ^ ((1 / 2) * q) := by congr 1; ring

end GaloisForLFunctions.HTGeometry
