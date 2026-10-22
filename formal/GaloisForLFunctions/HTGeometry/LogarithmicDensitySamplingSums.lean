import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Summing a logarithmic density against a quadratically decaying kernel

A point set whose count in the unit window at height `n` grows like `log(|n|+3)`, sampled against
the kernel `(1+u²)⁻¹`, produces the sum

`K(x) = Σ_{n ∈ ℤ} log(|n|+3) (1 + (n − x)²)⁻¹`,

and the content here is that `K(x) ≲ log(|x|+3)`: the logarithmic density is *reproduced*, not
amplified, by a kernel of quadratic decay.  The two ingredients are the submultiplicativity
`log(|n|+3) ≤ log(|x|+3) + log(|n−x|+3)` and the convergence of
`Σ_k log(k+4)(1+(k−1)²)⁻¹`, which follows from `log y ≤ 2√y` and the `3/2`-series.
-/

open Filter

namespace GaloisForLFunctions.HTGeometry.LogDensity

noncomputable section
set_option autoImplicit false

/-! ## Elementary bounds -/

/-- `log y ≤ 2√y` for positive `y`, from `log u ≤ u − 1` at `u = √y`. -/
theorem log_le_two_mul_sqrt {y : ℝ} (hy : 0 < y) : Real.log y ≤ 2 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have h := Real.log_le_sub_one_of_pos hs
  have hsplit : Real.log y = Real.log (Real.sqrt y) + Real.log (Real.sqrt y) := by
    rw [← Real.log_mul (ne_of_gt hs) (ne_of_gt hs), Real.mul_self_sqrt hy.le]
  rw [hsplit]
  linarith

/-- Submultiplicativity of the shifted logarithm. -/
theorem log_abs_add_three_le (n x : ℝ) :
    Real.log (|n| + 3) ≤ Real.log (|x| + 3) + Real.log (|n - x| + 3) := by
  have h1 : (0:ℝ) < |x| + 3 := by positivity
  have h2 : (0:ℝ) < |n - x| + 3 := by positivity
  have htri : |n| ≤ |x| + |n - x| := by
    have h := abs_sub_abs_le_abs_sub n x
    linarith
  have hprod : |n| + 3 ≤ (|x| + 3) * (|n - x| + 3) := by
    nlinarith [abs_nonneg x, abs_nonneg (n - x), mul_nonneg (abs_nonneg x) (abs_nonneg (n - x))]
  calc Real.log (|n| + 3) ≤ Real.log ((|x| + 3) * (|n - x| + 3)) :=
        Real.log_le_log (by positivity) hprod
    _ = Real.log (|x| + 3) + Real.log (|n - x| + 3) := Real.log_mul (ne_of_gt h1) (ne_of_gt h2)

/-! ## The dominating series -/

/-- The comparison series for the shifted kernel. -/
def seriesTerm (k : ℕ) : ℝ := Real.log ((k : ℝ) + 4) * (1 + ((k : ℝ) - 1) ^ 2)⁻¹

theorem seriesTerm_nonneg (k : ℕ) : 0 ≤ seriesTerm k := by
  have hk : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
  refine mul_nonneg (Real.log_nonneg (by linarith)) ?_
  positivity

theorem summable_seriesTerm : Summable seriesTerm := by
  have hbase : Summable fun k : ℕ => (((k : ℝ)) ^ (3 / 2 : ℝ))⁻¹ :=
    Real.summable_nat_rpow_inv.mpr (by norm_num)
  have hdom : Summable fun k : ℕ => (16 : ℝ) * ((((k : ℕ) + 2 : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
    have hshift : Summable fun k : ℕ => ((((k : ℕ) + 2 : ℝ)) ^ (3 / 2 : ℝ))⁻¹ := by
      have := (summable_nat_add_iff 2).mpr hbase
      refine this.congr fun k => ?_
      push_cast
      ring_nf
    exact hshift.mul_left 16
  rw [← summable_nat_add_iff 2]
  refine Summable.of_nonneg_of_le (fun k => seriesTerm_nonneg (k + 2)) ?_ hdom
  intro k
  have hkpos : (0:ℝ) < ((k : ℕ) + 2 : ℝ) := by positivity
  have hk2 : (2:ℝ) ≤ ((k : ℕ) + 2 : ℝ) := by
    have : (0:ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  set K : ℝ := ((k : ℕ) + 2 : ℝ) with hK
  have hcast : seriesTerm (k + 2) = Real.log (K + 4) * (1 + (K - 1) ^ 2)⁻¹ := by
    simp only [seriesTerm, hK]
    push_cast
    ring_nf
  have hden : (1 + (K - 1) ^ 2)⁻¹ ≤ 4 * (K ^ 2)⁻¹ := by
    have hpos1 : (0:ℝ) < 1 + (K - 1) ^ 2 := by positivity
    have hpos2 : (0:ℝ) < K ^ 2 := by positivity
    have hq : (0:ℝ) < K ^ 2 / 4 := by positivity
    have hle : K ^ 2 / 4 ≤ 1 + (K - 1) ^ 2 := by nlinarith
    have hstep : (1:ℝ) / (1 + (K - 1) ^ 2) ≤ 1 / (K ^ 2 / 4) :=
      one_div_le_one_div_of_le hq hle
    have heq1 : (1:ℝ) / (1 + (K - 1) ^ 2) = (1 + (K - 1) ^ 2)⁻¹ := one_div _
    have heq2 : (1:ℝ) / (K ^ 2 / 4) = 4 * (K ^ 2)⁻¹ := by
      field_simp
    rw [heq1, heq2] at hstep
    exact hstep
  have hlog : Real.log (K + 4) ≤ 4 * Real.sqrt K := by
    have h1 : Real.log (K + 4) ≤ 2 * Real.sqrt (K + 4) := log_le_two_mul_sqrt (by linarith)
    have hsq4 : Real.sqrt (4 : ℝ) = 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    have h2 : Real.sqrt (K + 4) ≤ 2 * Real.sqrt K := by
      rw [show (2 : ℝ) * Real.sqrt K = Real.sqrt (4 * K) by
        rw [Real.sqrt_mul (by norm_num), hsq4]]
      exact Real.sqrt_le_sqrt (by linarith)
    linarith
  have hrp : Real.sqrt K * (K ^ 2)⁻¹ = (K ^ (3 / 2 : ℝ))⁻¹ := by
    have hnat : (K ^ 2 : ℝ) = K ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast K 2]
      norm_num
    rw [Real.sqrt_eq_rpow, hnat, ← Real.rpow_neg hkpos.le, ← Real.rpow_add hkpos,
      ← Real.rpow_neg hkpos.le]
    norm_num
  rw [hcast]
  calc Real.log (K + 4) * (1 + (K - 1) ^ 2)⁻¹
      ≤ (4 * Real.sqrt K) * (4 * (K ^ 2)⁻¹) := by
        refine mul_le_mul hlog hden (by positivity) (by positivity)
    _ = 16 * (Real.sqrt K * (K ^ 2)⁻¹) := by ring
    _ = 16 * (K ^ (3 / 2 : ℝ))⁻¹ := by rw [hrp]

/-! ## The uniform bound on the integers -/

/-- Twice the comparison term, indexed by `ℤ` through the absolute value. -/
def domTerm (n : ℤ) : ℝ := 2 * seriesTerm n.natAbs

theorem domTerm_nonneg (n : ℤ) : 0 ≤ domTerm n := by
  have := seriesTerm_nonneg n.natAbs
  simp only [domTerm]
  linarith

theorem natAbs_neg_succ (n : ℕ) : (-((n : ℤ) + 1)).natAbs = n + 1 := by omega

theorem natAbs_cast (n : ℕ) : ((n : ℤ)).natAbs = n := by omega

theorem domTerm_neg_succ_eq : (fun n : ℕ => domTerm (-((n : ℤ) + 1))) =
    fun n : ℕ => 2 * seriesTerm (n + 1) := by
  funext n
  simp only [domTerm, natAbs_neg_succ]

theorem domTerm_cast_eq : (fun n : ℕ => domTerm (n : ℤ)) = fun n : ℕ => 2 * seriesTerm n := by
  funext n
  simp only [domTerm, natAbs_cast]

theorem summable_domTerm : Summable domTerm := by
  refine Summable.of_nat_of_neg_add_one ?_ ?_
  · rw [domTerm_cast_eq]
    exact summable_seriesTerm.mul_left 2
  · rw [domTerm_neg_succ_eq]
    exact ((summable_nat_add_iff 1).mpr summable_seriesTerm).mul_left 2

theorem tsum_domTerm_le : ∑' n : ℤ, domTerm n ≤ 4 * ∑' k : ℕ, seriesTerm k := by
  have h1 : Summable fun n : ℕ => domTerm (n : ℤ) := by
    rw [domTerm_cast_eq]; exact summable_seriesTerm.mul_left 2
  have h2 : Summable fun n : ℕ => domTerm (-((n : ℤ) + 1)) := by
    rw [domTerm_neg_succ_eq]
    exact ((summable_nat_add_iff 1).mpr summable_seriesTerm).mul_left 2
  rw [tsum_of_nat_of_neg_add_one h1 h2]
  have e1 : (∑' n : ℕ, domTerm (n : ℤ)) = 2 * ∑' k : ℕ, seriesTerm k := by
    rw [domTerm_cast_eq]; exact tsum_mul_left
  have e2 : (∑' n : ℕ, domTerm (-((n : ℤ) + 1))) ≤ 2 * ∑' k : ℕ, seriesTerm k := by
    rw [domTerm_neg_succ_eq, tsum_mul_left]
    have h0 : (∑' k : ℕ, seriesTerm k) = seriesTerm 0 + ∑' n : ℕ, seriesTerm (n + 1) :=
      summable_seriesTerm.tsum_eq_zero_add
    have hz := seriesTerm_nonneg 0
    have hle : (∑' n : ℕ, seriesTerm (n + 1)) ≤ ∑' k : ℕ, seriesTerm k := by linarith
    linarith
  linarith [e1, e2]

/-- One term of the shifted sum against the comparison term. -/
theorem log_kernel_frac_le {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y < 1) (m : ℤ) :
    Real.log (|(m : ℝ) - y| + 3) * (1 + ((m : ℝ) - y) ^ 2)⁻¹ ≤ domTerm m := by
  have hcast : |(m : ℝ)| = (m.natAbs : ℝ) := by simp
  have hnn : (0:ℝ) ≤ (m.natAbs : ℝ) := Nat.cast_nonneg _
  have hub : |(m : ℝ) - y| ≤ (m.natAbs : ℝ) + 1 := by
    have h := abs_sub (m : ℝ) y
    rw [hcast, abs_of_nonneg hy0] at h
    linarith
  have hlb : (m.natAbs : ℝ) - 1 ≤ |(m : ℝ) - y| := by
    have h := abs_sub_abs_le_abs_sub (m : ℝ) y
    rw [hcast, abs_of_nonneg hy0] at h
    linarith
  have hlog : Real.log (|(m : ℝ) - y| + 3) ≤ Real.log ((m.natAbs : ℝ) + 4) :=
    Real.log_le_log (by positivity) (by linarith)
  have hlogpos : 0 ≤ Real.log ((m.natAbs : ℝ) + 4) := Real.log_nonneg (by linarith)
  have hkerpos : (0:ℝ) < 1 + ((m : ℝ) - y) ^ 2 := by positivity
  have hdom : domTerm m =
      2 * (Real.log ((m.natAbs : ℝ) + 4) * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹) := by
    simp only [domTerm, seriesTerm]
  rcases Nat.lt_or_ge m.natAbs 2 with hklt | hkge
  · have hk1 : ((m.natAbs : ℝ) - 1) ^ 2 ≤ 1 := by
      interval_cases h : m.natAbs <;> norm_num
    have hcomp : (1:ℝ) ≤ 2 * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹ := by
      rw [le_mul_inv_iff₀ (by positivity)]
      linarith
    have hker : (1 + ((m : ℝ) - y) ^ 2)⁻¹ ≤ 1 := by
      rw [inv_le_one_iff₀]
      right
      nlinarith [sq_nonneg ((m : ℝ) - y)]
    rw [hdom]
    calc Real.log (|(m : ℝ) - y| + 3) * (1 + ((m : ℝ) - y) ^ 2)⁻¹
        ≤ Real.log ((m.natAbs : ℝ) + 4) * 1 := mul_le_mul hlog hker (by positivity) hlogpos
      _ ≤ Real.log ((m.natAbs : ℝ) + 4) * (2 * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹) :=
          mul_le_mul_of_nonneg_left hcomp hlogpos
      _ = 2 * (Real.log ((m.natAbs : ℝ) + 4) * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹) := by ring
  · have hk2 : (2:ℝ) ≤ (m.natAbs : ℝ) := by exact_mod_cast hkge
    have hsq : ((m.natAbs : ℝ) - 1) ^ 2 ≤ ((m : ℝ) - y) ^ 2 := by
      have habs : ((m.natAbs : ℝ) - 1) ^ 2 ≤ |(m : ℝ) - y| ^ 2 := by
        nlinarith [abs_nonneg ((m : ℝ) - y)]
      rwa [sq_abs] at habs
    have hker : (1 + ((m : ℝ) - y) ^ 2)⁻¹ ≤ (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹ := by
      have h1 : (0:ℝ) < 1 + ((m.natAbs : ℝ) - 1) ^ 2 := by positivity
      have h := one_div_le_one_div_of_le h1 (by linarith : 1 + ((m.natAbs : ℝ) - 1) ^ 2 ≤
        1 + ((m : ℝ) - y) ^ 2)
      rwa [one_div, one_div] at h
    have hposterm : 0 ≤ Real.log ((m.natAbs : ℝ) + 4) * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹ :=
      mul_nonneg hlogpos (by positivity)
    rw [hdom]
    calc Real.log (|(m : ℝ) - y| + 3) * (1 + ((m : ℝ) - y) ^ 2)⁻¹
        ≤ Real.log ((m.natAbs : ℝ) + 4) * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹ :=
          mul_le_mul hlog hker (by positivity) hlogpos
      _ ≤ 2 * (Real.log ((m.natAbs : ℝ) + 4) * (1 + ((m.natAbs : ℝ) - 1) ^ 2)⁻¹) := by linarith

/-- The log-weighted kernel family is summable over the integers, for every shift. -/
theorem summable_log_kernel (x : ℝ) :
    Summable fun n : ℤ => Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by
  set j : ℤ := ⌊x⌋ with hj
  set y : ℝ := Int.fract x with hy
  have hy0 : 0 ≤ y := Int.fract_nonneg x
  have hy1 : y < 1 := Int.fract_lt_one x
  have hxj : x = (j : ℝ) + y := by rw [hy, Int.fract, hj]; ring
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_three]
  have hlogx : (0:ℝ) ≤ Real.log (|x| + 3) := by
    have : (1:ℝ) ≤ Real.log (|x| + 3) := by
      refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
      linarith [abs_nonneg x]
    linarith
  have hterm : ∀ n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
      (Real.log (|x| + 3) + 1) * domTerm (n - j) := by
    intro n
    have hshift : (n : ℝ) - x = ((n - j : ℤ) : ℝ) - y := by
      rw [hxj]; push_cast; ring
    have hkerpos : (0:ℝ) < 1 + ((n : ℝ) - x) ^ 2 := by positivity
    have hsub := log_abs_add_three_le (n : ℝ) x
    have hone : (1:ℝ) ≤ Real.log (|(n : ℝ) - x| + 3) := by
      refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
      linarith [abs_nonneg ((n : ℝ) - x)]
    have hbase : Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
        domTerm (n - j) := by
      rw [hshift] at *
      exact log_kernel_frac_le hy0 hy1 (n - j)
    have hkerle : (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
        Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by
      nlinarith [inv_nonneg.mpr hkerpos.le]
    calc Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹
        ≤ (Real.log (|x| + 3) + Real.log (|(n : ℝ) - x| + 3)) *
            (1 + ((n : ℝ) - x) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr hkerpos.le)
      _ = Real.log (|x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ +
            Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by ring
      _ ≤ (Real.log (|x| + 3) + 1) * domTerm (n - j) := by
          nlinarith [hbase, hkerle, hlogx]
  have hmaj : Summable fun n : ℤ => (Real.log (|x| + 3) + 1) * domTerm (n - j) :=
    (((Equiv.subRight j).summable_iff).mpr summable_domTerm).mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) hterm hmaj
  have hp : (0:ℝ) < 1 + ((n : ℝ) - x) ^ 2 := by positivity
  exact mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ))])) (by positivity)

/-- **The kernel reproduces a logarithmic density.**  Sampling `log(|n|+3)(1+(n−x)²)⁻¹` over the
integers gives at most a constant multiple of `log(|x|+3)`, uniformly in `x`. -/
theorem exists_bound_tsum_log_kernel :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ,
      ∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
        C * Real.log (|x| + 3) := by
  have hS0 : 0 ≤ ∑' k : ℕ, seriesTerm k := tsum_nonneg seriesTerm_nonneg
  have hlog3 : (1:ℝ) ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    linarith [Real.exp_one_lt_three]
  refine ⟨8 * ∑' k : ℕ, seriesTerm k, by positivity, fun x => ?_⟩
  have hlogx : (1:ℝ) ≤ Real.log (|x| + 3) := by
    refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
    linarith [abs_nonneg x]
  set j : ℤ := ⌊x⌋ with hj
  set y : ℝ := Int.fract x with hy
  have hy0 : 0 ≤ y := Int.fract_nonneg x
  have hy1 : y < 1 := Int.fract_lt_one x
  have hxj : x = (j : ℝ) + y := by rw [hy, Int.fract, hj]; ring
  -- termwise comparison against a shifted copy of the comparison series
  have hterm : ∀ n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
      (Real.log (|x| + 3) + 1) * domTerm (n - j) := by
    intro n
    have hshift : (n : ℝ) - x = ((n - j : ℤ) : ℝ) - y := by
      rw [hxj]; push_cast; ring
    have hkerpos : (0:ℝ) < 1 + ((n : ℝ) - x) ^ 2 := by positivity
    have hsub := log_abs_add_three_le (n : ℝ) x
    have hone : (1:ℝ) ≤ Real.log (|(n : ℝ) - x| + 3) := by
      refine hlog3.trans (Real.log_le_log (by norm_num) ?_)
      linarith [abs_nonneg ((n : ℝ) - x)]
    have hbase : Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
        domTerm (n - j) := by
      rw [hshift] at *
      exact log_kernel_frac_le hy0 hy1 (n - j)
    have hkerle : (1 + ((n : ℝ) - x) ^ 2)⁻¹ ≤
        Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by
      nlinarith [inv_nonneg.mpr hkerpos.le]
    have hlogxpos : (0:ℝ) ≤ Real.log (|x| + 3) := by linarith
    calc Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹
        ≤ (Real.log (|x| + 3) + Real.log (|(n : ℝ) - x| + 3)) *
            (1 + ((n : ℝ) - x) ^ 2)⁻¹ :=
          mul_le_mul_of_nonneg_right hsub (inv_nonneg.mpr hkerpos.le)
      _ = Real.log (|x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ +
            Real.log (|(n : ℝ) - x| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by ring
      _ ≤ (Real.log (|x| + 3) + 1) * domTerm (n - j) := by
          nlinarith [hbase, hkerle, hlogxpos]
  -- the majorant is summable, with the same total as the comparison series
  have hmaj : Summable fun n : ℤ => (Real.log (|x| + 3) + 1) * domTerm (n - j) :=
    (((Equiv.subRight j).summable_iff).mpr summable_domTerm).mul_left _
  have hsum : Summable fun n : ℤ => Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹ := by
    refine Summable.of_nonneg_of_le (fun n => ?_) hterm hmaj
    have : (0:ℝ) < 1 + ((n : ℝ) - x) ^ 2 := by positivity
    exact mul_nonneg (Real.log_nonneg (by linarith [abs_nonneg ((n : ℝ))])) (by positivity)
  have htotal : (∑' n : ℤ, (Real.log (|x| + 3) + 1) * domTerm (n - j)) =
      (Real.log (|x| + 3) + 1) * ∑' n : ℤ, domTerm n := by
    rw [tsum_mul_left]
    congr 1
    exact (Equiv.subRight j).tsum_eq domTerm
  calc (∑' n : ℤ, Real.log (|(n : ℝ)| + 3) * (1 + ((n : ℝ) - x) ^ 2)⁻¹)
      ≤ ∑' n : ℤ, (Real.log (|x| + 3) + 1) * domTerm (n - j) :=
        Summable.tsum_le_tsum hterm hsum hmaj
    _ = (Real.log (|x| + 3) + 1) * ∑' n : ℤ, domTerm n := htotal
    _ ≤ (Real.log (|x| + 3) + 1) * (4 * ∑' k : ℕ, seriesTerm k) :=
        mul_le_mul_of_nonneg_left tsum_domTerm_le (by linarith)
    _ ≤ (8 * ∑' k : ℕ, seriesTerm k) * Real.log (|x| + 3) := by
        nlinarith [hlogx, hS0]

end

end GaloisForLFunctions.HTGeometry.LogDensity
