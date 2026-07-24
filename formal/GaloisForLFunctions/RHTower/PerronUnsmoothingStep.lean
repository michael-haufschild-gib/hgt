import GaloisForLFunctions.RHTower.PerronPowerLogPNT
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory

/-!
# The unsmoothing sandwich for the tent sum

`S(x) = ∑ Λ(n)·(log(x/n))⁺` increases by exactly `Λ(n)·log(y/x)` on
each `n ≤ x` and by at most that on `n ≤ y`, giving

`log(y/x)·ψ(⌊x⌋) ≤ S(y) − S(x) ≤ log(y/x)·ψ(⌊y⌋)`

— the two-sided difference quotient that recovers Chebyshev's `ψ`
from the smoothed Perron sum.
-/

noncomputable section

namespace RHTower

open ArithmeticFunction

/-- The real tent sum `∑ Λ(n)·(log(x/n))⁺`. -/
def perronTentSum (x : ℝ) : ℝ :=
  ∑' n : ℕ, ArithmeticFunction.vonMangoldt n
    * max (Real.log (x / n)) 0

/-- Tent terms vanish beyond `⌊x⌋`. -/
theorem perronTent_term_eq_zero {x : ℝ} {n : ℕ} (hx : 0 < x)
    (hn : ⌊x⌋₊ < n) :
    ArithmeticFunction.vonMangoldt n * max (Real.log (x / n)) 0
      = 0 := by
  have hxn : x < (n : ℝ) := (Nat.floor_lt hx.le).1 hn
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hlog : Real.log (x / n) ≤ 0 :=
    Real.log_nonpos (by positivity)
      (by rw [div_le_one hn0]; linarith)
  rw [max_eq_right hlog, mul_zero]

/-- The tent sum is summable (finite support). -/
theorem summable_perronTent {x : ℝ} (hx : 0 < x) :
    Summable (fun n : ℕ => ArithmeticFunction.vonMangoldt n
      * max (Real.log (x / n)) 0) := by
  apply summable_of_ne_finset_zero (s := Finset.range (⌊x⌋₊ + 1))
  intro n hn
  rw [Finset.mem_range, not_lt] at hn
  exact perronTent_term_eq_zero hx (by omega)

/-- The complex Perron sum realifies to the tent sum. -/
theorem norm_perron_sum_sub_eq {x : ℝ} :
    ‖(∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
        * ((max (Real.log (x / n)) 0 : ℝ) : ℂ)) - (x : ℂ)‖
      = |perronTentSum x - x| := by
  have h1 : (∑' n : ℕ, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
      * ((max (Real.log (x / n)) 0 : ℝ) : ℂ))
      = ((perronTentSum x : ℝ) : ℂ) := by
    rw [perronTentSum, Complex.ofReal_tsum]
    apply tsum_congr
    intro n
    rw [← Complex.ofReal_mul]
  rw [h1, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- **Lower sandwich**: `log(y/x)·ψ(⌊x⌋) ≤ S(y) − S(x)`. -/
theorem log_mul_psi_le_perronTent_sub {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    Real.log (y / x) * chebyshevPsi ⌊x⌋₊
      ≤ perronTentSum y - perronTentSum x := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  have hsx := summable_perronTent hx
  have hsy := summable_perronTent (x := y) hy0
  rw [perronTentSum, perronTentSum, ← Summable.tsum_sub hsy hsx]
  have hnonneg : ∀ n : ℕ,
      0 ≤ ArithmeticFunction.vonMangoldt n
          * max (Real.log (y / n)) 0
        - ArithmeticFunction.vonMangoldt n
          * max (Real.log (x / n)) 0 := by
    intro n
    have hmax : max (Real.log (x / n)) 0
        ≤ max (Real.log (y / n)) 0 := by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
        have hlog : Real.log (x / n) ≤ Real.log (y / n) :=
          Real.log_le_log (by positivity) (by gcongr)
        exact max_le_max hlog le_rfl
    have h2 := mul_le_mul_of_nonneg_left hmax
      (vonMangoldt_nonneg (n := n))
    linarith
  calc Real.log (y / x) * chebyshevPsi ⌊x⌋₊
      = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          ArithmeticFunction.vonMangoldt m * Real.log (y / x) := by
        rw [chebyshevPsi, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
    _ = ∑ m ∈ Finset.Icc 1 ⌊x⌋₊,
          (ArithmeticFunction.vonMangoldt m
              * max (Real.log (y / m)) 0
            - ArithmeticFunction.vonMangoldt m
              * max (Real.log (x / m)) 0) := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [Finset.mem_Icc] at hm
        have hm0 : (0 : ℝ) < (m : ℝ) := by
          exact_mod_cast hm.1
        have hmx : (m : ℝ) ≤ x :=
          le_trans (Nat.cast_le.2 hm.2) (Nat.floor_le hx.le)
        have hxm1 : 1 ≤ x / m := (one_le_div hm0).2 hmx
        have hym1 : 1 ≤ y / m :=
          (one_le_div hm0).2 (le_trans hmx hxy)
        rw [max_eq_left (Real.log_nonneg hxm1),
          max_eq_left (Real.log_nonneg hym1), ← mul_sub]
        congr 1
        rw [← Real.log_div (by positivity) (by positivity)]
        congr 1
        field_simp
    _ ≤ ∑' n : ℕ,
          (ArithmeticFunction.vonMangoldt n
              * max (Real.log (y / n)) 0
            - ArithmeticFunction.vonMangoldt n
              * max (Real.log (x / n)) 0) :=
        Summable.sum_le_tsum _ (fun n _ => hnonneg n) (hsy.sub hsx)

/-- **Upper sandwich**: `S(y) − S(x) ≤ log(y/x)·ψ(⌊y⌋)`. -/
theorem perronTent_sub_le_log_mul_psi {x y : ℝ} (hx : 0 < x)
    (hxy : x ≤ y) :
    perronTentSum y - perronTentSum x
      ≤ Real.log (y / x) * chebyshevPsi ⌊y⌋₊ := by
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le hx hxy
  have hsx := summable_perronTent hx
  have hsy := summable_perronTent (x := y) hy0
  rw [perronTentSum, perronTentSum, ← Summable.tsum_sub hsy hsx]
  have hlogyx : 0 ≤ Real.log (y / x) :=
    Real.log_nonneg ((one_le_div hx).2 hxy)
  have hgsum : Summable (fun n : ℕ =>
      if n ∈ Finset.Icc 1 ⌊y⌋₊
      then ArithmeticFunction.vonMangoldt n * Real.log (y / x)
      else 0) :=
    summable_of_ne_finset_zero (s := Finset.Icc 1 ⌊y⌋₊)
      (fun b hb => if_neg hb)
  have hpt : ∀ n : ℕ,
      ArithmeticFunction.vonMangoldt n * max (Real.log (y / n)) 0
        - ArithmeticFunction.vonMangoldt n
          * max (Real.log (x / n)) 0
      ≤ if n ∈ Finset.Icc 1 ⌊y⌋₊
        then ArithmeticFunction.vonMangoldt n * Real.log (y / x)
        else 0 := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [ArithmeticFunction.map_zero]
    · have hn0 : (0 : ℝ) < (n : ℝ) := Nat.cast_pos.2 hn
      rcases le_or_gt (n : ℝ) y with hny | hny
      · have hmem : n ∈ Finset.Icc 1 ⌊y⌋₊ :=
          Finset.mem_Icc.2 ⟨hn, Nat.le_floor hny⟩
        rw [if_pos hmem]
        rcases le_or_gt (n : ℝ) x with hnx | hnx
        · have h1 : 1 ≤ x / n := (one_le_div hn0).2 hnx
          have h2 : 1 ≤ y / n := (one_le_div hn0).2 hny
          rw [max_eq_left (Real.log_nonneg h1),
            max_eq_left (Real.log_nonneg h2), ← mul_sub]
          apply mul_le_mul_of_nonneg_left _
            (vonMangoldt_nonneg (n := n))
          apply le_of_eq
          rw [← Real.log_div (by positivity) (by positivity)]
          congr 1
          field_simp
        · have h3 : Real.log (x / n) ≤ 0 :=
            Real.log_nonpos (by positivity)
              (by rw [div_le_one hn0]; linarith)
          rw [max_eq_right h3, mul_zero, sub_zero]
          apply mul_le_mul_of_nonneg_left _
            (vonMangoldt_nonneg (n := n))
          apply max_le _ hlogyx
          apply Real.log_le_log (by positivity)
          exact div_le_div_of_nonneg_left hy0.le hx hnx.le
      · have hfl : ⌊y⌋₊ < n := (Nat.floor_lt hy0.le).2 hny
        have hnotmem : n ∉ Finset.Icc 1 ⌊y⌋₊ := by
          intro hmem
          exact absurd (Finset.mem_Icc.1 hmem).2 (by omega)
        rw [if_neg hnotmem]
        have h4 : Real.log (y / n) ≤ 0 :=
          Real.log_nonpos (by positivity)
            (by rw [div_le_one hn0]; linarith)
        have h5 : Real.log (x / n) ≤ 0 :=
          Real.log_nonpos (by positivity)
            (by rw [div_le_one hn0]; linarith)
        rw [max_eq_right h4, max_eq_right h5]
        norm_num
  calc ∑' n : ℕ,
        (ArithmeticFunction.vonMangoldt n
            * max (Real.log (y / n)) 0
          - ArithmeticFunction.vonMangoldt n
            * max (Real.log (x / n)) 0)
      ≤ ∑' n : ℕ,
          (if n ∈ Finset.Icc 1 ⌊y⌋₊
          then ArithmeticFunction.vonMangoldt n * Real.log (y / x)
          else 0) :=
        (hsy.sub hsx).tsum_le_tsum hpt hgsum
    _ = ∑ m ∈ Finset.Icc 1 ⌊y⌋₊,
          ArithmeticFunction.vonMangoldt m * Real.log (y / x) := by
        rw [tsum_eq_sum (s := Finset.Icc 1 ⌊y⌋₊)
          (fun b hb => if_neg hb)]
        apply Finset.sum_congr rfl
        intro m hm
        rw [if_pos hm]
    _ = Real.log (y / x) * chebyshevPsi ⌊y⌋₊ := by
        rw [chebyshevPsi, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring

end RHTower
