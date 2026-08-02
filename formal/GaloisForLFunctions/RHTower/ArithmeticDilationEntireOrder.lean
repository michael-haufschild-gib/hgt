import GaloisForLFunctions.RHTower.ArithmeticDilationDeterminantZeros
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exact half-order growth of the arithmetic dilation determinant

The constrained-prolate arithmetic eigenvalues have critical real-power summability exponent
`1/2`.  The bare positive Fredholm product therefore has global upper growth for every exponent
strictly larger than `1/2`.  A uniform reciprocal-square lower bound on the eigenvalues makes the
product grow at least exponentially in `N` along radii of size `N²`, ruling out every smaller
order.  This proves both exact divisor exponent and exact classical entire order `1/2`.
-/

noncomputable section

open Filter Set

namespace RHTower

theorem constrainedProlateArithmeticEigenvalue_le_log_div_sq (n : ℕ) :
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ≤
      2 * Real.log (((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ) ^ 2 := by
  let k : ℕ := n + 2
  have hklog : 0 ≤ Real.log k / (k : ℝ) ^ 2 := by
    exact div_nonneg (GaloisForLFunctions.log_natCast_nonneg k) (sq_nonneg _)
  have hs := GaloisForLFunctions.arcsine_slice_le_pi_half_log_div_sq k
  rw [GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_eq]
  dsimp only
  calc
    (16 / (11 * Real.pi)) * (Real.log (k : ℝ) / k * Real.arcsin (1 / (k : ℝ))) ≤
        (16 / (11 * Real.pi)) *
          (Real.pi / 2 * (Real.log k / (k : ℝ) ^ 2)) :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    _ = (8 / 11 : ℝ) * (Real.log k / (k : ℝ) ^ 2) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ 2 * Real.log k / (k : ℝ) ^ 2 := by
      rw [show 2 * Real.log k / (k : ℝ) ^ 2 =
        2 * (Real.log k / (k : ℝ) ^ 2) by ring]
      exact mul_le_mul_of_nonneg_right (by norm_num) hklog

theorem summable_constrainedProlateArithmeticEigenvalue_rpow
    {p : ℝ} (hp : 1 / 2 < p) :
    Summable (fun n =>
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ^ p) := by
  let ε : ℝ := (2 * p - 1) / (2 * p)
  have hp0 : 0 < p := by linarith
  have hε0 : 0 < ε := by
    dsimp [ε]
    exact div_pos (by linarith) (by positivity)
  have hs : 1 < p + 1 / 2 := by linarith
  have hbase : Summable (fun n : ℕ =>
      1 / |(n : ℝ) + 2| ^ (p + 1 / 2)) :=
    (Real.summable_one_div_nat_add_rpow 2 (p + 1 / 2)).mpr hs
  have hmajor : Summable (fun n : ℕ =>
      (2 / ε) ^ p / ((n + 2 : ℕ) : ℝ) ^ (p + 1 / 2)) := by
    refine hbase.mul_left ((2 / ε) ^ p) |>.congr (fun n => ?_)
    rw [abs_of_pos (by positivity : (0 : ℝ) < (n : ℝ) + 2)]
    simp [div_eq_mul_inv, Nat.cast_add, Nat.cast_ofNat]
  apply Summable.of_nonneg_of_le
    (fun n => Real.rpow_nonneg
      (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg n) p)
    (fun n => ?_) hmajor
  let k : ℝ := ((n + 2 : ℕ) : ℝ)
  have hk0 : 0 < k := by dsimp [k]; positivity
  have hlog := Real.log_le_rpow_div hk0.le hε0
  have heig := constrainedProlateArithmeticEigenvalue_le_log_div_sq n
  have hraw :
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ≤
        (2 / ε) * k ^ ε / k ^ 2 := by
    dsimp only [k]
    calc
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ≤
          2 * Real.log (((n + 2 : ℕ) : ℝ)) / ((n + 2 : ℕ) : ℝ) ^ 2 := heig
      _ ≤ 2 * (((n + 2 : ℕ) : ℝ) ^ ε / ε) /
          ((n + 2 : ℕ) : ℝ) ^ 2 := by
        gcongr
      _ = (2 / ε) * ((n + 2 : ℕ) : ℝ) ^ ε /
          ((n + 2 : ℕ) : ℝ) ^ 2 := by ring
  have hrpow := Real.rpow_le_rpow
    (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg n)
    hraw hp0.le
  calc
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ^ p ≤
        ((2 / ε) * k ^ ε / k ^ 2) ^ p := hrpow
    _ = (2 / ε) ^ p / k ^ (p + 1 / 2) := by
      rw [Real.div_rpow (mul_nonneg (by positivity) (Real.rpow_nonneg hk0.le ε))
        (sq_nonneg k), Real.mul_rpow (by positivity) (Real.rpow_nonneg hk0.le ε)]
      rw [← Real.rpow_mul hk0.le]
      rw [← Real.rpow_natCast k 2, ← Real.rpow_mul hk0.le]
      have hεp : ε * p = p - 1 / 2 := by
        dsimp [ε]
        field_simp
      rw [hεp]
      norm_num only [Nat.cast_ofNat]
      rw [show (2 / ε) ^ p * k ^ (p - 1 / 2) / k ^ (2 * p) =
        (2 / ε) ^ p * (k ^ (p - 1 / 2) / k ^ (2 * p)) by ring]
      rw [← Real.rpow_sub hk0]
      rw [show p - 1 / 2 - 2 * p = -(p + 1 / 2) by ring,
        Real.rpow_neg hk0.le]
      ring
    _ = (2 / ε) ^ p / ((n + 2 : ℕ) : ℝ) ^ (p + 1 / 2) := rfl

theorem one_add_le_exp_const_mul_rpow {x p : ℝ}
    (hx : 0 ≤ x) (hp0 : 0 < p) (hp1 : p ≤ 1) :
    1 + x ≤ Real.exp ((1 + 1 / p) * x ^ p) := by
  by_cases hx1 : x ≤ 1
  · have hxp : x ≤ x ^ p := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' hx hx1 hp0.le hp1
    calc
      1 + x ≤ Real.exp x := by simpa [add_comm] using Real.add_one_le_exp x
      _ ≤ Real.exp ((1 + 1 / p) * x ^ p) := by
        apply Real.exp_le_exp.mpr
        have hp_inv : 0 ≤ 1 / p := by positivity
        nlinarith [Real.rpow_nonneg hx p]
  · have hx1' : 1 < x := lt_of_not_ge hx1
    have hlog := Real.log_le_rpow_div hx hp0
    have hxpow1 : 1 ≤ x ^ p := Real.one_le_rpow hx1'.le hp0.le
    have hlog2 : Real.log 2 ≤ x ^ p := by
      linarith [Real.log_two_lt_d9]
    calc
      1 + x ≤ 2 * x := by linarith
      _ = Real.exp (Real.log 2 + Real.log x) := by
        rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log (by positivity)]
      _ ≤ Real.exp ((1 + 1 / p) * x ^ p) := by
        apply Real.exp_le_exp.mpr
        calc
          Real.log 2 + Real.log x ≤ x ^ p + x ^ p / p := add_le_add hlog2 hlog
          _ = (1 + 1 / p) * x ^ p := by ring

theorem arithmeticDiagonalFredholmDeterminant_norm_le_exp_rpow
    (g : ℕ → ℝ) (hg0 : ∀ n, 0 ≤ g n) (hg : Summable g) {p : ℝ}
    (hp0 : 0 < p) (hp1 : p ≤ 1)
    (hgp : Summable fun n => g n ^ p) (z : ℂ) :
    ‖arithmeticDiagonalFredholmDeterminant (fun n => (g n : ℂ)) z‖ ≤
      Real.exp ((1 + 1 / p) * ‖z‖ ^ p * ∑' n, g n ^ p) := by
  have hmult := multipliable_arithmeticDiagonalFredholmDeterminant
    (fun n => (g n : ℂ)) (by
      simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hg) z
  rw [arithmeticDiagonalFredholmDeterminant, hmult.norm_tprod]
  apply tprod_le_of_prod_le'
    (Real.one_le_exp (mul_nonneg
      (mul_nonneg (by positivity) (Real.rpow_nonneg (norm_nonneg z) p))
      (tsum_nonneg fun n => Real.rpow_nonneg (hg0 n) p)))
  intro s
  calc
    ∏ n ∈ s, ‖1 + z * (g n : ℂ)‖ ≤
        ∏ n ∈ s, Real.exp ((1 + 1 / p) * (‖z‖ * g n) ^ p) := by
      apply Finset.prod_le_prod
      · intro n _
        exact norm_nonneg _
      · intro n _
        calc
          ‖1 + z * (g n : ℂ)‖ ≤ 1 + ‖z‖ * g n := by
            simpa [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hg0 n)] using norm_add_le 1 (z * (g n : ℂ))
          _ ≤ Real.exp ((1 + 1 / p) * (‖z‖ * g n) ^ p) :=
            one_add_le_exp_const_mul_rpow (mul_nonneg (norm_nonneg z) (hg0 n)) hp0 hp1
    _ = Real.exp (∑ n ∈ s, ((1 + 1 / p) * (‖z‖ * g n) ^ p)) := by
      rw [← Real.exp_sum]
    _ ≤ Real.exp ((1 + 1 / p) * ‖z‖ ^ p * ∑' n, g n ^ p) := by
      apply Real.exp_le_exp.mpr
      have hconst : 0 ≤ (1 + 1 / p) * ‖z‖ ^ p := by positivity
      have heq : ∑ n ∈ s, (1 + 1 / p) * (‖z‖ * g n) ^ p =
          ((1 + 1 / p) * ‖z‖ ^ p) * ∑ n ∈ s, g n ^ p := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n _
        rw [Real.mul_rpow (norm_nonneg z) (hg0 n)]
        ring
      rw [heq]
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
        (hgp.sum_le_tsum s (fun n _ => Real.rpow_nonneg (hg0 n) p)) hconst

theorem one_tenth_div_sq_le_constrainedProlateArithmeticEigenvalue (n : ℕ) :
    (1 / 10 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2 ≤
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n := by
  let k : ℕ := n + 2
  have hk2 : (2 : ℝ) ≤ k := by
    exact_mod_cast (show 2 ≤ n + 2 by omega)
  have hklog : Real.log 2 ≤ Real.log k :=
    Real.log_le_log (by norm_num) hk2
  have hcoef : (1 / 10 : ℝ) ≤
      (16 / (11 * Real.pi)) * Real.log 2 := by
    rw [show (16 / (11 * Real.pi)) * Real.log 2 =
      16 * Real.log 2 / (11 * Real.pi) by ring]
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < 11 * Real.pi)]
    nlinarith [Real.pi_lt_four, Real.log_two_gt_d9]
  have hslice := GaloisForLFunctions.log_div_sq_le_arcsine_slice k
  rw [GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_eq]
  dsimp only
  calc
    (1 / 10 : ℝ) / (k : ℝ) ^ 2 ≤
        ((16 / (11 * Real.pi)) * Real.log 2) / (k : ℝ) ^ 2 := by
      gcongr
    _ ≤ ((16 / (11 * Real.pi)) * Real.log k) / (k : ℝ) ^ 2 := by
      gcongr
    _ = (16 / (11 * Real.pi)) * (Real.log k / (k : ℝ) ^ 2) := by ring
    _ ≤ (16 / (11 * Real.pi)) *
        (Real.log k / k * Real.arcsin (1 / (k : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hslice (by positivity)

theorem constrainedProlateArithmeticFredholmDeterminant_norm_lower_nat (N : ℕ) :
    (2 : ℝ) ^ N ≤
      ‖constrainedProlateArithmeticFredholmDeterminant
        ((10 * ((N + 2 : ℕ) : ℝ) ^ 2 : ℝ) : ℂ)‖ := by
  let R : ℝ := 10 * ((N + 2 : ℕ) : ℝ) ^ 2
  let g : ℕ → ℝ := GaloisForLFunctions.constrainedProlateArithmeticEigenvalue
  have hg0 : ∀ n, 0 ≤ g n :=
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg
  have hg : Summable g :=
    GaloisForLFunctions.summable_constrainedProlateArithmeticEigenvalue
  have hmult : Multipliable fun n : ℕ =>
      1 + (R : ℂ) * (g n : ℂ) :=
    multipliable_arithmeticDiagonalFredholmDeterminant
      (fun n => (g n : ℂ)) (by
        simpa [Real.norm_eq_abs, abs_of_nonneg (hg0 _)] using hg) R
  have hmultNorm : Multipliable fun n : ℕ =>
      ‖1 + (R : ℂ) * (g n : ℂ)‖ := hmult.hasProd.norm.multipliable
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hfac (n : ℕ) :
      ‖1 + (R : ℂ) * (g n : ℂ)‖ = 1 + R * g n := by
    have heq : 1 + (R : ℂ) * (g n : ℂ) = ((1 + R * g n : ℝ) : ℂ) := by
      norm_cast
    rw [heq, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by exact add_nonneg zero_le_one (mul_nonneg hR0 (hg0 n)))]
  rw [constrainedProlateArithmeticFredholmDeterminant,
    arithmeticDiagonalFredholmDeterminant, hmult.norm_tprod]
  calc
    (2 : ℝ) ^ N = ∏ _n ∈ Finset.range N, (2 : ℝ) := by simp
    _ ≤ ∏ n ∈ Finset.range N, ‖1 + (R : ℂ) * (g n : ℂ)‖ := by
      apply Finset.prod_le_prod
      · intro _ _
        positivity
      · intro n hn
        rw [hfac]
        have hnle : ((n + 2 : ℕ) : ℝ) ^ 2 ≤ ((N + 2 : ℕ) : ℝ) ^ 2 := by
          gcongr
          exact_mod_cast (Nat.le_of_lt (Finset.mem_range.mp hn))
        have heig := one_tenth_div_sq_le_constrainedProlateArithmeticEigenvalue n
        have hden : 0 < ((n + 2 : ℕ) : ℝ) ^ 2 := by positivity
        have hmain : 1 ≤ R * g n := by
          calc
            1 = R * ((1 / 10 : ℝ) / ((N + 2 : ℕ) : ℝ) ^ 2) := by
              dsimp [R]
              field_simp
            _ ≤ R * ((1 / 10 : ℝ) / ((n + 2 : ℕ) : ℝ) ^ 2) := by
              gcongr
            _ ≤ R * g n := mul_le_mul_of_nonneg_left heig hR0
        linarith
    _ ≤ ∏' n : ℕ, ‖1 + (R : ℂ) * (g n : ℂ)‖ := by
      apply ge_of_tendsto hmultNorm.hasProd
      filter_upwards [eventually_ge_atTop (Finset.range N)] with t ht
      exact Finset.prod_le_prod_of_subset_of_one_le ht
        (fun _ _ => norm_nonneg _)
        (fun n _ _ => by
          rw [hfac]
          exact le_add_of_nonneg_right (mul_nonneg hR0 (hg0 n)))

/- A global growth definition equivalent to classical exact order for an entire function. -/
def HasExactEntireOrder (f : ℂ → ℂ) (ρ : ℝ) : Prop :=
  Differentiable ℂ f ∧
    (∀ p : ℝ, ρ < p → ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) ^ p)) ∧
    ∀ p : ℝ, p < ρ → ∀ C : ℝ, 0 < C → ∃ z : ℂ,
      Real.exp (C * (1 + ‖z‖) ^ p) < ‖f z‖

theorem constrainedProlateArithmeticFredholmDeterminant_upper_order
    {p : ℝ} (hp : 1 / 2 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ,
      ‖constrainedProlateArithmeticFredholmDeterminant z‖ ≤
        Real.exp (C * (1 + ‖z‖) ^ p) := by
  let g : ℕ → ℝ := GaloisForLFunctions.constrainedProlateArithmeticEigenvalue
  have hg0 : ∀ n, 0 ≤ g n :=
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_nonneg
  have hg : Summable g :=
    GaloisForLFunctions.summable_constrainedProlateArithmeticEigenvalue
  by_cases hp1 : p ≤ 1
  · have hp0 : 0 < p := by linarith
    have hgp : Summable fun n => g n ^ p :=
      summable_constrainedProlateArithmeticEigenvalue_rpow hp
    let C : ℝ := (1 + 1 / p) * ∑' n, g n ^ p
    have hsumpos : 0 < ∑' n, g n ^ p := by
      exact hgp.tsum_pos (fun n => Real.rpow_nonneg (hg0 n) p) 0
        (Real.rpow_pos_of_pos
          (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos 0) p)
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, hC, fun z => ?_⟩
    have hdet := arithmeticDiagonalFredholmDeterminant_norm_le_exp_rpow
      g hg0 hg hp0 hp1 hgp z
    change ‖constrainedProlateArithmeticFredholmDeterminant z‖ ≤ _
    change ‖arithmeticDiagonalFredholmDeterminant (fun n => (g n : ℂ)) z‖ ≤ _
    refine hdet.trans (Real.exp_le_exp.mpr ?_)
    rw [show (1 + 1 / p) * ‖z‖ ^ p * ∑' n, g n ^ p = C * ‖z‖ ^ p by
      dsimp [C]
      ring]
    apply mul_le_mul_of_nonneg_left _ hC.le
    exact Real.rpow_le_rpow (norm_nonneg z) (by linarith [norm_nonneg z]) hp0.le
  · let q : ℝ := 3 / 4
    have hqhalf : 1 / 2 < q := by norm_num [q]
    have hq0 : 0 < q := by norm_num [q]
    have hq1 : q ≤ 1 := by norm_num [q]
    have hqp : q ≤ p := by dsimp [q]; linarith
    have hgq : Summable fun n => g n ^ q :=
      summable_constrainedProlateArithmeticEigenvalue_rpow hqhalf
    let C : ℝ := (1 + 1 / q) * ∑' n, g n ^ q
    have hsumpos : 0 < ∑' n, g n ^ q := by
      exact hgq.tsum_pos (fun n => Real.rpow_nonneg (hg0 n) q) 0
        (Real.rpow_pos_of_pos
          (GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos 0) q)
    have hC : 0 < C := by dsimp [C]; positivity
    refine ⟨C, hC, fun z => ?_⟩
    have hdet := arithmeticDiagonalFredholmDeterminant_norm_le_exp_rpow
      g hg0 hg hq0 hq1 hgq z
    change ‖constrainedProlateArithmeticFredholmDeterminant z‖ ≤ _
    change ‖arithmeticDiagonalFredholmDeterminant (fun n => (g n : ℂ)) z‖ ≤ _
    refine hdet.trans (Real.exp_le_exp.mpr ?_)
    rw [show (1 + 1 / q) * ‖z‖ ^ q * ∑' n, g n ^ q = C * ‖z‖ ^ q by
      dsimp [C]
      ring]
    apply mul_le_mul_of_nonneg_left _ hC.le
    calc
      ‖z‖ ^ q ≤ (1 + ‖z‖) ^ q :=
        Real.rpow_le_rpow (norm_nonneg z) (by linarith [norm_nonneg z]) hq0.le
      _ ≤ (1 + ‖z‖) ^ p :=
        Real.rpow_le_rpow_of_exponent_le (by linarith [norm_nonneg z]) hqp

theorem tendsto_arithmeticHalfOrderScale {p : ℝ} (hp : p < 1 / 2) :
    Tendsto (fun N : ℕ =>
      (1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2) ^ p / (N : ℝ))
      atTop (nhds 0) := by
  by_cases hp0 : p ≤ 0
  · apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_nonneg (Real.rpow_nonneg (by positivity) p) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      have hbase : (1 : ℝ) ≤ 1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2 := by
        nlinarith [sq_nonneg (((N + 2 : ℕ) : ℝ))]
      have hpow : (1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2) ^ p ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hbase hp0
      exact div_le_div_of_nonneg_right hpow (by positivity)
    · exact tendsto_one_div_atTop_nhds_zero_nat
  · have hp0' : 0 < p := lt_of_not_ge hp0
    let K : ℝ := 11 ^ p * 3 ^ (2 * p)
    have hK0 : 0 ≤ K := by dsimp [K]; positivity
    have hexp : 0 < 1 - 2 * p := by linarith
    have hpowReal : Tendsto (fun x : ℝ => x ^ (2 * p - 1)) atTop (nhds 0) := by
      simpa only [show 2 * p - 1 = -(1 - 2 * p) by ring] using
        (tendsto_rpow_neg_atTop hexp)
    have hmajor : Tendsto (fun N : ℕ => K * (N : ℝ) ^ (2 * p - 1))
        atTop (nhds 0) := by
      simpa using (hpowReal.comp tendsto_natCast_atTop_atTop).const_mul K
    apply squeeze_zero'
    · filter_upwards [eventually_ge_atTop 1] with N hN
      exact div_nonneg (Real.rpow_nonneg (by positivity) p) (by positivity)
    · filter_upwards [eventually_ge_atTop 1] with N hN
      let x : ℝ := (N : ℝ)
      let k : ℝ := ((N + 2 : ℕ) : ℝ)
      have hx0 : 0 < x := by dsimp [x]; positivity
      have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast hN
      have hk0 : 0 < k := by dsimp [k]; positivity
      have hk1 : 1 ≤ k := by dsimp [k]; exact_mod_cast (show 1 ≤ N + 2 by omega)
      have hbase : 1 + 10 * k ^ 2 ≤ 11 * k ^ 2 := by
        nlinarith [sq_nonneg (k - 1)]
      have hkx : k ≤ 3 * x := by
        dsimp [k, x]
        push_cast
        linarith
      have hbasepow := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ 1 + 10 * k ^ 2)
        hbase hp0'.le
      calc
        (1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2) ^ p / (N : ℝ) =
            (1 + 10 * k ^ 2) ^ p / x := rfl
        _ ≤ (11 * k ^ 2) ^ p / x :=
          div_le_div_of_nonneg_right hbasepow hx0.le
        _ = 11 ^ p * k ^ (2 * p) / x := by
          rw [Real.mul_rpow (by norm_num) (sq_nonneg k),
            ← Real.rpow_natCast k 2, ← Real.rpow_mul hk0.le]
          norm_num only [Nat.cast_ofNat]
        _ ≤ 11 ^ p * (3 * x) ^ (2 * p) / x := by
          gcongr
        _ = K * x ^ (2 * p - 1) := by
          rw [Real.mul_rpow (by norm_num) hx0.le, Real.rpow_sub hx0]
          simp only [Real.rpow_one]
          dsimp [K]
          ring
    · exact hmajor

theorem constrainedProlateArithmeticFredholmDeterminant_lower_order
    {p : ℝ} (hp : p < 1 / 2) (C : ℝ) (_hC : 0 < C) :
    ∃ z : ℂ, Real.exp (C * (1 + ‖z‖) ^ p) <
      ‖constrainedProlateArithmeticFredholmDeterminant z‖ := by
  have hscale := (tendsto_arithmeticHalfOrderScale hp).const_mul C
  have hscale' : Tendsto (fun N : ℕ =>
      C * ((1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2) ^ p / (N : ℝ)))
      atTop (nhds 0) := by simpa using hscale
  have hlog2 : 0 < Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hevent : ∀ᶠ N : ℕ in atTop,
      C * ((1 + 10 * ((N + 2 : ℕ) : ℝ) ^ 2) ^ p / (N : ℝ)) <
        Real.log 2 :=
    hscale'.eventually (Iio_mem_nhds hlog2)
  obtain ⟨N, hsmall, hN⟩ :=
    (hevent.and (eventually_ge_atTop 1)).exists
  let R : ℝ := 10 * ((N + 2 : ℕ) : ℝ) ^ 2
  have hR0 : 0 ≤ R := by dsimp [R]; positivity
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hsmall' :
      C * (1 + R) ^ p / (N : ℝ) < Real.log 2 := by
    simpa only [R, div_eq_mul_inv, mul_assoc] using hsmall
  have hgrowth : C * (1 + R) ^ p < (N : ℝ) * Real.log 2 := by
    have := (div_lt_iff₀ hN0).mp hsmall'
    nlinarith
  have hpowexp : (2 : ℝ) ^ N = Real.exp ((N : ℝ) * Real.log 2) := by
    symm
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  refine ⟨(R : ℂ), ?_⟩
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hR0]
  calc
    Real.exp (C * (1 + R) ^ p) < (2 : ℝ) ^ N := by
      rw [hpowexp]
      exact Real.exp_lt_exp.mpr hgrowth
    _ ≤ ‖constrainedProlateArithmeticFredholmDeterminant (R : ℂ)‖ := by
      exact constrainedProlateArithmeticFredholmDeterminant_norm_lower_nat N

/-- The constrained-prolate arithmetic Fredholm determinant has exact classical entire order
`1/2`: every larger power is a global growth envelope and no smaller power is. -/
theorem constrainedProlateArithmeticFredholmDeterminant_hasExactEntireOrder_half :
    HasExactEntireOrder constrainedProlateArithmeticFredholmDeterminant (1 / 2) := by
  refine ⟨constrainedProlateArithmeticFredholmDeterminant_differentiable,
    (fun _ hp => constrainedProlateArithmeticFredholmDeterminant_upper_order hp), ?_⟩
  intro p hp C hC
  exact constrainedProlateArithmeticFredholmDeterminant_lower_order hp C hC

/-- Exact exponent of convergence for an enumerated nonzero divisor. -/
def HasExponentOfConvergence (a : ℕ → ℂ) (ρ : ℝ) : Prop :=
  (∀ p : ℝ, ρ < p → Summable fun n => 1 / ‖a n‖ ^ p) ∧
    ¬Summable fun n => 1 / ‖a n‖ ^ ρ

/-- Reciprocal zero sequence of the constrained-prolate arithmetic determinant. -/
def constrainedProlateArithmeticFredholmZero (n : ℕ) : ℂ :=
  -(GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n : ℂ)⁻¹

theorem inv_norm_constrainedProlateArithmeticFredholmZero_rpow
    (n : ℕ) (p : ℝ) :
    1 / ‖constrainedProlateArithmeticFredholmZero n‖ ^ p =
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ^ p := by
  have hk0 : 0 < GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n :=
    GaloisForLFunctions.constrainedProlateArithmeticEigenvalue_pos n
  rw [constrainedProlateArithmeticFredholmZero, norm_neg, norm_inv,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hk0, Real.inv_rpow hk0.le]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos hk0 p)]

theorem constrainedProlateArithmeticEigenvalue_rpow_half_harmonic_lower (n : ℕ) :
    (1 / 4 : ℝ) / ((n + 2 : ℕ) : ℝ) ≤
      GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ^ (1 / 2 : ℝ) := by
  let k : ℝ := ((n + 2 : ℕ) : ℝ)
  have hk0 : 0 < k := by dsimp [k]; positivity
  have heig := one_tenth_div_sq_le_constrainedProlateArithmeticEigenvalue n
  have hsq : ((1 / 4 : ℝ) / k) ^ 2 ≤ (1 / 10 : ℝ) / k ^ 2 := by
    rw [div_pow]
    gcongr
    norm_num
  have hsqrt := Real.sqrt_le_sqrt (hsq.trans heig)
  rw [Real.sqrt_sq_eq_abs, abs_of_pos (div_pos (by norm_num) hk0),
    Real.sqrt_eq_rpow] at hsqrt
  exact hsqrt

theorem constrainedProlateArithmeticFredholmZero_hasExponentOfConvergence_half :
    HasExponentOfConvergence constrainedProlateArithmeticFredholmZero (1 / 2) := by
  constructor
  · intro p hp
    exact (summable_constrainedProlateArithmeticEigenvalue_rpow hp).congr
      (fun n => (inv_norm_constrainedProlateArithmeticFredholmZero_rpow n p).symm)
  · intro hsum
    have heigsum : Summable (fun n =>
        GaloisForLFunctions.constrainedProlateArithmeticEigenvalue n ^ (1 / 2 : ℝ)) :=
      hsum.congr (fun n => inv_norm_constrainedProlateArithmeticFredholmZero_rpow n (1 / 2))
    have hminor : Summable (fun n : ℕ =>
        (1 / 4 : ℝ) / ((n + 2 : ℕ) : ℝ)) :=
      Summable.of_nonneg_of_le (fun n => by positivity)
        constrainedProlateArithmeticEigenvalue_rpow_half_harmonic_lower heigsum
    have hharm : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
      refine hminor.mul_left 4 |>.congr (fun n => ?_)
      field_simp
    apply Real.not_summable_one_div_natCast
    exact (summable_nat_add_iff
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) 2).mp (by simpa using hharm)

end RHTower

