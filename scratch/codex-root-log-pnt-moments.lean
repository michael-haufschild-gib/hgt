import GaloisForLFunctions.HTGeometry.SubexponentialSqrtSummable
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs
import GaloisForLFunctions.RHTower.PsiDefectSqrtBound
import GaloisForLFunctions.RHTower.SelbergSymmetryCore

noncomputable section
open Filter Topology
namespace GaloisForLFunctions.HTGeometry

theorem summable_log_pow_exp_neg_sqrt_log_div (c : ℝ) (hc : 0 < c) (k : ℕ) :
    Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ k *
        Real.exp (-(c * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) := by
  have hroot : Tendsto (fun n : ℕ => Real.sqrt (Real.log (n : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hdecay : Tendsto (fun x : ℝ =>
      x ^ ((2 * k : ℕ) : ℝ) * Real.exp (-(c / 2) * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero _ _ (by positivity)
  have hsmall := (hdecay.comp hroot).eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1))
  have hbound : ∀ᶠ n : ℕ in atTop,
      Real.log (n : ℝ) ^ k *
        Real.exp (-(c / 2) * Real.sqrt (Real.log (n : ℝ))) ≤ 1 := by
    filter_upwards [hsmall, eventually_ge_atTop (1 : ℕ)] with n hn hn1
    have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn1
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnR
    have heq : Real.sqrt (Real.log (n : ℝ)) ^ ((2 * k : ℕ) : ℝ) =
        Real.log (n : ℝ) ^ k := by
      rw [Real.rpow_natCast, pow_mul, Real.sq_sqrt hlog]
    simp only [Function.comp_apply] at hn
    rw [heq] at hn
    exact hn.le
  obtain ⟨N, hN⟩ := eventually_atTop.1 hbound
  have hbase : Summable (fun n : ℕ =>
      Real.exp (-((c / 2) * Real.sqrt (Real.log (n : ℝ)))) / (n : ℝ)) :=
    summable_exp_neg_sqrt_log_div (by positivity : 0 < c / 2)
  apply (summable_nat_add_iff N).1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff N).2 hbase)
  have hn : Real.log ((n + N : ℕ) : ℝ) ^ k *
      Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) ≤ 1 :=
    hN (n + N) (by omega)
  have hexp : Real.exp (-(c * Real.sqrt (Real.log ((n + N : ℕ) : ℝ)))) =
      Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) *
        Real.exp (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ))) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hexp]
  have hmul := mul_le_mul_of_nonneg_right hn
    (Real.exp_pos (-(c / 2) * Real.sqrt (Real.log ((n + N : ℕ) : ℝ)))).le
  have hden : (0 : ℝ) ≤ (n + N : ℕ) := by positivity
  exact div_le_div_of_nonneg_right (by simpa [mul_assoc] using hmul) hden

theorem summable_log_pow_div_square (k : ℕ) :
    Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ k / ((n : ℝ) ^ (2 : ℕ))) := by
  have hbase := summable_log_pow_exp_neg_sqrt_log_div 1 (by norm_num) k
  obtain ⟨N, hN⟩ := exists_nat_ge (Real.exp 1)
  apply (summable_nat_add_iff N).1
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_nat_add_iff N).2 hbase)
  set x : ℝ := ((n + N : ℕ) : ℝ) with hx
  have hxge : Real.exp 1 ≤ x := by
    rw [hx]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    push_cast
    linarith
  have hxpos : 0 < x := (Real.exp_pos _).trans_le hxge
  have hlog : (1 : ℝ) ≤ Real.log x := by
    rw [← Real.log_exp (1 : ℝ)]
    exact Real.log_le_log (Real.exp_pos _) hxge
  have hsqrt : Real.sqrt (Real.log x) ≤ Real.log x := by
    have hsq := Real.sq_sqrt (by linarith : 0 ≤ Real.log x)
    have hnonneg := Real.sqrt_nonneg (Real.log x)
    nlinarith [sq_nonneg (Real.sqrt (Real.log x) - 1)]
  have hrec : 1 / x ≤ Real.exp (-Real.sqrt (Real.log x)) := by
    have hexp : Real.exp (-Real.log x) = 1 / x := by
      rw [Real.exp_neg, Real.exp_log hxpos]
      ring
    rw [← hexp]
    exact Real.exp_le_exp.mpr (neg_le_neg hsqrt)
  have hnonneg : 0 ≤ Real.log x ^ k / x := by positivity
  have hmul := mul_le_mul_of_nonneg_left hrec hnonneg
  simpa only [one_mul] using (show
    Real.log x ^ k / x ^ (2 : ℕ) ≤
      Real.log x ^ k * Real.exp (-Real.sqrt (Real.log x)) / x by
        calc
          _ = (Real.log x ^ k / x) * (1 / x) := by ring
          _ ≤ (Real.log x ^ k / x) * Real.exp (-Real.sqrt (Real.log x)) := hmul
          _ = _ := by ring)

end GaloisForLFunctions.HTGeometry

namespace RHTower

theorem summable_psi_error_weight_log_pow (k : ℕ) :
    Summable (fun n : ℕ =>
      |Chebyshev.psi ((n : ℝ) + 1) - ((n : ℝ) + 1)| *
        Real.log ((n : ℝ) + 1) ^ k / (((n : ℝ) + 1) ^ (2 : ℕ))) := by
  obtain ⟨C, c, hc, hC, hbound⟩ := exists_psi_error_eventually
  obtain ⟨X, hX⟩ := eventually_atTop.1 hbound
  obtain ⟨N, hN⟩ := exists_nat_ge (max X 1)
  have hbase := GaloisForLFunctions.HTGeometry.summable_log_pow_exp_neg_sqrt_log_div c hc k
  have hmaj : Summable (fun n : ℕ =>
      C * (Real.log ((n + (N + 1) : ℕ) : ℝ) ^ k *
        Real.exp (-(c * Real.sqrt (Real.log ((n + (N + 1) : ℕ) : ℝ)))) /
          ((n + (N + 1) : ℕ) : ℝ))) :=
    ((summable_nat_add_iff (N + 1)).2 hbase).mul_left C
  apply (summable_nat_add_iff N).1
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have hxge : (1 : ℝ) ≤ ((n + N : ℕ) : ℝ) + 1 := by
      have hnnonneg : (0 : ℝ) ≤ ((n + N : ℕ) : ℝ) := Nat.cast_nonneg _
      linarith
    exact div_nonneg (mul_nonneg (abs_nonneg _) (pow_nonneg (Real.log_nonneg hxge) _))
      (sq_nonneg _)
  set x : ℝ := ((n + (N + 1) : ℕ) : ℝ) with hx
  have hxval : ((n + N : ℕ) : ℝ) + 1 = x := by
    rw [hx]
    push_cast
    ring
  have hxpos : 0 < x := by rw [hx]; positivity
  have hXle : X ≤ x := by
    have h1 : X ≤ max X 1 := le_max_left X 1
    have h2 : max X 1 ≤ (N : ℝ) := hN
    have h3 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    rw [hx]
    push_cast
    linarith
  have hb := hX x hXle
  rw [hxval]
  have hmul := mul_le_mul_of_nonneg_right hb
    (show 0 ≤ Real.log x ^ k / x ^ (2 : ℕ) by positivity)
  have heq : (C * (x * Real.exp (-c * Real.sqrt (Real.log x)))) *
      (Real.log x ^ k / x ^ (2 : ℕ)) =
      C * (Real.log x ^ k * Real.exp (-c * Real.sqrt (Real.log x)) / x) := by
    field_simp
  simpa only [neg_mul, mul_div_assoc] using hmul.trans_eq heq

theorem summable_psiDefect_weight_log_pow (k : ℕ) :
    Summable (fun n : ℕ =>
      |psiDefect (n + 1)| * Real.log ((n : ℝ) + 1) ^ k /
        (((n : ℝ) + 1) ^ (2 : ℕ))) := by
  have hpsi := summable_psi_error_weight_log_pow k
  have hconst : Summable (fun n : ℕ =>
      |2 * Real.eulerMascheroniConstant| * Real.log ((n : ℝ) + 1) ^ k /
        (((n : ℝ) + 1) ^ (2 : ℕ))) := by
    have h := ((summable_nat_add_iff 1).2
      (GaloisForLFunctions.HTGeometry.summable_log_pow_div_square k)).mul_left
        |2 * Real.eulerMascheroniConstant|
    simpa only [Nat.cast_add, Nat.cast_one, mul_div_assoc] using h
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
    (hpsi.add hconst)
  · have hxge : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    exact div_nonneg (mul_nonneg (abs_nonneg _)
      (pow_nonneg (Real.log_nonneg hxge) _)) (sq_nonneg _)
  let x : ℝ := ((n : ℝ) + 1)
  have hxge : 1 ≤ x := by
    dsimp [x]
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hnonneg : 0 ≤ Real.log x ^ k / x ^ (2 : ℕ) :=
    div_nonneg (pow_nonneg (Real.log_nonneg hxge) _) (sq_nonneg _)
  have htri : |Chebyshev.psi x - x + 2 * Real.eulerMascheroniConstant| ≤
      |Chebyshev.psi x - x| + |2 * Real.eulerMascheroniConstant| := abs_add_le _ _
  have hmul := mul_le_mul_of_nonneg_right htri hnonneg
  have hbridge : chebyshevPsi (n + 1) = Chebyshev.psi x := by
    rw [chebyshevPsi_eq_psi]
    congr 1
    dsimp [x]
    push_cast
    ring
  change |psiDefect (n + 1)| * Real.log x ^ k / x ^ (2 : ℕ) ≤
      |Chebyshev.psi x - x| * Real.log x ^ k / x ^ (2 : ℕ) +
        |2 * Real.eulerMascheroniConstant| * Real.log x ^ k / x ^ (2 : ℕ)
  rw [psiDefect, hbridge]
  have hcast : ((n + 1 : ℕ) : ℝ) = x := by dsimp [x]; push_cast; ring
  rw [hcast]
  calc
    _ = |Chebyshev.psi x - x + 2 * Real.eulerMascheroniConstant| *
          (Real.log x ^ k / x ^ (2 : ℕ)) := by ring
    _ ≤ (|Chebyshev.psi x - x| + |2 * Real.eulerMascheroniConstant|) *
          (Real.log x ^ k / x ^ (2 : ℕ)) := hmul
    _ = _ := by ring

end RHTower
