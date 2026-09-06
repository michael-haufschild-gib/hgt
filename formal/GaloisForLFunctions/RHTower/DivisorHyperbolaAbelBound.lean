import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds
import GaloisForLFunctions.RHTower.DivisorCenteredHyperbola
import GaloisForLFunctions.RHTower.ChebyshevPsiLogSummatory
import GaloisForLFunctions.RHTower.HarmonicLogMascheroni

/-!
# Signed half-order bound for the complete divisor source

Centering the symmetric hyperbola separates a logarithmic smooth boundary from
periodic residue channels with a uniform signed Abel budget. Their exact sum
reconstructs the logarithmic-factorial minus divisor-summatory defect. The complete
half-order response is bounded by `(7+log M)*sqrt M`, and hence by `7*M^(3/4)`.
-/

noncomputable section
open Finset HTGeometry
namespace RHTower

/-- The smooth boundary remaining after centering the divisor hyperbola. -/
def divisorHyperbolaSmoothRemainder (N : ℕ) : ℝ :=
  (∑ m ∈ Icc 1 N, Real.log m) -
    (2 * (N : ℝ) + 1) * ((harmonic (Nat.sqrt N) : ℚ) : ℝ) +
      (Nat.sqrt N : ℝ)^2 + Nat.sqrt N + 2 * Real.eulerMascheroniConstant * N

private theorem hyperbola_log_boundary_bounds {x s : ℝ}
    (hs : 0 < s) (hlo : s^2 ≤ x) (hhi : x ≤ s^2+2*s) :
    0 ≤ x * (Real.log x - 2*Real.log s) - x + s^2 ∧
      x * (Real.log x - 2*Real.log s) - x + s^2 ≤ 4 := by
  have hx : 0 < x := lt_of_lt_of_le (sq_pos_of_pos hs) hlo
  have hs2 : 0 < s^2 := sq_pos_of_pos hs
  have hlower := Real.log_le_sub_one_of_pos (x := s^2/x) (by positivity)
  have hupper := Real.log_le_sub_one_of_pos (x := x/s^2) (by positivity)
  rw [Real.log_div (ne_of_gt hs2) hx.ne', Real.log_pow] at hlower
  rw [Real.log_div hx.ne' (ne_of_gt hs2), Real.log_pow] at hupper
  push_cast at hlower hupper
  have hlo' := mul_le_mul_of_nonneg_left hlower hx.le
  have hhi' := mul_le_mul_of_nonneg_left hupper hs2.le
  have hcancel1 : x*(s^2/x-1)=s^2-x := by field_simp
  have hcancel2 : s^2*(x/s^2-1)=x-s^2 := by field_simp
  rw [hcancel1] at hlo'
  rw [hcancel2] at hhi'
  have hlog : Real.log x - 2*Real.log s ≤ 2/s := by
    apply (le_of_mul_le_mul_left (a := s^2) ?_ hs2)
    have hcancel : s^2*(2/s)=2*s := by field_simp
    rw [hcancel]
    linarith only [hhi', hhi]
  have hdelta := mul_le_mul_of_nonneg_left hlog (sub_nonneg.mpr hlo)
  have hprod : (x-s^2)*(2/s) ≤ 4 := by
    rw [← mul_div_assoc, div_le_iff₀ hs]
    nlinarith only [hhi]
  constructor
  · nlinarith only [hlo']
  · nlinarith only [hdelta, hprod, hhi']

/-- Centering removes the square-root divisor error from the smooth boundary; the remaining
logarithmic estimate is uniform at every positive integer. -/
theorem abs_divisorHyperbolaSmoothRemainder_le {N : ℕ} (hN : 1 ≤ N) :
    |divisorHyperbolaSmoothRemainder N| ≤ 6 + Real.log ((N : ℝ)+1) := by
  let s := Nat.sqrt N
  have hs : 1 ≤ s := Nat.le_sqrt.mpr (by simpa using hN)
  have hsR : (0 : ℝ) < s := by positivity
  have hNpos : (0 : ℝ) < N := by positivity
  have hlo : (s : ℝ)^2 ≤ N := by
    rw [pow_two]
    exact_mod_cast Nat.sqrt_le N
  have hhi : (N : ℝ) ≤ (s : ℝ)^2+2*s := by
    have h := Nat.lt_succ_sqrt N
    change N < (s+1)*(s+1) at h
    have he : (s+1)*(s+1)=s*s+2*s+1 := by ring
    rw [he] at h
    have hn : N ≤ s*s+2*s := by omega
    rw [pow_two]
    exact_mod_cast hn
  have hlog := hyperbola_log_boundary_bounds hsR hlo hhi
  have hH := harmonic_mascheroni_half_bounds hs
  have hb_lower := mul_le_mul_of_nonneg_left hH.2 (show (0:ℝ) ≤ 2*N by positivity)
  have hb_upper := mul_le_mul_of_nonneg_left hH.1 (show (0:ℝ) ≤ 2*N by positivity)
  have hcancel1 : (2*(N:ℝ))*(1/(2*s))=(N:ℝ)/s := by field_simp
  have hcancel2 : (2*(N:ℝ))*(1/(2*((s:ℝ)+1)))=(N:ℝ)/((s:ℝ)+1) := by field_simp
  rw [hcancel1] at hb_lower
  rw [hcancel2] at hb_upper
  have hn_s : (N:ℝ)/s ≤ (s:ℝ)+2 := by
    rw [div_le_iff₀ hsR]
    nlinarith only [hhi]
  have hn_s1 : (s:ℝ)-1 ≤ (N:ℝ)/((s:ℝ)+1) := by
    rw [le_div_iff₀ (by positivity)]
    nlinarith only [hlo]
  have hb : -2 ≤ (s:ℝ)-2*N*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant) ∧
      (s:ℝ)-2*N*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant) ≤ 1 := by
    constructor <;> nlinarith only [hb_lower,hb_upper,hn_s,hn_s1]
  have hfactlow := stirling_le_sum_log N hN
  have hfacthi := sum_log_le_stirling N hN
  have hlstep := Real.log_le_sub_one_of_pos (x := ((N:ℝ)+1)/N) (by positivity)
  rw [Real.log_div (by positivity) hNpos.ne'] at hlstep
  have hmult := mul_le_mul_of_nonneg_left hlstep hNpos.le
  have hrat : (N:ℝ)*(((N:ℝ)+1)/N-1)=1 := by field_simp; ring
  rw [hrat] at hmult
  have hf : 1 ≤ (∑ m ∈ Icc 1 N, Real.log m) - (N:ℝ)*Real.log N + N ∧
      (∑ m ∈ Icc 1 N, Real.log m) - (N:ℝ)*Real.log N + N ≤ 1+Real.log ((N:ℝ)+1) := by
    constructor <;> nlinarith only [hfactlow,hfacthi,hmult]
  have hHnonneg : (0:ℝ) ≤ ((harmonic s:ℚ):ℝ) := by
    rw [← sum_inv_Icc_eq_ratCast_harmonic]
    exact sum_nonneg (fun _ _ => by positivity)
  have hHupper := harmonic_le_one_add_log s
  have hsN : (s:ℝ) ≤ (N:ℝ)+1 := by
    have h := Nat.sqrt_le_self N
    dsimp [s]
    exact_mod_cast (show Nat.sqrt N ≤ N+1 by omega)
  have hlogmono := Real.log_le_log hsR hsN
  have hHbound : ((harmonic s:ℚ):ℝ) ≤ 1+Real.log ((N:ℝ)+1) := by linarith
  have hid : divisorHyperbolaSmoothRemainder N =
      ((∑ m ∈ Icc 1 N, Real.log m) - (N:ℝ)*Real.log N + N) -
      ((harmonic s:ℚ):ℝ) +
      ((N:ℝ)*(Real.log N-2*Real.log s)-N+(s:ℝ)^2) +
      ((s:ℝ)-2*N*(((harmonic s:ℚ):ℝ)-Real.log s-Real.eulerMascheroniConstant)) := by
    dsimp [divisorHyperbolaSmoothRemainder,s]
    ring
  rw [hid,abs_le]
  constructor <;> linarith [hf.1,hf.2,hlog.1,hlog.2,hb.1,hb.2]

/-- The centered and smooth pieces reconstruct the literal logarithmic-factorial minus
floor-divisor source, with its Euler constant term intact. -/
theorem divisorHyperbolaSmooth_add_centered (N : ℕ) :
    divisorHyperbolaSmoothRemainder N + 2 * centeredDivisorHyperbola N =
      (∑ m ∈ Icc 1 N, Real.log m) -
        (∑ d ∈ Icc 1 N, ((N/d : ℕ) : ℝ)) +
          2 * Real.eulerMascheroniConstant * N := by
  rw [sum_floorDivisor_eq_centeredHyperbola]
  simp_rw [one_div, sum_inv_Icc_eq_ratCast_harmonic]
  unfold divisorHyperbolaSmoothRemainder
  ring

/-- Half-order Abel response of the smooth hyperbola boundary. -/
def divisorHyperbolaSmoothAbel (M : ℕ) : ℝ :=
  ∑ k ∈ range M, divisorHyperbolaSmoothRemainder k * halfOrderAbelStep 0 k

/-- The smooth boundary has only square-root times logarithmic Abel growth. -/
theorem abs_divisorHyperbolaSmoothAbel_le (M : ℕ) :
    |divisorHyperbolaSmoothAbel M| ≤ (6+Real.log M) * Real.sqrt M := by
  by_cases hM : M = 0
  · subst M
    simp [divisorHyperbolaSmoothAbel]
  · have hM1 : 1 ≤ M := by omega
    have hMlog : 0 ≤ Real.log M := Real.log_nonneg (by exact_mod_cast hM1)
    have hpoint (k : ℕ) (hk : k ∈ range M) :
        |divisorHyperbolaSmoothRemainder k| ≤ 6+Real.log M := by
      by_cases hk0 : k = 0
      · subst k
        simp only [divisorHyperbolaSmoothRemainder, Nat.sqrt_zero, Nat.cast_zero,
          Icc_eq_empty_of_lt (by omega : (0:ℕ)<1), sum_empty, harmonic_zero,
          Rat.cast_zero, mul_zero, sub_zero, zero_pow (by omega : (2:ℕ) ≠ 0), add_zero,
          abs_zero]
        linarith
      · have h := abs_divisorHyperbolaSmoothRemainder_le (by omega : 1 ≤ k)
        have hkm : (k:ℝ)+1 ≤ M := by exact_mod_cast (mem_range.mp hk)
        have hlog := Real.log_le_log (by positivity : (0:ℝ)<(k:ℝ)+1) hkm
        linarith
    have htel : (∑ k ∈ range M, halfOrderAbelStep 0 k) = Real.sqrt M := by
      simpa only [halfOrderAbelStep, Nat.zero_add, Nat.cast_zero, Real.sqrt_zero,
        sub_zero] using Finset.sum_range_sub (fun k : ℕ => Real.sqrt k) M
    unfold divisorHyperbolaSmoothAbel
    calc
      _ ≤ ∑ k ∈ range M, |divisorHyperbolaSmoothRemainder k * halfOrderAbelStep 0 k| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ range M, (6+Real.log M) * halfOrderAbelStep 0 k := by
        apply sum_le_sum
        intro k hk
        rw [abs_mul, abs_of_nonneg (halfOrderAbelStep_nonneg 0 k)]
        exact mul_le_mul_of_nonneg_right (hpoint k hk) (halfOrderAbelStep_nonneg 0 k)
      _ = _ := by rw [← mul_sum, htel]

/-- Signed time summation controls the complete divisor source before any Möbius aggregation. -/
theorem abs_divisorHyperbolaCompleteAbel_le (M : ℕ) :
    |divisorHyperbolaSmoothAbel M + 2 * centeredDivisorHyperbolaAbel M| ≤
      (7+Real.log M) * Real.sqrt M := by
  have hS := abs_divisorHyperbolaSmoothAbel_le M
  have hE := centeredDivisorHyperbolaAbel_bounds M
  have hs : (Nat.sqrt (M-1) : ℝ) ≤ Real.sqrt M := by
    have hnat := (Nat.sqrt_le (M-1)).trans (Nat.sub_le M 1)
    have hsq : (Nat.sqrt (M-1) : ℝ)^2 ≤ M := by
      rw [pow_two]
      exact_mod_cast hnat
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg (α := ℝ) M),
      Real.sqrt_nonneg (M:ℝ), Nat.cast_nonneg (α := ℝ) (Nat.sqrt (M-1))]
  have hEabs : |2 * centeredDivisorHyperbolaAbel M| ≤ Real.sqrt M / 8 := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos (by norm_num) hE.2)]
    linarith [hE.1]
  have h := (abs_add_le (divisorHyperbolaSmoothAbel M)
    (2*centeredDivisorHyperbolaAbel M)).trans (add_le_add hS hEabs)
  nlinarith [Real.sqrt_nonneg (M:ℝ)]

/-- A uniform three-quarter-power envelope, convenient for summing all dilation squares. -/
theorem abs_divisorHyperbolaCompleteAbel_le_threeQuarter (M : ℕ) :
    |divisorHyperbolaSmoothAbel M + 2 * centeredDivisorHyperbolaAbel M| ≤
      7 * Real.sqrt M * Real.sqrt (Real.sqrt M) := by
  by_cases hM : M = 0
  · subst M
    simp [divisorHyperbolaSmoothAbel, centeredDivisorHyperbolaAbel]
  · have hM1 : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
    have hs1 : 1 ≤ Real.sqrt M := by
      simpa using Real.sqrt_le_sqrt hM1
    have hr1 : 1 ≤ Real.sqrt (Real.sqrt M) := by
      simpa using Real.sqrt_le_sqrt hs1
    have hlog := Real.log_le_sub_one_of_pos
      (x := Real.sqrt (Real.sqrt M)) (by positivity)
    have heq1 := Real.log_sqrt (show (0:ℝ) ≤ M by positivity)
    have heq2 := Real.log_sqrt (Real.sqrt_nonneg (M:ℝ))
    have hcoef : 7+Real.log M ≤ 7*Real.sqrt (Real.sqrt M) := by
      linarith
    exact (abs_divisorHyperbolaCompleteAbel_le M).trans (by
      have h := mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg (M:ℝ))
      nlinarith only [h])

end RHTower
