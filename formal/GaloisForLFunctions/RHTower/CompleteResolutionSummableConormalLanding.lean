import GaloisForLFunctions.RHTower.CompleteResolutionSummableLanding

/-!
# Summable source conormal landing for the complete zeta resolution

The complete positive high-exponent resolution has an absolutely summable multiplier vector
whose coordinate sum is one throughout the open right half-plane.  At the closed right half of
the critical strip, every coordinate is analytic and the vector is therefore never annihilated
collectively.  At least one channel preserves the exact analytic order of the completed Riemann
function.

This closes the vector-valued conormal adapter without selecting a zero or a channel in advance.
-/

open scoped BigOperators

namespace RHTower

open Complex Filter

noncomputable section

private theorem analyticAt_inv_riemannZeta_const_mul_of_one_lt_re
    {a s : ℂ} (hs : 1 < (a * s).re) :
    AnalyticAt ℂ (fun z : ℂ => (riemannZeta (a * z))⁻¹) s := by
  have hne1 : a * s ≠ 1 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hlin : AnalyticAt ℂ (fun z : ℂ => a * z) s :=
    analyticAt_const.mul analyticAt_id
  have hcomp : AnalyticAt ℂ (fun z : ℂ => riemannZeta (a * z)) s :=
    (analyticOn_riemannZeta _ hne1).comp hlin
  exact hcomp.inv (riemannZeta_ne_zero_of_one_lt_re hs)

/-- Every multiplier in the complete high-exponent resolution is analytic on the closed
right half of the critical strip.  Individual shell differences may vanish on the boundary;
collective nonannihilation is supplied by their summable resolution of one. -/
theorem analyticAt_completeResolutionMultiplier_of_re_ge_half
    {K : ℕ} (hK : 12 ≤ K) (j : ℕ) {s : ℂ}
    (hs : 1 / 2 ≤ s.re) :
    AnalyticAt ℂ (completeResolutionMultiplier K j) s := by
  cases j with
  | zero =>
      have hscaled : 1 < (((K : ℂ) * s).re) := by
        simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
          zero_mul, sub_zero]
        have hKcast : (12 : ℝ) ≤ K := by exact_mod_cast hK
        calc
          1 < 6 := by norm_num
          _ ≤ (K : ℝ) * (1 / 2 : ℝ) := by nlinarith
          _ ≤ (K : ℝ) * s.re :=
            mul_le_mul_of_nonneg_left hs (by positivity)
      exact analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaled
  | succ j =>
      have hKj : 12 ≤ K + j := hK.trans (Nat.le_add_right K j)
      have hscaled : 1 < ((((K + j : ℕ) : ℂ) * s).re) := by
        simp only [Complex.mul_re, Nat.cast_add, Complex.add_re, Complex.add_im,
          Complex.natCast_re, Complex.natCast_im, add_zero, zero_mul, sub_zero]
        have hKjcast : (12 : ℝ) ≤ K + j := by exact_mod_cast hKj
        calc
          1 < 6 := by norm_num
          _ ≤ (K + j : ℝ) * (1 / 2 : ℝ) := by nlinarith
          _ ≤ (K + j : ℝ) * s.re :=
            mul_le_mul_of_nonneg_left hs (by positivity)
      have hscaledSucc :
          1 < (((((K + j : ℕ) : ℂ) + 1) * s).re) := by
        simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re,
          Complex.one_re, Complex.add_im, Complex.natCast_im, Complex.one_im,
          Nat.cast_add, add_zero, zero_mul, sub_zero]
        have hKjcast : (12 : ℝ) ≤ K + j := by exact_mod_cast hKj
        calc
          1 < 6 := by norm_num
          _ ≤ ((K + j : ℝ) + 1) * (1 / 2 : ℝ) := by nlinarith
          _ ≤ ((K + j : ℝ) + 1) * s.re :=
            mul_le_mul_of_nonneg_left hs (by positivity)
      change AnalyticAt ℂ (shellMultiplier (K + j)) s
      unfold shellMultiplier
      exact
        (analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaledSucc).sub
          (analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaled)

/-- Every complete-resolution multiplier is analytic wherever its first reciprocal-zeta
dilation already lies in the classical zero-free half-plane. -/
theorem analyticAt_completeResolutionMultiplier_of_one_lt_K_mul_re
    {K : ℕ} (j : ℕ) {s : ℂ}
    (hs : 1 < (K : ℝ) * s.re) :
    AnalyticAt ℂ (completeResolutionMultiplier K j) s := by
  have hsPos : 0 < s.re := by
    have hKnonneg : (0 : ℝ) ≤ K := by positivity
    nlinarith
  cases j with
  | zero =>
      have hscaled : 1 < (((K : ℂ) * s).re) := by
        simpa [Complex.mul_re] using hs
      exact analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaled
  | succ j =>
      have hscaled : 1 < ((((K + j : ℕ) : ℂ) * s).re) := by
        simp only [Complex.mul_re, Nat.cast_add, Complex.add_re,
          Complex.add_im, Complex.natCast_re, Complex.natCast_im,
          add_zero, zero_mul, sub_zero]
        have hjNonneg : (0 : ℝ) ≤ j := by positivity
        nlinarith
      have hscaledSucc :
          1 < (((((K + j : ℕ) : ℂ) + 1) * s).re) := by
        simp only [Complex.mul_re, Complex.add_re, Complex.natCast_re,
          Complex.one_re, Complex.add_im, Complex.natCast_im,
          Complex.one_im, Nat.cast_add, add_zero, zero_mul, sub_zero]
        have hjNonneg : (0 : ℝ) ≤ j := by positivity
        nlinarith
      change AnalyticAt ℂ (shellMultiplier (K + j)) s
      unfold shellMultiplier
      exact
        (analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaledSucc).sub
          (analyticAt_inv_riemannZeta_const_mul_of_one_lt_re hscaled)

/-- **Summable conormal landing.**  At every point in the closed right half of the critical
strip, the complete positive resolution is an `ℓ¹` vector of total coordinate one.  At least one
fixed source channel is nonzero there and multiplication by that channel preserves the exact
analytic order of `xi`. -/
theorem completeResolution_summable_conormalLanding
    {K : ℕ} (hK : 12 ≤ K) {rho : ℂ}
    (hrho : 1 / 2 ≤ rho.re) :
    Summable (fun j : ℕ => completeResolutionMultiplier K j rho) ∧
      HasSum (fun j : ℕ => completeResolutionMultiplier K j rho) 1 ∧
      ∃ j : ℕ,
        completeResolutionMultiplier K j rho ≠ 0 ∧
          analyticOrderAt
              (fun z => xi z * completeResolutionMultiplier K j z) rho =
            analyticOrderAt xi rho := by
  have hrhoPos : 0 < rho.re := by linarith
  refine ⟨summable_completeResolutionMultiplier K hrhoPos,
    hasSum_completeResolutionMultiplier_one K hrhoPos, ?_⟩
  obtain ⟨j, hj⟩ := exists_completeResolutionMultiplier_ne_zero K hrhoPos
  refine ⟨j, hj, ?_⟩
  have hxi : AnalyticAt ℂ xi rho :=
    xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have hM : AnalyticAt ℂ (completeResolutionMultiplier K j) rho :=
    analyticAt_completeResolutionMultiplier_of_re_ge_half hK j hrho
  have horderM :
      analyticOrderAt (completeResolutionMultiplier K j) rho = 0 :=
    hM.analyticOrderAt_eq_zero.mpr hj
  rw [show (fun z => xi z * completeResolutionMultiplier K j z) =
      xi * completeResolutionMultiplier K j from rfl,
    analyticOrderAt_mul hxi hM, horderM, add_zero]

/-- Safe-half-plane conormal landing with no fixed numerical depth.  The single hypothesis says
that every reciprocal-zeta coordinate is evaluated in `Re > 1`. -/
theorem completeResolution_safe_summable_conormalLanding
    {K : ℕ} {rho : ℂ}
    (hsafe : 1 < (K : ℝ) * rho.re) :
    Summable (fun j : ℕ => completeResolutionMultiplier K j rho) ∧
      HasSum (fun j : ℕ => completeResolutionMultiplier K j rho) 1 ∧
      ∃ j : ℕ,
        completeResolutionMultiplier K j rho ≠ 0 ∧
          analyticOrderAt
              (fun z => xi z * completeResolutionMultiplier K j z) rho =
            analyticOrderAt xi rho := by
  have hrhoPos : 0 < rho.re := by
    have hKnonneg : (0 : ℝ) ≤ K := by positivity
    nlinarith
  refine ⟨summable_completeResolutionMultiplier K hrhoPos,
    hasSum_completeResolutionMultiplier_one K hrhoPos, ?_⟩
  obtain ⟨j, hj⟩ := exists_completeResolutionMultiplier_ne_zero K hrhoPos
  refine ⟨j, hj, ?_⟩
  have hxi : AnalyticAt ℂ xi rho :=
    xi_analyticOnNhd_univ rho (Set.mem_univ rho)
  have hM : AnalyticAt ℂ (completeResolutionMultiplier K j) rho :=
    analyticAt_completeResolutionMultiplier_of_one_lt_K_mul_re j hsafe
  have horderM :
      analyticOrderAt (completeResolutionMultiplier K j) rho = 0 :=
    hM.analyticOrderAt_eq_zero.mpr hj
  rw [show (fun z => xi z * completeResolutionMultiplier K j z) =
      xi * completeResolutionMultiplier K j from rfl,
    analyticOrderAt_mul hxi hM, horderM, add_zero]

end

end RHTower
