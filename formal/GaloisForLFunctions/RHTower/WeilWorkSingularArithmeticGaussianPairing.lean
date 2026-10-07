import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticHerglotzPairing
import GaloisForLFunctions.RHTower.ZetaGaussianZeroSums
import GaloisForLFunctions.RHTower.ZetaVerticalStripPolynomialBound

/-!
# The positive Gaussian pairing of every full Weil source

The test `ζ(s) ζ(1-s) exp((s-1/2)^2/T^2)` satisfies all hypotheses of the
reflected Herglotz pairing. Consequently the real source integral equals a
nonnegative weighted critical-line zeta mass. Only full Weil positivity is
required of the source; no boundary limit or absolute arithmetic notch
condition is assumed.
-/

open Complex MeasureTheory Filter Topology Set
open scoped ComplexConjugate

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

def zetaGaussianPairingTest (T : ℝ) (s : ℂ) : ℂ :=
  riemannZeta s * riemannZeta (1 - s) * gaussWeight T s

theorem zetaGaussianPairingTest_conj (T : ℝ) (s : ℂ) :
    zetaGaussianPairingTest T (conj s) = conj (zetaGaussianPairingTest T s) := by
  simp only [zetaGaussianPairingTest, map_mul, gaussWeight_conj, riemannZeta_conj]
  rw [show 1 - conj s = conj (1 - s) by simp, riemannZeta_conj]

theorem zetaGaussianPairingTest_one_sub (T : ℝ) (s : ℂ) :
    zetaGaussianPairingTest T (1 - s) = zetaGaussianPairingTest T s := by
  have hg : gaussWeight T (1 - s) = gaussWeight T s := by
    unfold gaussWeight
    congr 1
    ring
  simp only [zetaGaussianPairingTest, sub_sub_cancel, hg]
  ring

theorem differentiableAt_zetaGaussianPairingTest (T : ℝ) {s : ℂ}
    (hs0 : 1 / 4 ≤ s.re) (hs1 : s.re ≤ 3 / 4) :
    DifferentiableAt ℂ (zetaGaussianPairingTest T) s := by
  have hne : s ≠ 1 := by intro h; rw [h] at hs1; norm_num at hs1
  have hne' : 1 - s ≠ 1 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  exact ((differentiableAt_riemannZeta hne).mul
    ((differentiableAt_riemannZeta hne').comp s (by fun_prop))).mul
      (differentiable_gaussWeight T s)

theorem zetaGaussianPairingTest_critical (T r : ℝ) :
    zetaGaussianPairingTest T ((1 / 2 : ℂ) + r * I) =
      ((‖riemannZeta ((1 / 2 : ℂ) + r * I)‖ ^ 2 * Real.exp (-(r ^ 2 / T ^ 2)) : ℝ) : ℂ) := by
  have hc : 1 - ((1 / 2 : ℂ) + r * I) = conj ((1 / 2 : ℂ) + r * I) := by
    simp only [map_add, map_div₀, map_one, map_ofNat, map_mul, conj_ofReal, conj_I]
    ring
  have hg : gaussWeight T ((1 / 2 : ℂ) + r * I) =
      ((Real.exp (-(r ^ 2 / T ^ 2)) : ℝ) : ℂ) := by
    unfold gaussWeight
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring_nf
    simp [I_sq]
  rw [zetaGaussianPairingTest, hc, riemannZeta_conj, Complex.mul_conj,
    Complex.normSq_eq_norm_sq, hg, Complex.ofReal_mul]

private theorem exists_zeta_quarter_strip_poly :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖riemannZeta s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨A, N, hA0, hA⟩ := exists_bound_norm_riemannZeta_strip 1
  let K : Set ℂ := Icc (1 / 4 : ℝ) (3 / 4) ×ℂ Icc (-1 : ℝ) 1
  have hK : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hc : ContinuousOn riemannZeta K := by
    intro s hs
    have hs1 : s.re ≤ 3 / 4 := hs.1.2
    exact (differentiableAt_riemannZeta (by intro h; rw [h] at hs1; norm_num at hs1)).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn hc
  refine ⟨|B| + A, N, by positivity, fun s hs0 hs1 => ?_⟩
  have hp : (1 : ℝ) ≤ (1 + |s.im|) ^ N := one_le_pow₀ (by linarith [abs_nonneg s.im])
  by_cases ht : 1 ≤ |s.im|
  · have hh := hA s.re s.im (abs_le.mpr ⟨by linarith, by linarith⟩) ht
    rw [Complex.re_add_im] at hh
    refine hh.trans ?_
    gcongr
    · exact le_add_of_nonneg_left (abs_nonneg B)
    · linarith
  · have hsK : s ∈ K := ⟨⟨hs0, hs1⟩,
      ⟨by linarith [neg_abs_le s.im], by linarith [le_abs_self s.im]⟩⟩
    calc ‖riemannZeta s‖ ≤ B := hB s hsK
      _ ≤ |B| + A := by linarith [le_abs_self B]
      _ ≤ (|B| + A) * (1 + |s.im|) ^ N := le_mul_of_one_le_right (by positivity) hp

/-- The actual Gaussian test has the uniform fourth-order decay needed by Fubini. -/
theorem exists_zetaGaussianPairingTest_decay {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, ∀ s : ℂ, 1 / 4 ≤ s.re → s.re ≤ 3 / 4 →
      ‖zetaGaussianPairingTest T s‖ * (1 + s.im ^ 2) ^ 2 ≤ C := by
  obtain ⟨A, N, hA0, hA⟩ := exists_zeta_quarter_strip_poly
  refine ⟨A ^ 2 * Real.exp 1 * ((2 * N + 4).factorial * Real.exp (3 / 2) * T ^ (2 * N + 4)),
    fun s hs0 hs1 => ?_⟩
  have hz := hA s hs0 hs1
  have hz' := hA (1 - s) (by simp; linarith) (by simp; linarith)
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hz'
  have hg := norm_gaussWeight_le_of_re hT (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hsq : (1 + s.im ^ 2) ^ 2 ≤ (1 + |s.im|) ^ 4 := by
    calc
      (1 + s.im ^ 2) ^ 2 ≤ ((1 + |s.im|) ^ 2) ^ 2 := by
        gcongr
        nlinarith [sq_abs s.im, abs_nonneg s.im]
      _ = _ := by ring
  have hbound : ‖zetaGaussianPairingTest T s‖ * (1 + s.im ^ 2) ^ 2 ≤
      A ^ 2 * Real.exp 1 * ((1 + |s.im|) ^ (2 * N + 4) * Real.exp (-(s.im ^ 2 / T ^ 2))) := by
    unfold zetaGaussianPairingTest
    rw [norm_mul, norm_mul]
    calc ‖riemannZeta s‖ * ‖riemannZeta (1 - s)‖ * ‖gaussWeight T s‖ * (1 + s.im ^ 2) ^ 2
        ≤ (A * (1 + |s.im|) ^ N) * (A * (1 + |s.im|) ^ N) *
          (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) * (1 + |s.im|) ^ 4 := by gcongr
      _ = _ := by rw [show 2 * N + 4 = N + N + 4 by omega, pow_add, pow_add]; ring
  refine hbound.trans ?_
  have hm := one_add_abs_pow_mul_exp_le (2 * N + 4) hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  exact mul_le_mul_of_nonneg_left
    (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

/-- The concrete source pairing is an absolutely integrable complex function. -/
theorem integrable_weilContinuation_mul_zetaGaussian {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    Integrable (fun t : ℝ => WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      zetaGaussianPairingTest T ((3 / 4 : ℂ) + t * I)) := by
  obtain ⟨C, hC⟩ := exists_zetaGaussianPairingTest_decay hT
  refine integrable_weilContinuation_mul_line_test hW
    (continuous_iff_continuousAt.mpr fun t =>
      (differentiableAt_zetaGaussianPairingTest T (by norm_num) (by simp)).continuousAt.comp
        (by fun_prop)) (C := C) ?_
  intro t
  simpa using hC ((3 / 4 : ℂ) + t * I) (by norm_num) (by simp)

/-- Exact positive-measure formula for the Gaussian pairing of every full source. -/
theorem re_integral_weilContinuation_mul_zetaGaussian_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      zetaGaussianPairingTest T ((3 / 4 : ℂ) + t * I)).re =
      Real.pi * ∫ r : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + r * I)‖ ^ 2 *
        Real.exp (-(r ^ 2 / T ^ 2)) ∂WeilSpectral.boundaryMeasure hW := by
  obtain ⟨C, hC⟩ := exists_zetaGaussianPairingTest_decay hT
  have h := re_integral_weilContinuation_mul_test_eq hW
    (fun _ => differentiableAt_zetaGaussianPairingTest T)
    (C := C) (f := zetaGaussianPairingTest T) ?_ ?_ hC
  · simpa only [zetaGaussianPairingTest_critical, Complex.ofReal_re] using h
  · intro t
    rw [show (1 / 4 : ℂ) + t * I = 1 - conj ((3 / 4 : ℂ) + t * I) by
      simp only [map_add, map_div₀, map_ofNat, map_mul, conj_ofReal, conj_I]; ring,
      zetaGaussianPairingTest_one_sub, zetaGaussianPairingTest_conj]
  · intro t
    rw [show (3 / 4 : ℂ) + (-t) * I = conj ((3 / 4 : ℂ) + t * I) by
      simp only [map_add, map_div₀, map_ofNat, map_mul, conj_ofReal, conj_I]; ring,
      zetaGaussianPairingTest_conj]

/-- Full positivity alone makes the actual Gaussian source pairing nonnegative. -/
theorem re_integral_weilContinuation_mul_zetaGaussian_nonneg {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    0 ≤ (∫ t : ℝ, WeilSpectral.weilContinuation hW ((3 / 4 : ℂ) + t * I) *
      zetaGaussianPairingTest T ((3 / 4 : ℂ) + t * I)).re := by
  rw [re_integral_weilContinuation_mul_zetaGaussian_eq hW hT]
  exact mul_nonneg Real.pi_pos.le (integral_nonneg fun _ => by positivity)

end RHTower.WeilSingularArithmetic
