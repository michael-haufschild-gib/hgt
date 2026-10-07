import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticPoleCancellation
import GaloisForLFunctions.RHTower.WeilPositiveProducerLindelof
import GaloisForLFunctions.HTGeometry.VerticalStripResidueShift

/-!
# Transport of the signed Gaussian contour to the Dirichlet half-plane

Full positivity supplies the growth bound for the actual logarithmic
remainder. The contour shift crosses just the pole at one; zeta zeros
cause no singularity. The resulting right-line identity retains the
negative spectral mass as well as the exact source pole coefficient.
-/

open Complex MeasureTheory Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower.WeilSingularArithmetic

open GaussZeroSum

private theorem exists_source_regularPart_linear {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 3 / 4 ≤ s.re →
      ‖zetaArchimedeanDatum s - WeilSpectral.weilContinuation hW s‖ ≤ C * (1 + |s.im|) := by
  obtain ⟨K, hK, hAK⟩ := exists_log_bound_zetaArchimedeanDatum
  have hH := WeilSpectral.herglotzWeilPositive_of_weilPositiveFull hW
  let L : ℝ := ∑' n : ℕ, |(if 2 ≤ n then lam n else 0 : ℝ)| / (n : ℝ) ^ (2 : ℝ)
  let B : ℝ := 4 * (6 * (K + 1 + L))
  have hL : 0 ≤ L := tsum_nonneg fun _ => by positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * B + L + 1, by positivity, fun s hs => ?_⟩
  have hid : ∀ z : ℂ, 1 < z.re → WeilSpectral.weilContinuation hW z =
      zetaArchimedeanDatum z + 1 / (z - 1) -
        LSeries (fun n => ((if 2 ≤ n then lam n else 0 : ℝ) : ℂ)) z := by
    intro z hz
    rw [WeilSpectral.weilContinuation_eq hW hz, WeilSpectral.weilFunction, zetaArchimedeanDatum]
    rfl
  have hb := norm_regularPart_le_of_re_ge hK hH.summable
    (WeilSpectral.differentiableOn_weilContinuation hW)
    (fun z hz => WeilSpectral.re_weilContinuation_nonneg hW hz) hid hAK
    (δ := 1 / 2) (by norm_num) (w := s) (by linarith)
  have he : 2 * (6 * (K + 1 + L)) / (1 / 2) = B := by dsimp [B]; ring
  change ‖zetaArchimedeanDatum s - WeilSpectral.weilContinuation hW s‖ ≤
    2 * (6 * (K + 1 + L)) / (1 / 2) * Real.log (|s.im| + 3) + L + 1 at hb
  rw [he] at hb
  have hlog : Real.log (|s.im| + 3) ≤ |s.im| + 2 := by
    have := Real.log_le_sub_one_of_pos (by positivity : 0 < |s.im| + 3)
    linarith
  refine hb.trans ?_
  nlinarith [mul_le_mul_of_nonneg_left hlog hB, mul_nonneg hB (abs_nonneg s.im),
    mul_nonneg hL (abs_nonneg s.im), abs_nonneg s.im]

private theorem exists_sourceZetaPairing_tail_poly {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 3 / 2 →
      2 ≤ |s.im| → ‖sourceZetaPairing hW s‖ ≤ C * (1 + |s.im|) ^ N := by
  obtain ⟨D, hD0, hD⟩ := exists_source_regularPart_linear hW
  obtain ⟨A, N, hA0, hA⟩ := exists_bound_norm_riemannZeta_strip 2
  obtain ⟨B, M, hB0, hB⟩ := exists_bound_norm_deriv_riemannZeta_strip 2
  refine ⟨((D + 1) * A + B * 2 ^ M) * A, 1 + N + M + N, by positivity,
    fun s hs0 hs1 ht => ?_⟩
  have hz := hA s.re s.im (abs_le.mpr ⟨by linarith, by linarith⟩) (by linarith)
  rw [Complex.re_add_im] at hz
  have hz' := hA (1 - s).re (1 - s).im
    (by simp only [Complex.sub_re, Complex.one_re]; rw [abs_le]; constructor <;> linarith)
    (by simpa using (show 1 ≤ |s.im| by linarith))
  rw [Complex.re_add_im] at hz'
  simp only [Complex.sub_im, Complex.one_im, zero_sub, abs_neg] at hz'
  have hd := hB s (abs_le.mpr ⟨by linarith, by linarith⟩) ht
  have hq : 1 ≤ 1 + |s.im| := by linarith [abs_nonneg s.im]
  have hN : |s.im| ^ N ≤ (1 + |s.im|) ^ N := by gcongr; linarith
  have hM : (1 + |s.im|) ^ M ≤ (1 + |s.im|) ^ (1 + N + M) :=
    pow_le_pow_right₀ hq (by omega)
  have hpole : ‖(1 : ℂ) / (s - 1)‖ ≤ 1 := by
    have hn : 1 ≤ ‖s - 1‖ := by
      have := Complex.abs_im_le_norm (s - 1)
      simp only [Complex.sub_im, Complex.one_im, sub_zero] at this
      linarith
    rw [norm_div, norm_one]
    exact div_le_one_of_le₀ hn (by linarith)
  have hcoef : ‖zetaArchimedeanDatum s + 1 / (s - 1) - WeilSpectral.weilContinuation hW s‖ ≤
      (D + 1) * (1 + |s.im|) := by
    have he : zetaArchimedeanDatum s + 1 / (s - 1) - WeilSpectral.weilContinuation hW s =
        (zetaArchimedeanDatum s - WeilSpectral.weilContinuation hW s) + 1 / (s - 1) := by ring
    rw [he]
    exact (norm_add_le _ _).trans ((add_le_add (hD s hs0) hpole).trans (by nlinarith))
  have hfirst : (D + 1) * (1 + |s.im|) * (A * (1 + |s.im|) ^ N) ≤
      (D + 1) * A * (1 + |s.im|) ^ (1 + N + M) := by
    calc _ = (D + 1) * A * (1 + |s.im|) ^ (1 + N) := by rw [pow_add, pow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hq (by omega)) (by positivity)
  have hd' : ‖deriv riemannZeta s‖ ≤ (B * 2 ^ M) * (1 + |s.im|) ^ M := by
    refine hd.trans ?_
    rw [mul_pow, mul_assoc]
    gcongr
    linarith
  unfold sourceZetaPairing
  rw [norm_mul]
  calc _ ≤ ((D + 1) * (1 + |s.im|) * (A * (1 + |s.im|) ^ N) +
        (B * 2 ^ M) * (1 + |s.im|) ^ M) * (A * (1 + |s.im|) ^ N) := by
      apply mul_le_mul _ (hz'.trans (mul_le_mul_of_nonneg_left hN hA0)) (norm_nonneg _) (by positivity)
      exact (norm_add_le _ _).trans (add_le_add
        (by rw [norm_mul]; exact mul_le_mul hcoef (hz.trans (mul_le_mul_of_nonneg_left hN hA0)) (norm_nonneg _) (by positivity)) hd')
    _ ≤ ((D + 1) * A * (1 + |s.im|) ^ (1 + N + M) +
        B * 2 ^ M * (1 + |s.im|) ^ (1 + N + M)) * (A * (1 + |s.im|) ^ N) :=
      mul_le_mul_of_nonneg_right (add_le_add hfirst
        (mul_le_mul_of_nonneg_left hM (by positivity))) (by positivity)
    _ = _ := by rw [pow_add]; ring

theorem exists_sourceZetaPairing_gaussian_tail_decay {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    ∃ C : ℝ, ∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 3 / 2 → 2 ≤ |s.im| →
      ‖sourceZetaPairing hW s * gaussWeight T s‖ ≤ C * (1 + s.im ^ 2)⁻¹ := by
  obtain ⟨A, N, hA, hb⟩ := exists_sourceZetaPairing_tail_poly hW
  refine ⟨A * Real.exp 1 * ((N + 2).factorial * Real.exp (3 / 2) * T ^ (N + 2)),
    fun s hs0 hs1 ht => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity : 0 < 1 + s.im ^ 2), norm_mul]
  have hg := norm_gaussWeight_le_of_re hT (s := s) (abs_le.mpr ⟨by linarith, by linarith⟩)
  have hs : 1 + s.im ^ 2 ≤ (1 + |s.im|) ^ 2 := by nlinarith [sq_abs s.im, abs_nonneg s.im]
  have hm := one_add_abs_pow_mul_exp_le (N + 2) hT s.im
  have he : Real.exp (-(s.im ^ 2 / (2 * T ^ 2))) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))
  calc ‖sourceZetaPairing hW s‖ * ‖gaussWeight T s‖ * (1 + s.im ^ 2)
      ≤ (A * (1 + |s.im|) ^ N) * (Real.exp 1 * Real.exp (-(s.im ^ 2 / T ^ 2))) *
        (1 + |s.im|) ^ 2 := by gcongr; exact hb s hs0 hs1 ht
    _ = A * Real.exp 1 * ((1 + |s.im|) ^ (N + 2) * Real.exp (-(s.im ^ 2 / T ^ 2))) := by
      rw [pow_add]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (hm.trans (mul_le_of_le_one_right (by positivity) he)) (by positivity)

theorem sourceZetaPairing_gaussian_shift {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) * gaussWeight T ((3 / 2 : ℂ) + t * I)) -
      (∫ t : ℝ, sourceZetaPairing hW ((3 / 4 : ℂ) + t * I) * gaussWeight T ((3 / 4 : ℂ) + t * I)) =
      -(Real.pi : ℂ) * sourcePoleNumerator hW 1 * gaussWeight T 1 := by
  obtain ⟨C, hC⟩ := exists_sourceZetaPairing_gaussian_tail_decay hW hT
  have hr := (tendsto_mul_sourceZetaPairing hW).mul
    ((differentiable_gaussWeight T 1).continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  simp only [mul_assoc] at hr
  have hs := integral_line_sub_integral_line_eq
    (F := fun s => sourceZetaPairing hW s * gaussWeight T s)
    (a := 3 / 4) (b := 3 / 2) (p := 1)
    (by norm_num) (by norm_num)
    (fun s hs0 _ hs1 => (differentiableAt_sourceZetaPairing hW (by linarith) hs1).mul
      (differentiable_gaussWeight T s)) hr hC
  push_cast at hs
  convert hs using 1 <;> ring

theorem re_integral_sourceZetaPairing_gaussian_right_eq {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I)).re =
      -(Real.pi * (sourcePoleNumerator hW 1).re * Real.exp (1 / (4 * T ^ 2))) -
        Real.pi * ∫ r : ℝ, ‖riemannZeta ((1 / 2 : ℂ) + r * I)‖ ^ 2 *
          Real.exp (-(r ^ 2 / T ^ 2)) ∂WeilSpectral.boundaryMeasure hW := by
  have hg : gaussWeight T 1 = ((Real.exp (1 / (4 * T ^ 2)) : ℝ) : ℂ) := by
    unfold gaussWeight
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hs := congrArg Complex.re (sourceZetaPairing_gaussian_shift hW hT)
  rw [hg, Complex.sub_re, re_integral_sourceZetaPairing_gaussian_eq hW hT] at hs
  simp only [Complex.re_mul_ofReal, Complex.mul_re, Complex.neg_re, Complex.ofReal_re,
    Complex.neg_im, Complex.ofReal_im, neg_zero, zero_mul, sub_zero] at hs
  linarith

theorem re_integral_sourceZetaPairing_gaussian_right_le {lam : ℕ → ℝ}
    (hW : WeilPositiveFull lam) {T : ℝ} (hT : 1 ≤ T) :
    (∫ t : ℝ, sourceZetaPairing hW ((3 / 2 : ℂ) + t * I) *
      gaussWeight T ((3 / 2 : ℂ) + t * I)).re ≤
      -(Real.pi * (sourcePoleNumerator hW 1).re * Real.exp (1 / (4 * T ^ 2))) := by
  rw [re_integral_sourceZetaPairing_gaussian_right_eq hW hT]
  exact sub_le_self _ (mul_nonneg Real.pi_pos.le (integral_nonneg fun _ => by positivity))

end RHTower.WeilSingularArithmetic
