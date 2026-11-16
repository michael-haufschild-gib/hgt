import GaloisForLFunctions.FamilyContinuationTheory.AngularMellinBounds
import GaloisForLFunctions.FamilyContinuationTheory.HarmonicGaussianPoissonGivesGrossencharacterContinuation
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.PrimitiveCharactersAndStripBounds

/-! # Vertical bounds for primitive Grössencharacter L-functions

The harmonic theta Mellin integral controls growth in a strip. The functional
equation and the angular Gamma quotient turn absolute convergence on the right
into a polynomial bound on the left.
-/

noncomputable section
set_option autoImplicit false
open Complex MeasureTheory Set Filter Asymptotics
open scoped Classical BigOperators ComplexConjugate nonZeroDivisors Topology
namespace GaloisForLFunctions.FamilyContinuationTheory
open HeckeLFunctions MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
open MetaplecticMobiusDescent.CubicEisenstein
local notation "O" => Eisenstein.O

/-- Absolute ideal convergence bounds the entire family uniformly to the right of one. -/
theorem grossenLFunction_uniform_right_bound (σ : ℝ) (hσ : 1 < σ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
      (k : ℕ), 1 ≤ k → ∀ w : ℂ, σ ≤ w.re → ‖grossenLFunction 𝔪 ψ k w‖ ≤ C := by
  let F : (Ideal O)⁰ → ℝ := fun I => ‖fullIdealWeight (σ : ℂ) I.val‖
  have hF : Summable F := (fullIdealWeight_summable_norm (σ : ℂ) (by simpa using hσ)).subtype _
  refine ⟨∑' I, F I, tsum_nonneg (fun _ => norm_nonneg _), ?_⟩
  intro 𝔪 ψ k hk w hw
  rw [grossenLFunction_eq_tsum_ideals 𝔪 ψ hk (hσ.trans_le hw)]
  have hs := summable_norm_grossenIdealTerm 𝔪 ψ k (hσ.trans_le hw)
  apply (norm_tsum_le_tsum_norm hs).trans (hs.tsum_le_tsum ?_ hF)
  intro I
  have hI : I.val ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp I.property
  have hc : ‖idealPsiSix I.val ^ k * primitiveIdealValue 𝔪 ψ I.val‖ ≤ 1 := by
    rw [norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) (norm_idealPsiSix_le_one _))
      (norm_nonneg _) (norm_primitiveIdealValue_le_one 𝔪 ψ _)
  change ‖(idealPsiSix I.val ^ k * primitiveIdealValue 𝔪 ψ I.val) *
    (Ideal.absNorm I.val : ℂ) ^ (-w)‖ ≤ _
  rw [norm_mul]
  apply (mul_le_of_le_one_left (norm_nonneg _) hc).trans
  have hh := HeckeReciprocalBound.normWeight_le_of_re_ge hw I.val
  simpa only [F, fullIdealWeight, if_neg hI] using hh

/-- The completed function is bounded on every closed vertical strip. -/
theorem grossenCompletedL_strip_bound (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ w : ℂ, w.re ∈ Icc a b →
      ‖grossenCompletedL 𝔪 ψ k w‖ ≤ C := by
  have hm (s : ℂ) : MellinConvergent (grossenTheta 𝔪 ψ k) s :=
    (isStrong_grossenFEPair 𝔪 ψ k hk).hasMellin s |>.1
  obtain ⟨C, hC, hb⟩ := mellin_uniform_strip_bound (grossenTheta 𝔪 ψ k)
    (a + (3 * k : ℕ)) (b + (3 * k : ℕ)) (hm _) (hm _)
  refine ⟨C / 6, by positivity, ?_⟩
  intro w hw
  rw [grossenCompletedL_eq_mellin 𝔪 ψ hk w, norm_mul]
  have hc : ‖(1 / 6 : ℂ)‖ = (1 / 6 : ℝ) := by norm_num
  rw [hc, one_div, inv_mul_eq_div]
  apply div_le_div_of_nonneg_right (hb (w + (3 * k : ℕ)) ?_ ?_) (by norm_num)
  · simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hw.1]
  · simp only [Complex.add_re, Complex.natCast_re]
    linarith only [hw.2]

/-- Reciprocal Gamma converts the bounded theta Mellin transform into exponential
growth of the uncompleted function; no zero-free hypothesis is used. -/
theorem grossenLFunction_strip_exp_bound (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (a b : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ w : ℂ, w.re ∈ Icc a b →
      ‖grossenLFunction 𝔪 ψ k w‖ ≤ A * Real.exp (Real.pi * |w.im|) := by
  obtain ⟨C, hC, hcomp⟩ := grossenCompletedL_strip_bound 𝔪 ψ hk a b
  obtain ⟨G, hG, hg⟩ := CubicGammaExponential.inverse_Gamma_strip_exp_bound_complex
    (a + (3 * k : ℕ)) (b + (3 * k : ℕ))
  let α := grossenAlpha 𝔪 ψ
  have hα : 0 < α := grossenAlpha_pos 𝔪 ψ
  let P := α ^ (a + (3 * k : ℕ)) + α ^ (b + (3 * k : ℕ))
  have hP : 0 ≤ P := add_nonneg (Real.rpow_nonneg hα.le _) (Real.rpow_nonneg hα.le _)
  refine ⟨C * P * G, by positivity, ?_⟩
  intro w hw
  have harg : (w + (3 * k : ℕ)).re ∈ Icc (a + (3 * k : ℕ)) (b + (3 * k : ℕ)) := by
    simp only [Complex.add_re, Complex.natCast_re, Set.mem_Icc]
    constructor <;> linarith only [hw.1, hw.2]
  have hp : ‖((α : ℂ) ^ (-(w + (3 * k : ℕ))))⁻¹‖ ≤ P := by
    rw [← Complex.cpow_neg, neg_neg, Complex.norm_cpow_eq_rpow_re_of_pos hα]
    exact rpow_between_endpoints α _ _ _ hα harg.1 harg.2
  have hgamma := hg (w + (3 * k : ℕ)) harg
  simp only [Complex.add_im, Complex.natCast_im, add_zero] at hgamma
  rw [grossenLFunction, grossenArchimedeanFactor, div_eq_mul_inv, mul_inv_rev]
  rw [norm_mul, norm_mul]
  change ‖grossenCompletedL 𝔪 ψ k w‖ *
    (‖(Complex.Gamma (w + (3 * k : ℕ)))⁻¹‖ *
      ‖((α : ℂ) ^ (-(w + (3 * k : ℕ))))⁻¹‖) ≤ _
  calc
    _ ≤ C * ((G * Real.exp (Real.pi * |w.im|)) * P) :=
      mul_le_mul (hcomp w hw) (mul_le_mul hgamma hp (norm_nonneg _) (by positivity))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hC
    _ = _ := by ring

/-- The functional equation reverses the real part and preserves height. Its norm
factor separates the conductor scale from the angular Gamma quotient. -/
theorem grossenLFunction_norm_reflection (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪)
    {k : ℕ} (hk : 1 ≤ k) (w : ℂ)
    (_hw : -(3 * (k : ℝ)) < w.re) (hw' : w.re < 1 + 3 * (k : ℝ)) :
    ‖grossenLFunction 𝔪 ψ k w‖ =
      grossenAlpha 𝔪 ψ ^ (2 * w.re - 1) *
        ‖Complex.Gamma (1 - w + (3 * k : ℕ)) / Complex.Gamma (w + (3 * k : ℕ))‖ *
          ‖grossenLFunction 𝔪 ψ k (1 - conj w)‖ := by
  have hd : -(3 * (k : ℝ)) < (1 - conj w).re := by
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    linarith only [hw']
  have he := congrArg norm (grossenCompletedL_one_sub 𝔪 ψ hk (1 - w))
  simp only [sub_sub_cancel, norm_mul, norm_grossenRootNumber, one_mul,
    Complex.norm_conj, map_sub, map_one] at he
  have hscale (z : ℂ) : ‖grossenArchimedeanFactor 𝔪 ψ k z‖ =
      grossenAlpha 𝔪 ψ ^ (-(z.re + (3 * k : ℕ))) * ‖Complex.Gamma (z + (3 * k : ℕ))‖ := by
    rw [grossenArchimedeanFactor, norm_mul,
      Complex.norm_cpow_eq_rpow_re_of_pos (grossenAlpha_pos 𝔪 ψ)]
    simp only [Complex.neg_re, Complex.add_re, Complex.natCast_re]
  have hgamma : ‖Complex.Gamma (1 - conj w + (3 * k : ℕ))‖ =
      ‖Complex.Gamma (1 - w + (3 * k : ℕ))‖ := by
    rw [show 1 - conj w + (3 * k : ℕ) = conj (1 - w + (3 * k : ℕ)) by
      simp only [map_add, map_sub, map_one, map_natCast],
      Complex.Gamma_conj, Complex.norm_conj]
  have hr : ‖grossenArchimedeanFactor 𝔪 ψ k (1 - conj w)‖ /
      ‖grossenArchimedeanFactor 𝔪 ψ k w‖ =
      grossenAlpha 𝔪 ψ ^ (2 * w.re - 1) *
        ‖Complex.Gamma (1 - w + (3 * k : ℕ)) / Complex.Gamma (w + (3 * k : ℕ))‖ := by
    rw [hscale, hscale, hgamma, norm_div]
    simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
    rw [mul_div_mul_comm, ← Real.rpow_sub (grossenAlpha_pos 𝔪 ψ)]
    congr 2
    ring
  calc
    ‖grossenLFunction 𝔪 ψ k w‖ =
        ‖grossenCompletedL 𝔪 ψ k w‖ / ‖grossenArchimedeanFactor 𝔪 ψ k w‖ := by
          rw [grossenLFunction, norm_div]
    _ = ‖grossenCompletedL 𝔪 ψ k (1 - conj w)‖ /
        ‖grossenArchimedeanFactor 𝔪 ψ k w‖ := by rw [he]
    _ = (‖grossenArchimedeanFactor 𝔪 ψ k (1 - conj w)‖ /
        ‖grossenArchimedeanFactor 𝔪 ψ k w‖) *
        ‖grossenLFunction 𝔪 ψ k (1 - conj w)‖ := by
          rw [grossenCompletedL_eq_archimedean_mul 𝔪 ψ k hd, norm_mul]
          ring
    _ = _ := by rw [hr]

/-- One polynomial degree controls the left boundary for every positive infinity type
and finite character, with the conductor scale explicit. -/
theorem grossenLFunction_left_polynomial_bound :
    ∃ d : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ), w.re = -(1 / 10) →
        ‖grossenLFunction 𝔪 ψ k w‖ ≤
          C * grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ)) * (3 + |w.im|) ^ d := by
  obtain ⟨d, hgamma⟩ := angular_gamma_quotient_strip (11 / 10) (11 / 10) (by norm_num)
  obtain ⟨D, hD, hright⟩ := grossenLFunction_uniform_right_bound (11 / 10) (by norm_num)
  refine ⟨d, ?_⟩
  intro k hk
  obtain ⟨G, hG, hg⟩ := hgamma (3 * k)
  refine ⟨G * D, by positivity, ?_⟩
  intro 𝔪 ψ w hw
  have hα := grossenAlpha_pos 𝔪 ψ
  have hαpow : 0 ≤ grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ)) := Real.rpow_nonneg hα.le _
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  rw [grossenLFunction_norm_reflection 𝔪 ψ hk w
    (by linarith only [hw, hkR]) (by linarith only [hw, hkR])]
  have he : 2 * w.re - 1 = -(6 / 5 : ℝ) := by rw [hw]; norm_num
  rw [he]
  have harg : ((11 / 10 : ℝ) : ℂ) + (-w.im : ℝ) * Complex.I = 1 - w := by
    (apply Complex.ext <;> simp [hw]); ring
  have hgb := hg (11 / 10) ⟨le_rfl, le_rfl⟩ (-w.im)
  rw [harg, sub_sub_cancel, abs_neg] at hgb
  have hdb := hright 𝔪 ψ k hk (1 - conj w) (by simp [hw]; norm_num)
  calc
    _ ≤ grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ)) * (G * (1 + |w.im|) ^ d) * D := by
      exact mul_le_mul
        (mul_le_mul_of_nonneg_left hgb (Real.rpow_nonneg (grossenAlpha_pos 𝔪 ψ).le _))
        hdb (norm_nonneg _) (mul_nonneg hαpow (mul_nonneg hG.le (by positivity)))
    _ ≤ grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ)) * (G * (3 + |w.im|) ^ d) * D := by
      gcongr; linarith only
    _ = _ := by ring

/-- Polynomial growth throughout a strip crossing the critical strip, with one
height degree for every primitive finite character and every positive infinity type. -/
theorem grossenLFunction_polynomial_strip_bound :
    ∃ d : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ), w ∈ HeckeStrip.closedStrip →
        ‖grossenLFunction 𝔪 ψ k w‖ ≤
          C * (1 + grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ))) * (3 + |w.im|) ^ d := by
  obtain ⟨d, hleft⟩ := grossenLFunction_left_polynomial_bound
  obtain ⟨D, hD, hright⟩ := grossenLFunction_uniform_right_bound (11 / 10) (by norm_num)
  refine ⟨d, ?_⟩
  intro k hk
  obtain ⟨B, hB, hb⟩ := hleft k hk
  refine ⟨(3 ^ d * (B + D)) * 2 ^ d, by positivity, ?_⟩
  intro 𝔪 ψ
  let P := grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ))
  have hP : 0 ≤ P := Real.rpow_nonneg (grossenAlpha_pos 𝔪 ψ).le _
  let E := (B + D) * (1 + P)
  have hE : 0 ≤ E := mul_nonneg (add_nonneg hB hD) (by positivity)
  have hleftC : B * P ≤ E := by dsimp only [E]; nlinarith only [hB, hD, hP, mul_nonneg hD hP]
  have hrightC : D ≤ E := by dsimp only [E]; nlinarith only [hB, hD, hP, mul_nonneg (add_nonneg hB hD) hP]
  let L := grossenLFunction 𝔪 ψ k
  let F : ℂ → ℂ := fun z => L z / (z + 2) ^ d
  have hden (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) : 1 ≤ ‖z + 2‖ ^ d :=
    one_le_pow₀ (HeckeStrip.shift_norm_lower z hz)
  have hdiff (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) : DifferentiableAt ℂ L z := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hz' : -(3 * (k : ℝ)) < z.re := by linarith only [hz.1, hkR]
    exact (differentiableOn_grossenLFunction 𝔪 ψ hk z hz').differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz')
  have hd : Differentiable ℂ (fun z : ℂ => (z + 2) ^ d) :=
    (differentiable_id.add_const 2).pow d
  have hF : DiffContOnCl ℂ F HeckeStrip.strip := by
    refine ⟨?_, ?_⟩
    · intro z hz
      have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le, hz.2.le⟩
      exact ((hdiff z hzc).div (hd z) (pow_ne_zero _ (HeckeStrip.shift_ne_zero z hzc))).differentiableWithinAt
    · intro z hz
      have hzc := HeckeStrip.closure_strip_subset hz
      exact ((hdiff z hzc).continuousAt.div (hd z).continuousAt
        (pow_ne_zero _ (HeckeStrip.shift_ne_zero z hzc))).continuousWithinAt
  obtain ⟨A, hA, hg⟩ := grossenLFunction_strip_exp_bound 𝔪 ψ hk (-(1 / 10)) (11 / 10)
  have hgrowth : ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀ z ∈ HeckeStrip.strip,
      ‖F z‖ ≤ A * Real.exp (B * |z.im|) := by
    refine ⟨A, Real.pi, hA, Real.pi_pos.le, ?_⟩
    intro z hz
    have hzc : z ∈ HeckeStrip.closedStrip := ⟨hz.1.le, hz.2.le⟩
    change ‖L z / (z + 2) ^ d‖ ≤ _
    rw [norm_div, norm_pow]
    exact (div_le_self (norm_nonneg _) (hden z hzc)).trans (hg z hzc)
  have hedge (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip)
      (hnum : ‖L z‖ ≤ E * (3 + |z.im|) ^ d) : ‖F z‖ ≤ 3 ^ d * E := by
    change ‖L z / (z + 2) ^ d‖ ≤ _
    rw [norm_div, norm_pow]
    apply (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hden z hz))).mpr
    calc
      _ ≤ E * (3 + |z.im|) ^ d := hnum
      _ ≤ E * (3 * ‖z + 2‖) ^ d := mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity) (HeckeStrip.height_le_shift_norm z hz) d) hE
      _ = _ := by rw [mul_pow]; ring
  have hnorm (z : ℂ) (hz : z ∈ HeckeStrip.closedStrip) : ‖F z‖ ≤ 3 ^ d * E := by
    apply HeckeStrip.vertical_strip_of_exp_bound F (3 ^ d * E) hF hgrowth ?_ ?_ z hz
    · intro w hw
      apply hedge w ⟨by rw [hw], by rw [hw]; norm_num⟩
      exact (hb 𝔪 ψ w hw).trans (mul_le_mul_of_nonneg_right hleftC (by positivity))
    · intro w hw
      apply hedge w ⟨by rw [hw]; norm_num, by rw [hw]⟩
      apply (hright 𝔪 ψ k hk w hw.ge).trans
      exact hrightC.trans
        (le_mul_of_one_le_right hE (one_le_pow₀ (by linarith [abs_nonneg w.im])))
  intro w hw
  have hh := hnorm w hw
  change ‖L w / (w + 2) ^ d‖ ≤ 3 ^ d * E at hh
  rw [norm_div, norm_pow] at hh
  have hmul := (div_le_iff₀ (lt_of_lt_of_le zero_lt_one (hden w hw))).mp hh
  calc
    _ ≤ (3 ^ d * E) * ‖w + 2‖ ^ d := hmul
    _ ≤ (3 ^ d * E) * (2 * (3 + |w.im|)) ^ d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (HeckeStrip.shift_norm_le_height w hw) d) (by positivity)
    _ = _ := by rw [mul_pow]; dsimp only [E, P]; ring

/-- The archimedean scale contributes the usual three-fifths power of the
primitive finite conductor norm on the chosen strip. -/
theorem grossenLFunction_conductor_strip_bound :
    ∃ d : ℕ, ∀ k : ℕ, 1 ≤ k → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (𝔪 : Modulus K) (ψ : HeckeCharacter 𝔪) (w : ℂ), w ∈ HeckeStrip.closedStrip →
        ‖grossenLFunction 𝔪 ψ k w‖ ≤
          C * (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ) ^ (3 / 5 : ℝ) *
            (3 + |w.im|) ^ d := by
  obtain ⟨d, hb⟩ := grossenLFunction_polynomial_strip_bound
  refine ⟨d, ?_⟩
  intro k hk
  obtain ⟨C, hC, hbound⟩ := hb k hk
  let c := (Real.sqrt 3 / (2 * Real.pi)) ^ (6 / 5 : ℝ)
  have hc : 0 ≤ c := Real.rpow_nonneg (by positivity) _
  refine ⟨C * (1 + c), by positivity, ?_⟩
  intro 𝔪 ψ w hw
  let Q : ℝ := Ideal.absNorm (heckeFiniteConductor 𝔪 ψ)
  have hQ1 : 1 ≤ Q := by
    have hNat : 1 ≤ Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) :=
      Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (heckeFiniteConductor_ne_bot 𝔪 ψ))
    change (1 : ℝ) ≤ (Ideal.absNorm (heckeFiniteConductor 𝔪 ψ) : ℝ)
    exact_mod_cast hNat
  have hQ : 0 < Q := zero_lt_one.trans_le hQ1
  have hscale : (grossenAlpha 𝔪 ψ)⁻¹ = HeckeStrip.completionScale Q := by
    rw [grossenAlpha, inv_div, HeckeStrip.completionScale,
      Real.sqrt_mul (show (0 : ℝ) ≤ 3 by norm_num)]
  have hp : grossenAlpha 𝔪 ψ ^ (-(6 / 5 : ℝ)) = c * Q ^ (3 / 5 : ℝ) := by
    rw [show -(6 / 5 : ℝ) = (-1) * (6 / 5) by ring,
      Real.rpow_mul (grossenAlpha_pos 𝔪 ψ).le, Real.rpow_neg_one, hscale,
      HeckeStrip.completionScale_left_power Q hQ]
  have hpow : 1 ≤ Q ^ (3 / 5 : ℝ) := Real.one_le_rpow hQ1 (by norm_num)
  have hh := hbound 𝔪 ψ w hw
  rw [hp] at hh
  apply hh.trans
  calc
    _ ≤ C * ((1 + c) * Q ^ (3 / 5 : ℝ)) * (3 + |w.im|) ^ d := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      apply mul_le_mul_of_nonneg_left _ hC
      nlinarith only [hpow]
    _ = _ := by ring

end GaloisForLFunctions.FamilyContinuationTheory
