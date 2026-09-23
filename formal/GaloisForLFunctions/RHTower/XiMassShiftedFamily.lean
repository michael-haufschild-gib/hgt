import GaloisForLFunctions.RHTower.XiSpectralFamilyRH
import GaloisForLFunctions.HTGeometry.PrincipalSquareRoot

/-!
# The mass-shifted spectral family

`beta_a q = sqrt (alpha^ q ^ (2 : ℕ) + a^(2 : ℕ))` with `a > 1/2`.  Writing `alpha^ = R + i J` with `R` the
height and `|J| < 1/2`, the argument of the root has

`Re = R^(2 : ℕ) - J^(2 : ℕ) + a^(2 : ℕ) >= a^(2 : ℕ)`,   `Im = 2 R J`,

so the root's real part exceeds `R` -- because `a^(2 : ℕ) > J^(2 : ℕ)` -- and its imaginary part is
`R |J| / Re beta_a < |J|`.  Every condition of `SpectralFamily` follows, with the height comparison
`R < Re beta_a` supplying summability and finite shells at once.

This is the carrier whose explicit formula converges: the corner of `exp(-t |r|)` is smoothed to
`exp(-t sqrt(r^(2 : ℕ) + a^(2 : ℕ)))`, whose Fourier transform decays like `exp(-a|x|)`.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- The argument of the mass-shifted root. -/
def xiMassArg (a : ℝ) (q : XiZeroCopy) : ℂ := xiPoissonPoint q ^ (2 : ℕ) + ((a ^ (2 : ℕ) : ℝ) : ℂ)

theorem xiMassArg_re (a : ℝ) (q : XiZeroCopy) :
    (xiMassArg a q).re =
      (xiPoissonPoint q).re ^ (2 : ℕ) - (xiPoissonPoint q).im ^ (2 : ℕ) + a ^ (2 : ℕ) := by
  rw [xiMassArg, Complex.add_re, Complex.ofReal_re, pow_two, Complex.mul_re]
  ring

theorem xiMassArg_im (a : ℝ) (q : XiZeroCopy) :
    (xiMassArg a q).im = 2 * ((xiPoissonPoint q).re * (xiPoissonPoint q).im) := by
  rw [xiMassArg, Complex.add_im, Complex.ofReal_im, pow_two, Complex.mul_im]
  ring

/-- Heights of the Poisson coordinate exceed three. -/
theorem three_lt_xiPoissonPoint_re (q : XiZeroCopy) : 3 < (xiPoissonPoint q).re := by
  have h1 : ‖xiPoissonPoint q‖ ≤ (xiPoissonPoint q).re + 1 / 2 := norm_xiPoissonPoint_le q
  have h2 : ‖xiPoissonPoint q‖ = ‖xiSpectralPoint q‖ := norm_xiPoissonPoint q
  have h3 : (4 : ℝ) < ‖xiSpectralPoint q‖ := four_lt_norm_xiSpectralPoint q
  rw [h2] at h1
  linarith

theorem xiMassArg_re_pos {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) : 0 < (xiMassArg a q).re := by
  have hR := three_lt_xiPoissonPoint_re q
  have hJ : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  have hJ2 : (xiPoissonPoint q).im ^ (2 : ℕ) < 1 / 4 := by
    have := abs_nonneg (xiPoissonPoint q).im
    nlinarith [sq_abs (xiPoissonPoint q).im]
  rw [xiMassArg_re]
  nlinarith [hR, hJ2, ha]

/-- The mass-shifted height strictly exceeds the Poisson height. -/
theorem xiPoissonPoint_re_lt_csqrtRe {a : ℝ} (ha : 1 / 2 ≤ a) (q : XiZeroCopy) :
    (xiPoissonPoint q).re < HTGeometry.csqrtRe (xiMassArg a q) := by
  have hR := three_lt_xiPoissonPoint_re q
  have hJ : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
  have hJ2 : (xiPoissonPoint q).im ^ (2 : ℕ) < a ^ (2 : ℕ) := by
    have h0 : (0 : ℝ) ≤ |(xiPoissonPoint q).im| := abs_nonneg _
    nlinarith [sq_abs (xiPoissonPoint q).im, ha]
  have hpos := xiMassArg_re_pos ha q
  have hle : (xiMassArg a q).re ≤ HTGeometry.csqrtRe (xiMassArg a q) ^ (2 : ℕ) :=
    HTGeometry.re_le_sq_csqrtRe hpos
  have hgt : (xiPoissonPoint q).re ^ (2 : ℕ) < (xiMassArg a q).re := by
    rw [xiMassArg_re]; linarith
  nlinarith [HTGeometry.csqrtRe_nonneg (xiMassArg a q), hR]

/-- **The mass-shifted family is admissible.** -/
def xiMassFamily {a : ℝ} (ha : 1 / 2 ≤ a) : SpectralFamily where
  pt := fun q => HTGeometry.csqrt (xiMassArg a q)
  inv := xiZeroCopyLineConjEquiv
  base := a
  base_pos := by linarith
  base_le := by
    intro q
    rw [HTGeometry.csqrt_re]
    have hpos := xiMassArg_re_pos ha q
    have hle : (xiMassArg a q).re ≤ HTGeometry.csqrtRe (xiMassArg a q) ^ (2 : ℕ) :=
      HTGeometry.re_le_sq_csqrtRe hpos
    have hJ2 : 0 ≤ (xiPoissonPoint q).im ^ (2 : ℕ) := sq_nonneg _
    have hR := three_lt_xiPoissonPoint_re q
    have hge : a ^ (2 : ℕ) ≤ (xiMassArg a q).re := by
      rw [xiMassArg_re]
      nlinarith [hR, abs_xiPoissonPoint_im_lt_half q, sq_abs (xiPoissonPoint q).im,
        abs_nonneg (xiPoissonPoint q).im]
    nlinarith [HTGeometry.csqrtRe_nonneg (xiMassArg a q), ha]
  abs_im_lt := by
    intro q
    rw [HTGeometry.csqrt_im]
    have hpos := xiMassArg_re_pos ha q
    have hgt := xiPoissonPoint_re_lt_csqrtRe ha q
    have hR := three_lt_xiPoissonPoint_re q
    have hJ : |(xiPoissonPoint q).im| < 1 / 2 := abs_xiPoissonPoint_im_lt_half q
    rw [HTGeometry.abs_csqrtIm hpos, xiMassArg_im]
    have hden : (0 : ℝ) < 2 * HTGeometry.csqrtRe (xiMassArg a q) := by linarith
    rw [div_lt_iff₀ hden, abs_mul, abs_mul]
    have h2 : |(2 : ℝ)| = 2 := by norm_num
    have hRabs : |(xiPoissonPoint q).re| = (xiPoissonPoint q).re :=
      abs_of_pos (by linarith)
    rw [h2, hRabs]
    nlinarith [hJ, abs_nonneg (xiPoissonPoint q).im, hgt, hR]
  summable_weight := by
    intro σ hσ
    refine Summable.of_nonneg_of_le (fun _ => (Real.exp_pos _).le) (fun q => ?_)
      (summable_xiPoissonWeight hσ)
    rw [xiPoissonWeight, HTGeometry.csqrt_re]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [xiPoissonPoint_re_lt_csqrtRe ha q, hσ]
  shell_finite := by
    intro R
    refine (finite_xiPoissonShell R).subset ?_
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    have := xiPoissonPoint_re_lt_csqrtRe ha q
    rw [HTGeometry.csqrt_re] at hq
    linarith
  conj_stable := by
    intro q
    have harg : xiMassArg a (xiZeroCopyLineConjEquiv q) = (starRingEnd ℂ) (xiMassArg a q) := by
      rw [xiMassArg, xiMassArg, xiPoissonPoint_lineConj, map_add, map_pow, Complex.conj_ofReal]
    rw [harg, HTGeometry.csqrt_conj]

/-- **Boundedness of the mass-shifted trace on one vertical line implies RH.**  The mass-shifted
carrier is the one whose explicit formula converges, so this is the criterion in prime-accessible
form. -/
theorem riemannHypothesis_of_xiMassTrace_line_bound {a σ C : ℝ} (ha : 1 / 2 ≤ a) (hσ : 0 < σ)
    (hline : ∀ x : ℝ, ‖(xiMassFamily ha).traceC ((σ : ℂ) + (x : ℂ) * I)‖ ≤ C) :
    RiemannHypothesis := by
  have hall := (xiMassFamily ha).im_eq_zero_of_line_bound_all hσ hline
  have hpoisson : ∀ q : XiZeroCopy, (xiPoissonPoint q).im = 0 := by
    intro q
    have h := hall q
    have hpos := xiMassArg_re_pos ha q
    have him : (xiMassArg a q).im = 0 := by
      rw [show (xiMassFamily ha).pt q = HTGeometry.csqrt (xiMassArg a q) from rfl,
        HTGeometry.csqrt_im] at h
      exact (HTGeometry.csqrtIm_eq_zero_iff hpos).mp h
    rw [xiMassArg_im] at him
    have hR := three_lt_xiPoissonPoint_re q
    have hne : (xiPoissonPoint q).re ≠ 0 := by linarith
    rcases mul_eq_zero.mp him with h2 | hprod
    · norm_num at h2
    · rcases mul_eq_zero.mp hprod with hre | hjm
      · exact absurd hre hne
      · exact hjm
  refine riemannHypothesis_of_xiSpectralPoint_real fun q => ⟨(xiSpectralPoint q).re, ?_⟩
  have him : (xiSpectralPoint q).im = 0 := by
    have h := hpoisson q
    rw [xiPoissonPoint] at h
    split_ifs at h with hc
    · exact h
    · rw [Complex.neg_im, neg_eq_zero] at h
      exact h
  conv_lhs => rw [← Complex.re_add_im (xiSpectralPoint q)]
  rw [him]
  simp

end

end RHTower
