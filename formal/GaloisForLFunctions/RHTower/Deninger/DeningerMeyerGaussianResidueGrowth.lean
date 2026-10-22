import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerXiGaussianGammaResidue
import GaloisForLFunctions.HTGeometry.GammaVerticalModulus

/-!
# Growth of the Gaussian Green residue along the critical strip

The completed singular Meyer lift has one simple pole at each strip point, with residue

`R(ρ) = -2π A(ρ) / (χ_c(ρ) (ρ - c))`,  `A(s) = s(s-1)/2 · Γ_ℝ(s)`,
`χ_c(s) = exp((s-c)²/(4π))`.

At the Gaussian centre `c = 2` the inverse Gaussian character grows like `exp(γ²/(4π))` in the
ordinate, while the Archimedean factor decays only like `exp(-π|γ|/2)`.  The Gaussian therefore
wins, and the residue family is unbounded along the strip.

The Archimedean lower bound uses no Stirling expansion: Euler reflection turns it into an upper
bound for `Γ` on the reflected line, which is the modulus bound on a vertical line together with
continuity of the real `Γ` on a compact interval.

* `norm_sin_le_exp_abs_im` : the elementary bound `‖sin w‖ ≤ exp |Im w|`.
* `pi_le_norm_Gamma_half_mul` : the uniform strip lower bound for `Γ(ρ/2)`.
* `norm_gaussianMellinCharacter` : the exact modulus of the Gaussian character.
-/

open Complex Filter Topology Set
open scoped Real

namespace RHTower
namespace DeningerMeyerGaussianGreen

noncomputable section

/-- **The elementary strip bound for the sine.**  Both exponentials in the sine have modulus at
most `exp |Im w|`. -/
theorem norm_sin_le_exp_abs_im (w : ℂ) : ‖Complex.sin w‖ ≤ Real.exp |w.im| := by
  have hsin : Complex.sin w = (Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)) *
      Complex.I / 2 := rfl
  have h1 : ‖Complex.exp (-w * Complex.I)‖ = Real.exp w.im := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have h2 : ‖Complex.exp (w * Complex.I)‖ = Real.exp (-w.im) := by
    rw [Complex.norm_exp]
    congr 1
    simp
  have hle1 : Real.exp w.im ≤ Real.exp |w.im| := Real.exp_le_exp.2 (le_abs_self _)
  have hle2 : Real.exp (-w.im) ≤ Real.exp |w.im| := Real.exp_le_exp.2 (neg_le_abs _)
  rw [hsin, norm_div, norm_mul, Complex.norm_I, mul_one, Complex.norm_ofNat]
  have hsub : ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ ≤
      Real.exp |w.im| + Real.exp |w.im| := by
    refine (norm_sub_le _ _).trans ?_
    rw [h1, h2]
    exact add_le_add hle1 hle2
  calc ‖Complex.exp (-w * Complex.I) - Complex.exp (w * Complex.I)‖ / 2
      ≤ (Real.exp |w.im| + Real.exp |w.im|) / 2 := by
        exact div_le_div_of_nonneg_right hsub (by norm_num)
    _ = Real.exp |w.im| := by ring

/-- **A uniform bound for the real `Γ` on the reflected line.**  The real `Γ` is continuous on the
compact interval `[1/2, 1]`, so it is bounded there. -/
theorem exists_gamma_bound_Icc :
    ∃ M : ℝ, 0 < M ∧ ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, Real.Gamma x ≤ M := by
  have hcont : ContinuousOn Real.Gamma (Set.Icc (1 / 2 : ℝ) 1) := by
    intro x hx
    refine ContinuousAt.continuousWithinAt ?_
    refine (Real.differentiableAt_Gamma ?_).continuousAt
    intro m hm
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le (by norm_num) hx.1
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    rw [hm] at hxpos
    linarith
  obtain ⟨M₀, hM₀⟩ := (isCompact_Icc (a := (1 / 2 : ℝ)) (b := 1)).exists_bound_of_continuousOn hcont
  refine ⟨M₀ + 1, ?_, fun x hx => ?_⟩
  · have hx0 : (1 / 2 : ℝ) ∈ Set.Icc (1 / 2 : ℝ) 1 := by constructor <;> norm_num
    have h1 := hM₀ _ hx0
    have h2 : (0 : ℝ) < Real.Gamma (1 / 2) := Real.Gamma_pos_of_pos (by norm_num)
    have h3 : Real.Gamma (1 / 2) ≤ M₀ := (le_abs_self _).trans h1
    linarith
  · exact ((le_abs_self _).trans (hM₀ x hx)).trans (by linarith)

theorem half_re {ρ : ℂ} : (ρ / 2).re = ρ.re / 2 := by
  simp

theorem half_im {ρ : ℂ} : (ρ / 2).im = ρ.im / 2 := by
  simp

/-- **The uniform strip lower bound for the Archimedean `Γ`.**  Euler reflection converts the lower
bound into the modulus bound for `Γ` on the reflected vertical line, whose real part lies in the
compact interval `[1/2, 1]`, together with the elementary bound for the sine. -/
theorem pi_le_norm_Gamma_half_mul {M : ℝ}
    (hM : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, Real.Gamma x ≤ M) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    Real.pi ≤ ‖Complex.Gamma (ρ / 2)‖ * M * Real.exp (Real.pi * |ρ.im| / 2) := by
  have hzre : (ρ / 2).re = ρ.re / 2 := half_re
  have hzim : (ρ / 2).im = ρ.im / 2 := half_im
  have hone : (1 - ρ / 2).re = 1 - ρ.re / 2 := by
    rw [Complex.sub_re, Complex.one_re, hzre]
  have honepos : 0 < (1 - ρ / 2).re := by rw [hone]; linarith
  have hmem : (1 - ρ / 2).re ∈ Set.Icc (1 / 2 : ℝ) 1 := by
    rw [hone]
    constructor <;> linarith
  -- reflection
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (ρ / 2)
  have hsinnorm : ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ ≤ Real.exp (Real.pi * |ρ.im| / 2) := by
    refine (norm_sin_le_exp_abs_im _).trans ?_
    refine Real.exp_le_exp.2 (le_of_eq ?_)
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, hzre, hzim, zero_mul, add_zero,
      abs_mul, abs_of_pos Real.pi_pos, abs_div]
    rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
    ring
  have hgamma1 : ‖Complex.Gamma (1 - ρ / 2)‖ ≤ M :=
    (GaloisForLFunctions.HTGeometry.norm_Gamma_le_Gamma_re honepos).trans (hM _ hmem)
  have hpi : ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ =
      ‖Complex.Gamma (ρ / 2)‖ * ‖Complex.Gamma (1 - ρ / 2)‖ := by
    rw [← norm_mul, hrefl]
  have hsinne : Complex.sin ((Real.pi : ℂ) * (ρ / 2)) ≠ 0 := by
    intro hz
    rw [hz, div_zero, norm_zero] at hpi
    have hg : Complex.Gamma (ρ / 2) * Complex.Gamma (1 - ρ / 2) = 0 := by
      rw [hrefl, hz, div_zero]
    rcases mul_eq_zero.1 hg with hg1 | hg2
    · exact (Complex.Gamma_ne_zero_of_re_pos (by rw [hzre]; linarith)) hg1
    · exact (Complex.Gamma_ne_zero_of_re_pos honepos) hg2
  have hnormpi : ‖(Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ =
      Real.pi / ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  have hsinpos : 0 < ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := norm_pos_iff.2 hsinne
  have hkey : ‖Complex.Gamma (ρ / 2)‖ * ‖Complex.Gamma (1 - ρ / 2)‖ *
      ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ = Real.pi := by
    rw [← hpi, hnormpi, div_mul_cancel₀ _ (ne_of_gt hsinpos)]
  have hg0 : 0 ≤ ‖Complex.Gamma (ρ / 2)‖ := norm_nonneg _
  calc Real.pi = ‖Complex.Gamma (ρ / 2)‖ * ‖Complex.Gamma (1 - ρ / 2)‖ *
        ‖Complex.sin ((Real.pi : ℂ) * (ρ / 2))‖ := hkey.symm
    _ ≤ ‖Complex.Gamma (ρ / 2)‖ * M * Real.exp (Real.pi * |ρ.im| / 2) := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left hgamma1 hg0) hsinnorm (norm_nonneg _) ?_
        exact mul_nonneg hg0 (le_trans (norm_nonneg _) hgamma1)

/-- **The exact modulus of the Gaussian character.** -/
theorem norm_gaussianMellinCharacter (c ρ : ℂ) :
    ‖gaussianMellinCharacter c ρ‖ =
      Real.exp (((ρ - c).re ^ 2 - (ρ - c).im ^ 2) / (4 * Real.pi)) := by
  rw [gaussianMellinCharacter, Complex.norm_exp]
  congr 1
  have hsq : ((ρ - c) ^ 2).re = (ρ - c).re ^ 2 - (ρ - c).im ^ 2 := by
    rw [pow_two, Complex.mul_re]
    ring
  have hfour : (4 * (Real.pi : ℂ)) = ((4 * Real.pi : ℝ) : ℂ) := by push_cast; ring
  rw [hfour, Complex.div_ofReal_re, hsq]

/-- **Lower bound for the Archimedean factor on the strip.**  The polynomial prefactor contributes
`|γ|²`, the power of `π` at least `π⁻¹`, and the `Γ` value the uniform strip bound. -/
theorem norm_archFactor_lower {M : ℝ} (hMpos : 0 < M)
    (hM : ∀ x ∈ Set.Icc (1 / 2 : ℝ) 1, Real.Gamma x ≤ M) {ρ : ℂ}
    (h0 : 0 < ρ.re) (h1 : ρ.re < 1) :
    ρ.im ^ 2 / (2 * M * Real.exp (Real.pi * |ρ.im| / 2)) ≤ ‖archFactor ρ‖ := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hexp : (0 : ℝ) < Real.exp (Real.pi * |ρ.im| / 2) := Real.exp_pos _
  -- the Gamma value
  have hGamma : Real.pi / (M * Real.exp (Real.pi * |ρ.im| / 2)) ≤ ‖Complex.Gamma (ρ / 2)‖ := by
    have hkey := pi_le_norm_Gamma_half_mul hM h0 h1
    rw [div_le_iff₀ (by positivity)]
    calc Real.pi ≤ ‖Complex.Gamma (ρ / 2)‖ * M * Real.exp (Real.pi * |ρ.im| / 2) := hkey
      _ = ‖Complex.Gamma (ρ / 2)‖ * (M * Real.exp (Real.pi * |ρ.im| / 2)) := by ring
  -- the power of π
  have hcpow : ‖(Real.pi : ℂ) ^ (-ρ / 2)‖ = Real.pi ^ (-ρ.re / 2) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hpi]
    congr 1
    simp
  have hpowge : Real.pi ⁻¹ ≤ Real.pi ^ (-ρ.re / 2) := by
    rw [← Real.rpow_neg_one Real.pi]
    refine Real.rpow_le_rpow_of_exponent_le (le_of_lt (lt_trans (by norm_num) Real.pi_gt_three)) ?_
    linarith
  -- the polynomial prefactor
  have hrho : |ρ.im| ≤ ‖ρ‖ := Complex.abs_im_le_norm ρ
  have hrho1 : |ρ.im| ≤ ‖ρ - 1‖ := by
    have h : (ρ - 1).im = ρ.im := by simp
    have := Complex.abs_im_le_norm (ρ - 1)
    rwa [h] at this
  have habs : (0 : ℝ) ≤ |ρ.im| := abs_nonneg _
  -- assemble
  have hnorm : ‖archFactor ρ‖ =
      ‖ρ‖ * ‖ρ - 1‖ / 2 * (Real.pi ^ (-ρ.re / 2) * ‖Complex.Gamma (ρ / 2)‖) := by
    rw [archFactor, Complex.Gammaℝ_def, norm_mul, norm_div, norm_mul, norm_mul,
      Complex.norm_ofNat, hcpow]
  rw [hnorm, div_le_iff₀ (by positivity)]
  have hstep1 : ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ - 1‖ := by
    have hmm : |ρ.im| * |ρ.im| ≤ ‖ρ‖ * ‖ρ - 1‖ :=
      mul_le_mul hrho hrho1 habs (norm_nonneg _)
    calc ρ.im ^ 2 = |ρ.im| ^ 2 := (sq_abs _).symm
      _ = |ρ.im| * |ρ.im| := pow_two _
      _ ≤ ‖ρ‖ * ‖ρ - 1‖ := hmm
  have hstep2 : Real.pi ⁻¹ * (Real.pi / (M * Real.exp (Real.pi * |ρ.im| / 2))) ≤
      Real.pi ^ (-ρ.re / 2) * ‖Complex.Gamma (ρ / 2)‖ :=
    mul_le_mul hpowge hGamma (by positivity) (le_trans (by positivity) hpowge)
  have hval : Real.pi ⁻¹ * (Real.pi / (M * Real.exp (Real.pi * |ρ.im| / 2))) =
      (M * Real.exp (Real.pi * |ρ.im| / 2))⁻¹ := by
    field_simp
  rw [hval] at hstep2
  have hMe : (0 : ℝ) < M * Real.exp (Real.pi * |ρ.im| / 2) := by positivity
  have hkey : ρ.im ^ 2 * ((M * Real.exp (Real.pi * |ρ.im| / 2))⁻¹ *
      (M * Real.exp (Real.pi * |ρ.im| / 2))) ≤
      ‖ρ‖ * ‖ρ - 1‖ * ((Real.pi ^ (-ρ.re / 2) * ‖Complex.Gamma (ρ / 2)‖) *
        (M * Real.exp (Real.pi * |ρ.im| / 2))) := by
    refine mul_le_mul hstep1 ?_ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hstep2 (le_of_lt hMe)
  rw [inv_mul_cancel₀ (ne_of_gt hMe), mul_one] at hkey
  calc ρ.im ^ 2 ≤ ‖ρ‖ * ‖ρ - 1‖ * ((Real.pi ^ (-ρ.re / 2) * ‖Complex.Gamma (ρ / 2)‖) *
        (M * Real.exp (Real.pi * |ρ.im| / 2))) := hkey
    _ = ‖ρ‖ * ‖ρ - 1‖ / 2 * (Real.pi ^ (-ρ.re / 2) * ‖Complex.Gamma (ρ / 2)‖) *
        (2 * M * Real.exp (Real.pi * |ρ.im| / 2)) := by ring

/-- **Gaussian-residue growth along the strip.**  At the Gaussian centre `2` the residue of the
completed singular Meyer lift grows at least like `exp(γ²/(32π))` in the ordinate: the inverse
Gaussian character grows like `exp(γ²/(4π))` while the Archimedean factor decays only like
`exp(-π|γ|/2)`, so the Gaussian wins by a definite margin. -/
theorem exists_residue_growth :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, 0 < T₀ ∧ ∀ ρ : ℂ, 0 < ρ.re → ρ.re < 1 → T₀ ≤ |ρ.im| →
      C * Real.exp (ρ.im ^ 2 / (32 * Real.pi)) ≤
        ‖-(2 * (Real.pi : ℂ) * archFactor ρ /
          (gaussianMellinCharacter 2 ρ * (ρ - 2)))‖ := by
  obtain ⟨M, hMpos, hM⟩ := exists_gamma_bound_Icc
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hpi3 : (3 : ℝ) < Real.pi := Real.pi_gt_three
  refine ⟨Real.pi / M * Real.exp (-(1 / Real.pi)), by positivity,
    8 * Real.pi ^ 2, by positivity, ?_⟩
  intro ρ h0 h1 hT
  have hg2 : (2 : ℝ) ≤ |ρ.im| := by nlinarith
  have hgpos : (0 : ℝ) < |ρ.im| := by linarith
  have hre2 : ((ρ - 2 : ℂ)).re = ρ.re - 2 := by simp
  have him2 : ((ρ - 2 : ℂ)).im = ρ.im := by simp
  have hchi : ‖gaussianMellinCharacter 2 ρ‖ =
      Real.exp (((ρ.re - 2) ^ 2 - ρ.im ^ 2) / (4 * Real.pi)) := by
    rw [norm_gaussianMellinCharacter, hre2, him2]
  have hrho2ne : ρ - 2 ≠ 0 := by
    intro h
    have hzero : ρ.re - 2 = 0 := by rw [← hre2, h]; simp
    linarith
  have hrho2pos : (0 : ℝ) < ‖ρ - 2‖ := norm_pos_iff.2 hrho2ne
  have hrho2le : ‖ρ - 2‖ ≤ 2 + |ρ.im| := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    rw [hre2, him2]
    have habs : |ρ.re - 2| ≤ 2 := by rw [abs_of_nonpos (by linarith)]; linarith
    linarith
  have hR : ‖-(2 * (Real.pi : ℂ) * archFactor ρ /
        (gaussianMellinCharacter 2 ρ * (ρ - 2)))‖ =
      2 * Real.pi * ‖archFactor ρ‖ / (‖gaussianMellinCharacter 2 ρ‖ * ‖ρ - 2‖) := by
    rw [norm_neg, norm_div, norm_mul, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos hpi]
  have hchipos : (0 : ℝ) < ‖gaussianMellinCharacter 2 ρ‖ := by
    rw [hchi]
    exact Real.exp_pos _
  rw [hR, le_div_iff₀ (mul_pos hchipos hrho2pos)]
  have harch := norm_archFactor_lower hMpos hM h0 h1
  have hb2 : (ρ.re - 2) ^ 2 ≤ 4 := by nlinarith
  have hexpo : -(1 / Real.pi) + ρ.im ^ 2 / (32 * Real.pi) +
      ((ρ.re - 2) ^ 2 - ρ.im ^ 2) / (4 * Real.pi) ≤ -(7 * ρ.im ^ 2 / (32 * Real.pi)) := by
    rw [← sub_nonneg]
    have hkey : -(7 * ρ.im ^ 2 / (32 * Real.pi)) -
        (-(1 / Real.pi) + ρ.im ^ 2 / (32 * Real.pi) +
          ((ρ.re - 2) ^ 2 - ρ.im ^ 2) / (4 * Real.pi))
        = (32 - 8 * (ρ.re - 2) ^ 2) / (32 * Real.pi) := by
      field_simp
      ring
    rw [hkey]
    apply div_nonneg _ (by positivity)
    nlinarith
  have hpoly : 2 + |ρ.im| ≤ ρ.im ^ 2 := by
    have h := sq_abs ρ.im
    nlinarith [hg2, hgpos]
  have hexpcmp : Real.exp (-(7 * ρ.im ^ 2 / (32 * Real.pi))) ≤
      Real.exp (-(Real.pi * |ρ.im| / 2)) := by
    refine Real.exp_le_exp.2 ?_
    rw [neg_le_neg_iff, div_le_div_iff₀ (by norm_num) (by positivity)]
    have h := sq_abs ρ.im
    nlinarith [hpi, hgpos, hT]
  calc Real.pi / M * Real.exp (-(1 / Real.pi)) * Real.exp (ρ.im ^ 2 / (32 * Real.pi)) *
        (‖gaussianMellinCharacter 2 ρ‖ * ‖ρ - 2‖)
      ≤ Real.pi / M * Real.exp (-(1 / Real.pi)) * Real.exp (ρ.im ^ 2 / (32 * Real.pi)) *
        (‖gaussianMellinCharacter 2 ρ‖ * (2 + |ρ.im|)) := by
        gcongr
    _ = Real.pi / M *
        Real.exp (-(1 / Real.pi) + ρ.im ^ 2 / (32 * Real.pi) +
          ((ρ.re - 2) ^ 2 - ρ.im ^ 2) / (4 * Real.pi)) * (2 + |ρ.im|) := by
        rw [hchi, Real.exp_add, Real.exp_add]
        ring
    _ ≤ Real.pi / M * Real.exp (-(7 * ρ.im ^ 2 / (32 * Real.pi))) * (2 + |ρ.im|) := by
        gcongr
    _ ≤ Real.pi / M * (Real.exp (-(Real.pi * |ρ.im| / 2)) * ρ.im ^ 2) := by
        rw [mul_assoc]
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        exact mul_le_mul hexpcmp hpoly (by positivity) (le_of_lt (Real.exp_pos _))
    _ = 2 * Real.pi * (ρ.im ^ 2 / (2 * M * Real.exp (Real.pi * |ρ.im| / 2))) := by
        rw [Real.exp_neg]
        field_simp
    _ ≤ 2 * Real.pi * ‖archFactor ρ‖ := by
        exact mul_le_mul_of_nonneg_left harch (by positivity)

end

end DeningerMeyerGaussianGreen
end RHTower
