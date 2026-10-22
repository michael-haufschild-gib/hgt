import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspWignerPairHelmholtzForm
import GaloisForLFunctions.HTGeometry.CoshFourierTransform

/-!
# The spectrum of the theta Wigner pair kernel

The universal pair kernel is a difference of two hyperbolic-secant powers, so its Fourier
transform is an explicit difference of Beta values.  The Gamma recurrence collapses that
difference completely: the two terms share `|Γ((s+2)/2)|²` and the leftover scalar is
`(σ+2)² + ξ² - (6σ+3) = ξ² + (σ-1)²`.

The result is

```text
∫_ℝ G_σ(y) e^(-iξy) dy = π^(-σ) |(s-1) Γ((s+2)/2)|² ,   s = σ + iξ ,
```

a nonnegative quantity, strictly positive off `s = 1`.  The universal pair kernel is therefore a
positive-definite function of the hyperbolic separation for every positive Mellin exponent, with no
arithmetic input: its only degeneracy sits at the abscissa of the zeta pole.
-/

open Real MeasureTheory Set

namespace RHTower

noncomputable section

theorem thetaCuspWignerPairKernel_eq_cosh_combination (σ y : ℝ) :
    thetaCuspWignerPairKernel σ y =
      (2 * Real.pi) ^ (-σ) * Real.Gamma (σ + 2) / 2 *
        ((σ + 2) * (σ + 3) * Real.cosh y ^ (-(σ + 4)) -
          (6 * σ + 3) * Real.cosh y ^ (-(σ + 2))) := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hinv : (1 / Real.cosh y) ^ (σ + 2) = Real.cosh y ^ (-(σ + 2)) := by
    rw [one_div, Real.inv_rpow hc.le, ← Real.rpow_neg hc.le]
  have hC2 : Real.cosh y ^ (-(σ + 4)) =
      Real.cosh y ^ (-(σ + 2)) / Real.cosh y ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast (Real.cosh y) 2, ← Real.rpow_sub hc]
    congr 1
    push_cast
    ring
  rw [thetaCuspWignerPairKernel, thetaCuspWignerRadialQ, hinv, hC2]
  field_simp
  ring

theorem integrable_cosh_rpow_neg_mul_fourier {a : ℝ} (ha : 0 < a) (ξ : ℝ) :
    Integrable (fun y : ℝ =>
      (((Real.cosh y) ^ (-a) : ℝ) : ℂ) *
        Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)) := by
  have hcont : Continuous fun y : ℝ => (Real.cosh y) ^ (-a) :=
    Real.continuous_cosh.rpow_const fun y => Or.inl (Real.cosh_pos y).ne'
  refine Integrable.mono' (HTGeometry.integrable_cosh_rpow_neg ha) ?_ ?_
  · refine (Continuous.aestronglyMeasurable ?_)
    exact (Complex.continuous_ofReal.comp hcont).mul
      (Complex.continuous_exp.comp (by fun_prop))
  · filter_upwards with y
    have hnorm : ‖Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)‖ = 1 := by
      rw [show -((ξ : ℂ) * (y : ℂ)) * Complex.I = ((-(ξ * y) : ℝ) : ℂ) * Complex.I by
        push_cast; ring, Complex.norm_exp_ofReal_mul_I]
    rw [norm_mul, hnorm, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.cosh_pos y) _), mul_one]

/-- Spectral density of the universal theta Wigner pair kernel. -/
def thetaCuspWignerPairSpectrum (σ ξ : ℝ) : ℝ :=
  Real.pi ^ (-σ) *
    Complex.normSq (Complex.Gamma ((((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2)) *
      (ξ ^ 2 + (σ - 1) ^ 2)

theorem integral_thetaCuspWignerPairKernel_mul_fourier {σ : ℝ} (hσ : 0 < σ) (ξ : ℝ) :
    (∫ y : ℝ, ((thetaCuspWignerPairKernel σ y : ℝ) : ℂ) *
        Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)) =
      ((thetaCuspWignerPairSpectrum σ ξ : ℝ) : ℂ) := by
  set c : ℝ := (2 * Real.pi) ^ (-σ) * Real.Gamma (σ + 2) / 2 with hc
  have h4 := integrable_cosh_rpow_neg_mul_fourier (a := σ + 4) (by linarith) ξ
  have h2 := integrable_cosh_rpow_neg_mul_fourier (a := σ + 2) (by linarith) ξ
  have hpt : ∀ y : ℝ, ((thetaCuspWignerPairKernel σ y : ℝ) : ℂ) *
      Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I) =
      (c * ((σ + 2) * (σ + 3)) : ℝ) *
          ((((Real.cosh y) ^ (-(σ + 4)) : ℝ) : ℂ) *
            Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)) -
        (c * (6 * σ + 3) : ℝ) *
          ((((Real.cosh y) ^ (-(σ + 2)) : ℝ) : ℂ) *
            Complex.exp (-((ξ : ℂ) * (y : ℂ)) * Complex.I)) := by
    intro y
    rw [thetaCuspWignerPairKernel_eq_cosh_combination, ← hc]
    push_cast
    ring
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_sub (h4.const_mul _) (h2.const_mul _), integral_const_mul, integral_const_mul,
    HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal (by linarith : (0:ℝ) < σ + 4),
    HTGeometry.integral_cosh_rpow_neg_mul_exp_eq_ofReal (by linarith : (0:ℝ) < σ + 2)]
  set z : ℂ := (((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2 with hzdef
  have hz0 : z ≠ 0 := by
    rw [hzdef]
    simp only [ne_eq, div_eq_zero_iff, OfNat.ofNat_ne_zero, or_false]
    intro h
    have hre : ((((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I)).re = 0 := by rw [h]; simp
    simp [Complex.add_re, Complex.mul_re] at hre
    linarith
  have hshift : (((σ + 4 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2 = z + 1 := by
    rw [hzdef]; push_cast; ring
  have hgam : Complex.Gamma ((((σ + 4 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2) =
      z * Complex.Gamma z := by rw [hshift, Complex.Gamma_add_one z hz0]
  have hnsq : Complex.normSq z = ((σ + 2) ^ 2 + ξ ^ 2) / 4 := by
    rw [hzdef]
    simp only [Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
    ring
  have hN4 : Complex.normSq (Complex.Gamma ((((σ + 4 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2)) =
      ((σ + 2) ^ 2 + ξ ^ 2) / 4 * Complex.normSq (Complex.Gamma z) := by
    rw [hgam, map_mul, hnsq]
  have hG2 : (0 : ℝ) < Real.Gamma (σ + 2) := Real.Gamma_pos_of_pos (by linarith)
  have hG4 : Real.Gamma (σ + 4) = (σ + 3) * ((σ + 2) * Real.Gamma (σ + 2)) := by
    rw [show σ + 4 = (σ + 3) + 1 by ring, Real.Gamma_add_one (by linarith : σ + 3 ≠ 0),
      show σ + 3 = (σ + 2) + 1 by ring, Real.Gamma_add_one (by linarith : σ + 2 ≠ 0)]
  have hp3 : (2 : ℝ) ^ (σ + 4 - 1) = 4 * (2 : ℝ) ^ (σ + 1) := by
    rw [show σ + 4 - 1 = (σ + 1) + 2 by ring, Real.rpow_add two_pos]
    rw [show ((2 : ℝ) ^ (2 : ℝ)) = 4 by
      rw [show ((2 : ℝ) : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num]
    ring
  have hp1 : (2 : ℝ) ^ (σ + 2 - 1) = (2 : ℝ) ^ (σ + 1) := by ring_nf
  have hcval : c * (2 : ℝ) ^ (σ + 1) / Real.Gamma (σ + 2) = Real.pi ^ (-σ) := by
    have h2pi : (2 * Real.pi) ^ (-σ) = (2 : ℝ) ^ (-σ) * Real.pi ^ (-σ) :=
      Real.mul_rpow (by norm_num) Real.pi_pos.le
    have hpow : (2 : ℝ) ^ (-σ) * (2 : ℝ) ^ (σ + 1) = 2 := by
      rw [← Real.rpow_add two_pos, show -σ + (σ + 1) = (1 : ℝ) by ring, Real.rpow_one]
    rw [hc, h2pi]
    field_simp
    nlinarith [hpow, Real.rpow_pos_of_pos Real.pi_pos (-σ), hG2]
  rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, ← Complex.ofReal_sub, Complex.ofReal_inj,
    thetaCuspWignerPairSpectrum, hN4, hG4, hp3, hp1, ← hzdef, ← hcval]
  field_simp
  ring

theorem thetaCuspWignerPairSpectrum_nonneg (σ ξ : ℝ) :
    0 ≤ thetaCuspWignerPairSpectrum σ ξ := by
  unfold thetaCuspWignerPairSpectrum
  have h1 : (0 : ℝ) < Real.pi ^ (-σ) := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : (0 : ℝ) ≤ Complex.normSq
      (Complex.Gamma ((((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2)) := Complex.normSq_nonneg _
  have h3 : (0 : ℝ) ≤ ξ ^ 2 + (σ - 1) ^ 2 := by positivity
  exact mul_nonneg (mul_nonneg h1.le h2) h3

theorem thetaCuspWignerPairSpectrum_pos {σ : ℝ} (hσ : 0 < σ) {ξ : ℝ}
    (h : ξ ≠ 0 ∨ σ ≠ 1) : 0 < thetaCuspWignerPairSpectrum σ ξ := by
  have hz : ∀ m : ℕ, (((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2 ≠ -(m : ℂ) := by
    intro m hm
    have hre := congrArg Complex.re hm
    simp only [Complex.div_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re, Complex.natCast_re,
      Complex.normSq_apply, Complex.re_ofNat, Complex.im_ofNat] at hre
    have : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    norm_num at hre
    linarith
  have hG : Complex.Gamma ((((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2) ≠ 0 :=
    Complex.Gamma_ne_zero hz
  have h1 : (0 : ℝ) < Real.pi ^ (-σ) := Real.rpow_pos_of_pos Real.pi_pos _
  have h2 : (0 : ℝ) < Complex.normSq
      (Complex.Gamma ((((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2)) :=
    Complex.normSq_pos.mpr hG
  have h3 : (0 : ℝ) < ξ ^ 2 + (σ - 1) ^ 2 := by
    rcases h with h | h
    · have : 0 < ξ ^ 2 := by positivity
      nlinarith [sq_nonneg (σ - 1)]
    · have : 0 < (σ - 1) ^ 2 := by positivity
      nlinarith [sq_nonneg ξ]
  unfold thetaCuspWignerPairSpectrum
  exact mul_pos (mul_pos h1 h2) h3

/-- The spectral density is `π^{-σ} |(s-1) Γ((s+2)/2)|²` at `s = σ + iξ`. -/
theorem thetaCuspWignerPairSpectrum_eq_normSq (σ ξ : ℝ) :
    thetaCuspWignerPairSpectrum σ ξ =
      Real.pi ^ (-σ) *
        Complex.normSq (((σ : ℂ) + (ξ : ℂ) * Complex.I - 1) *
          Complex.Gamma ((((σ : ℂ) + (ξ : ℂ) * Complex.I) + 2) / 2)) := by
  have harg : (((σ : ℂ) + (ξ : ℂ) * Complex.I) + 2) / 2 =
      (((σ + 2 : ℝ) : ℂ) + (ξ : ℂ) * Complex.I) / 2 := by push_cast; ring
  have hsq : Complex.normSq ((σ : ℂ) + (ξ : ℂ) * Complex.I - 1) = ξ ^ 2 + (σ - 1) ^ 2 := by
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im]
    ring
  rw [thetaCuspWignerPairSpectrum, harg, map_mul, hsq]
  ring

end

end RHTower
