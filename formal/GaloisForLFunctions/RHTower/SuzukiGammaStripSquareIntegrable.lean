import GaloisForLFunctions.RHTower.SuzukiGammaStripGluing
import GaloisForLFunctions.RHTower.SuzukiGammaStripCarrierIntegrability
import GaloisForLFunctions.HTGeometry.ExpSelfAdjointNormBound

/-!
# Square integrability of the glued strip solution on every interior line

On the line `z = x + iσ` with `0 < σ < 1` the holomorphic strip solution has modulus

`‖H(x+iσ)‖ = |z|^{-1/2} e^{-γσ} |Γ(1+iz)/Γ(1-iz)|^{1/2} ‖e^{-izT/2}c‖`,

and for self-adjoint `T` only the real part of the exponent contributes to the operator factor, so
that factor is bounded by `e^{σ‖T‖/2}‖c‖` uniformly in `x`.  The remaining density is exactly the
strip carrier whose integrability is the vertical Gamma-ratio theorem.  Hence a glued homogeneous
Gamma seam lies in `L²` on every interior line of the strip.
-/

open Set Complex MeasureTheory

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]
  [Nontrivial X]

/-- The shifted line lies in the unit strip. -/
theorem shift_mem_imStrip {σ : ℝ} (hσ0 : 0 < σ) (hσ1 : σ < 1) (x : ℝ) :
    ((x : ℂ) + (σ : ℂ) * Complex.I) ∈ imStrip (-1) 1 := by
  constructor <;> simp <;> linarith

/-- On the shifted line the Gamma ratio has the modulus of the corpus strip density. -/
theorem norm_gammaRatio_shift (σ x : ℝ) :
    ‖gammaRatio ((x : ℂ) + (σ : ℂ) * Complex.I)‖
      = ‖Complex.Gamma (((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ /
        ‖Complex.Gamma (((1 + σ : ℝ) : ℂ) + (x : ℂ) * Complex.I)‖ := by
  have hnum : (1 : ℂ) + Complex.I * ((x : ℂ) + (σ : ℂ) * Complex.I)
      = ((1 - σ : ℝ) : ℂ) + (x : ℂ) * Complex.I := by
    refine Complex.ext ?_ ?_ <;> simp <;> ring
  have hden : (1 : ℂ) - Complex.I * ((x : ℂ) + (σ : ℂ) * Complex.I)
      = (starRingEnd ℂ) (((1 + σ : ℝ) : ℂ) + (x : ℂ) * Complex.I) := by
    refine Complex.ext ?_ ?_ <;> simp <;> ring
  rw [gammaRatio, hnum, hden, Complex.Gamma_conj, norm_div]
  congr 1
  simp

/-- The pointwise modulus bound on the shifted line. -/
theorem norm_sq_stripSolution_shift_le {E : ℂ → ℂ} {T : X →L[ℂ] X} (hT : IsSelfAdjoint T)
    (hE : ∀ z ∈ imStrip (-1) 1, E z ^ 2 = gammaRatio z) (c : X) {σ : ℝ} (hσ0 : 0 < σ)
    (hσ1 : σ < 1) (x : ℝ) :
    ‖stripSolution E T c ((x : ℂ) + (σ : ℂ) * Complex.I)‖ ^ 2
      ≤ (Real.exp (-(2 * Real.eulerMascheroniConstant * σ)) * Real.exp (σ * ‖T‖) * ‖c‖ ^ 2)
        * suzukiGammaStripNormSq σ x := by
  set z : ℂ := (x : ℂ) + (σ : ℂ) * Complex.I with hz
  have hzim : z.im = σ := by rw [hz]; simp
  have hzre : z.re = x := by rw [hz]; simp
  have hzne : z ≠ 0 := by
    intro hcon
    rw [hcon] at hzim
    simp at hzim
    linarith
  have hznorm : (0 : ℝ) < ‖z‖ := norm_pos_iff.mpr hzne
  -- the three factors
  have hpow : ‖z ^ (-(1 : ℂ) / 2)‖ = ‖z‖ ^ (-(1 : ℝ) / 2) := by
    rw [Complex.norm_cpow_of_ne_zero hzne]
    norm_num
  have hphase : ‖Complex.exp (Complex.I * (Real.eulerMascheroniConstant : ℂ) * z)‖
      = Real.exp (-(Real.eulerMascheroniConstant * σ)) := by
    rw [Complex.norm_exp]
    congr 1
    simp [hzim, hzre]
  have hEsq : ‖E z‖ ^ 2 = ‖gammaRatio z‖ := by
    rw [← norm_pow, hE z (shift_mem_imStrip hσ0 hσ1 x)]
  have hop : ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T) c‖ ≤ Real.exp (σ / 2 * ‖T‖) * ‖c‖ := by
    refine le_trans (ContinuousLinearMap.le_opNorm _ c) ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg c)
    have hre : (-(Complex.I / 2) * z).re = σ / 2 := by
      simp [hz]
      ring
    have := norm_exp_smul_le hT (-(Complex.I / 2) * z)
    rw [hre, abs_of_pos (by linarith : (0 : ℝ) < σ / 2)] at this
    exact this
  -- assemble
  have hval : ‖stripSolution E T c z‖
      = ‖z‖ ^ (-(1 : ℝ) / 2) * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * ‖NormedSpace.exp ((-(Complex.I / 2) * z) • T) c‖ := by
    rw [stripSolution, norm_smul, stripTransport_apply, norm_smul, norm_mul, hpow, hphase]
    ring
  have hnn1 : (0 : ℝ) ≤ ‖z‖ ^ (-(1 : ℝ) / 2) := Real.rpow_nonneg hznorm.le _
  have hnn2 : (0 : ℝ) ≤ Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖ := by positivity
  have hbound : ‖stripSolution E T c z‖
      ≤ ‖z‖ ^ (-(1 : ℝ) / 2) * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * (Real.exp (σ / 2 * ‖T‖) * ‖c‖) := by
    rw [hval]
    exact mul_le_mul_of_nonneg_left hop (by positivity)
  have hsq := mul_self_le_mul_self (norm_nonneg _) hbound
  rw [← sq, ← sq] at hsq
  refine le_trans hsq ?_
  have hexpand : (‖z‖ ^ (-(1 : ℝ) / 2)
        * (Real.exp (-(Real.eulerMascheroniConstant * σ)) * ‖E z‖)
        * (Real.exp (σ / 2 * ‖T‖) * ‖c‖)) ^ 2
      = ((‖z‖ ^ (-(1 : ℝ) / 2)) ^ 2 * ‖E z‖ ^ 2)
        * (Real.exp (-(Real.eulerMascheroniConstant * σ)) ^ 2
          * Real.exp (σ / 2 * ‖T‖) ^ 2 * ‖c‖ ^ 2) := by
    ring
  rw [hexpand, hEsq]
  have hpow2 : (‖z‖ ^ (-(1 : ℝ) / 2)) ^ 2 = (‖z‖)⁻¹ := by
    rw [← Real.rpow_natCast (‖z‖ ^ (-(1 : ℝ) / 2)) 2, ← Real.rpow_mul hznorm.le]
    norm_num
    rw [Real.rpow_neg_one]
  have hexp1 : Real.exp (-(Real.eulerMascheroniConstant * σ)) ^ 2
      = Real.exp (-(2 * Real.eulerMascheroniConstant * σ)) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  have hexp2 : Real.exp (σ / 2 * ‖T‖) ^ 2 = Real.exp (σ * ‖T‖) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow2, hexp1, hexp2, suzukiGammaStripNormSq, norm_gammaRatio_shift]
  rw [← hz]
  ring_nf
  rfl

end

end GaloisForLFunctions.RHTower
