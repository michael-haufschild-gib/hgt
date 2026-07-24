import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderFiniteTail
import GaloisForLFunctions.HTGeometry.GammaFactorialAllOrderZetaLayer
import GaloisForLFunctions.RHTower.MobiusGammaContactTransgression

/-!
# Möbius-contact Gamma cross-parity zeta-ratio universality

The contact-normalized odd correction converges to a factorial times an even zeta value.  The
adjacent magnified even finite tail converges to the negative of the same factorial.  Dividing
the two channels cancels both the contact scale and factorial residue, leaving the nonzero
scale-free invariant `-2 ζ(2r+2)` at every order.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Möbius-contact presentation of the factorial scale used by adjacent parity channels. -/
def mobiusContactGammaCrossParityScale (n : ℕ) : ℂ :=
  (-2 - mobiusGammaContactPartialCharge n) / 2

theorem mobiusContactGammaCrossParityScale_eq (n : ℕ) :
    mobiusContactGammaCrossParityScale n =
      GaloisForLFunctions.reciprocalGammaFactorialScale n := by
  rw [mobiusContactGammaCrossParityScale, mobiusGammaContactPartialCharge_eq]
  simp only [GaloisForLFunctions.reciprocalGammaFactorialScale]
  ring

/-- Contact-normalized odd zeta correction. -/
def mobiusContactGammaOddCorrection
    (r n : ℕ) (x : ℂ) : ℂ :=
  (GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 1) n x -
      ((2 * r + 1).factorial : ℂ) / x ^ (2 * r + 2)) /
    mobiusContactGammaCrossParityScale n ^ (2 * r + 2)

/-- Magnified adjacent even finite tail. -/
def mobiusContactGammaEvenFiniteTail
    (r n : ℕ) (x : ℂ) : ℂ :=
  (((n + 1 : ℕ) : ℂ) ^ (2 * r + 2)) *
    ((GaloisForLFunctions.gammaFactorialScaledPolygamma (2 * r + 2) n x -
        (-(((2 * r + 2).factorial : ℂ) / x ^ (2 * r + 3)))) /
      mobiusContactGammaCrossParityScale n ^ (2 * r + 3))

/-- Scale-free quotient of adjacent odd and even Gamma correction channels. -/
def mobiusContactGammaCrossParityRatio
    (r n : ℕ) (x : ℂ) : ℂ :=
  mobiusContactGammaOddCorrection r n x /
    mobiusContactGammaEvenFiniteTail r n x

theorem tendsto_mobiusContactGammaOddCorrection
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => mobiusContactGammaOddCorrection r n x) atTop
      (𝓝 (2 * (((2 * r + 1).factorial : ℂ) *
        riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) := by
  simpa only [mobiusContactGammaOddCorrection,
    mobiusContactGammaCrossParityScale_eq] using
    (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_odd_correction
      r hx)

theorem tendsto_mobiusContactGammaEvenFiniteTail
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => mobiusContactGammaEvenFiniteTail r n x) atTop
      (𝓝 (-(((2 * r + 1).factorial : ℂ)))) := by
  simpa only [mobiusContactGammaEvenFiniteTail,
    mobiusContactGammaCrossParityScale_eq] using
    (GaloisForLFunctions.tendsto_gammaFactorialScaledPolygamma_even_finiteTail
      r hx)

/-- Adjacent parity division cancels the factorial residue and leaves an even zeta value. -/
theorem tendsto_mobiusContactGammaCrossParityRatio
    (r : ℕ) {x : ℂ} (hx : x ≠ 0) :
    Tendsto (fun n => mobiusContactGammaCrossParityRatio r n x) atTop
      (𝓝 (-2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ))) := by
  have hfactorial : (((2 * r + 1).factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (2 * r + 1)
  have hevenLimit : (-(((2 * r + 1).factorial : ℂ))) ≠ 0 :=
    neg_ne_zero.mpr hfactorial
  have hdiv :=
    (tendsto_mobiusContactGammaOddCorrection r hx).div
      (tendsto_mobiusContactGammaEvenFiniteTail r hx) hevenLimit
  have hvalue :
      (2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ))) /
        (-(((2 * r + 1).factorial : ℂ))) =
      -2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ) := by
    field_simp [hfactorial]
  rw [hvalue] at hdiv
  simpa only [mobiusContactGammaCrossParityRatio] using hdiv

theorem mobiusContactGammaCrossParityRatio_limit_ne_zero (r : ℕ) :
    -2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ) ≠ 0 := by
  apply mul_ne_zero (by norm_num)
  apply riemannZeta_ne_zero_of_one_lt_re
  rw [Complex.natCast_re]
  exact_mod_cast (show 1 < 2 * r + 2 by omega)

/-- **Möbius-contact Gamma cross-parity zeta-ratio law.** Every adjacent odd/even correction
pair has a nonzero scale-free limiting quotient equal to the corresponding even zeta value. -/
theorem mobiusContactGamma_crossParityZetaRatioUniversality :
    ∀ (r : ℕ) (x : ℂ), x ≠ 0 →
      Tendsto (fun n => mobiusContactGammaOddCorrection r n x) atTop
        (𝓝 (2 * (((2 * r + 1).factorial : ℂ) *
          riemannZeta ((2 * r + 2 : ℕ) : ℂ)))) ∧
      Tendsto (fun n => mobiusContactGammaEvenFiniteTail r n x) atTop
        (𝓝 (-(((2 * r + 1).factorial : ℂ)))) ∧
      Tendsto (fun n => mobiusContactGammaCrossParityRatio r n x) atTop
        (𝓝 (-2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ))) ∧
      -2 * riemannZeta ((2 * r + 2 : ℕ) : ℂ) ≠ 0 := by
  intro r x hx
  exact ⟨tendsto_mobiusContactGammaOddCorrection r hx,
    tendsto_mobiusContactGammaEvenFiniteTail r hx,
    tendsto_mobiusContactGammaCrossParityRatio r hx,
    mobiusContactGammaCrossParityRatio_limit_ne_zero r⟩

end

end GaloisForLFunctions.RHTower
