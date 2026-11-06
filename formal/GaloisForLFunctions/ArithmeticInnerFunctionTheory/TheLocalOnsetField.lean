import GaloisForLFunctions.ArithmeticInnerFunctionTheory.FarBubblesDoNotDecouple
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion

/-!
# The local onset field

Fix a profile `ψ`. The local onset field is Weil's form on the tests of aperture `a` spectrally localized near a height `X`:

`Ω_ψ(a, X) = Re W(f, f)`, `f(u) = ψ(u/a) e^{iXu}`.

Taking `a = λ · ½ log X` gives the aperture scale of the field. The transform is a rescaled translate of the transform of the profile (`paperFT_onsetTest`), so the field is a sum over the zeros seen at scale `1/a` around the height `−X` (`hasSum_onsetEnergy`):

`Ω_ψ(a, X) = Σ_ρ m_ρ a² ψ̂(a(γ_ρ + X)) conj ψ̂(a(γ̄_ρ + X))`.

* An on-line zero contributes `m_ρ a² |ψ̂(a(γ_ρ + X))|² ≥ 0` (`onsetSummand_of_onLine`), so all sign is in the off-line pairs.
* RH is the nonnegativity of the field at every profile, aperture and height (`riemannHypothesis_iff_onsetEnergy_nonneg`).

A sign for a fixed `λ` on density-one heights is a statement below RH, and it is not settled here.
-/

open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticInnerFunctionTheory

open ArithmeticCastelnuovoSeveri Zeta23 SpacingScaleHarmonicAnalysis GrowingWindowsOfSpecZ
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

/-- The test of aperture `a` at height `X` with profile `ψ`. -/
def onsetTest (ψ : ℝ → ℂ) (a X u : ℝ) : ℂ := ψ (u / a) * cexp (((X * u : ℝ) : ℂ) * I)

/-- The local onset field of the profile `ψ`. -/
def onsetEnergy (ψ : ℝ → ℂ) (a X : ℝ) : ℝ :=
  (zetaZeroConfig.W (onsetTest ψ a X) (onsetTest ψ a X)).re

variable {ψ : ℝ → ℂ} {a X : ℝ}

/-- The transform of the test is a rescaled translate of the transform of the profile. -/
theorem paperFT_onsetTest (ha : 0 < a) (z : ℂ) :
    paperFT (onsetTest ψ a X) z = a * paperFT ψ (a * (z + X)) := by
  have hac : (a : ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have h := Measure.integral_comp_div (fun v : ℝ => ψ v * cexp (I * (a * (z + X)) * v)) a
  rw [abs_of_pos ha, Complex.real_smul] at h
  rw [paperFT, paperFT, ← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [onsetTest]
  rw [mul_assoc, ← Complex.exp_add]
  congr 2
  push_cast
  field_simp
  ring

theorem contDiff_onsetTest (hψ : ContDiff ℝ 2 ψ) (a X : ℝ) : ContDiff ℝ 2 (onsetTest ψ a X) := by
  unfold onsetTest
  refine (hψ.comp (contDiff_id.div_const a)).mul ?_
  refine Complex.contDiff_exp.comp ?_
  refine ContDiff.mul ?_ contDiff_const
  exact Complex.ofRealCLM.contDiff.comp (contDiff_const.mul contDiff_id)

theorem hasCompactSupport_onsetTest (ha : 0 < a) (hψ : HasCompactSupport ψ) (X : ℝ) :
    HasCompactSupport (onsetTest ψ a X) := by
  have h : HasCompactSupport fun u : ℝ => ψ (u / a) := by
    have e : (fun u : ℝ => ψ (u / a)) = ψ ∘ (Homeomorph.mulRight₀ a⁻¹ (inv_ne_zero ha.ne')) := by
      funext u
      simp [div_eq_mul_inv]
    rw [e]
    exact hψ.comp_homeomorph _
  exact h.mul_right

/-- The summand of the field at one zero. -/
theorem onsetSummand (ha : 0 < a) (ψ : ℝ → ℂ) (X : ℝ) (Z : ZeroConfig) (ρ : ℂ) :
    Z.Wsummand (onsetTest ψ a X) (onsetTest ψ a X) ρ =
      (Z.mult ρ : ℂ) * (a ^ 2 : ℝ) * (paperFT ψ (a * (gammaOf ρ + X)) *
        conj (paperFT ψ (a * (conj (gammaOf ρ) + X)))) := by
  rw [ZeroConfig.Wsummand, paperFT_onsetTest ha, paperFT_onsetTest ha, map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-- **An on-line zero contributes a nonnegative term.** -/
theorem onsetSummand_of_onLine (ha : 0 < a) (ψ : ℝ → ℂ) (X : ℝ) (Z : ZeroConfig) {ρ : ℂ}
    (hρ : ρ.re = 1 / 2) :
    Z.Wsummand (onsetTest ψ a X) (onsetTest ψ a X) ρ =
      (((Z.mult ρ : ℝ) * a ^ 2 * ‖paperFT ψ (a * ((ρ.im : ℂ) + X))‖ ^ 2 : ℝ) : ℂ) := by
  rw [onsetSummand ha, gammaOf_of_re_eq_half hρ, Complex.conj_ofReal, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The field is a sum over the zeros seen at scale `1/a`.** -/
theorem hasSum_onsetEnergy (ha : 0 < a) (hψ : ContDiff ℝ 2 ψ) (hψc : HasCompactSupport ψ) (X : ℝ) :
    HasSum (fun ρ : zetaZeroConfig.carrier => (zetaZeroConfig.Wsummand (onsetTest ψ a X) (onsetTest ψ a X) ρ).re)
      (onsetEnergy ψ a X) := by
  have hs := summable_Wsummand zetaZeroConfig GaloisForLFunctions.SquareRootThreshold.temperedConfig_zetaZeroConfig
    (contDiff_onsetTest hψ a X) (hasCompactSupport_onsetTest ha hψc X)
    (contDiff_onsetTest hψ a X) (hasCompactSupport_onsetTest ha hψc X)
  have h := (hs.hasSum.mapL Complex.reCLM)
  exact h

/-- **RH is the nonnegativity of the local onset field.** -/
theorem riemannHypothesis_iff_onsetEnergy_nonneg :
    RiemannHypothesis ↔ ∀ ψ : ℝ → ℂ, ContDiff ℝ 2 ψ → HasCompactSupport ψ → ∀ a : ℝ, 0 < a → ∀ X : ℝ,
      0 ≤ onsetEnergy ψ a X := by
  constructor
  · intro hRH ψ hψ hψc a ha X
    rw [onsetEnergy, _root_.RHTower.WeilConditional.re_W_eq_tsum_zeroTerm hRH (contDiff_onsetTest hψ a X)
      (hasCompactSupport_onsetTest ha hψc X)]
    exact tsum_nonneg fun ρ => _root_.RHTower.WeilConditional.zeroTerm_nonneg _ ρ
  · intro h
    refine ArithmeticHodgeTheoryOfDegenerations.riemannHypothesis_iff_weilQuad_nonneg.mpr fun g hg hgc => ?_
    have h1 := h (cx g) (cx_contDiff hg) (cx_hasCompactSupport hgc) 1 one_pos 0
    have e : onsetTest (cx g) 1 0 = fun u => (g u : ℂ) := by
      funext u
      simp [onsetTest, cx]
    rw [onsetEnergy, e] at h1
    rw [LogCells.weilQuad_eq_zetaW hg hgc]
    exact h1

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
