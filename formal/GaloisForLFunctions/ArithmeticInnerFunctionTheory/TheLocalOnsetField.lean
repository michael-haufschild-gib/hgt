import GaloisForLFunctions.ArithmeticInnerFunctionTheory.FarBubblesDoNotDecouple
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonCriterion
import GaloisForLFunctions.WindowVisibilityLaw.TheOnsetExceedsTheEnlargedBase
import GaloisForLFunctions.SquareRootThreshold.IsolatedOffLinePairVisibilityLaw

/-!
# The local onset field

Fix a profile `ψ`. The local onset field is Weil's form on the tests of aperture `a` spectrally localized near a height `X`:

`Ω_ψ(a, X) = Re W(f, f)`, `f(u) = ψ(u/a) e^{iXu}`.

Taking `a = λ · ½ log X` gives the aperture scale of the field. The transform is a rescaled translate of the transform of the profile (`paperFT_onsetTest`), so the field is a sum over the zeros seen at scale `1/a` around the height `−X` (`hasSum_onsetEnergy`):

`Ω_ψ(a, X) = Σ_ρ m_ρ a² ψ̂(a(γ_ρ + X)) conj ψ̂(a(γ̄_ρ + X))`.

* An on-line zero contributes `m_ρ a² |ψ̂(a(γ_ρ + X))|² ≥ 0` (`onsetSummand_of_onLine`), so all sign is in the off-line pairs.
* **The cost of depth** (`re_onsetPair_ge`, `re_onsetPair_ge_of_small`). A pair at depth `δ` costs at most `2 S(δ, a) · a‖ψ‖²`, with `S(δ, a) = ∫_{−a}^{a} sinh²(δu) du` the pair energy, at every height. Since `(2/3)δ²a³ ≤ S(δ, a) ≤ (8/9)δ²a³` for `δa ≤ ½` (`two_thirds_le_pairEnergy`, `pairEnergy_le`), the cost is at most `(16/9)δ²a⁴‖ψ‖²`. If the on-line mass has its Landau size `a‖ψ‖² log X` (this comparison is not proved here), a pair of depth `A/log X` stays invisible up to `a³ ≲ log³X/A²`, which is `λ ≲ A^{−2/3}` at aperture `a = λ · ½ log X`.
* **Bounded apertures are positive at every height** (`onsetEnergy_nonneg_of_le`). Below the certified aperture the field is nonnegative for every profile and height, unconditionally: at aperture scale this is `λ ≲ 1/log X`.
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

/-! ### The cost of depth -/

theorem tsupport_onsetTest (ha : 0 < a) (hs : tsupport ψ ⊆ Icc (-1) 1) (X : ℝ) :
    tsupport (onsetTest ψ a X) ⊆ Icc (-a) a := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have h1 : ψ (u / a) ≠ 0 := fun h => hu (by simp [onsetTest, h])
  obtain ⟨hl, hr⟩ := hs (subset_tsupport _ h1)
  rw [le_div_iff₀ ha] at hl
  rw [div_le_iff₀ ha] at hr
  exact ⟨by linarith, by linarith⟩

/-- **Bounded apertures are positive at every height.** -/
theorem onsetEnergy_nonneg_of_le (hψ : ContDiff ℝ 2 ψ) (hs : tsupport ψ ⊆ Icc (-1) 1) (ha : 0 < a)
    (ha' : a ≤ ArithmeticIncidencePositivity.successorWeilFloorAperture) (X : ℝ) :
    0 ≤ onsetEnergy ψ a X :=
  WindowVisibilityLaw.windowPositiveAt_antitone ha'
    WindowVisibilityLaw.windowPositiveAt_successorWeilFloorAperture _
    (contDiff_onsetTest hψ a X) (tsupport_onsetTest ha hs X)

/-- The test has mass `a‖ψ‖²`, at every height. -/
theorem integral_norm_sq_onsetTest (ha : 0 < a) (ψ : ℝ → ℂ) (X : ℝ) :
    ∫ u, ‖onsetTest ψ a X u‖ ^ 2 = a * ∫ t, ‖ψ t‖ ^ 2 := by
  have h := Measure.integral_comp_div (fun v : ℝ => ‖ψ v‖ ^ 2) a
  rw [abs_of_pos ha, smul_eq_mul] at h
  rw [← h]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [onsetTest, norm_mul]
  rw [Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The cost of depth.** A pair at depth `δ` costs at most twice the pair energy times the mass of the test. -/
theorem re_onsetPair_ge (ha : 0 < a) (hψ : ContDiff ℝ 2 ψ) (hs : tsupport ψ ⊆ Icc (-1) 1) (X : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (γ₀ : ℝ) :
    -(2 * SquareRootThreshold.pairEnergy δ a * (a * ∫ t, ‖ψ t‖ ^ 2)) ≤
      (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) - I * δ) * conj (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) + I * δ)) +
        paperFT (onsetTest ψ a X) ((γ₀ : ℂ) + I * δ) *
          conj (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) - I * δ))).re := by
  have hpair := SquareRootThreshold.neg_half_normSq_sub_le_re_pair
    (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) - I * δ)) (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) + I * δ))
  have hrank := SquareRootThreshold.norm_sub_sq_le_pairEnergy hδ ha.le γ₀
    (contDiff_onsetTest hψ a X).continuous (tsupport_onsetTest ha hs X)
  rw [integral_norm_sq_onsetTest ha] at hrank
  linarith

/-- `|t| ≤ |sinh t|`, squared. -/
theorem sq_le_sq_sinh (t : ℝ) : t ^ 2 ≤ Real.sinh t ^ 2 := by
  have h : |t| ≤ |Real.sinh t| := by
    rw [Real.abs_sinh]
    exact Real.self_le_sinh_iff.mpr (abs_nonneg t)
  exact sq_le_sq.mpr h

/-- `sinh² t ≤ (4/3) t²` on `|t| ≤ ½`. -/
theorem sq_sinh_le {t : ℝ} (ht : |t| ≤ 1 / 2) : Real.sinh t ^ 2 ≤ 4 / 3 * t ^ 2 := by
  have hb : ∀ s ∈ Icc (-(1 / 2) : ℝ) (1 / 2), ‖Real.cosh s‖ ≤ 8 / 7 := fun s hs => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.cosh_pos s)]
    refine (Real.cosh_le_exp_half_sq s).trans ?_
    have h1 : s ^ 2 / 2 ≤ 1 / 8 := by nlinarith [hs.1, hs.2]
    calc Real.exp (s ^ 2 / 2) ≤ Real.exp (1 / 8) := Real.exp_le_exp.mpr h1
      _ ≤ 1 / (1 - 1 / 8) := Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = 8 / 7 := by norm_num
  have hm := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := Real.sinh) (f' := Real.cosh)
    (s := Icc (-(1 / 2) : ℝ) (1 / 2)) (x := 0) (y := t)
    (fun s _ => (Real.hasDerivAt_sinh s).hasDerivWithinAt) hb (convex_Icc _ _)
    (by norm_num) (abs_le.mp ht)
  rw [Real.sinh_zero, sub_zero, sub_zero, Real.norm_eq_abs, Real.norm_eq_abs] at hm
  have h2 : Real.sinh t ^ 2 ≤ (8 / 7 * |t|) ^ 2 := by
    rw [← sq_abs (Real.sinh t)]
    exact pow_le_pow_left₀ (abs_nonneg _) hm 2
  rw [mul_pow, sq_abs] at h2
  nlinarith [sq_nonneg t]

private theorem integral_mul_sq_Icc (c : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    ∫ u in Icc (-a) a, c * u ^ 2 = c * (2 / 3 * a ^ 3) := by
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul, integral_pow]
  push_cast
  ring

/-- **The pair energy from below.** `(2/3)δ²a³ ≤ S(δ, a)`. -/
theorem two_thirds_le_pairEnergy {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) :
    2 / 3 * δ ^ 2 * a ^ 3 ≤ SquareRootThreshold.pairEnergy δ a := by
  rw [← SquareRootThreshold.integral_sinh_sq_Icc hδ ha]
  have e := integral_mul_sq_Icc (δ ^ 2) ha
  have h1 : 2 / 3 * δ ^ 2 * a ^ 3 = δ ^ 2 * (2 / 3 * a ^ 3) := by ring
  rw [h1, ← e]
  have hc1 : Continuous fun u : ℝ => δ ^ 2 * u ^ 2 := by fun_prop
  have hc2 : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2 := by fun_prop
  refine setIntegral_mono_on hc1.integrableOn_Icc hc2.integrableOn_Icc measurableSet_Icc fun u _ => ?_
  rw [← mul_pow]
  exact sq_le_sq_sinh _

/-- **The pair energy from above.** `S(δ, a) ≤ (8/9)δ²a³` for `δa ≤ ½`. -/
theorem pairEnergy_le {δ a : ℝ} (hδ : 0 < δ) (ha : 0 ≤ a) (hδa : δ * a ≤ 1 / 2) :
    SquareRootThreshold.pairEnergy δ a ≤ 8 / 9 * δ ^ 2 * a ^ 3 := by
  rw [← SquareRootThreshold.integral_sinh_sq_Icc hδ ha]
  have e := integral_mul_sq_Icc (4 / 3 * δ ^ 2) ha
  have h1 : 8 / 9 * δ ^ 2 * a ^ 3 = 4 / 3 * δ ^ 2 * (2 / 3 * a ^ 3) := by ring
  rw [h1, ← e]
  have hc1 : Continuous fun u : ℝ => 4 / 3 * δ ^ 2 * u ^ 2 := by fun_prop
  have hc2 : Continuous fun u : ℝ => Real.sinh (δ * u) ^ 2 := by fun_prop
  refine setIntegral_mono_on hc2.integrableOn_Icc hc1.integrableOn_Icc measurableSet_Icc fun u hu => ?_
  have hu' : |δ * u| ≤ 1 / 2 := by
    rw [abs_mul, abs_of_pos hδ]
    exact (mul_le_mul_of_nonneg_left (abs_le.mpr hu) hδ.le).trans hδa
  have h2 := sq_sinh_le hu'
  rw [mul_pow] at h2
  linarith

/-- **The cost of depth at small `δa`.** -/
theorem re_onsetPair_ge_of_small (ha : 0 < a) (hψ : ContDiff ℝ 2 ψ) (hs : tsupport ψ ⊆ Icc (-1) 1) (X : ℝ)
    {δ : ℝ} (hδ : 0 < δ) (hδa : δ * a ≤ 1 / 2) (γ₀ : ℝ) :
    -(16 / 9 * δ ^ 2 * a ^ 4 * ∫ t, ‖ψ t‖ ^ 2) ≤
      (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) - I * δ) * conj (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) + I * δ)) +
        paperFT (onsetTest ψ a X) ((γ₀ : ℂ) + I * δ) *
          conj (paperFT (onsetTest ψ a X) ((γ₀ : ℂ) - I * δ))).re := by
  refine le_trans ?_ (re_onsetPair_ge ha hψ hs X hδ γ₀)
  have hI : 0 ≤ ∫ t, ‖ψ t‖ ^ 2 := integral_nonneg fun _ => by positivity
  have h1 := mul_le_mul_of_nonneg_right (pairEnergy_le hδ ha.le hδa)
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha.le) hI)
  nlinarith

end

end GaloisForLFunctions.ArithmeticInnerFunctionTheory
