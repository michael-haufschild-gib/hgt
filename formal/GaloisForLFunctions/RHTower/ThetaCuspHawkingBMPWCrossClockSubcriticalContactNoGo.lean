import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPWCrossClockTranslatedTests
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMQuarticResponseMellinTransport
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMFullSourceCircleGrowth

/-!
# PW-B subcritical square-contact obstruction

The literal cross-clock forcing has a nonzero translated log-cusp charge at a
hypothetical left-half Xi zero. The complete native square-source mean has
strictly lower cusp grade. Therefore no continuous height-dependent scalar
renormalization of that square mean with subcritical grade, even plus a
constant counterterm, can equal the actual cross-clock source mean.

This kills subcritical square-contact repairs of the PW-B producer. It does
not identify the literal two-event CTP with the ordered physical current.
-/

open Complex MeasureTheory Set Filter Topology UpperHalfPlane
open RHTower RHTower.D4BMModularCore
open RHTower.D4BMPWCrossClockLogIdentity
open RHTower.D4BMPWCrossClockMeanEquation
open RHTower.D4BMQuarticResponseMellinTransport
open RHTower.D4BMPWCrossClockTranslatedTests
open RHTower.D4BMNativeCircle RHTower.D4BMCuspResponse
open RHTower.D4BMGlobalAngularResponse RHTower.D4BMAngularSeries
open scoped ContDiff
open GaloisForLFunctions.HTGeometry
namespace RHTower.D4BMPWCrossClockSubcriticalContactNoGo
noncomputable section
set_option autoImplicit false

private theorem sourceMean_cusp_bound (q : XiZeroCopy) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : ℝ, 3 ≤ y →
      ‖sourceMean q y‖ ≤ C * y ^ (sourceGrowthExponent q) := by
  obtain ⟨C,hC,hQ⟩ := fullSquarePotential_global_growth q
  refine ⟨C,hC,?_⟩
  intro y hy
  rw [sourceMean_eq_horizontal]
  have hy0 : 0 < y := by linarith
  have hy1 : 1 ≤ y := by linarith
  have hrec : 1 / y ≤ y := by
    apply (div_le_iff₀ hy0).mpr
    nlinarith
  have hmax : max 1 (max y (1/y)) = y := by
    rw [max_eq_left hrec,max_eq_right hy1]
  have hb (x : ℝ) : ‖fullSquarePotential q ![x,y]‖ ≤ C * y ^ sourceGrowthExponent q := by
    let z : UpperHalfPlane := ⟨point x y, by simpa [point] using hy0⟩
    have h := hQ z
    have hzcoord : D4BMGlobalAngularResponse.coordinates z = ![x,y] := by
      ext i
      fin_cases i <;> simp [z, D4BMGlobalAngularResponse.coordinates, point]
    have hzim : z.im = y := by simp [z,point]
    rw [hzcoord,hzim] at h
    simpa only [hmax] using h
  have h := norm_setIntegral_le_of_norm_le_const
    (μ := (volume : Measure ℝ)) (s := Ioc (-1/2:ℝ) (1/2)) measure_Ioc_lt_top
    (fun x _ => hb x)
  change ‖∫ x in Ioc (-1/2:ℝ) (1/2), fullSquarePotential q ![x,y]‖ ≤ _
  norm_num at h ⊢
  exact h

private theorem sourceMean_exp_continuous (q : XiZeroCopy) :
    Continuous (fun t : ℝ => sourceMean q (Real.exp t)) := by
  have hs := cuspLeg_contDiffOn .scalar (center q)
  have hQ : ContDiffOn ℝ ∞ (fullSquarePotential q) domain :=
    contDiffOn_const.mul (hs.mul hs)
  have hF : ContDiffOn ℝ ∞
      (fun z : ℂ => fullSquarePotential q (angularCoordinates z))
      {z : ℂ | 0 < z.im} :=
    hQ.comp angularCoordinates.contDiff.contDiffOn (fun _ hz => hz)
  apply continuous_iff_continuousAt.mpr
  intro t
  have h := average_hasDerivAt
    (fun z : ℂ => fullSquarePotential q (angularCoordinates z)) hF (Real.exp_pos t)
  change HasDerivAt (sourceMean q) _ (Real.exp t) at h
  exact h.continuousAt.comp Real.continuous_exp.continuousAt

private theorem normalizedSquare_integrable (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    IntegrableOn (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
      sourceMean q (Real.exp t)) (Ioi (Real.log 3)) := by
  obtain ⟨C,hC,hbound⟩ := sourceMean_cusp_bound q
  have hdelta : sourceGrowthExponent q - (rate q).re < 0 := by
    have hg := (sourceGrowthExponent_bounds q).2
    have hr := (rate_re_bounds q hleft).1
    linarith
  have hm := ((integrableOn_exp_mul_Ioi hdelta (Real.log 3)).const_mul C)
  have hc : Continuous (fun t : ℝ =>
      Complex.exp (-rate q*(t:ℂ)) * sourceMean q (Real.exp t)) :=
    (by fun_prop : Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)))).mul
      (sourceMean_exp_continuous q)
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hty : 3 ≤ Real.exp t := by
    have h := Real.exp_le_exp.mpr (le_of_lt ht)
    simpa [Real.exp_log (by norm_num : (0:ℝ)<3)] using h
  have hb := hbound (Real.exp t) hty
  have hnorm : ‖Complex.exp (-rate q*(t:ℂ))‖ =
      Real.exp (-(rate q).re*t) := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [norm_mul,hnorm]
  calc
    Real.exp (-(rate q).re*t) * ‖sourceMean q (Real.exp t)‖ ≤
        Real.exp (-(rate q).re*t) * (C * (Real.exp t)^sourceGrowthExponent q) :=
      mul_le_mul_of_nonneg_left hb (Real.exp_pos _).le
    _ = C * Real.exp ((sourceGrowthExponent q - (rate q).re)*t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t),Real.log_exp]
      calc
        Real.exp (-(rate q).re*t) * (C * Real.exp (t*sourceGrowthExponent q)) =
            C * (Real.exp (-(rate q).re*t) * Real.exp (t*sourceGrowthExponent q)) := by ring
        _ = C * Real.exp (-(rate q).re*t+t*sourceGrowthExponent q) := by
          rw [Real.exp_add]
        _ = _ := by
          have he : -(rate q).re*t+t*sourceGrowthExponent q =
              (sourceGrowthExponent q-(rate q).re)*t := by ring
          rw [he]

/-- At a hypothetical left-half Xi copy, the actual cross-clock source cannot be
absorbed into any constant multiple of the literal full-square source mean,
even after adding an arbitrary constant scalar contact. -/
theorem forcingMean_not_affine_sourceMean_on_cusp (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (c d : ℂ) :
    ¬ ∀ y : ℝ, 3 ≤ y → forcingMean q y = c * sourceMean q y + d := by
  intro heq
  have hr : (-rate q).re < 0 := by
    have h := (rate_re_bounds q hleft).1
    simp only [Complex.neg_re]
    linarith
  have hi0 := (integrableOn_exp_mul_complex_Ioi hr (Real.log 3)).mul_const d
  have hi : IntegrableOn (fun t : ℝ =>
      c * (Complex.exp (-rate q*(t:ℂ)) * sourceMean q (Real.exp t)) +
        Complex.exp (-rate q*(t:ℂ)) * d) (Ioi (Real.log 3)) :=
    ((normalizedSquare_integrable q hleft).const_mul c).add hi0
  have hactual : IntegrableOn (normalizedForcing q) (Ioi (Real.log 3)) := by
    apply MeasureTheory.IntegrableOn.congr_fun hi _ measurableSet_Ioi
    intro t ht
    have hty : 3 ≤ Real.exp t := by
      have h := Real.exp_le_exp.mpr (le_of_lt ht)
      simpa [Real.exp_log (by norm_num : (0:ℝ)<3)] using h
    have he := heq (Real.exp t) hty
    change c * (Complex.exp (-rate q*(t:ℂ)) * sourceMean q (Real.exp t)) +
      Complex.exp (-rate q*(t:ℂ)) * d = normalizedForcing q t
    rw [normalizedForcing,he]
    ring
  exact normalizedForcing_cusp_not_integrable q hleft hactual

/-- Every continuous source-contact multiplier whose cusp grade stays below
the cross-clock grade leaves the normalized square mean integrable. -/
private theorem subcritical_square_contact_integrable (q : XiZeroCopy)
    (a : ℝ → ℂ) (ha : Continuous a)
    (M σ : ℝ) (hM : 0 ≤ M)
    (hσ : σ + sourceGrowthExponent q < (rate q).re)
    (haBound : ∀ t ∈ Ioi (Real.log 3), ‖a t‖ ≤ M * Real.exp (σ*t)) :
    IntegrableOn (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
      a t * sourceMean q (Real.exp t)) (Ioi (Real.log 3)) := by
  obtain ⟨C,hC,hbound⟩ := sourceMean_cusp_bound q
  have hδ : σ + sourceGrowthExponent q - (rate q).re < 0 := by linarith
  have hm := (integrableOn_exp_mul_Ioi hδ (Real.log 3)).const_mul (M*C)
  have hc : Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)) *
      a t * sourceMean q (Real.exp t)) :=
    (((by fun_prop : Continuous (fun t : ℝ => Complex.exp (-rate q*(t:ℂ)))).mul ha).mul
      (sourceMean_exp_continuous q))
  apply hm.mono' hc.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have hty : 3 ≤ Real.exp t := by
    have h := Real.exp_le_exp.mpr (le_of_lt ht)
    simpa [Real.exp_log (by norm_num : (0:ℝ)<3)] using h
  have hb := hbound (Real.exp t) hty
  have hnorm : ‖Complex.exp (-rate q*(t:ℂ))‖ =
      Real.exp (-(rate q).re*t) := by
    simp [Complex.norm_exp, Complex.mul_re]
  simp only [norm_mul,hnorm]
  calc
    Real.exp (-(rate q).re*t) * ‖a t‖ * ‖sourceMean q (Real.exp t)‖ ≤
        Real.exp (-(rate q).re*t) * (M*Real.exp (σ*t)) *
          (C*(Real.exp t)^sourceGrowthExponent q) := by
      gcongr
      · exact haBound t ht
    _ = (M*C)*Real.exp ((σ+sourceGrowthExponent q-(rate q).re)*t) := by
      rw [Real.rpow_def_of_pos (Real.exp_pos t),Real.log_exp]
      have he : Real.exp (-(rate q).re*t) * Real.exp (σ*t) *
          Real.exp (t*sourceGrowthExponent q) =
          Real.exp ((σ+sourceGrowthExponent q-(rate q).re)*t) := by
        rw [← Real.exp_add,← Real.exp_add]
        congr 1
        ring
      calc
        _ = (M*C)*(Real.exp (-(rate q).re*t) * Real.exp (σ*t) *
            Real.exp (t*sourceGrowthExponent q)) := by ring
        _ = _ := by rw [he]

theorem rate_re_eq_two_sourceGrowthExponent (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) :
    (rate q).re = 2 * sourceGrowthExponent q := by
  have hhalf : ((1/2:ℂ).re) = (1/2:ℝ) := by norm_num
  have hc : (D4BMGlobalAngularResponse.center q).re < 0 := by
    dsimp [D4BMGlobalAngularResponse.center]
    rw [hhalf]
    linarith
  have hr : (rate q).re = 4 - 4*(q.1 : ℂ).re := by
    change (2*(2-2*(q.1:ℂ))).re = 4 - 4*(q.1:ℂ).re
    norm_num [Complex.mul_re,Complex.sub_re]
    ring
  have hb : sourceGrowthExponent q = 2-2*(q.1:ℂ).re := by
    unfold sourceGrowthExponent
    rw [abs_of_neg hc]
    dsimp [D4BMGlobalAngularResponse.center]
    rw [hhalf]
    ring
  rw [hr,hb]
  ring

/-- Sharp subcritical-contact obstruction. Any height-dependent scalar
renormalization of the native full-square source below the cross-clock cusp
grade fails to reproduce the actual ordered source, even modulo a constant. -/
theorem forcingMean_not_subcritical_square_contact (q : XiZeroCopy)
    (hleft : (q.1 : ℂ).re < 1/2) (a : ℝ → ℂ) (ha : Continuous a)
    (M σ : ℝ) (hM : 0 ≤ M)
    (hσ : σ < sourceGrowthExponent q)
    (haBound : ∀ t ∈ Ioi (Real.log 3), ‖a t‖ ≤ M * Real.exp (σ*t))
    (d : ℂ) :
    ¬ ∀ y : ℝ, 3 ≤ y →
      forcingMean q y = a (Real.log y) * sourceMean q y + d := by
  intro heq
  have hr : (-rate q).re < 0 := by
    have h := (rate_re_bounds q hleft).1
    simp only [Complex.neg_re]
    linarith
  have hi0 := (integrableOn_exp_mul_complex_Ioi hr (Real.log 3)).mul_const d
  have hgrade : σ + sourceGrowthExponent q < (rate q).re := by
    rw [rate_re_eq_two_sourceGrowthExponent q hleft]
    linarith
  have hi : IntegrableOn (fun t : ℝ =>
      Complex.exp (-rate q*(t:ℂ)) * a t * sourceMean q (Real.exp t) +
        Complex.exp (-rate q*(t:ℂ)) * d) (Ioi (Real.log 3)) :=
    (subcritical_square_contact_integrable q a ha M σ hM hgrade haBound).add hi0
  have hactual : IntegrableOn (normalizedForcing q) (Ioi (Real.log 3)) := by
    apply MeasureTheory.IntegrableOn.congr_fun hi _ measurableSet_Ioi
    intro t ht
    have hty : 3 ≤ Real.exp t := by
      have h := Real.exp_le_exp.mpr (le_of_lt ht)
      simpa [Real.exp_log (by norm_num : (0:ℝ)<3)] using h
    have he := heq (Real.exp t) hty
    rw [Real.log_exp] at he
    change Complex.exp (-rate q*(t:ℂ)) * a t * sourceMean q (Real.exp t) +
      Complex.exp (-rate q*(t:ℂ)) * d = normalizedForcing q t
    rw [normalizedForcing,he]
    ring
  exact normalizedForcing_cusp_not_integrable q hleft hactual

end
end RHTower.D4BMPWCrossClockSubcriticalContactNoGo
