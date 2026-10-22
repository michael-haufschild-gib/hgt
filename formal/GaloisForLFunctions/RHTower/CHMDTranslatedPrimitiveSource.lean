import GaloisForLFunctions.RHTower.CHMDDoobSourceGraph
import GaloisForLFunctions.RHTower.MarkovShiftPolarizationAndEvenPrimitivePBAP
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspReflectedSourceOddStationary
import GaloisForLFunctions.RHTower.XiSliceHusimiHeatDictionary

/-!
# Primitive translations in the original theta-cosh mass

Translation preserves the complete Markov energy. A concrete nonzero compact test
has both hyperbolic half-moments zero, so all its translates remain primitive.
Their inverse-Doob theta-cosh mass tends to infinity. These source facts will produce
primitive escape in the actual completed graph, without changing any prime coefficient.
-/

open MeasureTheory Set Filter Topology
open scoped ComplexConjugate
open Zeta23
noncomputable section
namespace RHTower.CHMDTranslation

def translate (f : ℝ → ℝ) (t x : ℝ) : ℝ := f (x - t)

theorem continuous_translate {f : ℝ → ℝ} (hf : Continuous f) (t : ℝ) :
    Continuous (translate f t) := hf.comp (continuous_id.sub continuous_const)

theorem contDiff_translate {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f) (t : ℝ) :
    ContDiff ℝ 2 (translate f t) := hf.comp (contDiff_id.sub contDiff_const)

theorem compact_translate {f : ℝ → ℝ} (hf : HasCompactSupport f) (t : ℝ) :
    HasCompactSupport (translate f t) := hf.comp_homeomorph (Homeomorph.subRight t)

theorem weilTest_translate (f : ℝ → ℝ) (t y : ℝ) :
    EF.weilTest (fun x => (translate f t x : ℂ)) (fun x => (translate f t x : ℂ)) y =
      EF.weilTest (fun x => (f x : ℂ)) (fun x => (f x : ℂ)) y := by
  simp only [WeilSpectral.weilTest_apply, translate]
  simp_rw [show ∀ u : ℝ, u - y - t = (u - t) - y by intro u; ring]
  exact integral_sub_right_eq_self (fun u => (f u : ℂ) * conj (f (u - y) : ℂ)) t

/-- Complete arithmetic energy, not a truncated prime expression, is translation invariant. -/
theorem markovEnergy_translate (f : ℝ → ℝ) (t : ℝ) :
    markovEnergy (fun x => (translate f t x : ℂ)) = markovEnergy (fun x => (f x : ℂ)) := by
  unfold markovEnergy
  have he := funext (weilTest_translate f t)
  rw [he]

theorem coshHalfMoment_translate {f : ℝ → ℝ} (hf : Continuous f)
    (hfc : HasCompactSupport f) (t : ℝ) :
    coshHalfMoment (translate f t) =
      coshHalfMoment f * Real.cosh (t / 2) + sinhHalfMoment f * Real.sinh (t / 2) := by
  have hc : Integrable (fun x => f x * Real.cosh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  have hs : Integrable (fun x => f x * Real.sinh (x / 2)) :=
    (hf.mul (by fun_prop)).integrable_of_hasCompactSupport hfc.mul_right
  unfold coshHalfMoment sinhHalfMoment
  rw [← integral_add_right_eq_self (fun x => translate f t x * Real.cosh (x / 2)) t]
  simp only [translate, add_sub_cancel_right]
  have he (x : ℝ) : f x * Real.cosh ((x + t) / 2) =
      (f x * Real.cosh (x / 2)) * Real.cosh (t / 2) +
        (f x * Real.sinh (x / 2)) * Real.sinh (t / 2) := by
    rw [add_div, Real.cosh_add]
    ring
  simp_rw [he]
  rw [integral_add (hc.mul_const _) (hs.mul_const _), integral_mul_const, integral_mul_const]

def profile (x : ℝ) : ℝ :=
  evenShift (WeilOneSided.narrowBump 0) 4 x - Real.cosh 1 * WeilOneSided.narrowBump 0 x

theorem profile_contDiff : ContDiff ℝ 2 profile := by
  have hg : ContDiff ℝ 2 (WeilOneSided.narrowBump 0 : ℝ → ℝ) :=
    (WeilOneSided.narrowBump 0).contDiff
  exact (contDiff_evenShift hg 4).sub (contDiff_const.mul hg)

theorem profile_compact : HasCompactSupport profile :=
  (hasCompactSupport_evenShift (WeilOneSided.narrowBump 0).hasCompactSupport 4).sub
    (WeilOneSided.narrowBump 0).hasCompactSupport.mul_left

theorem profile_moments : coshHalfMoment profile = 0 ∧ sinhHalfMoment profile = 0 := by
  have hgd : ContDiff ℝ 2 (WeilOneSided.narrowBump 0 : ℝ → ℝ) :=
    (WeilOneSided.narrowBump 0).contDiff
  have hg := hgd.continuous
  have hc := (WeilOneSided.narrowBump 0).hasCompactSupport
  have hge := (contDiff_evenShift hgd 4).continuous
  have hce := hasCompactSupport_evenShift hc 4
  have he : profile = fun x => 1 * evenShift (WeilOneSided.narrowBump 0) 4 x +
      (-Real.cosh 1) * WeilOneSided.narrowBump 0 x := by funext x; unfold profile; ring
  rw [he, coshHalfMoment_linear_comb hge hce hg hc,
    sinhHalfMoment_linear_comb hge hce hg hc,
    coshHalfMoment_evenShift hg hc, sinhHalfMoment_evenShift hg hc]
  norm_num

theorem profile_zero : profile 0 = -Real.cosh 1 := by
  have hz : WeilOneSided.narrowBump 0 (0 : ℝ) = 1 :=
    (WeilOneSided.narrowBump 0).one_of_mem_closedBall
      (Metric.mem_closedBall_self (WeilOneSided.narrowBump 0).rIn_pos.le)
  have hp : WeilOneSided.narrowBump 0 (2 : ℝ) = 0 :=
    (WeilOneSided.narrowBump 0).zero_of_le_dist (by
      norm_num [WeilOneSided.narrowBump, Real.dist_eq])
  have hm : WeilOneSided.narrowBump 0 (-2 : ℝ) = 0 :=
    (WeilOneSided.narrowBump 0).zero_of_le_dist (by
      norm_num [WeilOneSided.narrowBump, Real.dist_eq])
  norm_num [profile, evenShift, hz, hp, hm]

theorem profile_ne_zero : profile ≠ 0 := by
  intro h
  have hh := congrFun h 0
  rw [profile_zero] at hh
  have := Real.cosh_pos (1 : ℝ)
  simp only [Pi.zero_apply] at hh
  linarith

theorem profile_translate_primitive (t : ℝ) : coshHalfMoment (translate profile t) = 0 := by
  rw [coshHalfMoment_translate profile_contDiff.continuous profile_compact,
    profile_moments.1, profile_moments.2]
  ring

/-- The physical source mass of an inverse Doob test. -/
def inverseWeight (x : ℝ) : ℝ := Real.cosh (x / 2) / riemannKernelReal x
def inverseMass (f : ℝ → ℝ) : ℝ := ∫ x, f x ^ 2 * inverseWeight x

theorem inverseWeight_pos (x : ℝ) : 0 < inverseWeight x :=
  div_pos (Real.cosh_pos _) (riemannKernelReal_pos _)

theorem inverseWeight_continuous : Continuous inverseWeight :=
  (Real.continuous_cosh.comp (continuous_id.div_const 2)).div continuous_riemannKernelReal
    (fun x => (riemannKernelReal_pos x).ne')

theorem integrable_inverseMass {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f) :
    Integrable (fun x => f x ^ 2 * inverseWeight x) := by
  have hs : HasCompactSupport (fun x => f x ^ 2) :=
    hc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  exact ((hf.pow 2).mul inverseWeight_continuous).integrable_of_hasCompactSupport hs.mul_right

theorem inverseMass_nonneg (f : ℝ → ℝ) : 0 ≤ inverseMass f :=
  integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (inverseWeight_pos x).le)

theorem inverseMass_pos {f : ℝ → ℝ} (hf : Continuous f) (hc : HasCompactSupport f)
    (hne : f ≠ 0) : 0 < inverseMass f := by
  obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
    by_contra h
    push Not at h
    exact hne (funext h)
  exact integral_pos_of_integrable_nonneg_nonzero
    ((hf.pow 2).mul inverseWeight_continuous) (integrable_inverseMass hf hc)
    (fun x => mul_nonneg (sq_nonneg _) (inverseWeight_pos x).le)
    (mul_ne_zero (pow_ne_zero _ hx) (inverseWeight_pos x).ne')

theorem inverseMass_translate (f : ℝ → ℝ) (t : ℝ) :
    inverseMass (translate f t) = ∫ x, f x ^ 2 * inverseWeight (x + t) := by
  have h := integral_add_right_eq_self (μ := volume)
    (fun x => translate f t x ^ 2 * inverseWeight x) t
  simpa only [inverseMass, translate, add_sub_cancel_right] using h.symm

theorem inverseWeight_atTop : Tendsto inverseWeight atTop atTop := by
  have ht : Tendsto riemannKernelReal atTop (𝓝 0) := by
    have he : thetaCuspFullSource = riemannKernelReal :=
      funext thetaCuspFullSource_eq_riemannKernelReal
    simpa only [he] using tendsto_thetaCuspFullSource_atTop_zero
  apply tendsto_atTop.2
  intro b
  have he : 0 < 1 / (max b 0 + 1) := by positivity
  filter_upwards [ht.eventually_lt_const he] with x hx
  have hb := le_max_left b 0
  have hb0 := le_max_right b 0
  have hm := (lt_div_iff₀ (by positivity : 0 < max b 0 + 1)).mp hx
  apply (le_div_iff₀ (riemannKernelReal_pos x)).2
  have hc := Real.one_le_cosh (x / 2)
  have hp := riemannKernelReal_pos x
  nlinarith

theorem support_interval {f : ℝ → ℝ} (hc : HasCompactSupport f) :
    ∃ R : ℝ, 0 < R ∧ ∀ x, f x ≠ 0 → -R ≤ x ∧ x ≤ R := by
  obtain ⟨L, hL⟩ := hc.isCompact.isBounded.subset_closedBall 0
  refine ⟨|L| + 1, by positivity, ?_⟩
  intro x hx
  have hx' := hL (subset_tsupport f (Function.mem_support.mpr hx))
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at hx'
  have := le_abs_self L
  constructor <;> linarith [hx'.1, hx'.2]

/-- Every nonzero compact profile has diverging inverse-Doob mass under right translation. -/
theorem inverseMass_translate_atTop {f : ℝ → ℝ} (hf : Continuous f)
    (hc : HasCompactSupport f) (hne : f ≠ 0) :
    Tendsto (fun t => inverseMass (translate f t)) atTop atTop := by
  have hs : HasCompactSupport (fun x => f x ^ 2) :=
    hc.comp_left (g := fun y : ℝ => y ^ 2) (by norm_num)
  have hi : Integrable (fun x => f x ^ 2) := (hf.pow 2).integrable_of_hasCompactSupport hs
  have hI : 0 < ∫ x, f x ^ 2 := by
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra h
      push Not at h
      exact hne (funext h)
    exact integral_pos_of_integrable_nonneg_nonzero (hf.pow 2) hi
      (fun _ => sq_nonneg _) (pow_ne_zero _ hx)
  obtain ⟨R, hR, hsupport⟩ := support_interval hc
  apply tendsto_atTop.2
  intro b
  obtain ⟨A, hA⟩ := eventually_atTop.1
    (inverseWeight_atTop.eventually (eventually_ge_atTop (b / (∫ x, f x ^ 2))))
  filter_upwards [eventually_ge_atTop (A + R)] with t ht
  rw [inverseMass_translate]
  have hj : Integrable (fun x => f x ^ 2 * inverseWeight (x + t)) := by
    have hcont : Continuous (fun x => f x ^ 2 * inverseWeight (x + t)) :=
      (hf.pow 2).mul (inverseWeight_continuous.comp (continuous_id.add continuous_const))
    exact hcont.integrable_of_hasCompactSupport hs.mul_right
  calc
    b = ∫ x, f x ^ 2 * (b / (∫ x, f x ^ 2)) := by
      rw [integral_mul_const]
      field_simp [hI.ne']
    _ ≤ _ := integral_mono (hi.mul_const _) hj (fun x => by
      by_cases hx : f x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_left (hA (x + t) (by
          have := (hsupport x hx).1
          linarith)) (sq_nonneg _))

end RHTower.CHMDTranslation
