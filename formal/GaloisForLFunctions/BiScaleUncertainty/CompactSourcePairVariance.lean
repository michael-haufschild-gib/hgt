import GaloisForLFunctions.BiScaleUncertainty.CompactSourceGraphAdmission
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral

/-!
# Exact compact-source pair variance and positive-lag transport

Continuous compact sources make every moment and pair integral finite. The
positive-lag pair integral is exactly the unnormalized weighted variance.
Its nullspace consists of states constant on the whole nonzero source, without
a connected-support or positive-mass hypothesis.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal NNReal CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.PathCongestion
set_option autoImplicit false

def sourceMoment (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (k : ℕ) : ℝ :=
  ∫ u, ψ u ^ 2 * f u ^ k

theorem integrable_sourceMoment (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (k : ℕ) :
    Integrable (fun u => ψ u ^ 2 * f u ^ k) := by
  apply ((ψ.continuous.pow 2).mul (f.continuous.pow k)).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact ψ.hasCompactSupport.isCompact
  intro u hu
  apply subset_closure
  apply Function.mem_support.mpr
  intro hψ
  simp [Function.mem_support, hψ] at hu

def weightedVariance (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) : ℝ :=
  sourceMoment ψ f 0 * sourceMoment ψ f 2 - sourceMoment ψ f 1 ^ 2

def pairGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (p : ℝ × ℝ) : ℝ :=
  ψ p.1 ^ 2 * ψ p.2 ^ 2 * (f p.2-f p.1)^2

theorem pairGap_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (p : ℝ × ℝ) :
    0 ≤ pairGap ψ f p := by unfold pairGap; positivity

theorem continuous_pairGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) : Continuous (pairGap ψ f) := by
  have hψ := ψ.continuous
  have hf := f.continuous
  unfold pairGap
  fun_prop

theorem integrable_pairGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    Integrable (pairGap ψ f) (volume.prod volume) := by
  apply (continuous_pairGap ψ f).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (ψ.hasCompactSupport.isCompact.prod ψ.hasCompactSupport.isCompact)
  intro p hp
  have h₁ : ψ p.1 ≠ 0 := by intro h; simp [Function.mem_support, pairGap, h] at hp
  have h₂ : ψ p.2 ≠ 0 := by intro h; simp [Function.mem_support, pairGap, h] at hp
  exact ⟨subset_closure (Function.mem_support.mpr h₁),
    subset_closure (Function.mem_support.mpr h₂)⟩

theorem integral_pairGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    (∫ p, pairGap ψ f p ∂volume.prod volume) = 2*weightedVariance ψ f := by
  let m (k : ℕ) (u : ℝ) := ψ u ^ 2 * f u ^ k
  have hi (k : ℕ) : Integrable (m k) := integrable_sourceMoment ψ f k
  have ha := (hi 0).mul_prod (hi 2)
  have hb := (hi 2).mul_prod (hi 0)
  have hc := (hi 1).mul_prod (hi 1)
  have hab : Integrable (fun p : ℝ × ℝ => m 0 p.1*m 2 p.2 + m 2 p.1*m 0 p.2)
      (volume.prod volume) := ha.add hb
  have hc2 : Integrable (fun p : ℝ × ℝ => 2*(m 1 p.1*m 1 p.2))
      (volume.prod volume) := hc.const_mul 2
  have he : pairGap ψ f = fun p =>
      (m 0 p.1*m 2 p.2 + m 2 p.1*m 0 p.2) - 2*(m 1 p.1*m 1 p.2) := by
    funext p
    dsimp [pairGap, m]
    ring
  rw [he]
  dsimp only
  rw [integral_sub hab hc2, integral_add ha hb,
    integral_const_mul, integral_prod_mul, integral_prod_mul, integral_prod_mul]
  change sourceMoment ψ f 0 * sourceMoment ψ f 2 +
    sourceMoment ψ f 2 * sourceMoment ψ f 0 -
      2*(sourceMoment ψ f 1 * sourceMoment ψ f 1) = _
  unfold weightedVariance
  ring

theorem weightedVariance_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    0 ≤ weightedVariance ψ f := by
  have h := MeasureTheory.integral_nonneg (f := pairGap ψ f)
    (μ := volume.prod volume) (fun p => pairGap_nonneg ψ f p)
  rw [integral_pairGap] at h
  linarith

def lagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) : ℝ :=
  pairGap ψ f (e.2,e.2+e.1)

theorem lagGap_nonneg (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (e : Edge) :
    0 ≤ lagGap ψ f e := pairGap_nonneg ψ f _

theorem continuous_lagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) : Continuous (lagGap ψ f) :=
  (continuous_pairGap ψ f).comp (continuous_snd.prodMk (continuous_snd.add continuous_fst))

theorem integrable_lagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    Integrable (lagGap ψ f) (volume.prod volume) := by
  apply (continuous_lagGap ψ f).integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact
    (isCompact_Icc.prod isCompact_Icc :
      IsCompact (Icc (-2*multiplierSourceRadius ψ) (2*multiplierSourceRadius ψ) ×ˢ
        Icc (-multiplierSourceRadius ψ) (multiplierSourceRadius ψ)))
  intro e he
  have hp : sourcePair ψ e ≠ 0 := by
    intro hp
    have hz : lagGap ψ f e = sourcePair ψ e * (f (e.2+e.1)-f e.2)^2 := rfl
    simp [Function.mem_support, hz, hp] at he
  rcases sourcePair_endpoints ψ e hp with ⟨h₁,h₂⟩
  exact ⟨⟨by linarith [h₁.2,h₂.1], by linarith [h₁.1,h₂.2]⟩,h₁⟩

theorem lagGap_integral_even (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) (h : ℝ) :
    (∫ u, lagGap ψ f (-h,u)) = ∫ u, lagGap ψ f (h,u) := by
  calc
    _ = ∫ u, lagGap ψ f (h,u-h) := by
      apply integral_congr_ae
      filter_upwards [] with u
      dsimp only [lagGap, pairGap]
      rw [sub_add_cancel]
      simp only [sub_eq_add_neg]
      ring
    _ = _ := integral_sub_right_eq_self (fun u => lagGap ψ f (h,u)) h

/-- Positive lags count each unordered source pair exactly once. -/
theorem integral_positive_lagGap (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    (∫ e, lagGap ψ f e ∂(volume.restrict (Ioi (0 : ℝ))).prod volume) =
      weightedVariance ψ f := by
  let H : ℝ → ℝ := fun h => ∫ u, lagGap ψ f (h,u)
  have hfull : (∫ h, H h) = 2*weightedVariance ψ f := by
    calc
      _ = ∫ u, ∫ h, lagGap ψ f (h,u) :=
        integral_integral_swap (integrable_lagGap ψ f)
      _ = ∫ u, ∫ v, pairGap ψ f (u,v) := by
        apply integral_congr_ae
        filter_upwards [] with u
        exact integral_add_left_eq_self (fun v => pairGap ψ f (u,v)) u
      _ = ∫ p, pairGap ψ f p ∂volume.prod volume :=
        (integral_prod _ (integrable_pairGap ψ f)).symm
      _ = _ := integral_pairGap ψ f
  have habs (h : ℝ) : H |h| = H h := by
    rcases le_total 0 h with hh | hh
    · rw [abs_of_nonneg hh]
    · rw [abs_of_nonpos hh]
      exact lagGap_integral_even ψ f h
  have hhalf := integral_comp_abs (f := H)
  simp_rw [habs] at hhalf
  rw [hfull] at hhalf
  rw [integral_prod _ ((integrable_lagGap ψ f).mono_measure
    (Measure.prod_mono Measure.restrict_le_self le_rfl))]
  change (∫ h in Ioi (0 : ℝ), H h) = weightedVariance ψ f
  linarith

theorem weightedVariance_eq_zero_iff (ψ : C_c(ℝ, ℝ)) (f : C(ℝ, ℝ)) :
    weightedVariance ψ f = 0 ↔
      ∀ u v : ℝ, ψ u ≠ 0 → ψ v ≠ 0 → f u = f v := by
  constructor
  · intro hv
    have hi : (∫ p, pairGap ψ f p ∂volume.prod volume) = 0 := by
      rw [integral_pairGap, hv, mul_zero]
    have hae := (integral_eq_zero_iff_of_nonneg_ae
      (Eventually.of_forall (pairGap_nonneg ψ f)) (integrable_pairGap ψ f)).mp hi
    have hz := Measure.eq_of_ae_eq hae (continuous_pairGap ψ f) continuous_const
    intro u v hu hv
    have hp := congrFun hz (u,v)
    have hcoeff : ψ u ^ 2 * ψ v ^ 2 ≠ 0 := mul_ne_zero (pow_ne_zero _ hu) (pow_ne_zero _ hv)
    have hs : (f v-f u)^2 = 0 := (mul_eq_zero.mp hp).resolve_left hcoeff
    exact (sub_eq_zero.mp (sq_eq_zero_iff.mp hs)).symm
  · intro hf
    have hz : pairGap ψ f = 0 := by
      funext p
      by_cases h₁ : ψ p.1 = 0
      · simp [pairGap, h₁]
      by_cases h₂ : ψ p.2 = 0
      · simp [pairGap, h₂]
      simp [pairGap, hf p.1 p.2 h₁ h₂]
    have hi := integral_pairGap ψ f
    simp only [hz, Pi.zero_apply, integral_zero] at hi
    linarith

end GaloisForLFunctions.BiScaleUncertainty.PathCongestion
