import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheSquareTrace
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.LogarithmicWindowsOfAZeroThetaMean
import Mathlib.MeasureTheory.Integral.Prod

/-!
# A bounded value of the cumulative square trace in every logarithmic window

A radially integrated translate of the square trace still has zero theta
mean. Positivity of theta forces a bounded value in each late logarithmic
window, even when the trace grows in both directions.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open MeasureTheory Filter Topology SurfaceOfSpecZ.ScaleLocality _root_.RHTower

private abbrev phi := thetaCuspFullSource
private abbrev window := Set.Ioc (0:ℝ) 1
private abbrev μ := (volume : Measure ℝ).restrict window
private abbrev kernel (t r : ℝ) := r^2*squareLongTrace (t+2*Real.log r)

/-- Normalized primitive corresponding to an unweighted prefix in the integer root. -/
def squarePrefixTrace (t : ℝ) := ∫ r in Set.Ioc (0:ℝ) 1, r^2*squareLongTrace (t+2*Real.log r)

private theorem kernel_measurable (t : ℝ) : Measurable (kernel t) :=
  (measurable_id.pow_const 2).mul (continuous_squareLongTrace.measurable.comp
    (measurable_const.add (measurable_const.mul Real.measurable_log)))

private theorem const_integrable (b : ℝ) : Integrable (fun _ : ℝ => b) μ := by
  change IntegrableOn (fun _ : ℝ => b) (Set.Ioc (0:ℝ) 1) volume
  have hi : IntegrableOn (fun _ : ℝ => b) (Set.Icc (0:ℝ) 1) volume :=
    continuousOn_const.integrableOn_Icc
  exact hi.mono_set Set.Ioc_subset_Icc_self

/-- The factor r² pays the exponential strip bound at the lower endpoint. -/
private theorem kernel_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ t r : ℝ, r ∈ window →
    |kernel t r| ≤ A*Real.exp (1/2*|t|) := by
  obtain ⟨A,hA,h⟩ := squareLongTrace_bound
  refine ⟨A,hA,fun t r hr => ?_⟩
  have he : Real.exp (1/2*|2*Real.log r|)=r⁻¹ := by
    rw [abs_of_nonpos (mul_nonpos_of_nonneg_of_nonpos two_pos.le (Real.log_nonpos hr.1.le hr.2)),
      show 1/2* -(2*Real.log r)= -Real.log r by ring,Real.exp_neg,Real.exp_log hr.1]
  have h₁ := exp_abs_add_le (by norm_num : (0:ℝ) ≤ 1/2) t (2*Real.log r)
  rw [he] at h₁
  rw [kernel,abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc _ ≤ r^2*(A*(Real.exp (1/2*|t|)*r⁻¹)) := mul_le_mul_of_nonneg_left
              ((h _).trans (mul_le_mul_of_nonneg_left h₁ hA)) (sq_nonneg r)
       _ = r*(A*Real.exp (1/2*|t|)) := by field_simp [hr.1.ne']
       _ ≤ A*Real.exp (1/2*|t|) := mul_le_of_le_one_left (by positivity) hr.2

private theorem prefix_strip_bound : ∃ A : ℝ, 0 ≤ A ∧ ∀ t : ℝ,
    |squarePrefixTrace t| ≤ A*Real.exp (1/2*|t|) := by
  obtain ⟨A,hA,h⟩ := kernel_bound
  refine ⟨A,hA,fun t => ?_⟩
  have hb : ∀ᵐ r : ℝ ∂μ, ‖kernel t r‖ ≤ A*Real.exp (1/2*|t|) :=
    (ae_restrict_mem (μ := volume) measurableSet_Ioc).mono fun r hr => (Real.norm_eq_abs _).trans_le (h t r hr)
  have hn := norm_integral_le_of_norm_le (const_integrable _) hb
  simpa only [squarePrefixTrace,Real.norm_eq_abs,setIntegral_const,Real.volume_real_Ioc,
    sub_zero,max_eq_left zero_le_one,one_smul] using hn

private theorem continuous_prefix : Continuous squarePrefixTrace := by
  obtain ⟨A,hA,h⟩ := kernel_bound
  apply continuous_iff_continuousAt.mpr
  intro t
  let B := A*Real.exp (1/2*(|t|+1))
  apply tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => B)
      (Eventually.of_forall (fun v => (kernel_measurable v).aestronglyMeasurable)) _ (const_integrable _) _
  · filter_upwards [(continuous_abs.continuousAt (x := t)).tendsto.eventually_le_const (lt_add_one |t|)] with v hv
    filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with r hr
    rw [Real.norm_eq_abs]
    exact (h v r hr).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hv (by norm_num : (0:ℝ) ≤ 1/2))) hA)
  · exact Eventually.of_forall fun r =>
      ((continuous_squareLongTrace.comp (continuous_id.add continuous_const)).const_mul (r^2)).continuousAt.tendsto

/-- Theta annihilates the normalized prefix primitive at every center. -/
theorem thetaMean_squarePrefixTrace (t : ℝ) :
    Integrable (fun x => thetaCuspFullSource x*squarePrefixTrace (t+x)) ∧
      (∫ x, thetaCuspFullSource x*squarePrefixTrace (t+x))=0 := by
  obtain ⟨A,hA,h⟩ := kernel_bound
  let G := fun x r : ℝ => phi x*kernel (t+x) r
  let B := A*Real.exp (1/2*|t|)
  have hm : Measurable (Function.uncurry G) :=
    (contDiff_thetaCuspFullSource.continuous.measurable.comp measurable_fst).mul
      ((measurable_snd.pow_const 2).mul (continuous_squareLongTrace.measurable.comp
        ((measurable_const.add measurable_fst).add (measurable_const.mul (Real.measurable_log.comp measurable_snd)))))
  have hi : Integrable (Function.uncurry G) (volume.prod μ) := by
    refine (((HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource (1/2)).const_mul B).mul_prod
      (const_integrable 1)).mono' hm.aestronglyMeasurable ?_
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := (volume : Measure ℝ)) (ν := μ)).ae
      (ae_restrict_mem (μ := volume) measurableSet_Ioc)] with p hp
    change ‖phi p.1*kernel (t+p.1) p.2‖ ≤ (B*(Real.exp (1/2*|p.1|)*phi p.1))*1
    rw [Real.norm_eq_abs,abs_mul,abs_of_pos (thetaCuspFullSource_pos _),mul_one]
    have he := (h _ _ hp).trans (mul_le_mul_of_nonneg_left (exp_abs_add_le (by norm_num : (0:ℝ) ≤ 1/2) t p.1) hA)
    exact (mul_le_mul_of_nonneg_left he (thetaCuspFullSource_pos _).le).trans_eq (by dsimp only [B]; ring)
  have hx (x : ℝ) : (∫ r, G x r ∂μ)=phi x*squarePrefixTrace (t+x) := integral_const_mul _ _
  have hr (r : ℝ) : (∫ x, G x r)=0 := by
    have he (x : ℝ) : G x r=r^2*(phi x*squareLongTrace ((t+2*Real.log r)+x)) := by
      dsimp only [G,kernel]; rw [show t+x+2*Real.log r=(t+2*Real.log r)+x by ring]; ring
    simp_rw [he]
    rw [integral_const_mul,(thetaMean_squareLongTrace _).2,mul_zero]
  refine ⟨hi.integral_prod_left.congr (Eventually.of_forall hx),?_⟩
  have he := integral_integral_swap hi
  simp_rw [hx,hr] at he
  simpa only [integral_zero] using he

/-- Every late logarithmic window contains a point where the signed
normalized integral for the unweighted prefix has absolute value at most one. -/
theorem squarePrefixTrace_bounded_in_every_window : ∀ᶠ T : ℝ in atTop, ∃ u : ℝ,
    |u-T| ≤ 8*Real.log (T+2) ∧ |squarePrefixTrace u| ≤ 1 := by
  obtain ⟨A,hA,h⟩ := prefix_strip_bound
  exact exists_abs_le_one_in_window_of_thetaMean_zero continuous_prefix hA h thetaMean_squarePrefixTrace

#print axioms thetaMean_squarePrefixTrace
#print axioms squarePrefixTrace_bounded_in_every_window

end GaloisForLFunctions.CountingHolography.Sections
