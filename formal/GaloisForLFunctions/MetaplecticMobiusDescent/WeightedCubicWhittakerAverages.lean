/-
Weighted Whittaker averages adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicWhittakerAverages

/-!
# Holomorphic Whittaker averages with arbitrary bounded height weights

A bounded continuous height weight preserves the product-integral
majorants. Rescaling any compact positive height interval into the
fixed cusp region proves holomorphy of its weighted Fourier average
throughout `Re s > 1`.
-/
noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein

lemma weightedWhittakerIntegrand_integrable (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s p) whittakerProductVolume := by
  apply ((whittaker_bound_integrable s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq s)).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s p s.re (by linarith) le_rfl) (norm_nonneg _) (norm_nonneg _))

lemma weightedWhittakerProduct_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := whittakerProductVolume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w p)
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w p)
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrand_continuous freq w)).aestronglyMeasurable))
    (weightedWhittakerIntegrand_integrable ρ freq s hs)
    ((ρ.continuous.comp continuous_fst).mul (whittakerIntegrandDeriv_continuous freq s)).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w p b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ => (whittakerIntegrand_hasDerivAt freq w p).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma weightedWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq s p∂whittakerProductVolume)=
      ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := weightedWhittakerIntegrand_integrable ρ freq s hs
  unfold whittakerProductVolume at hi ⊢
  rw [integral_prod _ hi]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*(hyperbolicKernel s z*tracePhase (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        rw [whittakerIntegrand_eq freq s v hv.1 z]
        ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerAverage_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have he : (fun w => ∫v in Set.Icc (5:ℝ) 6,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v))
      =ᶠ[𝓝 s](fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w p∂whittakerProductVolume) := by
    filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
    exact (weightedWhittakerProduct_eq_average ρ freq w hw).symm
  exact (weightedWhittakerProduct_differentiableAt ρ freq s hs).congr_of_eventuallyEq he
lemma whittaker_bound_integrable_finite («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (b : ℝ) (hb : 1<b) :
    Integrable (fun p : ℝ × ℂ => (1+‖p.2‖^2)^(-b)) («μ».prod volume) := by
  have hk : Integrable (fun z : ℂ => (1+‖z‖^2)^(-b)) := by
    convert (hyperbolicKernel_integrable (b:ℂ) hb).norm using 1
    funext z
    simp only [hyperbolicKernel,Complex.norm_cpow_eq_rpow_re_of_pos
      (by positivity : 0<1+‖z‖^2),Complex.neg_re,Complex.ofReal_re]
  have hv : Integrable (fun _ : ℝ => (1:ℝ)) «μ» := integrable_const _
  simpa only [one_mul] using hv.mul_prod hk

lemma scaledWhittakerIntegrand_integrable («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    Integrable (fun p : ℝ × ℂ => ρ p.1*whittakerIntegrand freq s (c*p.1,p.2)) («μ».prod volume) := by
  apply ((whittaker_bound_integrable_finite «μ» s.re hs).const_mul ‖ρ‖).mono'
  · exact ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrand_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
  · exact Eventually.of_forall (fun p => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrand_norm_bound freq s (c*p.1,p.2) s.re (by linarith) le_rfl)
        (norm_nonneg _) (norm_nonneg _))

lemma scaledWhittakerProduct_differentiableAt («μ» : Measure ℝ) [IsFiniteMeasure «μ»]
    (ρ : BoundedContinuousFunction ℝ ℂ) (c : ℝ) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand freq w (c*p.1,p.2)∂«μ».prod volume) s := by
  let b : ℝ := (s.re+1)/2
  let ε : ℝ := (s.re-1)/4
  have hb : 1<b := by dsimp [b]; linarith
  have hε : 0<ε := by dsimp [ε]; linarith
  have hsb : b+ε<s.re := by dsimp [b,ε]; linarith
  have hU : {w : ℂ | b+ε<w.re}∈𝓝 s :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hsb
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    («μ» := «μ».prod volume)
    (F := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrand freq w (c*p.1,p.2))
    (F' := fun w (p : ℝ × ℂ) => ρ p.1*whittakerIntegrandDeriv freq w (c*p.1,p.2))
    (bound := fun p => ‖ρ‖*(ε⁻¹*(1+‖p.2‖^2)^(-b))) hU
    (Eventually.of_forall (fun w =>
      ((ρ.continuous.comp continuous_fst).mul
        ((whittakerIntegrand_continuous freq w).comp (by fun_prop))).aestronglyMeasurable))
    (scaledWhittakerIntegrand_integrable «μ» ρ c freq s hs)
    ((ρ.continuous.comp continuous_fst).mul
      ((whittakerIntegrandDeriv_continuous freq s).comp (by fun_prop))).aestronglyMeasurable
    (Eventually.of_forall (fun p w hw => by
      rw [norm_mul]
      exact mul_le_mul (ρ.norm_coe_le_norm p.1)
        (whittakerIntegrandDeriv_norm_bound freq w (c*p.1,p.2) b ε (by linarith) hε hw.le)
        (norm_nonneg _) (norm_nonneg _)))
    (((whittaker_bound_integrable_finite «μ» b hb).const_mul ε⁻¹).const_mul ‖ρ‖)
    (Eventually.of_forall (fun p w _ =>
      (whittakerIntegrand_hasDerivAt freq w (c*p.1,p.2)).const_mul (ρ p.1)))
  exact h.2.differentiableAt

lemma whittakerIntegrand_scale (c v : ℝ) (hc : 0<c) (hv : 0<v) (hcv : 5≤c*v)
    (freq s : ℂ) (z : ℂ) :
    (c:ℂ)^(s+1)*whittakerIntegrand (freq/c) s (c*v,z)=
      (v:ℂ)^(-s-1)*(hyperbolicKernel s z*tracePhase (-(freq*v)*z)) := by
  have hcn : (c:ℂ)≠0 := by exact_mod_cast hc.ne'
  rw [whittakerIntegrand_eq (freq/c) s (c*v) hcv z,Complex.ofReal_mul,
    Complex.mul_cpow_ofReal_nonneg hc.le hv.le]
  have he : -(freq/(c:ℂ)*((c:ℂ)*v))*z=-(freq*v)*z := by field_simp
  rw [he]
  have hp : (c:ℂ)^(s+1)*(c:ℂ)^(-s-1)=1 := by
    rw [←Complex.cpow_add _ _ hcn,show s+1+(-s-1)=0 by ring,Complex.cpow_zero]
  calc
    _ = ((c:ℂ)^(s+1)*(c:ℂ)^(-s-1))*
      ((v:ℂ)^(-s-1)*(hyperbolicKernel s z*tracePhase (-(freq*v)*z))) := by ring
    _ = _ := by rw [hp,one_mul]

lemma scaledWhittakerProduct_eq_average (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    ((5/a:ℝ):ℂ)^(s+1)*
      (∫p : ℝ × ℂ,ρ p.1*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*p.1,p.2)
        ∂(volume.restrict (Set.Icc a b)).prod volume)=
      ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-s-1)*sourceFourierKernel s (freq*v) := by
  have hi := scaledWhittakerIntegrand_integrable (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs
  rw [integral_prod _ hi,←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
  have hvp : 0<v := ha.trans_le hv.1
  have hcv : 5≤(5/a)*v := by
    calc
      5=(5/a)*a := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left hv.1 (by positivity)
  rw [←integral_const_mul]
  calc
    _ = ∫z : ℂ,(ρ v*(v:ℂ)^(-s-1))*
        (hyperbolicKernel s z*tracePhase (-(freq*v)*z)) := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun z => by
        dsimp only
        calc
          _ = ρ v*(((5/a:ℝ):ℂ)^(s+1)*whittakerIntegrand (freq/(5/a:ℝ)) s ((5/a)*v,z)) := by ring
          _ = _ := by rw [whittakerIntegrand_scale (5/a) v (by positivity) hvp hcv freq s z]; ring)
    _ = _ := integral_const_mul _ _

theorem cuspWeightedWhittakerInterval_differentiableAt (ρ : BoundedContinuousFunction ℝ ℂ)
    (a b : ℝ) (ha : 0<a) (freq s : ℂ) (hs : 1<s.re) :
    DifferentiableAt ℂ
      (fun w => ∫v in Set.Icc a b,ρ v*(v:ℂ)^(-w-1)*sourceFourierKernel w (freq*v)) s := by
  have hc : ((5/a:ℝ):ℂ)≠0 := by exact_mod_cast (show (5/a:ℝ)≠0 by positivity)
  have hd := ((differentiableAt_id.add_const (1:ℂ)).const_cpow (Or.inl hc)).mul
    (scaledWhittakerProduct_differentiableAt (volume.restrict (Set.Icc a b)) ρ (5/a) (freq/(5/a:ℝ)) s hs)
  apply hd.congr_of_eventuallyEq
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs] with w hw
  exact (scaledWhittakerProduct_eq_average ρ a b ha freq w hw).symm


#print axioms cuspWeightedWhittakerAverage_differentiableAt
#print axioms cuspWeightedWhittakerInterval_differentiableAt
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
