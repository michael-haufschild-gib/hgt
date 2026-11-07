/-
The quotient Dirichlet form is adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothTestsOnTheCubicQuotient
import GaloisForLFunctions.MetaplecticMobiusDescent.HyperbolicActionPreservesEnergy
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-!
# The actual cubic quotient Dirichlet form

Pull smooth tests to upper half-space. The sum of real and imaginary
hyperbolic gradient energies is invariant under the arithmetic kernel, so
it descends to the quotient. Compact support makes the resulting density
integrable. Polarization gives a positive Hermitian Dirichlet form.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

lemma hyperbolicSpatialChart_toHyperbolic (p : EuclideanSpatial) (hp : 0<p 2) :
    hyperbolicSpatialChart (euclideanToHyperbolic p)=p.ofLp :=
  congrArg WithLp.ofLp (hyperbolicEuclideanCoordinates_toHyperbolic p hp)

lemma euclideanToHyperbolic_contMDiffAt (p : EuclideanSpatial) (hp : 0<p 2) :
    ContMDiffAt 𝓘(ℝ,EuclideanSpatial) 𝓘(ℝ,SpatialCoordinates) ∞ euclideanToHyperbolic p := by
  have ht : p.ofLp∈hyperbolicSpatialChart.target := by
    rw [←hyperbolicSpatialChart_toHyperbolic p hp]
    exact hyperbolicSpatialChart.map_source (Set.mem_univ _)
  have hs : ContMDiffOn 𝓘(ℝ,SpatialCoordinates) 𝓘(ℝ,SpatialCoordinates) ∞
      hyperbolicSpatialChart.symm hyperbolicSpatialChart.target := by
    simpa only [hyperbolicSpatial_chartAt] using
      (contMDiffOn_chart_symm (I := 𝓘(ℝ,SpatialCoordinates)) (n := ∞) (x := euclideanToHyperbolic p))
  have hd := (hs.contMDiffAt (hyperbolicSpatialChart.open_target.mem_nhds ht)).comp p
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 3 => ℝ)).contDiff.contDiffAt.contMDiffAt
  apply hd.congr_of_eventuallyEq
  filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
    with q hq
  change euclideanToHyperbolic q=hyperbolicSpatialChart.symm q.ofLp
  rw [←hyperbolicSpatialChart_toHyperbolic q hq,hyperbolicSpatialChart.left_inv (Set.mem_univ _)]

def kernelTestField (f : kernelSmoothTests) (p : EuclideanSpatial) : ℂ :=
  f.1 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p))

lemma kernelTestField_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f) p :=
  (((f.2.1.comp kernelProjection_contMDiff) (euclideanToHyperbolic p)).comp p
    (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt

lemma kernelTestField_re_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).re) p :=
  Complex.reCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_im_contDiffAt (f : kernelSmoothTests) (p : EuclideanSpatial) (hp : 0<p 2) :
    ContDiffAt ℝ ∞ (fun p => (kernelTestField f p).im) p :=
  Complex.imCLM.contDiff.contDiffAt.comp p (kernelTestField_contDiffAt f p hp)

lemma kernelTestField_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (p : EuclideanSpatial) :
    kernelTestField f (euclideanAction (integralComplexMatrix M) p)=kernelTestField f p := by
  simp only [kernelTestField,euclideanAction,euclideanToHyperbolic_coordinates,integralOrbitProjection_eq]

/-- Real and imaginary gradient energies, weighted by squared hyperbolic height. -/
def kernelTestEnergyDensity (f : kernelSmoothTests) (w : HyperbolicSpace) : ℝ :=
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)+
  euclideanScalarDirichletDensity (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)

lemma kernelTestEnergyDensity_nonneg (f : kernelSmoothTests) (w : HyperbolicSpace) :
    0≤kernelTestEnergyDensity f w := by
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  positivity

lemma kernelTestEnergyDensity_invariant (f : kernelSmoothTests) (M : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f (integralComplexMatrix M•w)=kernelTestEnergyDensity f w := by
  have he : hyperbolicEuclideanCoordinates (integralComplexMatrix M•w)=
      euclideanAction (integralComplexMatrix M) (hyperbolicEuclideanCoordinates w) := by
    simp only [euclideanAction,euclideanToHyperbolic_coordinates]
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  unfold kernelTestEnergyDensity
  rw [he]
  congr 1
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_re_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.re (kernelTestField_invariant f M p)
  · apply euclideanScalarDirichletDensity_invariant _ _ _ hp
    · exact (kernelTestField_im_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
    · funext p
      exact congrArg Complex.im (kernelTestField_invariant f M p)

/-- The invariant energy density on the actual quotient. -/
def kernelQuotientEnergyDensity (f : kernelSmoothTests) : KernelQuotient→ℝ :=
  Quotient.lift (kernelTestEnergyDensity f) (by
    intro u v huv
    obtain ⟨M,hM⟩ := huv
    rw [←hM]
    exact (kernelTestEnergyDensity_invariant f M u).symm)

lemma kernelTestEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelTestEnergyDensity f) := by
  rw [continuous_iff_continuousAt]
  intro w
  have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
  have hr := (kernelTestField_re_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have hi := (kernelTestField_im_contDiffAt f _ hp).continuousAt_fderiv (by simp)
  have ht : ContinuousAt (fun p : EuclideanSpatial => p 2) (hyperbolicEuclideanCoordinates w) := by fun_prop
  exact (((ht.pow 2).mul (hr.norm.pow 2)).add ((ht.pow 2).mul (hi.norm.pow 2))).comp
    hyperbolicEuclideanCoordinates_continuous.continuousAt

lemma kernelQuotientEnergyDensity_continuous (f : kernelSmoothTests) : Continuous (kernelQuotientEnergyDensity f) :=
  (kernelTestEnergyDensity_continuous f).quotient_lift _

lemma kernelQuotientEnergyDensity_nonneg (f : kernelSmoothTests) (q : KernelQuotient) :
    0≤kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_nonneg f w

lemma kernelQuotientEnergyDensity_support (f : kernelSmoothTests) :
    Function.support (kernelQuotientEnergyDensity f)⊆tsupport f.1 := by
  intro q hq
  by_contra hn
  have hz : f.1=ᶠ[𝓝 q]0 := notMem_tsupport_iff_eventuallyEq.mp hn
  induction q using Quotient.inductionOn with
  | _ w =>
    have hp : 0<hyperbolicEuclideanCoordinates w 2 := hyperbolicHeight_pos w
    have hc := (continuous_integralOrbitProjection globalKubotaKernel).continuousAt.comp
      (euclideanToHyperbolic_contMDiffAt _ hp).continuousAt
    change Tendsto (integralOrbitProjection globalKubotaKernel ∘ euclideanToHyperbolic)
      (𝓝 (hyperbolicEuclideanCoordinates w))
      (𝓝 (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic (hyperbolicEuclideanCoordinates w)))) at hc
    rw [euclideanToHyperbolic_coordinates] at hc
    have hzF : kernelTestField f=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := hz.comp_tendsto hc
    have hzr : (fun p => (kernelTestField f p).re)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    have hzi : (fun p => (kernelTestField f p).im)=ᶠ[𝓝 (hyperbolicEuclideanCoordinates w)]0 := by
      filter_upwards [hzF] with p hp
      simp [hp]
    apply hq
    change kernelTestEnergyDensity f w=0
    simp only [kernelTestEnergyDensity,euclideanScalarDirichletDensity,hzr.fderiv_eq,hzi.fderiv_eq,
      fderiv_zero,Pi.zero_apply,norm_zero,zero_pow (by decide : 2≠0),mul_zero,add_zero]

lemma kernelQuotientEnergyDensity_hasCompactSupport (f : kernelSmoothTests) :
    HasCompactSupport (kernelQuotientEnergyDensity f) :=
  HasCompactSupport.of_support_subset_isCompact f.2.2 (kernelQuotientEnergyDensity_support f)

lemma kernelQuotientEnergyDensity_integrable (f : kernelSmoothTests) :
    Integrable (kernelQuotientEnergyDensity f) (integralQuotientVolume globalKubotaKernel) :=
  (kernelQuotientEnergyDensity_continuous f).integrable_of_hasCompactSupport
    (kernelQuotientEnergyDensity_hasCompactSupport f)

def kernelDirichletEnergy (f : kernelSmoothTests) : ℝ :=
  ∫q,kernelQuotientEnergyDensity f q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletEnergy_nonneg (f : kernelSmoothTests) : 0≤kernelDirichletEnergy f :=
  integral_nonneg (kernelQuotientEnergyDensity_nonneg f)

def kernelTestPartial (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) : ℂ :=
  fderiv ℝ (kernelTestField f) (hyperbolicEuclideanCoordinates w) (EuclideanSpace.basisFun (Fin 3) ℝ j)

lemma kernelTestPartial_add (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f+g) w j=kernelTestPartial f w j+kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f+g)=kernelTestField f+kernelTestField g := rfl
  rw [he,fderiv_add ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_sub (f g : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (f-g) w j=kernelTestPartial f w j-kernelTestPartial g w j := by
  unfold kernelTestPartial
  have he : kernelTestField (f-g)=kernelTestField f-kernelTestField g := rfl
  rw [he,fderiv_sub ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))
    ((kernelTestField_contDiffAt g _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestPartial_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) (j : Fin 3) :
    kernelTestPartial (c•f) w j=c*kernelTestPartial f w j := by
  unfold kernelTestPartial
  have he : kernelTestField (c•f)=c•kernelTestField f := rfl
  rw [he,fderiv_const_smul ((kernelTestField_contDiffAt f _ (hyperbolicHeight_pos w)).differentiableAt (by simp))]
  rfl

lemma kernelTestEnergyDensity_eq_partials (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w=(hyperbolicHeight w)^2*∑j:Fin 3,‖kernelTestPartial f w j‖^2 := by
  have hd := ((kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)).hasFDerivAt
  have hr := (Complex.reCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  have hi := (Complex.imCLM.hasFDerivAt.comp (hyperbolicEuclideanCoordinates w) hd).fderiv
  change fderiv ℝ (fun p => (kernelTestField f p).re) (hyperbolicEuclideanCoordinates w)=_ at hr
  change fderiv ℝ (fun p => (kernelTestField f p).im) (hyperbolicEuclideanCoordinates w)=_ at hi
  unfold kernelTestEnergyDensity euclideanScalarDirichletDensity
  rw [hr,hi,(EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,
    (EuclideanSpace.basisFun (Fin 3) ℝ).norm_dual,←mul_add,←Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  change (kernelTestPartial f w j).re^2+(kernelTestPartial f w j).im^2=‖kernelTestPartial f w j‖^2
  simpa only [Complex.normSq_apply,pow_two] using Complex.normSq_eq_norm_sq (kernelTestPartial f w j)

lemma kernelTestEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (c•f) w=‖c‖^2*kernelTestEnergyDensity f w := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_smul,norm_mul,mul_pow,←Finset.mul_sum]
  ring

lemma kernelTestEnergyDensity_parallelogram (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (f+g) w+kernelTestEnergyDensity (f-g) w=
      2*(kernelTestEnergyDensity f w+kernelTestEnergyDensity g w) := by
  simp only [kernelTestEnergyDensity_eq_partials,kernelTestPartial_add,kernelTestPartial_sub]
  rw [←mul_add,←Finset.sum_add_distrib]
  simp only [parallelogram_law_with_norm ℂ,←Finset.mul_sum,Finset.sum_add_distrib]
  ring

lemma kernelQuotientEnergyDensity_smul (c : ℂ) (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (c•f) q=‖c‖^2*kernelQuotientEnergyDensity f q := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_smul c f w

lemma kernelQuotientEnergyDensity_parallelogram (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelQuotientEnergyDensity (f+g) q+kernelQuotientEnergyDensity (f-g) q=
      2*(kernelQuotientEnergyDensity f q+kernelQuotientEnergyDensity g q) := by
  induction q using Quotient.inductionOn with
  | _ w => exact kernelTestEnergyDensity_parallelogram f g w

lemma kernelDirichletEnergy_smul (c : ℂ) (f : kernelSmoothTests) :
    kernelDirichletEnergy (c•f)=‖c‖^2*kernelDirichletEnergy f := by
  unfold kernelDirichletEnergy
  simp_rw [kernelQuotientEnergyDensity_smul]
  exact integral_const_mul _ _

lemma kernelDirichletEnergy_parallelogram (f g : kernelSmoothTests) :
    kernelDirichletEnergy (f+g)+kernelDirichletEnergy (f-g)=
      2*(kernelDirichletEnergy f+kernelDirichletEnergy g) := by
  unfold kernelDirichletEnergy
  rw [←integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]
  simp_rw [kernelQuotientEnergyDensity_parallelogram]
  rw [integral_const_mul,integral_add (kernelQuotientEnergyDensity_integrable _) (kernelQuotientEnergyDensity_integrable _)]

open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff Manifold ENNReal MatrixGroups InnerProductSpace

def kernelGradientAt (w : HyperbolicSpace) : kernelSmoothTests→ₗ[ℂ]EuclideanSpace ℂ (Fin 3) where
  toFun f := WithLp.toLp 2 (fun j => (hyperbolicHeight w:ℂ)*kernelTestPartial f w j)
  map_add' f g := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_add,mul_add]
  map_smul' c f := by
    apply (WithLp.equiv 2 (Fin 3→ℂ)).injective
    funext j
    simp [kernelTestPartial_smul,smul_eq_mul,mul_left_comm]

lemma kernelGradientAt_norm_sq (w : HyperbolicSpace) (f : kernelSmoothTests) :
    ‖kernelGradientAt w f‖^2=kernelTestEnergyDensity f w := by
  rw [PiLp.norm_sq_eq_of_L2,kernelTestEnergyDensity_eq_partials]
  change (∑j:Fin 3,‖(hyperbolicHeight w:ℂ)*kernelTestPartial f w j‖^2)=_
  simp only [norm_mul,mul_pow,Complex.norm_real,Real.norm_of_nonneg (hyperbolicHeight_pos w).le,
    Finset.mul_sum]

/-- Polarization of the descended energy density. -/
def kernelDirichletPairDensity (f g : kernelSmoothTests) (q : KernelQuotient) : ℂ :=
  ((kernelQuotientEnergyDensity (f+g) q:ℂ)-(kernelQuotientEnergyDensity (f-g) q:ℂ)+
    ((kernelQuotientEnergyDensity (f-Complex.I•g) q:ℂ)-
      (kernelQuotientEnergyDensity (f+Complex.I•g) q:ℂ))*Complex.I)/4

lemma kernelDirichletPairDensity_coordinate (f g : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)=
      inner ℂ (kernelGradientAt w f) (kernelGradientAt w g) := by
  rw [inner_eq_sum_norm_sq_div_four]
  simp only [←map_add,←map_sub,←map_smul,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
  rfl

lemma kernelDirichletPairDensity_integrable (f g : kernelSmoothTests) :
    Integrable (kernelDirichletPairDensity f g) (integralQuotientVolume globalKubotaKernel) := by
  have hf : ∀h : kernelSmoothTests,Integrable (fun q => (kernelQuotientEnergyDensity h q:ℂ))
      (integralQuotientVolume globalKubotaKernel) := fun h =>
    (kernelQuotientEnergyDensity_integrable h).ofReal
  exact ((hf (f+g)).sub (hf (f-g)) |>.add (((hf (f-Complex.I•g)).sub (hf (f+Complex.I•g))).mul_const _)).div_const _

lemma kernelDirichletPairDensity_add_right (f g h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (g+h) q=kernelDirichletPairDensity f g q+kernelDirichletPairDensity f h q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_add,inner_add_right]

lemma kernelDirichletPairDensity_smul_right (c : ℂ) (f g : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (c•g) q=c*kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w => simp only [←show integralOrbitProjection globalKubotaKernel w=Quotient.mk _ w from rfl,
      kernelDirichletPairDensity_coordinate,map_smul,inner_smul_right]

lemma kernelDirichletPairDensity_conj (f g : kernelSmoothTests) (q : KernelQuotient) :
    star (kernelDirichletPairDensity g f q)=kernelDirichletPairDensity f g q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change star (kernelDirichletPairDensity g f (integralOrbitProjection globalKubotaKernel w))=
      kernelDirichletPairDensity f g (integralOrbitProjection globalKubotaKernel w)
    rw [kernelDirichletPairDensity_coordinate,kernelDirichletPairDensity_coordinate]
    exact inner_conj_symm _ _

lemma kernelDirichletPairDensity_self (f : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f f q=(kernelQuotientEnergyDensity f q:ℂ) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f f (integralOrbitProjection globalKubotaKernel w)=_
    rw [kernelDirichletPairDensity_coordinate,inner_self_eq_norm_sq_to_K,RCLike.ofReal_eq_complex_ofReal,←Complex.ofReal_pow,kernelGradientAt_norm_sq]
    rfl

def kernelDirichletForm (f g : kernelSmoothTests) : ℂ :=
  ∫q,kernelDirichletPairDensity f g q ∂integralQuotientVolume globalKubotaKernel

lemma kernelDirichletForm_add_right (f g h : kernelSmoothTests) :
    kernelDirichletForm f (g+h)=kernelDirichletForm f g+kernelDirichletForm f h := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_add_right]
  exact integral_add (kernelDirichletPairDensity_integrable f g) (kernelDirichletPairDensity_integrable f h)

lemma kernelDirichletForm_smul_right (c : ℂ) (f g : kernelSmoothTests) :
    kernelDirichletForm f (c•g)=c*kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp_rw [kernelDirichletPairDensity_smul_right]
  exact integral_const_mul _ _

lemma kernelDirichletForm_conj (f g : kernelSmoothTests) :
    star (kernelDirichletForm g f)=kernelDirichletForm f g := by
  unfold kernelDirichletForm
  simp only [Complex.star_def]
  rw [←integral_conj]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (kernelDirichletPairDensity_conj f g)

lemma kernelDirichletForm_self (f : kernelSmoothTests) :
    kernelDirichletForm f f=(kernelDirichletEnergy f:ℂ) := by
  unfold kernelDirichletForm kernelDirichletEnergy
  simp_rw [kernelDirichletPairDensity_self]
  exact integral_complex_ofReal

lemma kernelDirichletForm_self_nonneg (f : kernelSmoothTests) : 0≤(kernelDirichletForm f f).re := by
  rw [kernelDirichletForm_self,Complex.ofReal_re]
  exact kernelDirichletEnergy_nonneg f

#print axioms kernelTestEnergyDensity_invariant
#print axioms kernelQuotientEnergyDensity_integrable
#print axioms kernelDirichletForm_add_right
#print axioms kernelDirichletForm_smul_right
#print axioms kernelDirichletForm_conj
#print axioms kernelDirichletForm_self_nonneg
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
