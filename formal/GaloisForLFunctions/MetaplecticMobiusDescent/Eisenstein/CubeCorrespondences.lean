/-
Finite correspondences and cube residues adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.IntegralCoverCorrespondences

/-!
# Finite correspondences and cube residues

Finite correspondence covers `FiniteCorrespondenceCover` extend to the completed energy graph,
have Dirichlet-form adjoints, and commute with the variational resolvent. Cube residues and
the cube average matrix `cubeAverageMatrix` organise the cube cusp data `CubeCuspData`.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix

lemma kernelTestEnergyDensity_eq_cover (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity f w = coverEnergyDensity (kernelTestField f) (hyperbolicEuclideanCoordinates w) := rfl

lemma kernelTestField_comp_contDiffAt (f : kernelSmoothTests) (g : SL(2, ℂ))
    (p : EuclideanSpatial) (hp : 0 < p 2) :
    ContDiffAt ℝ ∞ (kernelTestField f ∘ euclideanAction g) p := by
  have hd := ((((f.2.1.comp kernelProjection_contMDiff).comp (hyperbolicAction_contMDiff g))
    (euclideanToHyperbolic p)).comp p (euclideanToHyperbolic_contMDiffAt p hp)).contDiffAt
  simpa only [Function.comp_def, kernelTestField, euclideanAction, euclideanToHyperbolic_coordinates] using hd

section CorrespondenceEnergy
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

def kernelCorrespondenceMatrix (q : IntegralCoverCosets H globalKubotaKernel) : SL(2, ℂ) :=
  g * integralComplexMatrix (((integralCoverRep H globalKubotaKernel q)⁻¹ : globalKubotaKernel) : SL(2, O))

lemma kernelCorrespondenceTest_field (f : kernelSmoothTests) (p : EuclideanSpatial) :
    kernelTestField (kernelCorrespondenceTest hHK hJK e g he f) p =
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      ∑ q : IntegralCoverCosets H globalKubotaKernel,
        kernelTestField f (euclideanAction (kernelCorrespondenceMatrix g q) p) := by
  letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  change kernelCorrespondenceFunction hJK e g he f.1
    (integralOrbitProjection globalKubotaKernel (euclideanToHyperbolic p)) = _
  rw [kernelCorrespondenceFunction_lift]
  apply Finset.sum_congr rfl
  intro q _
  change f.1 (integralOrbitProjection globalKubotaKernel
    (kernelCorrespondenceMatrix g q • euclideanToHyperbolic p)) =
      f.1 (integralOrbitProjection globalKubotaKernel
        (euclideanToHyperbolic (euclideanAction (kernelCorrespondenceMatrix g q) p)))
  rw [euclideanAction, euclideanToHyperbolic_coordinates]

/-- Cauchy–Schwarz on the finite fiber bounds the energy of a trace. -/
lemma kernelCorrespondenceTest_energyDensity_le (f : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelTestEnergyDensity (kernelCorrespondenceTest hHK hJK e g he f) w ≤
      (H.relIndex globalKubotaKernel : ℝ) *
        (kernelCorrespondenceFunction hJK e g he (fun q => (kernelQuotientEnergyDensity f q : ℂ))
          (integralOrbitProjection globalKubotaKernel w)).re := by
  letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  let p := hyperbolicEuclideanCoordinates w
  let A := kernelCorrespondenceMatrix (H := H) g
  have hd (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f) (euclideanAction (A q) p) :=
    (kernelTestField_contDiffAt f _ (euclideanAction_positive _ _)).differentiableAt (by simp)
  have hc (q : IntegralCoverCosets H globalKubotaKernel) :
      DifferentiableAt ℝ (kernelTestField f ∘ euclideanAction (A q)) p :=
    (kernelTestField_comp_contDiffAt f (A q) p (hyperbolicHeight_pos w)).differentiableAt (by simp)
  have hfield := funext (kernelCorrespondenceTest_field hHK hJK e g he f)
  rw [kernelTestEnergyDensity_eq_cover, hfield]
  change coverEnergyDensity (fun p => ∑ q : IntegralCoverCosets H globalKubotaKernel,
    kernelTestField f (euclideanAction (A q) p)) p ≤ _
  calc
    _ ≤ (Fintype.card (IntegralCoverCosets H globalKubotaKernel) : ℝ) *
        ∑ q : IntegralCoverCosets H globalKubotaKernel,
          coverEnergyDensity (kernelTestField f ∘ euclideanAction (A q)) p := by
      simpa only [Finset.card_univ, Function.comp_def] using
        coverEnergyDensity_sum_le Finset.univ
          (fun q : IntegralCoverCosets H globalKubotaKernel => kernelTestField f ∘ euclideanAction (A q))
          p (fun q _ => hc q)
    _ = _ := by
      have hcard : Fintype.card (IntegralCoverCosets H globalKubotaKernel) = H.relIndex globalKubotaKernel := by
        rw [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]
      rw [hcard, kernelCorrespondenceFunction_lift]
      simp only [Complex.re_sum, Complex.ofReal_re]
      congr 1
      apply Finset.sum_congr rfl
      intro q _
      rw [coverEnergyDensity_comp (A q) _ p (hyperbolicHeight_pos w) (hd q)]
      change coverEnergyDensity (kernelTestField f) (euclideanAction (A q) p) = kernelTestEnergyDensity f (A q • w)
      rw [kernelTestEnergyDensity_eq_cover]
      congr 1
      dsimp [p, euclideanAction]
      rw [euclideanToHyperbolic_coordinates]

lemma kernelCorrespondenceTest_energy_le (f : kernelSmoothTests) :
    kernelDirichletEnergy (kernelCorrespondenceTest hHK hJK e g he f) ≤
      (H.relIndex globalKubotaKernel : ℝ) * (J.relIndex globalKubotaKernel : ℝ) * kernelDirichletEnergy f := by
  let density : KernelQuotient → ℂ := fun q => (kernelQuotientEnergyDensity f q : ℂ)
  have hm : Measurable density := Complex.continuous_ofReal.measurable.comp
    (kernelQuotientEnergyDensity_continuous f).measurable
  have hi : Integrable density (integralQuotientVolume globalKubotaKernel) :=
    (kernelQuotientEnergyDensity_integrable f).ofReal
  have hTi := kernelCorrespondenceFunction_integrable hHK hJK e g he density hm hi
  have hint := kernelCorrespondenceFunction_integral hHK hJK e g he density hm hi
  have hre : (∫ q, (kernelCorrespondenceFunction hJK e g he density q).re
      ∂integralQuotientVolume globalKubotaKernel) =
        (J.relIndex globalKubotaKernel : ℝ) * kernelDirichletEnergy f := by
    have htr := integral_re hTi
    have hdf := integral_re hi
    simp only [RCLike.re_to_complex] at htr hdf
    rw [htr, hint]
    simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    rw [← hdf]
    rfl
  unfold kernelDirichletEnergy
  calc
    _ ≤ ∫ q, (H.relIndex globalKubotaKernel : ℝ) *
        (kernelCorrespondenceFunction hJK e g he density q).re
        ∂integralQuotientVolume globalKubotaKernel := by
      apply integral_mono (kernelQuotientEnergyDensity_integrable _) (hTi.re.const_mul _)
      intro q
      induction q using Quotient.inductionOn with
      | _ w => exact kernelCorrespondenceTest_energyDensity_le hHK hJK e g he f w
    _ = _ := by rw [integral_const_mul, hre]; exact (mul_assoc _ _ _).symm

def kernelCorrespondenceTestLinear : kernelSmoothTests →ₗ[ℂ] kernelSmoothTests where
  toFun := kernelCorrespondenceTest hHK hJK e g he
  map_add' f h := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (f + h).1 (integralOrbitProjection globalKubotaKernel w) =
        kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w) +
        kernelCorrespondenceFunction hJK e g he h.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift, Submodule.coe_add, Pi.add_apply, Finset.sum_add_distrib]
  map_smul' c f := by
    apply Subtype.ext
    funext q
    induction q using Quotient.inductionOn with
    | _ w =>
      letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
      change kernelCorrespondenceFunction hJK e g he (c • f).1 (integralOrbitProjection globalKubotaKernel w) =
        c • kernelCorrespondenceFunction hJK e g he f.1 (integralOrbitProjection globalKubotaKernel w)
      simp only [kernelCorrespondenceFunction_lift, Submodule.coe_smul, Pi.smul_apply, Finset.smul_sum]

lemma kernelCorrespondenceTest_graph_norm (f : kernelSmoothTests) :
    ‖kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f)‖ ≤
      Real.sqrt ((H.relIndex globalKubotaKernel : ℝ) * (J.relIndex globalKubotaKernel : ℝ)) *
        ‖kernelEnergyGraphCore f‖ := by
  have hm := kernelCorrespondenceL2_norm_le hHK hJK e g he (kernelSmoothTestsToL2 f)
  have hs := (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mpr hm
  rw [← kernelCorrespondenceTest_mass hHK hJK e g he, mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))] at hs
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [kernelEnergyGraphCore_norm_sq, mul_pow,
    Real.sq_sqrt (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)), kernelEnergyGraphCore_norm_sq]
  have hE := kernelCorrespondenceTest_energy_le hHK hJK e g he f
  nlinarith only [hs, hE]

/-- The finite correspondence extends continuously to the completed mass-gradient graph. -/
def kernelCorrespondenceEnergy : KernelEnergyGraph →L[ℂ] KernelEnergyGraph :=
  (kernelEnergyGraphCore.comp (kernelCorrespondenceTestLinear hHK hJK e g he)).extendOfNorm kernelEnergyGraphCore

lemma kernelCorrespondenceEnergy_core (f : kernelSmoothTests) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f) =
      kernelEnergyGraphCore (kernelCorrespondenceTest hHK hJK e g he f) :=
  LinearMap.extendOfNorm_eq kernelEnergyGraphCore_dense
    ⟨_, kernelCorrespondenceTest_graph_norm hHK hJK e g he⟩ f

lemma kernelCorrespondenceEnergy_mass (u : KernelEnergyGraph) :
    kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he u) =
      kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass u) := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (kernelEnergyMass.continuous.comp (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    ((kernelCorrespondenceL2 hHK hJK e g he).continuous.comp kernelEnergyMass.continuous) ?_) u
  funext f
  change kernelEnergyMass (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore f)) =
    kernelCorrespondenceL2 hHK hJK e g he (kernelEnergyMass (kernelEnergyGraphCore f))
  rw [kernelCorrespondenceEnergy_core, kernelEnergyMass_core, kernelEnergyMass_core, kernelCorrespondenceTest_mass]

end CorrespondenceEnergy

lemma coverGradientAt_lift_continuous (F : EuclideanSpatial → ℂ)
    (hF : ∀ p, 0 < p 2 → ContDiffAt ℝ ∞ F p) :
    Continuous (fun w : HyperbolicSpace => coverGradientAt F (hyperbolicEuclideanCoordinates w)) := by
  apply (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin 3 => ℂ)).symm.continuous.comp
  apply continuous_pi
  intro j
  apply (Complex.continuous_ofReal.comp hyperbolicHeight_continuous).mul
  rw [continuous_iff_continuousAt]
  intro w
  exact (((hF _ (hyperbolicHeight_pos w)).continuousAt_fderiv (by simp)).clm_apply
    continuousAt_const).comp hyperbolicEuclideanCoordinates_continuous.continuousAt

/-- Mixed Dirichlet density on a common cover. -/
def kernelCorrespondencePairLift (g : SL(2, ℂ)) (f h : kernelSmoothTests) (w : HyperbolicSpace) : ℂ :=
  coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)

lemma kernelCorrespondencePairLift_continuous (g : SL(2, ℂ)) (f h : kernelSmoothTests) :
    Continuous (kernelCorrespondencePairLift g f h) :=
  (coverGradientAt_lift_continuous _ (kernelTestField_contDiffAt f)).inner
    (coverGradientAt_lift_continuous _ (kernelTestField_comp_contDiffAt h g))

section CorrespondencePair
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

include hHK hJK he in
lemma kernelCorrespondencePairLift_invariant (f h : kernelSmoothTests) (k : H) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (k • w) = kernelCorrespondencePairLift g f h w := by
  let A := integralComplexMatrix (k : SL(2, O))
  let B := integralComplexMatrix (e k : SL(2, O))
  have hfi : kernelTestField f ∘ euclideanAction A = kernelTestField f :=
    funext (kernelTestField_invariant f ⟨(k : SL(2, O)), hHK k.property⟩)
  have hhi : (kernelTestField h ∘ euclideanAction g) ∘ euclideanAction A =
      kernelTestField h ∘ euclideanAction g := by
    rw [Function.comp_assoc, ← euclideanAction_mul, he k, euclideanAction_mul, ← Function.comp_assoc]
    have hh : kernelTestField h ∘ euclideanAction B = kernelTestField h :=
      funext (kernelTestField_invariant h ⟨(e k : SL(2, O)), hJK (e k).property⟩)
    rw [hh]
  have hh := coverDirichletPair_comp A (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)
    ((kernelTestField_contDiffAt f _ (euclideanAction_positive A _)).differentiableAt (by simp))
    ((kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive A _)).differentiableAt (by simp))
  rw [hfi, hhi] at hh
  change _ = coverDirichletPair (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
    (hyperbolicEuclideanCoordinates w)
  rw [integralSubgroup_smul]
  simpa only [kernelCorrespondencePairLift, A, euclideanAction, euclideanToHyperbolic_coordinates] using hh.symm

def kernelCorrespondencePair (f h : kernelSmoothTests) : IntegralOrbitQuotient H → ℂ :=
  Quotient.lift (kernelCorrespondencePairLift g f h) (by
    rintro w v ⟨k, rfl⟩
    exact (kernelCorrespondencePairLift_invariant hHK hJK e g he f h k w).symm)

lemma kernelCorrespondencePair_projection (f h : kernelSmoothTests) (w : HyperbolicSpace) :
    kernelCorrespondencePair hHK hJK e g he f h (integralOrbitProjection H w) =
      kernelCorrespondencePairLift g f h w := rfl

lemma kernelCorrespondencePair_measurable (f h : kernelSmoothTests) :
    Measurable (kernelCorrespondencePair hHK hJK e g he f h) :=
  measurable_from_quotient.mpr (kernelCorrespondencePairLift_continuous g f h).measurable

lemma kernelCorrespondencePair_norm_le (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    ‖kernelCorrespondencePair hHK hJK e g he f h q‖ ≤
      (kernelQuotientEnergyDensity f (integralCoverMap hHK q) +
        kernelQuotientEnergyDensity h (integralCoverMap hJK (integralConjugateMap e g he q))) / 2 := by
  induction q using Quotient.inductionOn with
  | _ w =>
    have hf := (kernelTestField_contDiffAt f (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt h g (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hb := coverDirichletPair_norm_le (kernelTestField f) (kernelTestField h ∘ euclideanAction g)
      (hyperbolicEuclideanCoordinates w) hf hh
    rw [coverEnergyDensity_comp g _ _ (hyperbolicHeight_pos w)
      ((kernelTestField_contDiffAt h _ (euclideanAction_positive g _)).differentiableAt (by simp))] at hb
    change ‖kernelCorrespondencePairLift g f h w‖ ≤ (kernelTestEnergyDensity f w + kernelTestEnergyDensity h (g • w)) / 2
    simpa only [kernelCorrespondencePairLift, kernelTestEnergyDensity_eq_cover, euclideanAction,
      euclideanToHyperbolic_coordinates] using hb

variable [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]

lemma kernelCorrespondencePair_integrable (f h : kernelSmoothTests) :
    Integrable (kernelCorrespondencePair hHK hJK e g he f h) (integralQuotientVolume H) := by
  have hf := (integralCoverMap_measurePreserving hHK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable f).smul_measure (c := (H.relIndex globalKubotaKernel : ℝ≥0∞)) (by simp))
  have hh := (integralCoverMap_measurePreserving hJK globalKubotaKernel_le_levelThree).integrable_comp_of_integrable
    ((kernelQuotientEnergyDensity_integrable h).smul_measure (c := (J.relIndex globalKubotaKernel : ℝ≥0∞)) (by simp))
  have hhh := (integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).integrable_comp_of_integrable hh
  apply ((hf.add hhh).div_const 2).mono' (kernelCorrespondencePair_measurable hHK hJK e g he f h).aestronglyMeasurable
  exact Filter.Eventually.of_forall (kernelCorrespondencePair_norm_le hHK hJK e g he f h)

end CorrespondencePair

lemma kernelCorrespondencePairLift_kernel (g : SL(2, ℂ)) (f h : kernelSmoothTests)
    (r : globalKubotaKernel) (w : HyperbolicSpace) :
    kernelCorrespondencePairLift g f h (r • w) =
      coverDirichletPair (kernelTestField f)
        (kernelTestField h ∘ euclideanAction (g * integralComplexMatrix (r : SL(2, O))))
        (hyperbolicEuclideanCoordinates w) := by
  have hf := (kernelTestField_contDiffAt f _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hh := (kernelTestField_comp_contDiffAt h g _ (euclideanAction_positive (integralComplexMatrix r) (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
  have hp := coverDirichletPair_comp (integralComplexMatrix r) (kernelTestField f)
    (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
  have hfi : kernelTestField f ∘ euclideanAction (integralComplexMatrix r) = kernelTestField f :=
    funext (kernelTestField_invariant f r)
  rw [hfi, Function.comp_assoc, ← euclideanAction_mul] at hp
  simpa only [kernelCorrespondencePairLift, integralSubgroup_smul, euclideanAction,
    euclideanToHyperbolic_coordinates] using hp.symm

lemma kernelTestField_comp_inverse (f : kernelSmoothTests) (g : SL(2, ℂ)) :
    (kernelTestField f ∘ euclideanAction g⁻¹) ∘ euclideanAction g = kernelTestField f := by
  funext p
  simp only [Function.comp_def, kernelTestField, euclideanAction, euclideanToHyperbolic_coordinates, inv_smul_smul]

section CorrespondenceForm
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondencePair_trace (f h : kernelSmoothTests) (q : KernelQuotient) :
    kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h) q =
      integralCoverTraceFunction H globalKubotaKernel (kernelCorrespondencePair hHK hJK e g he f h) q := by
  letI : Fintype (IntegralCoverCosets H globalKubotaKernel) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelDirichletPairDensity f (kernelCorrespondenceTest hHK hJK e g he h)
      (integralOrbitProjection globalKubotaKernel w) = _
    rw [kernelDirichletPairDensity_eq_cover, funext (kernelCorrespondenceTest_field hHK hJK e g he h)]
    have hd (r : IntegralCoverCosets H globalKubotaKernel) :
        DifferentiableAt ℝ (kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
          (hyperbolicEuclideanCoordinates w) :=
      (kernelTestField_comp_contDiffAt h _ _ (hyperbolicHeight_pos w)).differentiableAt (by simp)
    have hsum := coverDirichletPair_sum_right Finset.univ (kernelTestField f)
      (fun r => kernelTestField h ∘ euclideanAction (kernelCorrespondenceMatrix g r))
      (hyperbolicEuclideanCoordinates w) (fun r _ => hd r)
    simp only [Function.comp_apply] at hsum
    rw [hsum]
    change (∑ r : IntegralCoverCosets H globalKubotaKernel, _) =
      ∑ r : IntegralCoverCosets H globalKubotaKernel,
        kernelCorrespondencePair hHK hJK e g he f h (integralCoverFiberPoint H globalKubotaKernel r w)
    apply Finset.sum_congr rfl
    intro r _
    rw [integralCoverFiberPoint_rep, kernelCorrespondencePair_projection, kernelCorrespondencePairLift_kernel]
    rfl

lemma kernelCorrespondenceForm_integral (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h) =
      ∫ q, kernelCorrespondencePair hHK hJK e g he f h q ∂integralQuotientVolume H := by
  unfold kernelDirichletForm
  simp_rw [kernelCorrespondencePair_trace]
  exact integralCoverTraceFunction_integral hHK globalKubotaKernel_le_levelThree _
    (kernelCorrespondencePair_measurable hHK hJK e g he f h)
    (kernelCorrespondencePair_integrable hHK hJK e g he f h)

omit [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel] in
lemma kernelCorrespondencePair_conjugate (f h : kernelSmoothTests) (q : IntegralOrbitQuotient H) :
    kernelCorrespondencePair hHK hJK e g he f h q =
      star (kernelCorrespondencePair hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) h f
        (integralConjugateMap e g he q)) := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change kernelCorrespondencePairLift g f h w = star (kernelCorrespondencePairLift g⁻¹ h f (g • w))
    have hf := (kernelTestField_contDiffAt h _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hh := (kernelTestField_comp_contDiffAt f g⁻¹ _ (euclideanAction_positive g (hyperbolicEuclideanCoordinates w))).differentiableAt (by simp)
    have hc := coverDirichletPair_comp g (kernelTestField h) (kernelTestField f ∘ euclideanAction g⁻¹)
      (hyperbolicEuclideanCoordinates w) (hyperbolicHeight_pos w) hf hh
    rw [kernelTestField_comp_inverse] at hc
    have hs := congrArg star hc
    have hswap : star (inner ℂ
        (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w))
        (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))) =
        inner ℂ (coverGradientAt (kernelTestField f) (hyperbolicEuclideanCoordinates w))
          (coverGradientAt (kernelTestField h ∘ euclideanAction g) (hyperbolicEuclideanCoordinates w)) := inner_conj_symm _ _
    rw [coverDirichletPair, hswap] at hs
    simpa only [kernelCorrespondencePairLift, coverDirichletPair, euclideanAction, euclideanToHyperbolic_coordinates] using hs

/-- Reversing the finite correspondence gives its Dirichlet-form adjoint. -/
theorem kernelCorrespondenceForm_adjoint (f h : kernelSmoothTests) :
    kernelDirichletForm f (kernelCorrespondenceTest hHK hJK e g he h) =
      kernelDirichletForm (kernelCorrespondenceTest hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) f) h := by
  let opposite := kernelCorrespondencePair hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) h f
  have hom := kernelCorrespondencePair_measurable hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) h f
  have hm := integralConjugateMap_measurePreserving e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)
  rw [kernelCorrespondenceForm_integral]
  calc
    _ = ∫ q, star (opposite (integralConjugateMap e g he q)) ∂integralQuotientVolume H :=
      integral_congr_ae (Filter.Eventually.of_forall (kernelCorrespondencePair_conjugate hHK hJK e g he f h))
    _ = ∫ q, star (opposite q) ∂integralQuotientVolume J := by
      have hh := integral_map (μ := integralQuotientVolume H) hm.measurable.aemeasurable
        (continuous_star.measurable.comp hom).aestronglyMeasurable
      rw [hm.map_eq] at hh
      exact hh.symm
    _ = star (∫ q, opposite q ∂integralQuotientVolume J) := by
      simp only [Complex.star_def]
      exact integral_conj
    _ = _ := by
      rw [← kernelCorrespondenceForm_integral hJK hHK e.symm g⁻¹
        (integralCoverIntertwines_inverse e g he), kernelDirichletForm_conj]

end CorrespondenceForm

section CorrespondenceLaplacian
variable {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel)
    [H.IsFiniteRelIndex globalKubotaKernel] [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)

lemma kernelCorrespondenceL2_pairing_right (F G : KernelQuotientL2) :
    inner ℂ F (kernelCorrespondenceL2 hHK hJK e g he G) =
      inner ℂ (kernelCorrespondenceL2 hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) F) G := by
  have hh := congrArg star (kernelCorrespondenceL2_pairing hHK hJK e g he G F)
  simpa only [← starRingEnd_apply, inner_conj_symm] using hh

lemma kernelCorrespondenceEnergy_pairing_core (f h : kernelSmoothTests) :
    inner ℂ (kernelEnergyGraphCore f) (kernelCorrespondenceEnergy hHK hJK e g he (kernelEnergyGraphCore h)) =
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he)
        (kernelEnergyGraphCore f)) (kernelEnergyGraphCore h) := by
  rw [kernelCorrespondenceEnergy_core, kernelCorrespondenceEnergy_core,
    kernelEnergyGraph_inner, kernelEnergyGraph_inner]
  simp only [kernelEnergyMass_core, kernelEnergyGradient_core, kernelGradientToL2_inner]
  rw [kernelCorrespondenceTest_mass, kernelCorrespondenceTest_mass,
    kernelCorrespondenceL2_pairing_right, kernelCorrespondenceForm_adjoint]

theorem kernelCorrespondenceEnergy_pairing (u v : KernelEnergyGraph) :
    inner ℂ u (kernelCorrespondenceEnergy hHK hJK e g he v) =
      inner ℂ (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) u) v := by
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_id.inner continuous_const)
    ((kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹
      (integralCoverIntertwines_inverse e g he)).continuous.inner continuous_const) ?_) u
  funext f
  apply congrFun (kernelEnergyGraphCore_dense.equalizer
    (continuous_const.inner (kernelCorrespondenceEnergy hHK hJK e g he).continuous)
    (continuous_const.inner continuous_id) ?_) v
  funext h
  exact kernelCorrespondenceEnergy_pairing_core hHK hJK e g he f h

lemma kernelCorrespondenceEnergy_pairing_left (u v : KernelEnergyGraph) :
    inner ℂ (kernelCorrespondenceEnergy hHK hJK e g he u) v =
      inner ℂ u (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) v) := by
  calc
    _ = star (inner ℂ v (kernelCorrespondenceEnergy hHK hJK e g he u)) :=
      (inner_conj_symm (𝕜 := ℂ) (kernelCorrespondenceEnergy hHK hJK e g he u) v).symm
    _ = star (inner ℂ
        (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) v) u) :=
      congrArg star (kernelCorrespondenceEnergy_pairing hHK hJK e g he v u)
    _ = _ := inner_conj_symm (𝕜 := ℂ) u
      (kernelCorrespondenceEnergy hJK hHK e.symm g⁻¹ (integralCoverIntertwines_inverse e g he) v)

theorem kernelCorrespondence_variationalSolution (F : KernelQuotientL2) :
    kernelCorrespondenceEnergy hHK hJK e g he (kernelVariationalSolution F) =
      kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F) := by
  apply kernelVariationalSolution_unique
  intro v
  rw [← kernelEnergyGraph_inner, kernelCorrespondenceEnergy_pairing_left,
    kernelEnergyGraph_inner, kernelVariationalSolution_equation, kernelCorrespondenceEnergy_mass]
  exact (kernelCorrespondenceL2_pairing hHK hJK e g he F (kernelEnergyMass v)).symm

/-- Finite geometric correspondences commute with the variational resolvent. -/
theorem kernelCorrespondence_variationalResolvent (F : KernelQuotientL2) :
    kernelVariationalResolvent (kernelCorrespondenceL2 hHK hJK e g he F) =
      kernelCorrespondenceL2 hHK hJK e g he (kernelVariationalResolvent F) := by
  change kernelEnergyMass (kernelVariationalSolution (kernelCorrespondenceL2 hHK hJK e g he F)) = _
  rw [← kernelCorrespondence_variationalSolution, kernelCorrespondenceEnergy_mass]
  rfl

theorem kernelCorrespondence_operatorGraph (F G : KernelQuotientL2)
    (hFG : (F, G) ∈ kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F, kernelCorrespondenceL2 hHK hJK e g he G) ∈ kernelEnergyLaplacian.graph := by
  rw [kernelEnergyLaplacian_graph, mem_kernelLaplacianGraph] at hFG ⊢
  rw [← map_add, kernelCorrespondence_variationalResolvent, hFG]

theorem kernelCorrespondence_eigenvector (F : KernelQuotientL2) (eigenvalue : ℂ)
    (hF : (F, eigenvalue • F) ∈ kernelEnergyLaplacian.graph) :
    (kernelCorrespondenceL2 hHK hJK e g he F,
      eigenvalue • kernelCorrespondenceL2 hHK hJK e g he F) ∈ kernelEnergyLaplacian.graph := by
  simpa only [map_smul] using kernelCorrespondence_operatorGraph hHK hJK e g he F (eigenvalue • F) hF

end CorrespondenceLaplacian

lemma integralCoverIntertwines_trans {H J K : Subgroup (SL(2, O))}
    (e : H ≃* J) (f : J ≃* K) (g h : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) :
    IntegralCoverIntertwines (e.trans f) (h * g) := by
  intro k
  change (h * g) * integralComplexMatrix (k : SL(2, O)) =
    integralComplexMatrix (f (e k) : SL(2, O)) * (h * g)
  rw [mul_assoc, he k, ← mul_assoc, hf (e k), mul_assoc]

lemma integralConjugateMap_trans {H J K : Subgroup (SL(2, O))}
    (e : H ≃* J) (f : J ≃* K) (g h : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h) (q : IntegralOrbitQuotient H) :
    integralConjugateMap f h hf (integralConjugateMap e g he q) =
      integralConjugateMap (e.trans f) (h * g) (integralCoverIntertwines_trans e f g h he hf) q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection K (h • (g • w)) = integralOrbitProjection K ((h * g) • w)
    rw [mul_smul]

lemma integralConjugatePullback_trans {H J K : Subgroup (SL(2, O))}
    (e : H ≃* J) (f : J ≃* K) (g h : SL(2, ℂ))
    (he : IntegralCoverIntertwines e g) (hf : IntegralCoverIntertwines f h)
    (hH : H ≤ levelThree) (hJ : J ≤ levelThree) (hK : K ≤ levelThree) (F : IntegralQuotientL2 K) :
    integralConjugatePullback e g he hH hJ (integralConjugatePullback f h hf hJ hK F) =
      integralConjugatePullback (e.trans f) (h * g) (integralCoverIntertwines_trans e f g h he hf) hH hK F := by
  apply Lp.ext
  have hinner := (integralConjugateMap_measurePreserving e g he hH hJ).quasiMeasurePreserving.ae_eq_comp
    (integralConjugatePullback_ae f h hf hJ hK F)
  filter_upwards [integralConjugatePullback_ae e g he hH hJ _, hinner,
    integralConjugatePullback_ae (e.trans f) (h * g) (integralCoverIntertwines_trans e f g h he hf) hH hK F] with q ho hi ht
  dsimp only [Function.comp_def] at hi
  rw [ho, hi, ht, integralConjugateMap_trans]

lemma kernelCoverLeg_representative {H J : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hJK : J ≤ globalKubotaKernel) [J.IsFiniteRelIndex globalKubotaKernel]
    (e : H ≃* J) (g : SL(2, ℂ)) (he : IntegralCoverIntertwines e g)
    (F : KernelQuotientL2) (f : KernelQuotient → ℂ)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f) :
    kernelCoverLeg hHK hJK e g he F =ᵐ[integralQuotientVolume H]
      fun q => f (integralCoverMap hJK (integralConjugateMap e g he q)) := by
  have hc := (integralCoverPullback_ae hJK globalKubotaKernel_le_levelThree F).trans
    ((integralCoverMap_quasiMeasurePreserving hJK globalKubotaKernel_le_levelThree).ae_eq_comp hrep)
  exact (integralConjugatePullback_ae e g he
    (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree) _).trans
    ((integralConjugateMap_measurePreserving e g he
      (hHK.trans globalKubotaKernel_le_levelThree) (hJK.trans globalKubotaKernel_le_levelThree)).quasiMeasurePreserving.ae_eq_comp hc)

/-- Two legs on a common cover compose to a correspondence on the base quotient. -/
theorem kernelCoverLeg_adjoint_comp {H Ji Jj : Subgroup (SL(2, O))}
    (hHK : H ≤ globalKubotaKernel) (hiK : Ji ≤ globalKubotaKernel) (hjK : Jj ≤ globalKubotaKernel)
    [Ji.IsFiniteRelIndex globalKubotaKernel] [Jj.IsFiniteRelIndex globalKubotaKernel]
    (ei : H ≃* Ji) (ej : H ≃* Jj) (gi gj : SL(2, ℂ))
    (hei : IntegralCoverIntertwines ei gi) (hej : IntegralCoverIntertwines ej gj) :
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej)).comp (kernelCoverLeg hHK hiK ei gi hei) =
      kernelCorrespondenceL2 hjK hiK (ej.symm.trans ei) (gi * gj⁻¹)
        (integralCoverIntertwines_trans ej.symm ei gj⁻¹ gi (integralCoverIntertwines_inverse ej gj hej) hei) := by
  apply ContinuousLinearMap.ext
  intro F
  change ContinuousLinearMap.adjoint (kernelCoverLeg hHK hjK ej gj hej) (kernelCoverLeg hHK hiK ei gi hei F) = _
  rw [kernelCoverLeg_adjoint]
  change integralCoverTrace hjK globalKubotaKernel_le_levelThree
    (integralConjugatePullback ej.symm gj⁻¹ (integralCoverIntertwines_inverse ej gj hej)
      (hjK.trans globalKubotaKernel_le_levelThree) (hHK.trans globalKubotaKernel_le_levelThree)
      (integralConjugatePullback ei gi hei
        (hHK.trans globalKubotaKernel_le_levelThree) (hiK.trans globalKubotaKernel_le_levelThree)
        (integralCoverPullback hiK globalKubotaKernel_le_levelThree F))) = _
  rw [integralConjugatePullback_trans]
  rfl

theorem kernelCoverLeg_adjoint_sum_eigenvector
    {H : Subgroup (SL(2, O))} {ι : Type*} [Fintype ι]
    (J : ι → Subgroup (SL(2, O))) (hHK : H ≤ globalKubotaKernel) (hJK : ∀ i, J i ≤ globalKubotaKernel)
    [∀ i, (J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀ i, H ≃* J i) (g : ι → SL(2, ℂ)) (he : ∀ i, IntegralCoverIntertwines (e i) (g i))
    (F : KernelQuotientL2) (eigenvalue : ℂ) (hF : (F, eigenvalue • F) ∈ kernelEnergyLaplacian.graph)
    (c : ι → ℂ) (j : ι) :
    let D := ∑ i, c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F
    (ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D,
      eigenvalue • ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)) D) ∈ kernelEnergyLaplacian.graph := by
  let traced (i : ι) := ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))
    (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i) F)
  have hi (i : ι) : (traced i, eigenvalue • traced i) ∈ kernelEnergyLaplacian.graph := by
    change (((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F,
      eigenvalue • ((ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK j) (e j) (g j) (he j))).comp
      (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))) F) ∈ kernelEnergyLaplacian.graph
    rw [kernelCoverLeg_adjoint_comp]
    exact kernelCorrespondence_eigenvector _ _ _ _ _ F eigenvalue hF
  have hsum : (∑ i, c i • (traced i, eigenvalue • traced i)) ∈ kernelEnergyLaplacian.graph :=
    kernelEnergyLaplacian.graph.sum_mem (fun i _ => kernelEnergyLaplacian.graph.smul_mem (c i) (hi i))
  have hEq : (∑ i, c i • (traced i, eigenvalue • traced i)) =
      (∑ i, c i • traced i, eigenvalue • ∑ i, c i • traced i) := by
    apply Prod.ext <;> simp only [Prod.fst_sum, Prod.snd_sum, Prod.smul_fst, Prod.smul_snd,
      Finset.smul_sum, smul_smul, mul_comm]
  rw [hEq] at hsum
  simpa only [map_sum, map_smul] using hsum

/-- A nonzero integral diagonal matrix defines a correspondence before imposing a character kernel. -/
def integralDiagonalCorrespondence (d : O) : Subgroup (SL(2, O) × SL(2, O)) where
  carrier := {MN | (!![d, 0; 0, 1] : Matrix (Fin 2) (Fin 2) O) * MN.1.val =
    MN.2.val * !![d, 0; 0, 1]}
  one_mem' := by simp
  mul_mem' := by
    rintro ⟨M, N⟩ ⟨M', N'⟩ h h'
    change !![d, 0; 0, 1] * (M.val * M'.val) = (N.val * N'.val) * !![d, 0; 0, 1]
    rw [← Matrix.mul_assoc, h, Matrix.mul_assoc, h', ← Matrix.mul_assoc]
  inv_mem' := by
    rintro ⟨M, N⟩ h
    change !![d, 0; 0, 1] * (M⁻¹).val = (N⁻¹).val * !![d, 0; 0, 1]
    calc
      _ = ((N⁻¹).val * (N.val * !![d, 0; 0, 1])) * (M⁻¹).val := by
        simp only [← Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mul]
      _ = ((N⁻¹).val * (!![d, 0; 0, 1] * M.val)) * (M⁻¹).val := by rw [h]
      _ = _ := by
        simp only [Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul,
          mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

def integralDiagonalLeft (d : O) : integralDiagonalCorrespondence d →* SL(2, O) :=
  (MonoidHom.fst _ _).comp (integralDiagonalCorrespondence d).subtype

def integralDiagonalRight (d : O) : integralDiagonalCorrespondence d →* SL(2, O) :=
  (MonoidHom.snd _ _).comp (integralDiagonalCorrespondence d).subtype

lemma integralDiagonal_entries (d : O) (MN : integralDiagonalCorrespondence d) :
    d * MN.1.1 0 0 = MN.1.2 0 0 * d ∧ d * MN.1.1 0 1 = MN.1.2 0 1 ∧
      MN.1.1 1 0 = MN.1.2 1 0 * d ∧ MN.1.1 1 1 = MN.1.2 1 1 := by
  have h := MN.property
  have h00 := congrArg (fun A : Matrix (Fin 2) (Fin 2) O => A 0 0) h
  have h01 := congrArg (fun A : Matrix (Fin 2) (Fin 2) O => A 0 1) h
  have h10 := congrArg (fun A : Matrix (Fin 2) (Fin 2) O => A 1 0) h
  have h11 := congrArg (fun A : Matrix (Fin 2) (Fin 2) O => A 1 1) h
  norm_num [Matrix.mul_apply, Fin.sum_univ_two] at h00 h01 h10 h11
  exact ⟨h00, h01, h10, h11⟩

lemma integralDiagonalLeft_injective (d : O) (hd : d ≠ 0) : Function.Injective (integralDiagonalLeft d) := by
  intro x y h
  have hx := integralDiagonal_entries d x
  have hy := integralDiagonal_entries d y
  have hM : x.1.1 = y.1.1 := h
  apply Subtype.ext
  refine Prod.ext hM ?_
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_right_cancel₀ hd (hx.1.symm.trans (by rw [hM]; exact hy.1))
  · exact hx.2.1.symm.trans (by rw [hM]; exact hy.2.1)
  · exact mul_right_cancel₀ hd (hx.2.2.1.symm.trans (by rw [hM]; exact hy.2.2.1))
  · exact hx.2.2.2.symm.trans (by rw [hM]; exact hy.2.2.2)

lemma integralDiagonalRight_injective (d : O) (hd : d ≠ 0) : Function.Injective (integralDiagonalRight d) := by
  intro x y h
  have hx := integralDiagonal_entries d x
  have hy := integralDiagonal_entries d y
  have hN : x.1.2 = y.1.2 := h
  apply Subtype.ext
  refine Prod.ext ?_ hN
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact mul_left_cancel₀ hd (hx.1.trans (by rw [hN]; exact hy.1.symm))
  · exact mul_left_cancel₀ hd (hx.2.1.trans (by rw [hN]; exact hy.2.1.symm))
  · exact hx.2.2.1.trans (by rw [hN]; exact hy.2.2.1.symm)
  · exact hx.2.2.2.trans (by rw [hN]; exact hy.2.2.2.symm)

def integralPrincipalLevel (d : O) : Subgroup (SL(2, O)) :=
  (Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {d}))).ker

lemma integralPrincipalLevel_entry (d : O) (M : integralPrincipalLevel d) (i j : Fin 2) :
    d ∣ (M : SL(2, O)) i j - (if i = j then 1 else 0) := by
  have hm : Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {d})) (M : SL(2, O)) = 1 := M.property
  have h := congrArg (fun N : SL(2, O ⧸ Ideal.span {d}) => N i j) hm
  change Ideal.Quotient.mk (Ideal.span {d}) ((M : SL(2, O)) i j) =
    (1 : Matrix (Fin 2) (Fin 2) (O ⧸ Ideal.span {d})) i j at h
  apply Ideal.mem_span_singleton.mp
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp
  simpa only [Matrix.one_apply, apply_ite, map_one, map_zero] using h

lemma integralPrincipalLevel_finiteIndex (d : O) (hd : d ≠ 0) : (integralPrincipalLevel d).FiniteIndex := by
  letI : Finite (O ⧸ Ideal.span {d}) := (Ideal.span {d}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr hd)
  unfold integralPrincipalLevel
  infer_instance

lemma integralPrincipalLevel_le_diagonalLeft (d : O) : integralPrincipalLevel d ≤ (integralDiagonalLeft d).range := by
  intro M hM
  obtain ⟨c, hc⟩ : d ∣ M 1 0 := by simpa using integralPrincipalLevel_entry d ⟨M, hM⟩ 1 0
  let N : SL(2, O) := ⟨!![M 0 0, d * M 0 1; c, M 1 1], by
    have hdet := M.property
    rw [Matrix.det_fin_two, hc] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  refine ⟨⟨(M, N), ?_⟩, rfl⟩
  change !![d, 0; 0, 1] * M.val = N.val * !![d, 0; 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [N, Matrix.mul_apply, Fin.sum_univ_two, hc, mul_comm]

lemma integralPrincipalLevel_le_diagonalRight (d : O) : integralPrincipalLevel d ≤ (integralDiagonalRight d).range := by
  intro N hN
  obtain ⟨b, hb⟩ : d ∣ N 0 1 := by simpa using integralPrincipalLevel_entry d ⟨N, hN⟩ 0 1
  let M : SL(2, O) := ⟨!![N 0 0, b; d * N 1 0, N 1 1], by
    have hdet := N.property
    rw [Matrix.det_fin_two, hb] at hdet
    rw [Matrix.det_fin_two_of]
    linear_combination hdet⟩
  refine ⟨⟨(M, N), ?_⟩, rfl⟩
  change !![d, 0; 0, 1] * M.val = N.val * !![d, 0; 0, 1]
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j <;> simp [M, Matrix.mul_apply, Fin.sum_univ_two, hb, mul_comm]

lemma integralDiagonal_finite_covers (d : O) (hd : d ≠ 0) :
    (integralDiagonalLeft d).range.FiniteIndex ∧ (integralDiagonalRight d).range.FiniteIndex := by
  letI := integralPrincipalLevel_finiteIndex d hd
  exact ⟨Subgroup.finiteIndex_of_le (integralPrincipalLevel_le_diagonalLeft d),
    Subgroup.finiteIndex_of_le (integralPrincipalLevel_le_diagonalRight d)⟩

lemma finiteIndex_preimage {G G' : Type*} [Group G] [Group G']
    (K : Subgroup G') [K.FiniteIndex] (f : G →* G') : (K.comap f).FiniteIndex := by
  constructor
  rw [Subgroup.index_comap]
  exact fun h => (Subgroup.FiniteIndex.index_ne_zero (H := K)) (K.index_eq_zero_of_relIndex_eq_zero h)

lemma finiteIndex_image {G G' : Type*} [Group G] [Group G']
    (H : Subgroup G) [H.FiniteIndex] (f : G →* G') (hf : Function.Injective f)
    [f.range.FiniteIndex] : (H.map f).FiniteIndex := by
  constructor
  rw [Subgroup.index_map_of_injective _ hf]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := H))
    (Subgroup.FiniteIndex.index_ne_zero (H := f.range))

/-- Restrict both sides to the actual multiplier kernel. Both restrictions retain finite index. -/
def integralDiagonalKernel (d : O) : Subgroup (integralDiagonalCorrespondence d) :=
  globalKubotaKernel.comap (integralDiagonalLeft d) ⊓ globalKubotaKernel.comap (integralDiagonalRight d)

def integralDiagonalKernelLeft (d : O) : integralDiagonalKernel d →* SL(2, O) :=
  (integralDiagonalLeft d).comp (integralDiagonalKernel d).subtype

def integralDiagonalKernelRight (d : O) : integralDiagonalKernel d →* SL(2, O) :=
  (integralDiagonalRight d).comp (integralDiagonalKernel d).subtype

lemma integralDiagonalKernelLeft_le (d : O) : (integralDiagonalKernelLeft d).range ≤ globalKubotaKernel := by
  rintro M ⟨x, rfl⟩
  exact x.property.1

lemma integralDiagonalKernelRight_le (d : O) : (integralDiagonalKernelRight d).range ≤ globalKubotaKernel := by
  rintro M ⟨x, rfl⟩
  exact x.property.2

lemma integralDiagonalKernelLeft_injective (d : O) (hd : d ≠ 0) : Function.Injective (integralDiagonalKernelLeft d) :=
  (integralDiagonalLeft_injective d hd).comp (integralDiagonalKernel d).subtype_injective

lemma integralDiagonalKernelRight_injective (d : O) (hd : d ≠ 0) : Function.Injective (integralDiagonalKernelRight d) :=
  (integralDiagonalRight_injective d hd).comp (integralDiagonalKernel d).subtype_injective

lemma integralDiagonalKernel_finiteIndex (d : O) : (integralDiagonalKernel d).FiniteIndex := by
  letI := globalKubotaKernel_finiteIndex
  letI := finiteIndex_preimage globalKubotaKernel (integralDiagonalLeft d)
  letI := finiteIndex_preimage globalKubotaKernel (integralDiagonalRight d)
  unfold integralDiagonalKernel
  infer_instance

lemma integralDiagonalKernel_finite_covers (d : O) (hd : d ≠ 0) :
    (integralDiagonalKernelLeft d).range.FiniteIndex ∧ (integralDiagonalKernelRight d).range.FiniteIndex := by
  letI := integralDiagonalKernel_finiteIndex d
  letI := (integralDiagonal_finite_covers d hd).1
  letI := (integralDiagonal_finite_covers d hd).2
  constructor
  · rw [integralDiagonalKernelLeft, MonoidHom.range_comp, Subgroup.range_subtype]
    exact finiteIndex_image _ _ (integralDiagonalLeft_injective d hd)
  · rw [integralDiagonalKernelRight, MonoidHom.range_comp, Subgroup.range_subtype]
    exact finiteIndex_image _ _ (integralDiagonalRight_injective d hd)

def integralDiagonalKernelEquiv (d : O) (hd : d ≠ 0) :
    (integralDiagonalKernelLeft d).range ≃* (integralDiagonalKernelRight d).range :=
  (MonoidHom.ofInjective (integralDiagonalKernelLeft_injective d hd)).symm.trans
    (MonoidHom.ofInjective (integralDiagonalKernelRight_injective d hd))

lemma integralDiagonalKernel_pair (d : O) (hd : d ≠ 0) (M : (integralDiagonalKernelLeft d).range) :
    ((M : SL(2, O)), (integralDiagonalKernelEquiv d hd M : SL(2, O))) ∈ integralDiagonalCorrespondence d := by
  let x := (MonoidHom.ofInjective (integralDiagonalKernelLeft_injective d hd)).symm M
  have hx : integralDiagonalKernelLeft d x = M := MonoidHom.apply_ofInjective_symm _ M
  change ((M : SL(2, O)), integralDiagonalKernelRight d x) ∈ integralDiagonalCorrespondence d
  rw [← hx]
  exact x.1.property

lemma integralDiagonal_complex_intertwines (d : O) (hd : d ≠ 0) (z : ℂ) (hz : z ≠ 0)
    (hsq : z ^ 2 = ringComplex d) (MN : integralDiagonalCorrespondence d) :
    complexDiagonal z hz * integralComplexMatrix MN.1.1 =
      integralComplexMatrix MN.1.2 * complexDiagonal z hz := by
  have he := integralDiagonal_entries d MN
  have ha : MN.1.1 0 0 = MN.1.2 0 0 := mul_left_cancel₀ hd (he.1.trans (mul_comm _ _))
  have h01 := congrArg ringComplex he.2.1
  have h10 := congrArg ringComplex he.2.2.1
  have h11 := congrArg ringComplex he.2.2.2
  simp only [map_mul, ← hsq] at h01 h10
  have hentry (M : SL(2, O)) (i j : Fin 2) : integralComplexMatrix M i j = ringComplex (M i j) := rfl
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two, complexDiagonal, hentry]
  · rw [ha, mul_comm]
  · rw [← h01]
    field_simp [hz]
  · rw [h10]
    field_simp [hz]
  · rw [h11, mul_comm]

lemma integralDiagonalKernel_intertwines (d : O) (hd : d ≠ 0) (z : ℂ) (hz : z ≠ 0)
    (hsq : z ^ 2 = ringComplex d) : IntegralCoverIntertwines (integralDiagonalKernelEquiv d hd) (complexDiagonal z hz) := by
  intro M
  exact integralDiagonal_complex_intertwines d hd z hz hsq
    ⟨_, integralDiagonalKernel_pair d hd M⟩

namespace FiniteCorrespondenceCover
variable {G : Type*} [Group G] {ι : Type*}

/-- Intersect finitely many conjugated source subgroups inside the base group. -/
def common (K R : Subgroup G) (a : ι → G ≃* G) : Subgroup G := K ⊓ ⨅ i, R.comap (a i).toMonoidHom

lemma common_le (K R : Subgroup G) (a : ι → G ≃* G) : common K R a ≤ K := inf_le_left

lemma common_le_preimage (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    common K R a ≤ R.comap (a i).toMonoidHom := inf_le_right.trans (iInf_le _ i)

lemma common_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] : (common K R a).FiniteIndex := by
  letI : (⨅ i, R.comap (a i).toMonoidHom).FiniteIndex :=
    Subgroup.finiteIndex_iInf (fun i => finiteIndex_preimage R (a i).toMonoidHom)
  unfold common
  infer_instance

def toSource (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : common K R a →* R where
  toFun h := ⟨a i (h : G), common_le_preimage K R a i h.property⟩
  map_one' := Subtype.ext (map_one (a i))
  map_mul' x y := Subtype.ext (map_mul (a i) (x : G) (y : G))

lemma toSource_injective (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) : Function.Injective (toSource K R a i) := by
  intro x y hxy
  apply Subtype.ext
  exact (a i).injective (congrArg (fun r : R => (r : G)) hxy)

lemma toSource_range (K R : Subgroup G) (a : ι → G ≃* G) (i : ι) :
    (toSource K R a i).range = (common K R a).comap ((a i).symm.toMonoidHom.comp R.subtype) := by
  ext r
  constructor
  · rintro ⟨h, rfl⟩
    change (a i).symm (a i (h : G)) ∈ common K R a
    simpa only [MulEquiv.symm_apply_apply] using h.property
  · intro hr
    refine ⟨⟨(a i).symm (r : G), hr⟩, ?_⟩
    apply Subtype.ext
    exact (a i).apply_symm_apply (r : G)

lemma toSource_range_finiteIndex [Finite ι] (K R : Subgroup G) (a : ι → G ≃* G)
    [K.FiniteIndex] [R.FiniteIndex] (i : ι) : (toSource K R a i).range.FiniteIndex := by
  letI := common_finiteIndex K R a
  rw [toSource_range]
  exact finiteIndex_preimage _ _

def hom (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) : common K R a →* G :=
  L.subtype.comp (e.toMonoidHom.comp (toSource K R a i))

lemma hom_injective (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) :
    Function.Injective (hom K R L a e i) := L.subtype_injective.comp (e.injective.comp (toSource_injective K R a i))

def target (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) : Subgroup G := (hom K R L a e i).range

lemma target_le (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) : target K R L a e i ≤ L := by
  rintro x ⟨h, rfl⟩
  exact (e (toSource K R a i h)).property

lemma target_finiteIndex [Finite ι] (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L)
    [K.FiniteIndex] [R.FiniteIndex] [L.FiniteIndex] (i : ι) : (target K R L a e i).FiniteIndex := by
  letI := toSource_range_finiteIndex K R a i
  constructor
  rw [target, hom, MonoidHom.range_comp, MonoidHom.range_comp, Subgroup.index_map_subtype,
    Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
  exact mul_ne_zero (Subgroup.FiniteIndex.index_ne_zero (H := (toSource K R a i).range))
    (Subgroup.FiniteIndex.index_ne_zero (H := L))

def equiv (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) : common K R a ≃* target K R L a e i :=
  MonoidHom.ofInjective (hom_injective K R L a e i)

lemma equiv_coe (K R L : Subgroup G) (a : ι → G ≃* G) (e : R ≃* L) (i : ι) (h : common K R a) :
    (equiv K R L a e i h : G) = (e (toSource K R a i h) : G) := rfl

end FiniteCorrespondenceCover

abbrev CubeResidues (p : O) := O ⧸ Ideal.span {p ^ 3}

def cubeResidueRepresentative (p : O) (r : CubeResidues p) : O := Classical.choose (Ideal.Quotient.mk_surjective r)

lemma cubeResidueRepresentative_spec (p : O) (r : CubeResidues p) :
    Ideal.Quotient.mk (Ideal.span {p ^ 3}) (cubeResidueRepresentative p r) = r :=
  Classical.choose_spec (Ideal.Quotient.mk_surjective r)

def cubeCommonAutomorphism (p : O) (r : CubeResidues p) : SL(2, O) ≃* SL(2, O) :=
  MulAut.conj (integralTranslation (3 * cubeResidueRepresentative p r))

/-- A single integral cover supports all translated cube-dilation branches. -/
def cubeCommonCover (p : O) : Subgroup (SL(2, O)) :=
  FiniteCorrespondenceCover.common globalKubotaKernel (integralDiagonalKernelRight (p ^ 3)).range
    (cubeCommonAutomorphism p)

lemma cubeCommonCover_le (p : O) : cubeCommonCover p ≤ globalKubotaKernel :=
  FiniteCorrespondenceCover.common_le _ _ _

lemma cubeCommonCover_finiteIndex (p : O) (hp : p ≠ 0) : (cubeCommonCover p).FiniteIndex := by
  letI := globalKubotaKernel_finiteIndex
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI := (integralDiagonalKernel_finite_covers (p ^ 3) (pow_ne_zero 3 hp)).2
  exact FiniteCorrespondenceCover.common_finiteIndex _ _ _

def cubeCommonTarget (p : O) (hp : p ≠ 0) (r : CubeResidues p) : Subgroup (SL(2, O)) :=
  FiniteCorrespondenceCover.target globalKubotaKernel (integralDiagonalKernelRight (p ^ 3)).range
    (integralDiagonalKernelLeft (p ^ 3)).range (cubeCommonAutomorphism p)
    (integralDiagonalKernelEquiv (p ^ 3) (pow_ne_zero 3 hp)).symm r

lemma cubeCommonTarget_le (p : O) (hp : p ≠ 0) (r : CubeResidues p) : cubeCommonTarget p hp r ≤ globalKubotaKernel :=
  (FiniteCorrespondenceCover.target_le _ _ _ _ _ r).trans (integralDiagonalKernelLeft_le (p ^ 3))

lemma cubeCommonTarget_finiteIndex (p : O) (hp : p ≠ 0) (r : CubeResidues p) :
    (cubeCommonTarget p hp r).FiniteIndex := by
  letI := globalKubotaKernel_finiteIndex
  letI : Finite (CubeResidues p) := (Ideal.span {p ^ 3}).finiteQuotientOfFreeOfNeBot
    (Ideal.span_singleton_eq_bot.not.mpr (pow_ne_zero 3 hp))
  letI := (integralDiagonalKernel_finite_covers (p ^ 3) (pow_ne_zero 3 hp)).1
  letI := (integralDiagonalKernel_finite_covers (p ^ 3) (pow_ne_zero 3 hp)).2
  exact FiniteCorrespondenceCover.target_finiteIndex _ _ _ _ _ r

def cubeCommonEquiv (p : O) (hp : p ≠ 0) (r : CubeResidues p) : cubeCommonCover p ≃* cubeCommonTarget p hp r :=
  FiniteCorrespondenceCover.equiv globalKubotaKernel (integralDiagonalKernelRight (p ^ 3)).range
    (integralDiagonalKernelLeft (p ^ 3)).range (cubeCommonAutomorphism p)
    (integralDiagonalKernelEquiv (p ^ 3) (pow_ne_zero 3 hp)).symm r

def cubeDilationRoot (p : O) : ℂ :=
  Classical.choose (IsAlgClosed.exists_pow_nat_eq (ringComplex (p ^ 3)) (by norm_num : 0 < 2))

lemma cubeDilationRoot_sq (p : O) : cubeDilationRoot p ^ 2 = ringComplex (p ^ 3) :=
  Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq (ringComplex (p ^ 3)) (by norm_num : 0 < 2))

lemma cubeDilationRoot_ne_zero (p : O) (hp : p ≠ 0) : cubeDilationRoot p ≠ 0 := by
  intro hz
  have hs := cubeDilationRoot_sq p
  rw [hz, zero_pow (by norm_num)] at hs
  exact ringComplex_ne_zero (pow_ne_zero 3 hp) hs.symm

def cubeDilationMatrix (p : O) (hp : p ≠ 0) : SL(2, ℂ) := complexDiagonal (cubeDilationRoot p) (cubeDilationRoot_ne_zero p hp)

def cubeAverageMatrix (p : O) (hp : p ≠ 0) (q : O) : SL(2, ℂ) :=
  (cubeDilationMatrix p hp)⁻¹ * integralComplexMatrix (integralTranslation (3 * q))

lemma cubeDilation_intertwines (p : O) (hp : p ≠ 0) :
    IntegralCoverIntertwines (integralDiagonalKernelEquiv (p ^ 3) (pow_ne_zero 3 hp)) (cubeDilationMatrix p hp) :=
  integralDiagonalKernel_intertwines (p ^ 3) (pow_ne_zero 3 hp) _ (cubeDilationRoot_ne_zero p hp) (cubeDilationRoot_sq p)

/-- Every translated dilation acts between the two explicit finite-index subgroup quotients. -/
lemma cubeCommon_intertwines (p : O) (hp : p ≠ 0) (r : CubeResidues p) :
    IntegralCoverIntertwines (cubeCommonEquiv p hp r)
      (cubeAverageMatrix p hp (cubeResidueRepresentative p r)) := by
  intro h
  let T := integralTranslation (3 * cubeResidueRepresentative p r)
  let x := FiniteCorrespondenceCover.toSource globalKubotaKernel
    (integralDiagonalKernelRight (p ^ 3)).range (cubeCommonAutomorphism p) r h
  let e := integralDiagonalKernelEquiv (p ^ 3) (pow_ne_zero 3 hp)
  have hT : T * (h : SL(2, O)) = (x : SL(2, O)) * T := by
    change T * (h : SL(2, O)) = (T * (h : SL(2, O)) * T⁻¹) * T
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  have hx := integralCoverIntertwines_inverse e (cubeDilationMatrix p hp) (cubeDilation_intertwines p hp) x
  change ((cubeDilationMatrix p hp)⁻¹ * integralComplexMatrix T) * integralComplexMatrix (h : SL(2, O)) =
    integralComplexMatrix (e.symm x : SL(2, O)) * ((cubeDilationMatrix p hp)⁻¹ * integralComplexMatrix T)
  rw [mul_assoc, ← map_mul, hT, map_mul, ← mul_assoc, hx, mul_assoc]

def cubeCommonLeg (p : O) (hp : p ≠ 0) (r : CubeResidues p) : KernelQuotientL2 →L[ℂ] IntegralQuotientL2 (cubeCommonCover p) := by
  letI := cubeCommonTarget_finiteIndex p hp r
  letI : (cubeCommonTarget p hp r).IsFiniteRelIndex globalKubotaKernel := Subgroup.isFiniteRelIndex_of_finiteIndex
  exact kernelCoverLeg (cubeCommonCover_le p) (cubeCommonTarget_le p hp r) (cubeCommonEquiv p hp r)
    (cubeAverageMatrix p hp (cubeResidueRepresentative p r)) (cubeCommon_intertwines p hp r)

lemma integralProjection_translates_disjoint (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree)
    (S : Set HyperbolicSpace) (hinj : Set.InjOn (integralOrbitProjection H) S) :
    Pairwise (fun M N : H => Disjoint (M • S) (N • S)) := by
  letI : IsCancelSMul H HyperbolicSpace := integralSubgroupFree H hH
  intro M N hMN
  apply Set.disjoint_left.mpr
  rintro _ ⟨w, hw, rfl⟩ ⟨u, hu, he⟩
  have hwu : w = u := hinj hw hu (by
    calc
      integralOrbitProjection H w = integralOrbitProjection H (M • w) := (integralOrbitProjection_eq H M w).symm
      _ = integralOrbitProjection H (N • u) := congrArg _ he.symm
      _ = integralOrbitProjection H u := integralOrbitProjection_eq H N u)
  subst u
  exact hMN (IsCancelSMul.right_cancel M N w he.symm)

lemma integralProjection_measure_image (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree)
    (S : Set HyperbolicSpace) (hS : MeasurableSet S) (hinj : Set.InjOn (integralOrbitProjection H) S) :
    integralQuotientVolume H (integralOrbitProjection H '' S) = hyperbolicVolume S := by
  have himg := hS.image_of_continuousOn_injOn (continuous_integralOrbitProjection H).continuousOn hinj
  rw [integralQuotientVolume, Measure.map_apply (measurable_integralOrbitProjection _) himg,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) himg),
    integralOrbitProjection_preimage_image, Set.iUnion_inter]
  rw [measure_iUnion]
  · exact ((hyperbolicFundamentalSet_isFundamentalDomain H hH hyperbolicVolume).measure_eq_tsum S).symm
  · intro M N hMN
    exact (integralProjection_translates_disjoint H hH S hinj hMN).mono Set.inter_subset_left Set.inter_subset_left
  · intro M
    exact (hS.const_smul M).inter (hyperbolicFundamentalSet_measurable _)

/-- An injective measurable chart transports hyperbolic volume exactly to any level-three subgroup quotient. -/
theorem integralProjection_measurePreserving_on (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree)
    (U : Set HyperbolicSpace) (hU : MeasurableSet U) (hinj : Set.InjOn (integralOrbitProjection H) U) :
    MeasurePreserving (integralOrbitProjection H) (hyperbolicVolume.restrict U)
      ((integralQuotientVolume H).restrict (integralOrbitProjection H '' U)) := by
  refine ⟨measurable_integralOrbitProjection _, ?_⟩
  apply Measure.ext
  intro B hB
  rw [Measure.map_apply (measurable_integralOrbitProjection _) hB,
    Measure.restrict_apply ((measurable_integralOrbitProjection _) hB), Measure.restrict_apply hB]
  have he : B ∩ (integralOrbitProjection H '' U) =
      integralOrbitProjection H '' (integralOrbitProjection H ⁻¹' B ∩ U) := by
    ext q
    constructor
    · rintro ⟨hq, w, hw, rfl⟩
      exact ⟨w, ⟨hq, hw⟩, rfl⟩
    · rintro ⟨w, ⟨hw, hu⟩, rfl⟩
      exact ⟨hw, ⟨w, hu, rfl⟩⟩
  rw [he, integralProjection_measure_image H hH _ (((measurable_integralOrbitProjection _) hB).inter hU)
    (hinj.mono Set.inter_subset_right)]

lemma integralProjection_cuspPeriodRegion_injective (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree) :
    Set.InjOn (integralOrbitProjection H) cuspPeriodRegion := by
  intro u hu v hv he
  obtain ⟨M, hM⟩ := (integralOrbitProjection_eq_iff H u v).mp he
  have hMu : integralComplexMatrix (M : SL(2, O)) • v = u := hM
  have hc : (M : SL(2, O)) 1 0 = 0 := by
    by_contra hn
    have hb := integral_hyperbolicHeight_mul_le_one (M : SL(2, O)) hn v
    rw [hMu] at hb
    have hhu : 1 < hyperbolicHeight u := hu.2
    have hhv : 1 < hyperbolicHeight v := hv.2
    nlinarith only [hb, hhu, hhv, mul_pos (sub_pos.mpr hhu) (sub_pos.mpr hhv)]
  let N : levelThree := ⟨M, hH M.property⟩
  have ht := levelThree_integral_eq_translation N hc
  obtain ⟨z, t, htpos, hvrep⟩ := upperPoint_surjective v
  have hua : u = upperPoint (z + ringComplex ((M : SL(2, O)) 0 1)) t htpos := by
    rw [← hMu, ← hvrep, ht, complexTranslation_action]
  have hvl : hyperbolicHorizontal v = z := by rw [← hvrep, hyperbolicHorizontal_upperPoint]
  have hul : hyperbolicHorizontal u = z + ringComplex ((M : SL(2, O)) 0 1) := by
    rw [hua, hyperbolicHorizontal_upperPoint]
  obtain ⟨k, hk⟩ := levelThree_upper N
  have hp : ringComplex ((M : SL(2, O)) 0 1) ∈ periodLattice := by
    change ringComplex ((N : levelThree).1 0 1) ∈ periodLattice
    rw [hk, map_mul, map_ofNat]
    exact three_embedding_mem k
  have hz := periodDomain_unique_translate _ _ _ hu.1 hv.1 hp (by rw [hul, hvl])
  have hez : z + ringComplex ((M : SL(2, O)) 0 1) = z := by simpa only [hul, hvl] using hz
  rw [hua, hez, ← hvrep]

lemma integralProjection_cuspPeriodStrip_injective (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree)
    (a b : ℝ) (ha : 1 < a) : Set.InjOn (integralOrbitProjection H) (cuspPeriodStrip a b) := by
  apply (integralProjection_cuspPeriodRegion_injective H hH).mono
  intro w hw
  exact ⟨hw.1, ha.trans_le hw.2.1⟩

lemma integralProjection_cuspPeriodStrip_measurePreserving (H : Subgroup (SL(2, O))) (hH : H ≤ levelThree)
    (a b : ℝ) (ha : 1 < a) :
    MeasurePreserving (integralOrbitProjection H) (hyperbolicVolume.restrict (cuspPeriodStrip a b))
      ((integralQuotientVolume H).restrict (integralOrbitProjection H '' cuspPeriodStrip a b)) := by
  apply integralProjection_measurePreserving_on H hH _ (cuspPeriodStrip_measurable a b)
  exact integralProjection_cuspPeriodStrip_injective H hH a b ha

lemma integralCoverTraceFunction_continuous (H K : Subgroup (SL(2, O))) [H.IsFiniteRelIndex K]
    (f : IntegralOrbitQuotient H → ℂ) (hf : Continuous f) : Continuous (integralCoverTraceFunction H K f) := by
  letI : Fintype (IntegralCoverCosets H K) := Fintype.ofFinite _
  have hc : Continuous (integralCoverTraceLift H K f) :=
    continuous_finsetSum Finset.univ (fun q _ => hf.comp (integralCoverFiberPoint_continuous H K q))
  exact hc.quotient_lift _

section CuspAverageOrthogonality
local instance kernelLevelFiniteCover : globalKubotaKernel.IsFiniteRelIndex levelThree := by
  letI := globalKubotaKernel_finiteIndex
  exact Subgroup.isFiniteRelIndex_of_finiteIndex

/-- Fiber trace of the pairing with a fixed compact-height defect. -/
def kernelDefectTrace (f : KernelQuotient → ℂ) : IntegralOrbitQuotient levelThree → ℂ :=
  integralCoverTraceFunction globalKubotaKernel levelThree
    (fun q => star (f q) * kernelQuotientDefect 5 6 (4 / 3) q)

lemma kernelDefectTrace_continuous (f : KernelQuotient → ℂ) (hf : Continuous f) : Continuous (kernelDefectTrace f) :=
  integralCoverTraceFunction_continuous _ _ _
    (hf.star.mul (kernelQuotientDefect_contMDiff 5 6 (4 / 3) (by norm_num) (by norm_num)).continuous)

lemma kernelDefectTrace_integral (f : KernelQuotient → ℂ) (hf : Continuous f) :
    (∫ q, kernelDefectTrace f q ∂integralQuotientVolume levelThree) =
      ∫ q, star (f q) * kernelQuotientDefect 5 6 (4 / 3) q ∂integralQuotientVolume globalKubotaKernel := by
  apply integralCoverTraceFunction_integral globalKubotaKernel_le_levelThree le_rfl
  · exact hf.star.measurable.mul (kernelQuotientDefect_measurable 5 6 (4 / 3) (by norm_num) (by norm_num))
  · apply (hf.star.mul (kernelQuotientDefect_contMDiff 5 6 (4 / 3) (by norm_num) (by norm_num)).continuous).integrable_of_hasCompactSupport
    exact (kernelQuotientDefect_hasCompactSupport 5 6 (by norm_num) (by norm_num) (4 / 3)).mul_left

lemma kernelDefectTrace_upper (f : KernelQuotient → ℂ) (z : ℂ) (v : ℝ) (hv : 0 < v) (hv1 : 1 < v) :
    kernelDefectTrace f (integralOrbitProjection levelThree (upperPoint z v hv)) =
      letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
      ∑ r : IntegralCoverCosets globalKubotaKernel levelThree,
        (star (f (integralOrbitProjection globalKubotaKernel
          (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv))) *
            complexCharacter ((integralCoverRep globalKubotaKernel levelThree r)⁻¹)) *
              cuspSeedDefectProfile 5 6 (4 / 3) v := by
  letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
  change (∑ r : IntegralCoverCosets globalKubotaKernel levelThree,
    star (f (integralCoverFiberPoint globalKubotaKernel levelThree r (upperPoint z v hv))) *
      kernelQuotientDefect 5 6 (4 / 3) (integralCoverFiberPoint globalKubotaKernel levelThree r (upperPoint z v hv))) = _
  apply Finset.sum_congr rfl
  intro r _
  rw [integralCoverFiberPoint_rep, integralSubgroup_smul, integralComplexMatrix_levelThree]
  change star (f (integralOrbitProjection globalKubotaKernel
    (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv))) *
      cuspCutoffCorrection 1 (cuspSeedDefectProfile 5 6 (4 / 3))
        (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv) = _
  rw [cuspCutoffCorrection_automorphy 1 le_rfl, cuspCutoffCorrection_upperPoint _ z v hv hv1]
  exact (mul_assoc _ _ _).symm

lemma kernelDefectTrace_average_zero (f : KernelQuotient → ℂ) (hf : Continuous f)
    (v : ℝ) (hv : 0 < v) (hv1 : 1 < v)
    (havg : ∀ M : levelThree, (∫ z in periodDomain,
      f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) = 0) :
    (∫ z in periodDomain, kernelDefectTrace f (integralOrbitProjection levelThree (upperPoint z v hv))) = 0 := by
  letI := periodDomain_finiteMeasure
  letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
  have hc (M : levelThree) : Continuous (fun z : ℂ =>
      f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) :=
    ((hf.comp (continuous_integralOrbitProjection _)).comp (continuous_hyperbolic_action _)).comp
      (upperCoordinatesHomeomorph.continuous.comp
        (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))
  simp_rw [kernelDefectTrace_upper f _ v hv hv1]
  have hi (r : IntegralCoverCosets globalKubotaKernel levelThree) : Integrable
      (fun z : ℂ => (star (f (integralOrbitProjection globalKubotaKernel
        (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv))) *
          complexCharacter ((integralCoverRep globalKubotaKernel levelThree r)⁻¹)) *
            cuspSeedDefectProfile 5 6 (4 / 3) v) (volume.restrict periodDomain) := by
    apply (periodDomain_continuous_memLp _ ?_).integrable (by norm_num)
    exact (((hc ((integralCoverRep globalKubotaKernel levelThree r)⁻¹)).star.mul continuous_const).mul continuous_const)
  rw [integral_finsetSum Finset.univ (fun r _ => hi r)]
  apply Finset.sum_eq_zero
  intro r _
  rw [integral_mul_const, integral_mul_const]
  have hstar : (∫ z in periodDomain,
      star (f (integralOrbitProjection globalKubotaKernel
        (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv)))) =
      star (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel
        (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • upperPoint z v hv))) := by
    simp only [Complex.star_def]
    exact integral_conj
  rw [hstar, havg, star_zero, zero_mul, zero_mul]

lemma kernelDefectTrace_strip_integral_zero (f : KernelQuotient → ℂ) (hf : Continuous f)
    (havg : ∀ M : levelThree, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) = 0) :
    (∫ w in cuspPeriodStrip 5 6, kernelDefectTrace f (integralOrbitProjection levelThree w) ∂hyperbolicVolume) = 0 := by
  let G : HyperbolicSpace → ℂ := fun w => kernelDefectTrace f (integralOrbitProjection levelThree w)
  have hg : Continuous G := (kernelDefectTrace_continuous f hf).comp (continuous_integralOrbitProjection _)
  change (∫ w in cuspPeriodStrip 5 6, G w ∂hyperbolicVolume) = 0
  rw [cuspPeriodStrip_integral_coordinates G hg.aestronglyMeasurable (cuspCoordinateLift_weighted_integrable G hg)]
  calc
    _ = ∫ v in Set.Icc (5 : ℝ) 6, (0 : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Icc
      intro v hv
      have hp : 0 < v := lt_of_lt_of_le (by norm_num) hv.1
      have h1 : 1 < v := lt_of_lt_of_le (by norm_num) hv.1
      have hz := kernelDefectTrace_average_zero f hf v hp h1 (fun M => havg M v hp h1)
      simp only [G, cuspCoordinateLift_positive v _ hp]
      rw [hz, zero_div]
    _ = 0 := by simp only [integral_zero]

lemma periodDomain_reduction (z : ℂ) : ∃ n : O, z + 3 * ringComplex n ∈ periodDomain := by
  obtain ⟨p, hp, _⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain periodBasis z
  obtain ⟨n, rfl⟩ := periodEquiv.surjective p
  change 3 * ringComplex n + z ∈ periodDomain at hp
  exact ⟨n, by simpa only [add_comm] using hp⟩

lemma levelProjection_mem_cuspStrip_of_height (w : HyperbolicSpace)
    (hw : hyperbolicHeight w ∈ Set.Icc (5 : ℝ) 6) :
    integralOrbitProjection levelThree w ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6 := by
  obtain ⟨z, v, hv, rfl⟩ := upperPoint_surjective w
  obtain ⟨n, hn⟩ := periodDomain_reduction z
  refine ⟨upperPoint (z + 3 * ringComplex n) v hv, ?_, ?_⟩
  · exact ⟨by simpa only [hyperbolicHorizontal_upperPoint] using hn,
      by simpa only [hyperbolicHeight_upperPoint] using hw⟩
  · exact congrArg (integralCoverMap globalKubotaKernel_le_levelThree)
      (kernelProjection_upper_period v hv z n)

lemma smoothCuspSeedDefect_support_levelStrip (w : HyperbolicSpace)
    (hw : smoothCuspSeedDefect 5 6 (4 / 3) w ≠ 0) :
    integralOrbitProjection levelThree w ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6 := by
  obtain ⟨r, hr⟩ := smoothCuspSeedDefect_support 5 6 (4 / 3) (by norm_num) w hw
  induction r using Quotient.inductionOn with
  | _ M =>
    change (5 : ℝ) ≤ cosetHeight (cosetOf M) w ∧ cosetHeight (cosetOf M) w ≤ 6 at hr
    rw [cosetHeight_cosetOf] at hr
    have hm := levelProjection_mem_cuspStrip_of_height (complexMatrix M • w) hr
    simpa only [← integralComplexMatrix_levelThree, integralOrbitProjection_eq] using hm

/-- The finite character trace is supported in one ordinary cusp strip. -/
lemma kernelDefectTrace_support (f : KernelQuotient → ℂ) (q : IntegralOrbitQuotient levelThree)
    (hq : kernelDefectTrace f q ≠ 0) :
    q ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6 := by
  letI : Fintype (IntegralCoverCosets globalKubotaKernel levelThree) := Fintype.ofFinite _
  induction q using Quotient.inductionOn with
  | _ w =>
    change integralOrbitProjection levelThree w ∈ integralOrbitProjection levelThree '' cuspPeriodStrip 5 6
    change (∑ r : IntegralCoverCosets globalKubotaKernel levelThree,
      star (f (integralCoverFiberPoint globalKubotaKernel levelThree r w)) *
        kernelQuotientDefect 5 6 (4 / 3) (integralCoverFiberPoint globalKubotaKernel levelThree r w)) ≠ 0 at hq
    obtain ⟨r, _, hr⟩ := Finset.exists_ne_zero_of_sum_ne_zero hq
    have hd := (mul_ne_zero_iff.mp hr).2
    rw [integralCoverFiberPoint_rep, integralSubgroup_smul, integralComplexMatrix_levelThree] at hd
    have hs := smoothCuspSeedDefect_support_levelStrip
      (complexMatrix ((integralCoverRep globalKubotaKernel levelThree r)⁻¹) • w) hd
    simpa only [← integralComplexMatrix_levelThree, integralOrbitProjection_eq] using hs

lemma kernelDefectTrace_integral_zero (f : KernelQuotient → ℂ) (hf : Continuous f)
    (havg : ∀ M : levelThree, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) = 0) :
    (∫ q, kernelDefectTrace f q ∂integralQuotientVolume levelThree) = 0 := by
  let S := integralOrbitProjection levelThree '' cuspPeriodStrip 5 6
  have hS : MeasurableSet S := (cuspPeriodStrip_measurable 5 6).image_of_continuousOn_injOn
    (continuous_integralOrbitProjection levelThree).continuousOn
    (integralProjection_cuspPeriodStrip_injective levelThree le_rfl 5 6 (by norm_num))
  have he : S.indicator (kernelDefectTrace f) = kernelDefectTrace f := by
    funext q
    by_cases hq : q ∈ S
    · exact Set.indicator_of_mem hq _
    · rw [Set.indicator_of_notMem hq]
      exact (not_not.mp (fun hn => hq (kernelDefectTrace_support f q hn))).symm
  calc
    _ = ∫ q in S, kernelDefectTrace f q ∂integralQuotientVolume levelThree := by
      rw [← integral_indicator hS, he]
    _ = ∫ w in cuspPeriodStrip 5 6,
        kernelDefectTrace f (integralOrbitProjection levelThree w) ∂hyperbolicVolume := by
      rw [← (integralProjection_cuspPeriodStrip_measurePreserving levelThree le_rfl 5 6 (by norm_num)).map_eq]
      exact integral_map (measurable_integralOrbitProjection _).aemeasurable
        (kernelDefectTrace_continuous f hf).aestronglyMeasurable
    _ = 0 := kernelDefectTrace_strip_integral_zero f hf havg

lemma kernelL2Defect_inner_zero_of_cusp_averages (F : KernelQuotientL2)
    (f : KernelQuotient → ℂ) (hf : Continuous f)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (havg : ∀ M : levelThree, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) = 0) :
    inner ℂ F (kernelL2Defect 5 6 (by norm_num) (by norm_num) (4 / 3)) = 0 := by
  rw [L2.inner_def]
  calc
    _ = ∫ q, star (f q) * kernelQuotientDefect 5 6 (4 / 3) q ∂integralQuotientVolume globalKubotaKernel := by
      apply integral_congr_ae
      filter_upwards [hrep, kernelL2Defect_ae_eq 5 6 (by norm_num) (by norm_num) (4 / 3)] with q hq hd
      rw [hq, hd, RCLike.inner_apply, starRingEnd_apply, mul_comm]
    _ = ∫ q, kernelDefectTrace f q ∂integralQuotientVolume levelThree := (kernelDefectTrace_integral f hf).symm
    _ = 0 := kernelDefectTrace_integral_zero f hf havg

/-- Vanishing cusp averages annihilate the residue pairing at eigenvalue eight ninths. -/
theorem cubicEisensteinResidue_orthogonal_of_zero_cusp_averages
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hf : Continuous f)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (havg : ∀ M : levelThree, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (complexMatrix M • upperPoint z v hv))) = 0) :
    inner ℂ F cubicEisensteinResidue = 0 := by
  have he : cubicEisensteinResidue = kernelEisensteinResidueVector 5 6 (by norm_num) (by norm_num) :=
    kernelEisensteinResidueVector_cutoff_independent 2 3 5 6 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [he, kernelEisensteinResidueVector_pairing _ _ _ _ F hF,
    kernelL2Defect_inner_zero_of_cusp_averages F f hf hrep havg, mul_zero]

lemma cubicEisensteinResidue_translate_orthogonal_of_zero_averages
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hf : Continuous f)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (havg : ∀ N : SL(2, O), ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))) = 0)
    (g : rationalExtension) : inner ℂ F (kernelRationalPullback g cubicEisensteinResidue) = 0 := by
  rw [kernelRationalPullback_pairing_inverse]
  have hrepG : kernelRationalPullback g⁻¹ F =ᵐ[integralQuotientVolume globalKubotaKernel]
      fun q => f (kernelRationalAction g⁻¹ q) :=
    (kernelRationalPullback_ae g⁻¹ F).trans
      ((kernelRationalAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
  apply cubicEisensteinResidue_orthogonal_of_zero_cusp_averages _
    (kernelRational_eigenvector g⁻¹ F (8 / 9) hF) _ (hf.comp (kernelRationalAction_continuous _)) hrepG
  intro N v hv hlarge
  simpa only [Function.comp_apply, kernelRationalAction_mk, map_mul, mul_smul, integralComplexMatrix_levelThree] using
    havg ((g⁻¹ : rationalExtension) * (N : SL(2, O))) v hv hlarge

theorem cubicSourceResidue_orthogonal_of_zero_integral_cusp_averages
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hf : Continuous f)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (havg : ∀ N : SL(2, O), ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))) = 0) :
    inner ℂ F (kernelRationalSourceProjection cubicEisensteinResidue) = 0 := by
  rw [kernelRationalSourceProjection_apply, inner_smul_right, inner_sum]
  simp only [cubicEisensteinResidue_translate_orthogonal_of_zero_averages F hF f hf hrep havg,
    Finset.sum_const_zero, mul_zero]

/-- A finite correspondence combination vanishes if every adjoint has zero cusp averages. -/
theorem commonCover_source_span_vanish_of_zero_averages
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    {ι : Type*} [Fintype ι] (leg : ι → KernelQuotientL2 →L[ℂ] E) (c : ι → ℂ) (D : E)
    (hD : D = ∑ i, c i • leg i (kernelRationalSourceProjection cubicEisensteinResidue))
    (hEig : ∀ i, (ContinuousLinearMap.adjoint (leg i) D,
      (8 / 9 : ℂ) • ContinuousLinearMap.adjoint (leg i) D) ∈ kernelEnergyLaplacian.graph)
    (f : ι → KernelQuotient → ℂ) (hf : ∀ i, Continuous (f i))
    (hrep : ∀ i, ContinuousLinearMap.adjoint (leg i) D =ᵐ[integralQuotientVolume globalKubotaKernel] f i)
    (havg : ∀ i, ∀ N : SL(2, O), ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      (∫ z in periodDomain, f i (integralOrbitProjection globalKubotaKernel (integralComplexMatrix N • upperPoint z v hv))) = 0) :
    D = 0 := by
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  calc
    inner ℂ D D = inner ℂ D (∑ i, c i • leg i (kernelRationalSourceProjection cubicEisensteinResidue)) :=
      congrArg (inner ℂ D) hD
    _ = ∑ i, c i * inner ℂ D (leg i (kernelRationalSourceProjection cubicEisensteinResidue)) := by
      simp only [inner_sum, inner_smul_right]
    _ = 0 := by
      apply Finset.sum_eq_zero
      intro i _
      rw [← ContinuousLinearMap.adjoint_inner_left,
        cubicSourceResidue_orthogonal_of_zero_integral_cusp_averages _ (hEig i) (f i) (hf i) (hrep i) (havg i), mul_zero]

end CuspAverageOrthogonality

section PeriodAffineAverages
local instance : MeasureSpace UnitAddCircle := ⟨AddCircle.haarAddCircle⟩
local instance : Measure.IsAddHaarMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (Measure.IsAddHaarMeasure AddCircle.haarAddCircle)
local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) :=
  inferInstanceAs (IsProbabilityMeasure AddCircle.haarAddCircle)

/-- Integral multiplication descends to an endomorphism of the cusp torus. -/
def periodMultiplication (b : O) : UnitAddTorus (Fin 2) →+ UnitAddTorus (Fin 2) where
  toFun t := ![(Coordinates.coords b).1 • t 0 + (Coordinates.coords (b * omega)).1 • t 1,
    (Coordinates.coords b).2 • t 0 + (Coordinates.coords (b * omega)).2 • t 1]
  map_zero' := by ext i; fin_cases i <;> simp
  map_add' t u := by ext i; fin_cases i <;> simp [smul_add, add_add_add_comm]

lemma periodVector_mul (b : O) (x : Fin 2 → ℝ) :
    ringComplex b * periodVector x = periodVector
      ![(Coordinates.coords b).1 * x 0 + (Coordinates.coords (b * omega)).1 * x 1,
        (Coordinates.coords b).2 * x 0 + (Coordinates.coords (b * omega)).2 * x 1] := by
  have he (c : O) : ringComplex c = (Coordinates.coords c).1 + (Coordinates.coords c).2 * ringComplex omega := by
    conv_lhs => rw [← Coordinates.eval_coords c, ringComplex_eval]
  rw [periodVector_apply, periodVector_apply]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
  push_cast
  calc
    ringComplex b * (3 * ((x 0 : ℂ) + (x 1 : ℂ) * ringComplex omega)) =
        3 * ((x 0 : ℂ) * ringComplex b + (x 1 : ℂ) * ringComplex (b * omega)) := by rw [map_mul]; ring
    _ = _ := by rw [he b, he (b * omega)]; ring

lemma periodTorus_mul (b : O) (z : ℂ) :
    periodTorus (ringComplex b * z) = periodMultiplication b (periodTorus z) := by
  obtain ⟨x, rfl⟩ := periodVector.surjective z
  rw [periodVector_mul, periodTorus_periodVector, periodTorus_periodVector]
  ext i
  fin_cases i <;> simp only [periodMultiplication, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    ← AddCircle.coe_zsmul, ← AddCircle.coe_add, zsmul_eq_mul] <;> rfl

lemma periodMultiplication_continuous (b : O) : Continuous (periodMultiplication b) := by
  apply continuous_pi
  intro i
  fin_cases i <;> change Continuous (fun t : UnitAddTorus (Fin 2) => _ • t 0 + _ • t 1) <;> fun_prop

lemma periodMultiplication_surjective (b : O) (hb : b ≠ 0) : Function.Surjective (periodMultiplication b) := by
  intro t
  refine ⟨periodTorus (periodSection t / ringComplex b), ?_⟩
  have hc : ringComplex b * (periodSection t / ringComplex b) = periodSection t := by
    field_simp [ringComplex_ne_zero hb]
  rw [← periodTorus_mul, hc, periodTorus_section]

lemma periodMultiplication_measurePreserving (b : O) (hb : b ≠ 0) :
    MeasurePreserving (periodMultiplication b) volume volume :=
  AddMonoidHom.measurePreserving (periodMultiplication_continuous b) (periodMultiplication_surjective b hb) rfl

lemma periodFunction_descends (f : ℂ → ℂ)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z)
    (z w : ℂ) (he : periodTorus z = periodTorus w) : f z = f w := by
  have hs (i : Fin 2) : ((periodBasis.equivFunL (z - w) i : ℝ) : UnitAddCircle) = 0 := by
    simp only [map_sub, Pi.sub_apply, AddCircle.coe_sub]
    exact sub_eq_zero.mpr (congrFun he i)
  obtain ⟨a, ha⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hs 0)
  obtain ⟨b, hb⟩ := (AddCircle.coe_eq_zero_iff (1 : ℝ)).mp (hs 1)
  simp only [zsmul_eq_mul, mul_one] at ha hb
  have hx : periodBasis.equivFunL (z - w) = ![(a : ℝ), (b : ℝ)] := by
    ext i
    fin_cases i
    · exact ha.symm
    · exact hb.symm
  have hd : z - w = 3 * ringComplex (Coordinates.eval a b) := by
    calc
      z - w = periodVector (periodBasis.equivFunL (z - w)) := (periodBasis.equivFunL.symm_apply_apply _).symm
      _ = _ := by
        rw [hx, periodVector_apply, ringComplex_eval]
        simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Complex.ofReal_intCast]
  have hz : z = w + 3 * ringComplex (Coordinates.eval a b) := by linear_combination hd
  rw [hz, hper]

/-- A nonzero integral dilation preserves the normalized average of a periodic function. -/
theorem period_integral_eisenstein_mul (f : ℂ → ℂ) (hf : Measurable f)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z) (b : O) (hb : b ≠ 0) :
    (∫ z in periodDomain, f (ringComplex b * z)) = ∫ z in periodDomain, f z := by
  let F := f ∘ periodSection
  have hF : Measurable F := hf.comp periodSection_measurableEmbedding.measurable
  have hdesc (z : ℂ) : F (periodTorus z) = f z :=
    periodFunction_descends f hper _ _ (periodTorus_section _)
  have hi : (∫ t, F (periodMultiplication b t)) = ∫ t, F t := by
    calc
      _ = ∫ t, F t ∂Measure.map (periodMultiplication b) volume :=
        (integral_map (periodMultiplication_continuous b).measurable.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [(periodMultiplication_measurePreserving b hb).map_eq]
  rw [periodTorus_integral, periodTorus_integral] at hi
  simp_rw [← periodTorus_mul, hdesc] at hi
  have hc : (periodCovolumeDensity : ℝ) ≠ 0 := by exact_mod_cast periodCovolumeDensity_pos.ne'
  have hi' := congrArg (fun x : ℂ => (periodCovolumeDensity : ℝ)⁻¹ • x) hi
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hi' 

lemma period_integral_eisenstein_affine (f : ℂ → ℂ) (hf : Measurable f)
    (hper : ∀ (n : O) (z : ℂ), f (z + 3 * ringComplex n) = f z)
    (b : O) (hb : b ≠ 0) (c : ℂ) :
    (∫ z in periodDomain, f (ringComplex b * z + c)) = ∫ z in periodDomain, f z := by
  have hshift : (∫ z in periodDomain, f (z + c)) = ∫ z in periodDomain, f z := by
    simpa only [add_comm] using period_integral_translation f hper c
  calc
    _ = ∫ z in periodDomain, f (z + c) := period_integral_eisenstein_mul _
      (hf.comp (continuous_id.add continuous_const).measurable)
      (fun n z => by simpa only [Function.comp_apply, Pi.add_apply, id_eq, add_right_comm] using hper n (z + c)) b hb
    _ = _ := hshift

end PeriodAffineAverages

lemma kernelRationalCusp_period (f : KernelQuotient → ℂ) (M : rationalExtension)
    (v : ℝ) (hv : 0 < v) (n : O) (z : ℂ) :
    f (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (M : SL(2, O)) • upperPoint (z + 3 * ringComplex n) v hv)) =
    f (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (M : SL(2, O)) • upperPoint z v hv)) := by
  simpa only [kernelRationalAction_mk] using
    congrArg (fun q => f (kernelRationalAction M q)) (kernelProjection_upper_period v hv z n)

lemma kernelRationalCusp_average_eq_enlarged (f : KernelQuotient → ℂ) (hf : Continuous f)
    (M : rationalExtension) (v : ℝ) (hv : 0 < v) (b : O) (hb : b ≠ 0) :
    (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (M : SL(2, O)) • upperPoint (ringComplex b * z) v hv))) =
    ∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (M : SL(2, O)) • upperPoint z v hv)) := by
  refine period_integral_eisenstein_mul
    (fun z => f (integralOrbitProjection globalKubotaKernel
      (integralComplexMatrix (M : SL(2, O)) • upperPoint z v hv))) ?_
    (kernelRationalCusp_period f M v hv) b hb
  exact (((hf.comp (continuous_integralOrbitProjection _)).comp (continuous_hyperbolic_action _)).comp
    (upperCoordinatesHomeomorph.continuous.comp
      (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))).measurable

/-- Enlarged cusp cells suffice: integral dilations preserve the ordinary cusp average. -/
theorem cubicSourceResidue_orthogonal_of_zero_enlarged_cusp_averages
    (F : KernelQuotientL2) (hF : (F, (8 / 9 : ℂ) • F) ∈ kernelEnergyLaplacian.graph)
    (f : KernelQuotient → ℂ) (hf : Continuous f)
    (hrep : F =ᵐ[integralQuotientVolume globalKubotaKernel] f)
    (havg : ∀ N : rationalExtension, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ∃ b : O, b ≠ 0 ∧ (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix (N : SL(2, O)) • upperPoint (ringComplex b * z) v hv))) = 0) :
    inner ℂ F (kernelRationalSourceProjection cubicEisensteinResidue) = 0 := by
  have hzero (N : rationalExtension) (v : ℝ) (hv : 0 < v) (h1 : 1 < v) :
      (∫ z in periodDomain, f (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix (N : SL(2, O)) • upperPoint z v hv))) = 0 := by
    obtain ⟨b, hb, hav⟩ := havg N v hv h1
    rw [kernelRationalCusp_average_eq_enlarged f hf N v hv b hb] at hav
    exact hav
  rw [kernelRationalSourceProjection_apply, inner_smul_right, inner_sum]
  have htranslate (g : rationalExtension) : inner ℂ F (kernelRationalPullback g cubicEisensteinResidue) = 0 := by
    rw [kernelRationalPullback_pairing_inverse]
    have hrepG : kernelRationalPullback g⁻¹ F =ᵐ[integralQuotientVolume globalKubotaKernel]
        fun q => f (kernelRationalAction g⁻¹ q) :=
      (kernelRationalPullback_ae g⁻¹ F).trans
        ((kernelRationalAction_measurePreserving g⁻¹).quasiMeasurePreserving.ae_eq_comp hrep)
    apply cubicEisensteinResidue_orthogonal_of_zero_cusp_averages _
      (kernelRational_eigenvector g⁻¹ F (8 / 9) hF) _ (hf.comp (kernelRationalAction_continuous _)) hrepG
    intro N v hv hlarge
    let N' : rationalExtension := ⟨N, levelThree_le_rationalExtension N.property⟩
    simpa only [Function.comp_apply, kernelRationalAction_mk, map_mul, mul_smul,
      Subgroup.coe_mul, integralComplexMatrix_levelThree, N'] using hzero (g⁻¹ * N') v hv hlarge
  simp only [htranslate, Finset.sum_const_zero, mul_zero]

/-- Energy compatibility supplies the adjoint eigenvector property for actual common-cover legs. -/
theorem kernelCoverLeg_source_sum_vanish_of_zero_enlarged_averages
    {H : Subgroup (SL(2, O))} {ι : Type*} [Fintype ι]
    (J : ι → Subgroup (SL(2, O))) (hHK : H ≤ globalKubotaKernel) (hJK : ∀ i, J i ≤ globalKubotaKernel)
    [∀ i, (J i).IsFiniteRelIndex globalKubotaKernel]
    (e : ∀ i, H ≃* J i) (g : ι → SL(2, ℂ)) (he : ∀ i, IntegralCoverIntertwines (e i) (g i))
    (c : ι → ℂ)
    (f : ι → KernelQuotient → ℂ) (hf : ∀ i, Continuous (f i))
    (hrep : ∀ i, ContinuousLinearMap.adjoint (kernelCoverLeg hHK (hJK i) (e i) (g i) (he i))
      (∑ j, c j • kernelCoverLeg hHK (hJK j) (e j) (g j) (he j)
        (kernelRationalSourceProjection cubicEisensteinResidue)) =ᵐ[integralQuotientVolume globalKubotaKernel] f i)
    (havg : ∀ i, ∀ N : rationalExtension, ∀ v : ℝ, ∀ hv : 0 < v, 1 < v →
      ∃ b : O, b ≠ 0 ∧ (∫ z in periodDomain, f i (integralOrbitProjection globalKubotaKernel
        (integralComplexMatrix (N : SL(2, O)) • upperPoint (ringComplex b * z) v hv))) = 0) :
    (∑ i, c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
      (kernelRationalSourceProjection cubicEisensteinResidue)) = 0 := by
  let D := ∑ i, c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
    (kernelRationalSourceProjection cubicEisensteinResidue)
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  change inner ℂ D D = 0
  change inner ℂ D (∑ i, c i • kernelCoverLeg hHK (hJK i) (e i) (g i) (he i)
    (kernelRationalSourceProjection cubicEisensteinResidue)) = 0
  rw [inner_sum]
  apply Finset.sum_eq_zero
  intro i _
  rw [inner_smul_right, ← ContinuousLinearMap.adjoint_inner_left]
  have heig := kernelCoverLeg_adjoint_sum_eigenvector J hHK hJK e g he
    (kernelRationalSourceProjection cubicEisensteinResidue) (8 / 9)
    kernelRationalSourceProjection_cubicEisensteinResidue_eigenvector c i
  rw [cubicSourceResidue_orthogonal_of_zero_enlarged_cusp_averages _ heig (f i) (hf i) (hrep i) (havg i), mul_zero]

/-- Extract a prime power up to a prescribed exponent, including the zero input. -/
lemma bounded_prime_power_factor (p a : O) (n : ℕ) :
    ∃ j ≤ n, ∃ b, a = p ^ j * b ∧ (j = n ∨ ¬ p ∣ b) := by
  induction n generalizing a with
  | zero => exact ⟨0, le_rfl, a, by simp, Or.inl rfl⟩
  | succ n ih =>
    by_cases h : p ∣ a
    · obtain ⟨a', rfl⟩ := h
      obtain ⟨j, hj, b, hb, hn⟩ := ih a'
      refine ⟨j + 1, Nat.succ_le_succ hj, b, ?_, ?_⟩
      · rw [hb, pow_succ]; ring
      · exact hn.elim (fun he => Or.inl (congrArg (fun k => k + 1) he)) Or.inr
    · exact ⟨0, Nat.zero_le _, a, by simp, Or.inr h⟩

lemma primary_pow_mod_three (p : O) (hp : lambda ^ 2 ∣ p - 1) (n : ℕ) :
    (3 : O) ∣ p ^ n - 1 := by
  simpa only [one_pow] using (three_dvd_primary_sub_one p hp).trans (sub_dvd_pow_sub_pow p 1 n)

/-- Primitive normalization of a translated prime-power branch preserves its cusp class modulo three. -/
theorem primePowerCusp_reduction (A : SL(2, O)) (p q : O) (n : ℕ)
    (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    ∃ j ≤ n, ∃ N : SL(2, O),
      A 0 0 + 3 * q * A 1 0 = p ^ j * N 0 0 ∧
      p ^ n * A 1 0 = p ^ j * N 1 0 ∧ N * A⁻¹ ∈ levelThree ∧
      (j = n ∨ ¬ p ∣ N 0 0) := by
  let a := A 0 0 + 3 * q * A 1 0
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have haC : IsCoprime a (A 1 0) := by
    refine ⟨A 1 1, -(A 0 1 + 3 * q * A 1 1), ?_⟩
    dsimp only [a]
    linear_combination hd
  obtain ⟨j, hj, b, hab, hb⟩ := bounded_prime_power_factor p a n
  have hbC : IsCoprime b (A 1 0) := by
    rw [hab] at haC
    exact haC.of_mul_left_right
  have hbY : IsCoprime b (p ^ (n - j) * A 1 0) := by
    rcases hb with h | h
    · simpa only [h, Nat.sub_self, pow_zero, one_mul] using hbC
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hbC
  have hbA : (3 : O) ∣ b - A 0 0 := by
    have h1 : (3 : O) ∣ a - A 0 0 := ⟨q * A 1 0, by dsimp only [a]; ring⟩
    have h2 : (3 : O) ∣ a - b := by
      rw [hab]
      convert (primary_pow_mod_three p hprimary j).mul_right b using 1 <;> ring
    convert dvd_sub h1 h2 using 1 <;> ring
  have hyC : (3 : O) ∣ p ^ (n - j) * A 1 0 - A 1 0 := by
    convert (primary_pow_mod_three p hprimary (n - j)).mul_right (A 1 0) using 1 <;> ring
  obtain ⟨N, hN0, hN1, hNA⟩ := exists_congruent_cusp_completion A b (p ^ (n - j) * A 1 0) hbY hbA hyC
  refine ⟨j, hj, N, ?_, ?_, hNA, ?_⟩
  · rw [hN0]; exact hab
  · rw [hN1, ← mul_assoc, ← pow_add, Nat.add_sub_of_le hj]
  · simpa only [hN0] using hb

/-- The inverse branch has the same congruence-preserving normalization. -/
theorem primePowerCusp_inverse_reduction (A : SL(2, O)) (p q : O) (n : ℕ)
    (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    ∃ j ≤ n, ∃ N : SL(2, O),
      p ^ n * A 0 0 - 3 * q * A 1 0 = p ^ j * N 0 0 ∧
      A 1 0 = p ^ j * N 1 0 ∧ N * A⁻¹ ∈ levelThree := by
  have hd : A 0 0 * A 1 1 - A 0 1 * A 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using A.property
  have hCA : IsCoprime (A 1 0) (A 0 0) := by
    refine ⟨-A 0 1, A 1 1, ?_⟩
    linear_combination hd
  obtain ⟨j, hj, c, hC, hc⟩ := bounded_prime_power_factor p (A 1 0) n
  have hcA : IsCoprime c (A 0 0) := by
    rw [hC] at hCA
    exact hCA.of_mul_left_right
  have hcY : IsCoprime c (p ^ (n - j) * A 0 0) := by
    rcases hc with h | h
    · simpa only [h, Nat.sub_self, pow_zero, one_mul] using hcA
    · exact ((hp.coprime_iff_not_dvd.mpr h).symm.pow_right).mul_right hcA
  let a := p ^ (n - j) * A 0 0 - 3 * q * c
  have hac : IsCoprime a c := by
    obtain ⟨u, v, huv⟩ := hcY
    refine ⟨v, u + 3 * q * v, ?_⟩
    dsimp only [a]
    linear_combination huv
  have ha : (3 : O) ∣ a - A 0 0 := by
    have h1 := (primary_pow_mod_three p hprimary (n - j)).mul_right (A 0 0)
    have h2 : (3 : O) ∣ 3 * q * c := ⟨q * c, by ring⟩
    convert dvd_sub h1 h2 using 1 <;> dsimp only [a] <;> ring
  have hc : (3 : O) ∣ c - A 1 0 := by
    rw [hC]
    convert dvd_neg.mpr ((primary_pow_mod_three p hprimary j).mul_right c) using 1 <;> ring
  obtain ⟨N, hN0, hN1, hNA⟩ := exists_congruent_cusp_completion A a c hac ha hc
  refine ⟨j, hj, N, ?_, by rw [hN1]; exact hC, hNA⟩
  rw [hN0, hC]
  dsimp only [a]
  have hpow : p ^ j * p ^ (n - j) = p ^ n := by rw [← pow_add, Nat.add_sub_of_le hj]
  linear_combination -(A 0 0) * hpow

lemma rationalExtension_of_congruent (A : rationalExtension) (N : SL(2, O))
    (hNA : N * (A : SL(2, O))⁻¹ ∈ levelThree) : N ∈ rationalExtension := by
  have h := rationalExtension.mul_mem (levelThree_le_rationalExtension hNA) A.property
  simpa only [inv_mul_cancel_right] using h

/-- The four possible common prime-power factors of a translated cube branch. -/
structure CubeCuspData (A : SL(2, O)) (p q : O) where
  exponent : Fin 4
  matrix : SL(2, O)
  first : A 0 0 + 3 * q * A 1 0 = p ^ exponent.val * matrix 0 0
  second : p ^ 3 * A 1 0 = p ^ exponent.val * matrix 1 0
  congruent : matrix * A⁻¹ ∈ levelThree

def actualCubeCuspData (A : SL(2, O)) (p q : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1) :
    CubeCuspData A p q := by
  let h := primePowerCusp_reduction A p q 3 hp hprimary
  let j := Classical.choose h
  have hj : j ≤ 3 := (Classical.choose_spec h).1
  let N := Classical.choose (Classical.choose_spec h).2
  have hN := Classical.choose_spec (Classical.choose_spec h).2
  exact ⟨⟨j, by omega⟩, N, hN.1, hN.2.1, hN.2.2.1⟩

lemma CubeCuspData.lower_eq {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    d.matrix 1 0 = p ^ (3 - d.exponent.val) * A 1 0 := by
  apply mul_left_cancel₀ (pow_ne_zero d.exponent.val hp)
  rw [← d.second, ← mul_assoc, ← pow_add, Nat.add_sub_of_le (by omega : d.exponent.val ≤ 3)]

lemma CubeCuspData.rational_mem {A : rationalExtension} {p q : O}
    (d : CubeCuspData (A : SL(2, O)) p q) : d.matrix ∈ rationalExtension :=
  rationalExtension_of_congruent A d.matrix d.congruent

/-- The source constant term in any rational cusp, with its exact multiplier. -/
def rationalSourceCuspConstant (M : rationalExtension) : ℂ :=
  extendedComplexCharacter M * ((9 * Real.sqrt 3 / 2 : ℝ) : ℂ) *
    (3 * (Real.pi : ℂ)) * constantArithmeticResidue

theorem rationalSourceCusp_average_enlarged_affine (M : rationalExtension) (b : O) (hb : b ≠ 0)
    (c : ℂ) (v : ℝ) (hv : 0 < v) :
    (∫ z in periodDomain, cubicSourceResidualFunction
      (integralComplexMatrix (M : SL(2, O)) • upperPoint (ringComplex b * z + c) v hv)) =
      rationalSourceCuspConstant M * (v : ℂ) ^ (2 / 3 : ℂ) := by
  have hc : Continuous (fun z : ℂ => cubicSourceResidualFunction (upperPoint z v hv)) :=
    cubicSourceResidualFunction_continuous.comp
      (upperCoordinatesHomeomorph.continuous.comp
        (show Continuous (fun z : ℂ => (⟨(z, v), hv⟩ : UpperCoordinates)) by fun_prop))
  simp_rw [cubicSourceResidualFunction_automorphy]
  rw [integral_const_mul, period_integral_eisenstein_affine _ hc.measurable
    (fun n z => cubicSourceResidualFunction_period v hv z n) b hb c,
    cubicSourceResidualFunction_fourier_zero]
  unfold rationalSourceCuspConstant
  ring

lemma rationalExtension_entry_integer (M : rationalExtension) (i j : Fin 2) :
    ∃ r : ℤ, (3 : O) ∣ (M : SL(2, O)) i j - (r : O) := by
  obtain ⟨n, r, hr⟩ := M.property
  let red := Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
  have hn : red (n : SL(2, O)) = 1 := n.property
  have he : red (M : SL(2, O)) = red (rationalEmbedding r) := by rw [← hr, map_mul, hn, one_mul]
  refine ⟨r i j, Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp ?_)⟩
  exact congrArg (fun A : SL(2, O ⧸ Ideal.span {(3 : O)}) => A i j) he

/-- A determinant-one matrix with reduced first row and lower-left entry is the identity modulo three. -/
lemma integralMatrix_levelThree_of_entries (N : SL(2, O))
    (h00 : (3 : O) ∣ N 0 0 - 1) (h01 : (3 : O) ∣ N 0 1) (h10 : (3 : O) ∣ N 1 0) : N ∈ levelThree := by
  let R := O ⧸ Ideal.span {(3 : O)}
  let red := Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
  have ha : red N 0 0 = (1 : R) := by
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr h00)
  have hb : red N 0 1 = (0 : R) := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h01)
  have hc : red N 1 0 = (0 : R) := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr h10)
  have hd : red N 1 1 = (1 : R) := by
    have hdet := (red N).property
    simpa only [Matrix.det_fin_two, ha, hb, hc, one_mul, zero_mul, sub_zero] using hdet
  change red N = 1
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  fin_cases i <;> fin_cases j
  · exact ha
  · exact hb
  · exact hc
  · exact hd

/-- On the rational extension, a primary upper-left entry reads the character from the first column. -/
theorem extendedComplexCharacter_primary (M : rationalExtension)
    (hM : lambda ^ 2 ∣ (M : SL(2, O)) 0 0 - 1) :
    extendedComplexCharacter M = ringComplex (symbol ((M : SL(2, O)) 1 0) ((M : SL(2, O)) 0 0)) := by
  obtain ⟨b, hb⟩ := rationalExtension_entry_integer M 0 1
  obtain ⟨c, hc⟩ := rationalExtension_entry_integer M 1 0
  let L : SL(2, ℤ) := ⟨!![1, 0; -c, 1], by simp [Matrix.det_fin_two]⟩
  let U := rationalUnipotent (-b)
  let L' := rationalSourceLift L
  let U' := rationalSourceLift U
  let N := L' * M * U'
  have hN00 : (N : SL(2, O)) 0 0 = (M : SL(2, O)) 0 0 := by
    simp [N, L', U', L, U, rationalSourceLift, rationalEmbedding, rationalUnipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have hN01 : (N : SL(2, O)) 0 1 = (M : SL(2, O)) 0 1 - (b : O) * (M : SL(2, O)) 0 0 := by
    simp [N, L', U', L, U, rationalSourceLift, rationalEmbedding, rationalUnipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have hN10 : (N : SL(2, O)) 1 0 = (M : SL(2, O)) 1 0 - (c : O) * (M : SL(2, O)) 0 0 := by
    simp [N, L', U', L, U, rationalSourceLift, rationalEmbedding, rationalUnipotent,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  have ha := three_dvd_primary_sub_one _ hM
  have hn : (N : SL(2, O)) ∈ levelThree := by
    apply integralMatrix_levelThree_of_entries
    · rwa [hN00]
    · rw [hN01]
      convert dvd_sub hb (ha.mul_left (b : O)) using 1 <;> ring
    · rw [hN10]
      convert dvd_sub hc (ha.mul_left (c : O)) using 1 <;> ring
  have hchar : extendedComplexCharacter N = extendedComplexCharacter M := by
    dsimp only [N]
    rw [map_mul, map_mul, extendedComplexCharacter_sourceLift, extendedComplexCharacter_sourceLift, one_mul, mul_one]
  have hres : extendedComplexCharacter N = complexCharacter ⟨(N : SL(2, O)), hn⟩ :=
    extendedComplexCharacter_restrict ⟨(N : SL(2, O)), hn⟩
  rw [← hchar, hres]
  change ringComplex (symbol ((N : SL(2, O)) 1 0) ((N : SL(2, O)) 0 0)) = _
  rw [hN00, hN10]
  apply congrArg ringComplex
  apply symbol_congr
  exact ⟨-(c : O), by ring⟩

lemma integer_congruence_primary_cases (c : O) (r : ℤ) (h : (3 : O) ∣ c - (r : O)) :
    (3 : O) ∣ c ∨ lambda ^ 2 ∣ c - 1 ∨ lambda ^ 2 ∣ -c - 1 := by
  have hr : (3 : ℤ) ∣ r ∨ (3 : ℤ) ∣ r - 1 ∨ (3 : ℤ) ∣ r + 1 := by omega
  rcases hr with hr | hr | hr
  · left
    obtain ⟨t, ht⟩ := hr
    have hn : (3 : O) ∣ (r : O) := ⟨(t : O), by exact_mod_cast ht⟩
    simpa only [sub_add_cancel] using dvd_add h hn
  · right; left
    obtain ⟨t, ht⟩ := hr
    have hn : (3 : O) ∣ (r : O) - 1 := ⟨(t : O), by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    simpa only [sub_add_sub_cancel] using dvd_add h hn
  · right; right
    obtain ⟨t, ht⟩ := hr
    have hn : (3 : O) ∣ (r : O) + 1 := ⟨(t : O), by exact_mod_cast ht⟩
    apply lambda_sq_dvd_three.trans
    convert dvd_neg.mpr (dvd_add h hn) using 1 <;> ring

lemma symbol_three_shift_primary (c a t : O) (hc : lambda ^ 2 ∣ c - 1) (ha : lambda ^ 2 ∣ a - 1) :
    symbol c (a + 3 * t * c) = symbol c a := by
  have hs : lambda ^ 2 ∣ a + 3 * t * c - 1 := by
    convert dvd_add ha ((lambda_sq_dvd_three.mul_right t).mul_right c) using 1 <;> ring
  rw [symbol_reciprocity c _ hc hs]
  calc
    symbol (a + 3 * t * c) c = symbol a c := symbol_congr ⟨3 * t, by ring⟩
    _ = symbol c a := symbol_reciprocity a c ha hc

lemma symbol_three_shift_integer (c a t : O) (r : ℤ)
    (ha : lambda ^ 2 ∣ a - 1) (hc : (3 : O) ∣ c - (r : O)) :
    symbol c (a + 3 * t * c) = symbol c a := by
  rcases integer_congruence_primary_cases c r hc with h | h | h
  · exact symbol_three_shift c a t ha h
  · exact symbol_three_shift_primary c a t h ha
  · have hh := symbol_three_shift_primary (-c) a (-t) h ha
    have hs : lambda ^ 2 ∣ a + 3 * t * c - 1 := by
      convert dvd_add ha ((lambda_sq_dvd_three.mul_right t).mul_right c) using 1 <;> ring
    rw [show a + 3 * (-t) * (-c) = a + 3 * t * c by ring,
      symbol_neg_numerator _ _ hs, symbol_neg_numerator _ _ ha] at hh
    exact hh

lemma principalResidueRep_mk_sub_dvd (c a : O) :
    c ∣ principalResidueRep c (Ideal.Quotient.mk (Ideal.span {c}) a) - a :=
  Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp (principalResidueRep_spec _ _))

/-- A residue modulo a prime cube is its exact valuation and an invertible residual factor. -/
abbrev CubeResidueStrata (p : O) := Σ j : Fin 4, CubicUnitResidue (p ^ (3 - j.val))

def cubeResidueStratumMap (p : O) (x : CubeResidueStrata p) : CubeResidues p :=
  Ideal.Quotient.mk _ (p ^ x.1.val * principalResidueRep (p ^ (3 - x.1.val)) x.2.1)

lemma cubicUnitResidue_rep_coprime (c : O) (x : CubicUnitResidue c) : IsCoprime c (principalResidueRep c x.1) := by
  apply (isUnit_quotient_span_iff _ _).mp
  simpa only [principalResidueRep_spec] using x.2

lemma cube_strata_exponents (p : O) (hp : Prime p) (j k : Fin 4) (b d : O)
    (hb : IsCoprime (p ^ (3 - j.val)) b) (he : p ^ 3 ∣ p ^ j.val * b - p ^ k.val * d) : ¬j.val < k.val := by
  intro hjk
  have hj3 : j.val + 1 ≤ 3 := by omega
  have hjk' : j.val + 1 ≤ k.val := by omega
  have h1 : p ^ (j.val + 1) ∣ p ^ j.val * b - p ^ k.val * d := (pow_dvd_pow p hj3).trans he
  have h2 : p ^ (j.val + 1) ∣ p ^ k.val * d := dvd_mul_of_dvd_left (pow_dvd_pow p hjk') d
  have h3 : p ^ (j.val + 1) ∣ p ^ j.val * b := by simpa only [sub_add_cancel] using dvd_add h1 h2
  rw [pow_succ] at h3
  have hpb : p ∣ b := (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp h3
  have hpc : IsCoprime p b := hb.of_isCoprime_of_dvd_left (dvd_pow_self p (by omega : 3 - j.val ≠ 0))
  exact (hp.coprime_iff_not_dvd.mp hpc) hpb

lemma cubeResidueStratumMap_injective (p : O) (hp : Prime p) : Function.Injective (cubeResidueStratumMap p) := by
  rintro ⟨j, b⟩ ⟨k, d⟩ he
  have hd : p ^ 3 ∣ p ^ j.val * principalResidueRep (p ^ (3 - j.val)) b.1 -
      p ^ k.val * principalResidueRep (p ^ (3 - k.val)) d.1 :=
    Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)
  have hle := cube_strata_exponents p hp j k _ _ (cubicUnitResidue_rep_coprime _ b) hd
  have hge := cube_strata_exponents p hp k j _ _ (cubicUnitResidue_rep_coprime _ d)
    (by simpa only [neg_sub] using dvd_neg.mpr hd)
  have hjk : j = k := Fin.ext (by omega)
  subst k
  have hpow : p ^ 3 = p ^ j.val * p ^ (3 - j.val) := by rw [← pow_add, Nat.add_sub_of_le (by omega : j.val ≤ 3)]
  rw [hpow, ← mul_sub] at hd
  have hrep := (mul_dvd_mul_iff_left (pow_ne_zero j.val hp.ne_zero)).mp hd
  have hbd : b = d := by
    apply Subtype.ext
    rw [← principalResidueRep_spec (p ^ (3 - j.val)) b.1,
      ← principalResidueRep_spec (p ^ (3 - j.val)) d.1]
    exact (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr (Ideal.mem_span_singleton.mpr hrep)
  subst d
  rfl

lemma cubeResidueStratumMap_surjective (p : O) (hp : Prime p) : Function.Surjective (cubeResidueStratumMap p) := by
  intro r
  let a := principalResidueRep (p ^ 3) r
  obtain ⟨j, hj, b, hab, hb⟩ := bounded_prime_power_factor p a 3
  have hcop : IsCoprime (p ^ (3 - j)) b := by
    rcases hb with h | h
    · simp only [h, Nat.sub_self, pow_zero, isCoprime_one_left]
    · exact (hp.coprime_iff_not_dvd.mpr h).pow_left
  let u : CubicUnitResidue (p ^ (3 - j)) := ⟨Ideal.Quotient.mk _ b, (isUnit_quotient_span_iff _ _).mpr hcop⟩
  refine ⟨⟨⟨j, by omega⟩, u⟩, ?_⟩
  change Ideal.Quotient.mk (Ideal.span {p ^ 3}) (p ^ j * principalResidueRep (p ^ (3 - j)) u.1) = r
  rw [← principalResidueRep_spec (p ^ 3) r]
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p ^ 3 ∣ p ^ j * principalResidueRep (p ^ (3 - j)) (Ideal.Quotient.mk _ b) - a
  rw [hab, ← mul_sub, show p ^ 3 = p ^ j * p ^ (3 - j) by rw [← pow_add, Nat.add_sub_of_le hj]]
  exact mul_dvd_mul_left _ (principalResidueRep_mk_sub_dvd _ _)

def cubeResidueStrataEquiv (p : O) (hp : Prime p) : CubeResidueStrata p ≃ CubeResidues p :=
  Equiv.ofBijective (cubeResidueStratumMap p)
    ⟨cubeResidueStratumMap_injective p hp, cubeResidueStratumMap_surjective p hp⟩

/-- The cubic character on an exact valuation stratum. -/
def cubeStratumSymbol (p C : O) (j : Fin 4) (b : CubicUnitResidue (p ^ (3 - j.val))) : ℂ :=
  ringComplex (symbol (principalResidueRep (p ^ (3 - j.val)) b.1 * C) (p ^ (3 - j.val)))

lemma cubeUnitStratum_symbol_gauss (p C : O) (n : ℕ) :
    (∑' b : CubicUnitResidue (p ^ n), ringComplex (symbol (principalResidueRep (p ^ n) b.1 * C) (p ^ n))) =
      cubicUnitGaussSum 0 (p ^ n) * ringComplex (symbol C (p ^ n)) := by
  rw [cubicUnitGaussSum]
  simp only [mul_zero, residueAdditive, map_zero, cuspFrequency, zero_div, zero_mul,
    AddChar.map_zero_eq_one, mul_one]
  rw [← tsum_mul_right]
  apply tsum_congr
  intro b
  rw [symbol_mul_numerator, map_mul]

lemma cubeStratumSymbol_sum (p C : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (hC : IsCoprime C p) (j : Fin 4) :
    (∑' b : CubicUnitResidue (p ^ (3 - j.val)), cubeStratumSymbol p C j b) =
      if j = 0 then (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1)
      else if j = 3 then 1 else 0 := by
  have h3 : ringComplex (symbol C (p ^ 3)) = 1 := by
    rw [symbol_pow_denominator, symbol_cube_of_isCoprime C p hprimary hC, map_one]
  unfold cubeStratumSymbol
  rw [cubeUnitStratum_symbol_gauss p C (3 - j.val)]
  fin_cases j
  · have hh := cubicUnitGaussSum_prime_power_zero p hp hprimary 2
    norm_num at hh ⊢
    rw [hh, h3, mul_one]
  · have hh := cubicUnitGaussSum_prime_power_zero p hp hprimary 1
    norm_num at hh ⊢
    simp [hh]
  · have hh := cubicUnitGaussSum_prime_power_zero p hp hprimary 0
    norm_num at hh ⊢
    simp [hh]
  · simp

lemma cubeStrata_weighted_sum (p C : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (hC : IsCoprime C p) (w : Fin 4 → ℂ) :
    (∑ j : Fin 4, w j * ∑' b : CubicUnitResidue (p ^ (3 - j.val)), cubeStratumSymbol p C j b) =
      w 0 * (Ideal.absNorm (Ideal.span {p}) : ℂ) ^ 2 * ((Ideal.absNorm (Ideal.span {p}) : ℂ) - 1) + w 3 := by
  simp_rw [cubeStratumSymbol_sum p C hp hprimary hC]
  simp [Fin.sum_univ_succ] <;> ring

lemma integralMatrix_comparison_mod_three (A N : SL(2, O)) (hNA : N * A⁻¹ ∈ levelThree)
    (i j : Fin 2) : (3 : O) ∣ N i j - A i j := by
  let red := Matrix.SpecialLinearGroup.map (n := Fin 2) (Ideal.Quotient.mk (Ideal.span {(3 : O)}))
  have hh : red (N * A⁻¹) = 1 := hNA
  rw [map_mul, map_inv] at hh
  have he := congrArg (fun M : SL(2, O ⧸ Ideal.span {(3 : O)}) => M i j) (mul_inv_eq_one.mp hh)
  exact Ideal.mem_span_singleton.mp ((Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mp he)

lemma integralMatrix_comparison_primary (A N : SL(2, O)) (hNA : N * A⁻¹ ∈ levelThree)
    (hA : lambda ^ 2 ∣ A 0 0 - 1) : lambda ^ 2 ∣ N 0 0 - 1 := by
  have h := lambda_sq_dvd_three.trans (integralMatrix_comparison_mod_three A N hNA 0 0)
  simpa only [sub_add_sub_cancel] using dvd_add h hA

/-- Reciprocity balances the multipliers before and after extracting the common prime power. -/
lemma rationalCusp_cube_phase_balance (A N : rationalExtension) (p q : O) (j : ℕ)
    (hp : lambda ^ 2 ∣ p - 1)
    (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1) (hN : lambda ^ 2 ∣ (N : SL(2, O)) 0 0 - 1)
    (hx : (A : SL(2, O)) 0 0 + 3 * q * (A : SL(2, O)) 1 0 = p ^ j * (N : SL(2, O)) 0 0)
    (hc : (N : SL(2, O)) 1 0 = p ^ (3 - j) * (A : SL(2, O)) 1 0) :
    extendedComplexCharacter N * ringComplex (symbol ((A : SL(2, O)) 1 0) p) ^ j =
      extendedComplexCharacter A * ringComplex (symbol ((N : SL(2, O)) 0 0) p) ^ (3 - j) := by
  obtain ⟨r, hr⟩ := rationalExtension_entry_integer A 1 0
  have hs : symbol ((A : SL(2, O)) 1 0) ((A : SL(2, O)) 0 0) =
      symbol ((A : SL(2, O)) 1 0) p ^ j * symbol ((A : SL(2, O)) 1 0) ((N : SL(2, O)) 0 0) := by
    rw [← symbol_three_shift_integer _ _ q r hA hr, hx, symbol_mul_denominator, symbol_pow_denominator]
  rw [extendedComplexCharacter_primary N hN, extendedComplexCharacter_primary A hA, hc,
    symbol_mul_numerator, symbol_pow_numerator _ _ hN,
    symbol_reciprocity p ((N : SL(2, O)) 0 0) hp hN,
    hs, map_mul, map_pow, map_mul, map_pow]
  ring

lemma rationalCusp_comparison_character (A N : rationalExtension)
    (hNA : (N : SL(2, O)) * (A : SL(2, O))⁻¹ ∈ levelThree) :
    complexCharacter ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, hNA⟩ * extendedComplexCharacter A =
      extendedComplexCharacter N := by
  rw [← extendedComplexCharacter_restrict ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, hNA⟩]
  change extendedComplexCharacter (N * A⁻¹) * extendedComplexCharacter A = extendedComplexCharacter N
  rw [← map_mul, inv_mul_cancel_right]

lemma rationalCusp_cube_comparison_phase (A N : rationalExtension) (p q : O) (j : ℕ) (hj : j ≤ 3)
    (hp : lambda ^ 2 ∣ p - 1)
    (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1) (hN : lambda ^ 2 ∣ (N : SL(2, O)) 0 0 - 1)
    (hx : (A : SL(2, O)) 0 0 + 3 * q * (A : SL(2, O)) 1 0 = p ^ j * (N : SL(2, O)) 0 0)
    (hc : (N : SL(2, O)) 1 0 = p ^ (3 - j) * (A : SL(2, O)) 1 0)
    (hC : IsCoprime ((A : SL(2, O)) 1 0) p)
    (hNA : (N : SL(2, O)) * (A : SL(2, O))⁻¹ ∈ levelThree) :
    complexCharacter ⟨(N : SL(2, O)) * (A : SL(2, O))⁻¹, hNA⟩ =
      ringComplex (symbol ((N : SL(2, O)) 0 0 * (A : SL(2, O)) 1 0) p) ^ (3 - j) := by
  let a := ringComplex (symbol ((A : SL(2, O)) 1 0) p)
  let b := ringComplex (symbol ((N : SL(2, O)) 0 0) p)
  have ha3 : a ^ 3 = 1 := by
    dsimp only [a]
    rw [← map_pow, symbol_cube_of_isCoprime _ _ hp hC, map_one]
  have hpow : a ^ j * a ^ (3 - j) = 1 := by rw [← pow_add, Nat.add_sub_of_le hj, ha3]
  have hbal := rationalCusp_cube_phase_balance A N p q j hp hA hN hx hc
  change extendedComplexCharacter N * a ^ j = extendedComplexCharacter A * b ^ (3 - j) at hbal
  have he : extendedComplexCharacter N = extendedComplexCharacter A * (b * a) ^ (3 - j) := by
    calc
      _ = extendedComplexCharacter N * (a ^ j * a ^ (3 - j)) := by rw [hpow, mul_one]
      _ = (extendedComplexCharacter N * a ^ j) * a ^ (3 - j) := (mul_assoc _ _ _).symm
      _ = (extendedComplexCharacter A * b ^ (3 - j)) * a ^ (3 - j) := by rw [hbal]
      _ = _ := by rw [mul_pow]; ring
  have hbase : extendedComplexCharacter A ≠ 0 := by
    intro hz
    have hh := extendedComplexCharacter_cube A
    rw [hz] at hh
    norm_num at hh
  rw [symbol_mul_numerator, map_mul]
  apply mul_right_cancel₀ hbase
  rw [rationalCusp_comparison_character A N hNA, he]
  ring

lemma CubeCuspData.unit_top {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p ^ (3 - d.exponent.val)}) (d.matrix 0 0)) := by
  apply (isUnit_quotient_span_iff _ _).mpr
  refine ⟨-d.matrix 0 1 * A 1 0, d.matrix 1 1, ?_⟩
  have hd : d.matrix 0 0 * d.matrix 1 1 - d.matrix 0 1 * d.matrix 1 0 = 1 := by
    simpa only [Matrix.det_fin_two] using d.matrix.property
  rw [d.lower_eq hp] at hd
  linear_combination hd

def CubeCuspData.stratum {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) : CubeResidueStrata p :=
  ⟨d.exponent, ⟨Ideal.Quotient.mk _ (d.matrix 0 0), d.unit_top hp⟩⟩

lemma CubeCuspData.stratum_map {A : SL(2, O)} {p q : O} (d : CubeCuspData A p q) (hp : p ≠ 0) :
    cubeResidueStratumMap p (d.stratum hp) = Ideal.Quotient.mk (Ideal.span {p ^ 3}) (A 0 0 + 3 * q * A 1 0) := by
  apply (Ideal.Quotient.mk_eq_mk_iff_sub_mem _ _).mpr
  apply Ideal.mem_span_singleton.mpr
  change p ^ 3 ∣ p ^ d.exponent.val * principalResidueRep (p ^ (3 - d.exponent.val))
    (Ideal.Quotient.mk _ (d.matrix 0 0)) - (A 0 0 + 3 * q * A 1 0)
  rw [d.first, ← mul_sub]
  have hpow : p ^ 3 = p ^ d.exponent.val * p ^ (3 - d.exponent.val) := by
    rw [← pow_add, Nat.add_sub_of_le (by omega : d.exponent.val ≤ 3)]
  rw [hpow]
  exact mul_dvd_mul_left _ (principalResidueRep_mk_sub_dvd _ _)

lemma CubeCuspData.comparison_phase {p q : O} (A : rationalExtension)
    (d : CubeCuspData (A : SL(2, O)) p q) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (hA : lambda ^ 2 ∣ (A : SL(2, O)) 0 0 - 1) (hC : IsCoprime ((A : SL(2, O)) 1 0) p) :
    complexCharacter ⟨d.matrix * (A : SL(2, O))⁻¹, d.congruent⟩ =
      cubeStratumSymbol p ((A : SL(2, O)) 1 0) d.exponent (d.stratum hp.ne_zero).2 := by
  let N : rationalExtension := ⟨d.matrix, d.rational_mem⟩
  have hN := integralMatrix_comparison_primary (A : SL(2, O)) d.matrix d.congruent hA
  have he := rationalCusp_cube_comparison_phase A N p q d.exponent.val
    (by omega : d.exponent.val ≤ 3) hprimary hA hN d.first (d.lower_eq hp.ne_zero) hC d.congruent
  rw [he]
  unfold cubeStratumSymbol
  rw [← map_pow, ← symbol_pow_denominator]
  apply congrArg ringComplex
  apply symbol_congr
  have hd := principalResidueRep_mk_sub_dvd (p ^ (3 - d.exponent.val)) (d.matrix 0 0)
  change p ^ (3 - d.exponent.val) ∣ d.matrix 0 0 * (A : SL(2, O)) 1 0 -
    principalResidueRep (p ^ (3 - d.exponent.val)) (Ideal.Quotient.mk _ (d.matrix 0 0)) * (A : SL(2, O)) 1 0
  convert (dvd_neg.mpr hd).mul_right ((A : SL(2, O)) 1 0) using 1 <;> ring

lemma cube_affine_coefficient_unit (p C : O) (hprimary : lambda ^ 2 ∣ p - 1) (hC : IsCoprime C p) :
    IsUnit (Ideal.Quotient.mk (Ideal.span {p ^ 3}) (3 * C)) := by
  obtain ⟨t, ht⟩ := three_dvd_primary_sub_one p hprimary
  have hp3 : IsCoprime p (3 : O) := by
    refine ⟨1, -t, ?_⟩
    linear_combination ht
  apply (isUnit_quotient_span_iff _ _).mpr
  exact hp3.pow_left.mul_right hC.symm.pow_left

def cubeCuspAffineEquiv (p A C : O) (hprimary : lambda ^ 2 ∣ p - 1) (hC : IsCoprime C p) : CubeResidues p ≃ CubeResidues p := by
  let a := Ideal.Quotient.mk (Ideal.span {p ^ 3}) A
  let u := (cube_affine_coefficient_unit p C hprimary hC).unit
  exact {
    toFun := fun r => a + (u : _) * r
    invFun := fun r => (↑u⁻¹ : _) * (r - a)
    left_inv := fun r => by simp only [add_sub_cancel_left, ← mul_assoc, Units.inv_mul, one_mul]
    right_inv := fun r => by simp only [← mul_assoc, Units.mul_inv, one_mul, add_sub_cancel] }

lemma cubeCuspAffineEquiv_mk (p A C q : O) (hprimary : lambda ^ 2 ∣ p - 1) (hC : IsCoprime C p) :
    cubeCuspAffineEquiv p A C hprimary hC (Ideal.Quotient.mk _ q) =
      Ideal.Quotient.mk (Ideal.span {p ^ 3}) (A + 3 * q * C) := by
  simp only [cubeCuspAffineEquiv, Equiv.coe_fn_mk, IsUnit.unit_spec, map_add, map_mul]
  ring

/-- Weighted multiplier sum over the actual translated cube branches. -/
def actualCubeCuspPhaseSum (A : rationalExtension) (p : O) (hp : Prime p) (hprimary : lambda ^ 2 ∣ p - 1)
    (w : Fin 4 → ℂ) : ℂ :=
  ∑' r : CubeResidues p,
    let d := actualCubeCuspData (A : SL(2, O)) p (cubeResidueRepresentative p r) hp hprimary
    w d.exponent * complexCharacter ⟨d.matrix * (A : SL(2, O))⁻¹, d.congruent⟩

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
