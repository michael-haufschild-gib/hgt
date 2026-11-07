/-
The incoming L² correction and its residue adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicMeromorphicResolvent
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicCompactHeightProfiles

/-!
# Meromorphic correction and spectral residue of the incoming family

Apply the actual quotient resolvent to the entire incoming defect.
The local spectral decomposition gives a simple-pole numerator and its
finite-dimensional residue at `s=4/3`, satisfying the eigenvalue equation
with eigenvalue `8/9`. These statements do not assert residue nonvanishing.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

def kernelEisensteinL2Correction (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  kernelEisensteinResolvent s (kernelL2Defect a b ha hab s)

lemma kernelEisensteinL2Correction_meromorphicAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelEisensteinL2Correction a b ha hab) (4/3:ℂ) :=
  kernelEisensteinResolvent_forcing_meromorphicAt _
    ((kernelL2Defect_entire a b ha hab).analyticAt (4/3)).meromorphicAt

lemma kernelEisensteinL2Correction_analyticAt_nonreal
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelEisensteinL2Correction a b ha hab) s := by
  exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab s,kernelEisensteinResolvent s)).comp₂
      ((kernelL2Defect_entire a b ha hab).analyticAt s)
      (kernelEisensteinResolvent_analyticAt_nonreal s hs hi)

lemma kernelEisensteinL2Correction_graph (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s))) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelSpectralResolvent_graph _ hs _

lemma kernelEisensteinL2Correction_graph_nonreal (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph :=
  kernelEisensteinL2Correction_graph a b ha hab s
    (kernelSpectralFormOperator_isUnit_nonreal _ (kernelEisensteinSpectralParameter_nonreal s hs hi))

lemma kernelEisensteinL2Correction_graph_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
    (kernelEisensteinL2Correction a b ha hab s,
      kernelL2Defect a b ha hab s + kernelEisensteinSpectralParameter s •
        kernelEisensteinL2Correction a b ha hab s)∈kernelEnergyLaplacian.graph := by
  filter_upwards [kernelEisensteinPencil_eventually_isUnit] with s hs
  exact kernelEisensteinL2Correction_graph a b ha hab s hs

lemma kernelEisensteinL2Correction_unique (a b : ℝ) (ha : 0<a) (hab : a<b)
    (s : ℂ) (hs : IsUnit (kernelSpectralFormOperator (kernelEisensteinSpectralParameter s)))
    (u : KernelQuotientL2)
    (hu : (u,kernelL2Defect a b ha hab s+kernelEisensteinSpectralParameter s•u)∈kernelEnergyLaplacian.graph) :
    kernelEisensteinL2Correction a b ha hab s=u :=
  kernelSpectralResolvent_unique _ hs _ _ hu

open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelThetaMassProjection : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM kernelThetaNull.starProjection

def kernelRegularL2Resolvent (z : ℂ) : KernelQuotientL2→L[ℂ]KernelQuotientL2 :=
  kernelL2SandwichCLM (kernelRegularInverseLift z)

lemma kernelRegularL2Resolvent_analyticAt :
    AnalyticAt ℂ kernelRegularL2Resolvent (8/9:ℂ) := by
  exact (ContinuousLinearMap.analyticAt (𝕜 := ℂ)
    (E := KernelEnergyGraph→L[ℂ]KernelEnergyGraph)
    (F := KernelQuotientL2→L[ℂ]KernelQuotientL2) kernelL2SandwichCLM
      (kernelRegularInverseLift (8/9))).comp_of_eq kernelRegularInverseLift_analyticAt rfl

lemma kernelSpectralResolvent_decomposition (z : ℂ) (hne : z≠8/9)
    (hz : IsUnit (kernelRegularPencil z)) (F : KernelQuotientL2) :
    kernelSpectralResolvent z F=((17/9)/(8/9-z):ℂ)•kernelThetaMassProjection F+
      kernelRegularL2Resolvent z F := by
  unfold kernelSpectralResolvent
  rw [←kernelLocalEnergyResolvent_eq_inverse z hne hz]
  simp only [kernelLocalEnergyResolvent,map_add,map_smul,_root_.add_apply,
    _root_.smul_apply,kernelThetaMassProjection,kernelRegularL2Resolvent]

def kernelEisensteinCorrectionNumerator (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    KernelQuotientL2 :=
  ((17/9)/(s-2/3):ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab s)+
    (s-4/3)•kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)
      (kernelL2Defect a b ha hab s)

def kernelEisensteinResidueVector (a b : ℝ) (ha : 0<a) (hab : a<b) : KernelQuotientL2 :=
  (17/6:ℂ)•kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))

lemma kernelEisensteinCorrectionNumerator_center (a b : ℝ) (ha : 0<a) (hab : a<b) :
    kernelEisensteinCorrectionNumerator a b ha hab (4/3)=kernelEisensteinResidueVector a b ha hab := by
  simp only [kernelEisensteinCorrectionNumerator,kernelEisensteinResidueVector,sub_self,zero_smul,add_zero]
  congr 1
  norm_num

lemma kernelEisensteinCorrectionNumerator_analyticAt (a b : ℝ) (ha : 0<a) (hab : a<b) :
    AnalyticAt ℂ (kernelEisensteinCorrectionNumerator a b ha hab) (4/3:ℂ) := by
  have hf := (kernelL2Defect_entire a b ha hab).analyticAt (4/3:ℂ)
  have hp := (ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2)
    (F := KernelQuotientL2) kernelThetaMassProjection (kernelL2Defect a b ha hab (4/3))).comp_of_eq hf rfl
  have hr : AnalyticAt ℂ (fun s => kernelRegularL2Resolvent (kernelEisensteinSpectralParameter s)) (4/3:ℂ) := by
    have hreg : AnalyticAt ℂ kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularL2Resolvent_analyticAt
    exact hreg.comp_of_eq (by unfold kernelEisensteinSpectralParameter; fun_prop) rfl
  have happ := ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
    (kernelL2Defect a b ha hab (4/3),kernelRegularL2Resolvent (kernelEisensteinSpectralParameter (4/3)))).comp₂ hf hr
  have hscalar : AnalyticAt ℂ (fun s : ℂ => (17/9)/(s-2/3)) (4/3:ℂ) := by
    apply AnalyticAt.div analyticAt_const (analyticAt_id.sub analyticAt_const)
    norm_num
  exact (hscalar.smul hp).add ((analyticAt_id.sub analyticAt_const).smul happ)

lemma kernelEisensteinCorrectionNumerator_eventually (a b : ℝ) (ha : 0<a) (hab : a<b) :
    ∀ᶠ s : ℂ in 𝓝[≠] (4/3:ℂ),
      (s-4/3)•kernelEisensteinL2Correction a b ha hab s=
        kernelEisensteinCorrectionNumerator a b ha hab s := by
  have hc : ContinuousAt kernelEisensteinSpectralParameter (4/3:ℂ) := by
    unfold kernelEisensteinSpectralParameter
    fun_prop
  have hp : ∀ᶠ s : ℂ in 𝓝 (4/3:ℂ), IsUnit (kernelRegularPencil (kernelEisensteinSpectralParameter s)) := by
    have hh : ∀ᶠ z : ℂ in 𝓝 (kernelEisensteinSpectralParameter (4/3)), IsUnit (kernelRegularPencil z) := by
      rw [kernelEisensteinSpectralParameter_center]
      exact kernelRegularPencil_eventually_isUnit
    exact hc.eventually hh
  filter_upwards [hp.filter_mono nhdsWithin_le_nhds,
    eventually_ne_nhdsWithin (show (4/3:ℂ)≠2/3 by norm_num),self_mem_nhdsWithin] with s hs htwo hfour
  have hfactor : (8/9:ℂ)-kernelEisensteinSpectralParameter s=(s-4/3)*(s-2/3) := by
    unfold kernelEisensteinSpectralParameter
    ring
  have hne : kernelEisensteinSpectralParameter s≠8/9 := by
    intro he
    have hh := mul_ne_zero (sub_ne_zero.mpr hfour) (sub_ne_zero.mpr htwo)
    rw [←hfactor,he,sub_self] at hh
    exact hh rfl
  change (s-4/3)•kernelSpectralResolvent (kernelEisensteinSpectralParameter s)
    (kernelL2Defect a b ha hab s)=_
  rw [kernelSpectralResolvent_decomposition _ hne hs,smul_add,smul_smul]
  have hscalar : (s-4/3)*((17/9)/(8/9-kernelEisensteinSpectralParameter s))=(17/9)/(s-2/3) := by
    rw [hfactor]
    have hcancel (x y c : ℂ) (hx : x≠0) : x*(c/(x*y))=c/y := by
      rw [div_eq_mul_inv,mul_inv_rev]
      calc
        _ = (x*x⁻¹)*(c*y⁻¹) := by ring
        _ = c/y := by rw [mul_inv_cancel₀ hx,one_mul,div_eq_mul_inv]
    exact hcancel _ _ _ (sub_ne_zero.mpr hfour)
  rw [hscalar]
  rfl

lemma kernelEisensteinResidueVector_limit (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelEisensteinL2Correction a b ha hab s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 (kernelEisensteinResidueVector a b ha hab)) := by
  apply (tendsto_congr' (kernelEisensteinCorrectionNumerator_eventually a b ha hab)).mpr
  rw [←kernelEisensteinCorrectionNumerator_center a b ha hab]
  exact (kernelEisensteinCorrectionNumerator_analyticAt a b ha hab).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

instance kernelThetaMassProjection_range_finiteDimensional :
    FiniteDimensional ℂ kernelThetaMassProjection.range := by
  let B : kernelThetaNull→L[ℂ]KernelQuotientL2 := kernelEnergyMass.comp kernelThetaNull.subtypeL
  have : FiniteDimensional ℂ B.range := LinearMap.finiteDimensional_range B.toLinearMap
  apply Submodule.finiteDimensional_of_le (S₂ := B.range)
  rintro y ⟨x,rfl⟩
  exact ⟨kernelThetaNull.orthogonalProjectionOnto (kernelEnergyMass.adjoint x),rfl⟩

lemma kernelEisensteinResidueVector_graph (a b : ℝ) (ha : 0<a) (hab : a<b) :
    (kernelEisensteinResidueVector a b ha hab,(8/9:ℂ)•kernelEisensteinResidueVector a b ha hab)
      ∈kernelEnergyLaplacian.graph := by
  let v : KernelEnergyGraph := (17/6:ℂ)•kernelThetaNull.starProjection
    (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3)))
  have hv : kernelSpectralFormOperator (8/9) v=kernelVariationalSolution 0 := by
    change kernelSpectralFormOperator (8/9) ((17/6:ℂ)•kernelThetaNull.starProjection _)=_
    rw [map_smul]
    have hz : kernelSpectralFormOperator (8/9) (kernelThetaNull.starProjection
        (kernelVariationalSolution (kernelL2Defect a b ha hab (4/3))))=0 :=
      kernelThetaNull.starProjection_apply_mem _
    rw [hz,smul_zero,map_zero]
  have hh := kernelSpectralFormOperator_solution_graph (8/9) 0 v hv
  simpa only [v,map_smul,zero_add,kernelEisensteinResidueVector,kernelThetaMassProjection,
    kernelL2SandwichCLM,ContinuousLinearMap.comp_apply,ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.flip_apply,kernelVariationalSolution] using! hh


#print axioms kernelEisensteinL2Correction_meromorphicAt
#print axioms kernelEisensteinResidueVector_limit
#print axioms kernelEisensteinResidueVector_graph
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
