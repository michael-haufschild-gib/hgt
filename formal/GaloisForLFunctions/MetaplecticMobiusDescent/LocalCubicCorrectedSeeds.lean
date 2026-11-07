/-
Local corrected seeds adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.TheCubicIncomingResidue

/-!
# The corrected incoming family on compact quotient sets

The smooth cusp barrier bounds all seed heights on each compact quotient
set. A compact-height Banach exponential therefore realizes the local
seed as an entire L² family. Adding the actual resolvent correction gives
a local meromorphic family with the restricted spectral residue.
-/
noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology ContDiff InnerProductSpace MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicKubota

section
lemma fullCuspHeight_le_barrier (x : FullCuspClasses) (w : HyperbolicSpace) :
    fullCuspHeight x w≤ max 3 (cuspBarrier 2 3 w) := by
  by_cases hx : fullCuspHeight x w≤3
  · exact hx.trans (le_max_left _ _)
  · have he : cuspBarrier 2 3 w=fullCuspHeight x w := by
      rw [cuspBarrier,fullCuspProfileSum_eq_single _
        (fun v hv => cuspBarrierProfile_zero 2 3 (by norm_num) v (by linarith)) w x (by linarith),
        cuspBarrierProfile,cuspTransition_one 2 3 _ (by norm_num) (by linarith),one_mul]
      ring
    rw [he]
    exact le_max_right _ _

lemma cosetHeight_le_barrier (r : CuspCosets) (w : HyperbolicSpace) :
    cosetHeight r w≤ max 3 (cuspBarrier 2 3 w) := by
  induction r using Quotient.inductionOn with
  | _ M =>
    change cosetHeight (cosetOf M) w≤ max 3 (cuspBarrier 2 3 w)
    rw [cosetHeight_cosetOf]
    exact fullCuspHeight_le_barrier (fullCuspOf M.1) w

lemma kernel_compact_seed_height_bound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    ∃B : ℝ,a≤B ∧ 3≤B ∧ ∀q∈S,kernelQuotientBarrier 2 3 q≤B := by
  obtain ⟨B,hB⟩ := (hS.image (kernelQuotientBarrier_contMDiff 2 3 (by norm_num) (by norm_num)).continuous).bddAbove
  refine ⟨max a (max 3 B),le_max_left _ _,(le_max_left 3 B).trans (le_max_right _ _),?_⟩
  intro q hq
  exact (hB (Set.mem_image_of_mem _ hq)).trans ((le_max_right 3 B).trans (le_max_right _ _))

def kernelSeedHeightBound (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) : ℝ :=
  Classical.choose (kernel_compact_seed_height_bound a S hS)

lemma kernelSeedHeightBound_spec (a : ℝ) (S : Set KernelQuotient) (hS : IsCompact S) :
    a≤kernelSeedHeightBound a S hS ∧ 3≤kernelSeedHeightBound a S hS ∧
      ∀q∈S,kernelQuotientBarrier 2 3 q≤kernelSeedHeightBound a S hS :=
  Classical.choose_spec (kernel_compact_seed_height_bound a S hS)

def compactSeedTransition (a b B : ℝ) : C(Set.Icc a B,ℂ) :=
  ⟨fun v => (cuspTransition a b (v:ℝ):ℂ),Complex.continuous_ofReal.comp
    ((cuspTransition_contDiff a b).continuous.comp continuous_subtype_val)⟩

def compactSeedProfile (a b B : ℝ) (ha : 0<a) (s : ℂ) : C(Set.Icc a B,ℂ) :=
  compactSeedTransition a b B * NormedSpace.exp (s • compactLogProfile a B ha)

lemma compactSeedProfile_entire (a b B : ℝ) (ha : 0<a) :
    Differentiable ℂ (compactSeedProfile a b B ha) :=
  (differentiable_const _).mul (differentiable_exp_smul_const ℂ (compactLogProfile a B ha))

lemma compactSeedProfile_apply (a b B : ℝ) (ha : 0<a) (s : ℂ) (v : Set.Icc a B) :
    compactSeedProfile a b B ha s v=cuspSeedProfile a b s v := by
  have he := NormedSpace.map_exp (ContinuousMap.evalAlgHom ℂ ℂ v)
    (continuous_eval_const v) (s • compactLogProfile a B ha)
  change (NormedSpace.exp (s • compactLogProfile a B ha)) v=
    NormedSpace.exp ((s • compactLogProfile a B ha) v) at he
  change (cuspTransition a b (v:ℝ):ℂ)*(NormedSpace.exp (s • compactLogProfile a B ha)) v=_
  rw [he,←Complex.exp_eq_exp_ℂ]
  simp only [compactLogProfile,ContinuousMap.smul_apply,smul_eq_mul,cuspSeedProfile,
    positiveHeightPower,logRatioPower,Real.log_one,sub_zero,ContinuousMap.coe_mk]

lemma compactHeightProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (s : ℂ) (v : ℝ) (hv : v≤B) :
    compactHeightProfile a B hB (compactSeedProfile a b B ha s) v=cuspSeedProfile a b s v := by
  by_cases hva : a≤v
  · rw [compactHeightProfile,Set.indicator_of_mem (show v∈Set.Icc a B from ⟨hva,hv⟩),
      Set.projIcc_of_mem hB ⟨hva,hv⟩,compactSeedProfile_apply]
  · rw [compactHeightProfile,Set.indicator_of_notMem (by simp [Set.mem_Icc,hva]),
      cuspSeedProfile,cuspTransition_zero a b v hab (le_of_not_ge hva)]
    simp

lemma kernelCompactProfile_seed (a b B : ℝ) (ha : 0<a) (hab : a<b) (hB : a≤B)
    (hthree : 3≤B) (s : ℂ) (q : KernelQuotient) (hq : kernelQuotientBarrier 2 3 q≤B) :
    kernelCompactProfile a B hB (compactSeedProfile a b B ha s) q=kernelQuotientSeed a b s q := by
  induction q using Quotient.inductionOn with
  | _ w =>
    change cuspCutoffCorrection 1 (compactHeightProfile a B hB (compactSeedProfile a b B ha s)) w=
      cuspCutoffCorrection 1 (cuspSeedProfile a b s) w
    unfold cuspCutoffCorrection
    apply tsum_congr
    intro r
    unfold cuspCutoffTerm
    rw [compactHeightProfile_seed a b B ha hab hB s _
      ((cosetHeight_le_barrier r w).trans (max_le hthree hq))]

def kernelLocalSeedL2 (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (s : ℂ) : KernelQuotientL2 :=
  kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1
      (compactSeedProfile a b (kernelSeedHeightBound a S hS) ha s))

lemma kernelLocalSeedL2_entire (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) : Differentiable ℂ (kernelLocalSeedL2 S hS a b ha) := by
  exact (kernelMassRestrictionCLM S hS.measurableSet).differentiable.comp
    ((compactProfileL2 a (kernelSeedHeightBound a S hS) (kernelSeedHeightBound_spec a S hS).1).differentiable.comp
      (compactSeedProfile_entire a b (kernelSeedHeightBound a S hS) ha))

lemma kernelLocalSeedL2_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalSeedL2 S hS a b ha s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelQuotientSeed a b s) := by
  let B := kernelSeedHeightBound a S hS
  have hB := kernelSeedHeightBound_spec a S hS
  filter_upwards [kernelMassRestriction_coe S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)),
    compactProfileL2_ae_eq a B hB.1 (compactSeedProfile a b B ha s)] with q hr hp
  change kernelMassRestrictionCLM S hS.measurableSet
    (compactProfileL2 a B hB.1 (compactSeedProfile a b B ha s)) q=S.indicator (kernelQuotientSeed a b s) q
  rw [hr]
  by_cases hq : q∈S
  · rw [Set.indicator_of_mem hq,Set.indicator_of_mem hq,hp]
    exact kernelCompactProfile_seed a b B ha hab hB.1 hB.2.1 s q (hB.2.2 q hq)
  · rw [Set.indicator_of_notMem hq,Set.indicator_of_notMem hq]

end

section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace

def kernelCorrectedSeed (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotient→ℂ :=
  fun q => kernelQuotientSeed a b s q+kernelEisensteinL2Correction a b ha hab s q

def kernelLocalCorrectedSeed (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) : KernelQuotientL2 :=
  kernelLocalSeedL2 S hS a b ha s +
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)

lemma kernelLocalCorrectedSeed_meromorphicAt (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    MeromorphicAt (kernelLocalCorrectedSeed S hS a b ha hab) (4/3:ℂ) := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt (4/3)).meromorphicAt.add
    (meromorphicAt_clm (kernelMassRestrictionCLM S hS.measurableSet)
      (kernelEisensteinL2Correction_meromorphicAt a b ha hab))

lemma kernelLocalCorrectedSeed_analyticAt_nonreal (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) (hs : s.re≠1) (hi : s.im≠0) :
    AnalyticAt ℂ (kernelLocalCorrectedSeed S hS a b ha hab) s := by
  exact ((kernelLocalSeedL2_entire S hS a b ha).analyticAt s).add
    ((ContinuousLinearMap.analyticAt (𝕜 := ℂ) (E := KernelQuotientL2) (F := KernelQuotientL2)
      (kernelMassRestrictionCLM S hS.measurableSet) (kernelEisensteinL2Correction a b ha hab s)).comp_of_eq
        (kernelEisensteinL2Correction_analyticAt_nonreal a b ha hab s hs hi) rfl)

lemma kernelLocalCorrectedSeed_ae_eq (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) (s : ℂ) :
    (kernelLocalCorrectedSeed S hS a b ha hab s : KernelQuotient→ℂ)=ᵐ[integralQuotientVolume globalKubotaKernel]
      S.indicator (kernelCorrectedSeed a b ha hab s) := by
  filter_upwards [Lp.coeFn_add (kernelLocalSeedL2 S hS a b ha s)
      (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)),
    kernelLocalSeedL2_ae_eq S hS a b ha hab s,
    kernelMassRestriction_coe S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)]
    with q hsum hseed hcor
  change (kernelLocalSeedL2 S hS a b ha s+
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s)) q=_
  rw [hsum]
  change kernelLocalSeedL2 S hS a b ha s q+
    kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinL2Correction a b ha hab s) q=_
  rw [hseed,hcor]
  by_cases hq : q∈S
  · simp only [Set.indicator_of_mem hq,kernelCorrectedSeed]
  · simp only [Set.indicator_of_notMem hq,add_zero]

lemma kernelLocalCorrectedSeed_residue_limit (S : Set KernelQuotient) (hS : IsCompact S)
    (a b : ℝ) (ha : 0<a) (hab : a<b) :
    Tendsto (fun s : ℂ => (s-4/3)•kernelLocalCorrectedSeed S hS a b ha hab s)
      (𝓝[≠] (4/3:ℂ))
      (𝓝 (kernelMassRestrictionCLM S hS.measurableSet (kernelEisensteinResidueVector a b ha hab))) := by
  have hseed : Tendsto (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s)
      (𝓝[≠] (4/3:ℂ)) (𝓝 0) := by
    have hh : ContinuousAt (fun s : ℂ => (s-4/3)•kernelLocalSeedL2 S hS a b ha s) (4/3:ℂ) :=
      (continuousAt_id.sub continuousAt_const).smul
        ((kernelLocalSeedL2_entire S hS a b ha).continuous.continuousAt)
    simpa only [sub_self,zero_smul] using hh.tendsto.mono_left
      (show 𝓝[≠] (4/3:ℂ)≤𝓝 (4/3:ℂ) from nhdsWithin_le_nhds)
  have hcor := (kernelMassRestrictionCLM S hS.measurableSet).continuous.continuousAt.tendsto.comp
    (kernelEisensteinResidueVector_limit a b ha hab)
  have hh := hseed.add hcor
  simpa only [kernelLocalCorrectedSeed,smul_add,map_smul,Function.comp_def,zero_add] using hh

end


#print axioms kernelLocalCorrectedSeed_ae_eq
#print axioms kernelLocalSeedL2_entire
#print axioms kernelLocalCorrectedSeed_meromorphicAt
#print axioms kernelLocalCorrectedSeed_residue_limit
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
