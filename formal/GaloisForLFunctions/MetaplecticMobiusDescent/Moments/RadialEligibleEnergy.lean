/-
Radial eligible energy adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Hecke.RayFamiliesAndPrimeRows
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.SourceMassAndAbsoluteEnergy

/-!
# Radial eligible energy

Induction and radial eligible energies with child energies; redundant ideals of natural
primitives; bounded radial summability and the comparison reflection height control.
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
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentPositiveSummability
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentSourceMass
open CenteredMomentHeckeExpansion CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentRetainedProfile CenteredMomentDivisorRetained
open CenteredMomentDivisorRectangle CenteredMomentDivisorExtraction CenteredMomentDivisorAllocation
local notation "O" => Eisenstein.O

lemma plain_finite_norm (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b X:ℝ)
    (hs:Function.support W⊆Set.Iic b) (hX:0< X) :
    ‖rowTwistedSum η m A z W t X‖≤∑I∈idealBall (b*X),‖W ((Ideal.absNorm I:ℝ)/X)‖ := by
  rw [rowTwistedSum_eq_weight,tsum_eq_sum (s:=idealBall (b*X)) ?_]
  · apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro I hI
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (rowWeight_norm_le_one_all η m A z t I)
  · intro I hI
    by_cases h0:I=0
    · subst I
      simp only [map_zero,zero_mul]
    · have hw:W ((Ideal.absNorm I:ℝ)/X)=0 := by
        by_contra hn
        have hh:=hs hn
        have hbound:(Ideal.absNorm I:ℝ)≤ b*X:=(div_le_iff₀ hX).mp hh
        exact hI ((mem_idealBall _ _).mpr ⟨h0,hbound⟩)
      rw [hw,mul_zero]

lemma slot_finite_norm (η:Character) (m A z:O) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) :
    ‖rowSlot η m A z S β t‖≤∑I∈S,‖β I‖ := by
  rw [rowSlot_eq_weight]
  exact finite_hecke_polynomial_norm η m A z t S β

lemma bounded_radial_summable (F:O→ℂ) (B:ℝ) (hF:∀z,‖F z‖≤ B)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) :
    Summable (fun z:O=> if keep z then ‖F z‖^2*(Φ (‖ringComplex z‖^2/K)).re else 0) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _)
    (f:=fun z:O=> B^2*‖Φ (‖ringComplex z‖^2/K)‖)
  · intro z
    split_ifs
    · rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (sq_nonneg _)]
      exact mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) (hF z) 2)
        (Complex.abs_re_le_norm _) (abs_nonneg _) (sq_nonneg _)
    · simp only [norm_zero]
      positivity
  · exact (radial_norm_summable Φ K hK).mul_left _

lemma product_bounded {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (c:ℂ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) :
    ∃B:ℝ,∀z:O,‖c*((rowTwistedSum η m A z W₁ t X₁*
      rowTwistedSum η m A z W₂ t X₂)*∏i,rowSlot η m A z (S i) (β i) t)‖≤ B := by
  refine ⟨‖c‖*((∑I∈idealBall (b₁*X₁),‖W₁ ((Ideal.absNorm I:ℝ)/X₁)‖)*
    (∑I∈idealBall (b₂*X₂),‖W₂ ((Ideal.absNorm I:ℝ)/X₂)‖)*
    ∏i,∑I∈S i,‖β i I‖),?_⟩
  intro z
  rw [norm_mul,norm_mul,norm_mul,norm_prod]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply mul_le_mul
  · exact mul_le_mul (plain_finite_norm η m A z t W₁ b₁ X₁ hs₁ hX₁)
      (plain_finite_norm η m A z t W₂ b₂ X₂ hs₂ hX₂) (norm_nonneg _) (by positivity)
  · exact Finset.prod_le_prod (fun _ _=> norm_nonneg _) (fun i _=> slot_finite_norm η m A z t (S i) (β i))
  · positivity
  · positivity

 theorem retained_positive_summable {ι:Type*} [Fintype ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) :
    Summable (fun z:O=> if keep z then ‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (Φ (‖ringComplex z‖^2/K)).re else 0) := by
  unfold retainedPositiveRow positiveSlotRow
  simp_rw [←clipped_rowTwistedSum η m A _ W₁ t X₁ hX₁,
    ←clipped_rowTwistedSum η m A _ W₂ t X₂ hX₂]
  obtain ⟨B,hB⟩:=product_bounded η m A t
    (Real.sqrt (clippedScale X₁*clippedScale X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  exact bounded_radial_summable _ B hB keep Φ K hK

theorem allocated_positive_summable {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (D:Ideal O) (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) :
    Summable (fun z:O=> if keep z then ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2*
      (Φ (‖ringComplex z‖^2/K)).re else 0) := by
  have hN (j:Fin 2):(0:ℝ)< Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  unfold allocatedPositiveRow
  exact retained_positive_summable η m A t W₁ W₂ b₁ b₂ _ _ hs₁ hs₂
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) _ _ _ keep Φ K hK

end CenteredMomentPositiveSummability

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentRadialEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
open CenteredMomentDivisorRetained CenteredMomentPositiveSummability
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

structure Radial where
  keep : O→Prop
  profile : 𝓢(ℝ,ℂ)
  scale : ℝ
  scale_pos : 0< scale
  nonneg : ∀z:O,0≤(profile (‖ringComplex z‖^2/scale)).re

def Radial.weight (r:Radial) (z:O) : ℝ :=
  if r.keep z then (r.profile (‖ringComplex z‖^2/r.scale)).re else 0

lemma Radial.weight_nonneg (r:Radial) (z:O) : 0≤ r.weight z := by
  unfold Radial.weight
  split_ifs
  · exact r.nonneg z
  · rfl

def finiteData (s:Data ι) (r:Radial) (S:Finset O) : Data ι :=
  {s with rows:=S,weight:=r.weight,weight_nonneg:=fun z _=> r.weight_nonneg z}

def energy (s:Data ι) (r:Radial) (D:Ideal O) : ℝ :=
  ∑'z:O,r.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    CenteredMomentDivisorRowEnergy.maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D
      s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def childEnergy (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑'z:O,r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

lemma child_summable (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    Summable (fun z:O=> r.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)) := by
  have hX:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.X₁ s.X₂
    s.support₁ s.support₂ s.X₁_pos s.X₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  have hY:=allocated_positive_summable s.η s.m s.A s.t s.W₁ s.W₂ s.b₁ s.b₂ s.Y₁ s.Y₂
    s.support₁ s.support₂ s.Y₁_pos s.Y₂_pos s.slots s.coefficient s.P D a
    r.keep r.profile r.scale r.scale_pos
  convert hX.add hY using 1
  funext z
  unfold Radial.weight
  split_ifs <;> ring

lemma finite_child_le (s:Data ι) (r:Radial) (S:Finset O) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :
    (finiteData s r S).childEnergy D a≤ childEnergy s r D a := by
  exact sum_le_hasSum S (fun z _=> mul_nonneg (r.weight_nonneg z)
    (add_nonneg (sq_nonneg _) (sq_nonneg _))) (child_summable s r D a).hasSum

lemma energy_nonneg (s:Data ι) (r:Radial) (D:Ideal O) : 0≤ energy s r D :=
  tsum_nonneg (fun z=> mul_nonneg (r.weight_nonneg z) (sq_nonneg _))

lemma child_nonneg (s:Data ι) (r:Radial) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤ childEnergy s r D a :=
  tsum_nonneg (fun z=> mul_nonneg (r.weight_nonneg z) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤ E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤ E) →
      energy s r D≤ C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=CenteredMomentEligibleEnergy.actual_source_from_children N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s r D hD E hE hchild
  apply Real.tsum_le_of_sum_le (fun z=> mul_nonneg (r.weight_nonneg z) (sq_nonneg _))
  intro S
  exact hbound (finiteData s r S) D hD E hE
    (fun a ha=>(finite_child_le s r S D a).trans (hchild a ha))

 theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀(s:Data ι) (r:Radial),∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤ E →
      (∀a∈s.toSource.active D,childEnergy s r D a≤ E) →
      Real.sqrt (energy s r D)≤ C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s r D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤ s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=> div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s r D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end CenteredMomentRadialEligibleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section

open scoped Classical BigOperators ContDiff Topology
open MeasureTheory Set Complex
namespace CenteredMomentFrequencyScaleSupremum
open HeckeFamily HeckeDyadic HeckeDetectorRowwise HeckeDetectorDyadicBridge JointLogSeparation
open CenteredMomentScaleSupremum (scaleTest scaleTest_continuous scaleTest_support)
open HeckeInverseAmplification (scaleProfile scaleProfile_continuous scaleProfile_support
  scale_normalization scaleSupport scaleSupport_cover)
def frequencyScaleSum (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ) : ℂ :=
  Complex.exp (-(l : ℂ)/2)*∑ J∈S,
    (coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-l))

theorem frequencyScaleSum_continuous (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Continuous W) : Continuous (frequencyScaleSum χ inv W freq S) := by
  unfold frequencyScaleSum
  fun_prop

theorem frequencyScaleSum_deriv (χ : Character) (inv : Bool) (W : ℝ→ℂ) (freq : ℝ) (S : Finset (Ideal O))
    (hW : Differentiable ℝ W) (l : ℝ) :
    HasDerivAt (frequencyScaleSum χ inv W freq S) (frequencyScaleSum χ inv (scaleProfile W) freq S l) l := by
  have hE : HasDerivAt (fun t : ℝ => Complex.exp (-(t : ℂ)/2))
      (Complex.exp (-(l : ℂ)/2)*(-(1 : ℂ)/2)) l := by
    convert ((Complex.ofRealCLM.hasDerivAt (x:=l)).neg.div_const (2 : ℂ)).cexp using 1
    all_goals rfl
  have hd (J : Ideal O) (hJ : J∈S) :
      HasDerivAt (fun t => (coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*W ((J.absNorm : ℝ)*Real.exp (-t)))
        ((coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))) l := by
    have hy := ((hasDerivAt_id l).neg.exp).const_mul (J.absNorm : ℝ)
    convert ((hW _).hasDerivAt.scomp l hy).const_mul ((coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))) using 1
    all_goals try rfl
    change (coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(deriv W ((J.absNorm : ℝ)*Real.exp (-l))*
          (-((J.absNorm : ℝ)*Real.exp (-l)) : ℝ))=
        (coefficient χ inv J*kernelLogPhase (freq/(2*Real.pi)) (Real.log (J.absNorm : ℝ)))*(((J.absNorm : ℝ)*(Real.exp (-l)*(-1))) •
          deriv W ((J.absNorm : ℝ)*Real.exp (-l)))
    rw [Complex.real_smul]
    push_cast
    ring
  convert hE.mul (HasDerivAt.sum (u:=S) hd) using 1
  all_goals try rfl
  · funext t
    simp only [frequencyScaleSum,Pi.mul_apply,Finset.sum_apply]
  · dsimp [frequencyScaleSum,scaleProfile]
    simp only [Finset.sum_apply]
    simp_rw [Finset.mul_sum]
    rw [←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro J hJ
    push_cast
    ring

lemma ratio_frequency_phase (x l freq : ℝ) (hx : 0< x) :
    (((x/Real.exp l : ℝ):ℂ)^(-shift 0 freq))=
      kernelLogPhase (freq/(2*Real.pi)) (-l)*kernelLogPhase (freq/(2*Real.pi)) (Real.log x) := by
  have ht : 2*Real.pi*(freq/(2*Real.pi))=freq := by field_simp
  have hh := HeckeDetectorDyadicBridge.norm_phase x (Real.exp l) hx (Real.exp_pos l) 0 (freq/(2*Real.pi))
  rw [ht] at hh
  simp only [neg_zero,Complex.cpow_zero,one_mul,zero_re,zero_im,sub_zero] at hh
  rw [←hh,Real.log_div hx.ne' (Real.exp_pos l).ne',Real.log_exp]
  rw [show Real.log x-l=(-l)+Real.log x by ring,kernelLogPhase_add]

theorem frequencyScaleSum_eq_polynomial (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    polynomial χ inv W (Real.exp l) 0 freq=
      kernelLogPhase (freq/(2*Real.pi)) (-l)*frequencyScaleSum χ inv W freq S l := by
  rw [polynomial_eq_finite χ inv W (Real.exp l) 0 freq S hc,scale_normalization]
  unfold frequencyScaleSum
  rw [mul_left_comm]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro J hJ
  by_cases h0 : J=0
  · subst J
    simp only [coefficient_zero,zero_mul,mul_zero]
  have hpos : 0<(J.absNorm : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr h0)
  rw [ratio_frequency_phase _ l freq hpos,Real.exp_neg,div_eq_mul_inv]
  ring

theorem frequencyScaleSum_norm (χ : Character) (inv : Bool) (W : ℝ→ℂ)
    (freq : ℝ) (S : Finset (Ideal O)) (l : ℝ)
    (hc : ∀J : Ideal O,J≠0 → W ((J.absNorm : ℝ)/Real.exp l)≠0 → J∈S) :
    ‖frequencyScaleSum χ inv W freq S l‖=‖polynomial χ inv W (Real.exp l) 0 freq‖ := by
  rw [frequencyScaleSum_eq_polynomial χ inv W freq S l hc,norm_mul,kernelLogPhase_norm,one_mul]

theorem paired_rowwise_scales {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤ b) (hd : 0≤ d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤ hi) (hlw : low≤ high) (lx ly : ι→ℝ)
    (hlx : ∀ i∈rows,lx i∈Icc lo hi) (hly : ∀ i∈rows,ly i∈Icc low high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤ E) :
    ∑ i∈rows,‖polynomial (χ i) false W (Real.exp (lx i)) 0 (freq₁ i) *
      polynomial (ψ i) false V (Real.exp (ly i)) 0 (freq₂ i) * P i‖^2≤
      (1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (j k : Fin 2) (i : ι) (x y : ℝ) :=
    frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x *
      frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y * P i
  have eqW (i : ι) (j : Fin 2) (x : ℝ) (hx : x∈Icc lo hi) :=
    frequencyScaleSum_norm (χ i) false (scaleTest W j) (freq₁ i) S x
      (scaleSupport_cover _ a b hi x hb (scaleTest_support W a b hWs j) hx.2)
  have eqV (i : ι) (k : Fin 2) (y : ℝ) (hy : y∈Icc low high) :=
    frequencyScaleSum_norm (ψ i) false (scaleTest V k) (freq₂ i) T y
      (scaleSupport_cover _ c d high y hd (scaleTest_support V c d hVs k) hy.2)
  have hc (j k : Fin 2) (i : ι) : Continuous (Function.uncurry (F j k i)) := by
    exact (((frequencyScaleSum_continuous (χ i) false _ (freq₁ i) S (scaleTest_continuous W hW j)).comp
      continuous_fst).mul ((frequencyScaleSum_continuous (ψ i) false _ (freq₂ i) T
      (scaleTest_continuous V hV k)).comp continuous_snd)).mul continuous_const
  have hx (k : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (fun u=> F 0 k i u y) (F 1 k i x y) x := by
    simpa [F,scaleTest] using
      (frequencyScaleSum_deriv (χ i) false W (freq₁ i) S (hW.differentiable (by simp)) x).mul_const
        (frequencyScaleSum (ψ i) false (scaleTest V k) (freq₂ i) T y) |>.mul_const (P i)
  have hy (j : Fin 2) (i : ι) (x y : ℝ) :
      HasDerivAt (F j 0 i x) (F j 1 i x y) y := by
    simpa [F,scaleTest] using
      ((frequencyScaleSum_deriv (ψ i) false V (freq₂ i) T (hV.differentiable (by simp)) y).const_mul
        (frequencyScaleSum (χ i) false (scaleTest W j) (freq₁ i) S x)).mul_const (P i)
  have hh := rowwise_energy_two rows F (fun j k i _=> hc j k i)
    (fun k i _ x y=> hx k i x y) (fun j i _ x y=> hy j i x y)
    lo hi low high E hlh hlw lx ly hlx hly (by
      intro j k x hx y hy
      simpa only [F,norm_mul,eqW _ j x hx,eqV _ k y hy] using henergy j k x hx y hy)
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i hi
  dsimp only [F]
  simp only [norm_mul]
  rw [eqW i 0 (lx i) (hlx i hi),eqV i 0 (ly i) (hly i hi)]
  simp only [scaleTest,ite_true]

theorem exists_paired_scale_majorant {ι : Type*} (rows : Finset ι)
    (χ ψ : ι→Character) (freq₁ freq₂ : ι→ℝ) (P : ι→ℂ) (W V : ℝ→ℂ)
    (a b c d : ℝ) (hb : 0≤ b) (hd : 0≤ d)
    (hWs : Function.support W⊆Icc a b) (hVs : Function.support V⊆Icc c d)
    (hW : ContDiff ℝ ∞ W) (hV : ContDiff ℝ ∞ V)
    (lo hi low high E : ℝ) (hlh : lo≤ hi) (hlw : low≤ high)
    (henergy : ∀ j k : Fin 2,∀ x∈Icc lo hi,∀ y∈Icc low high,
      ∑ i∈rows,‖polynomial (χ i) false (scaleTest W j) (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false (scaleTest V k) (Real.exp y) 0 (freq₂ i) * P i‖^2≤ E) :
    ∃ B : ι→ℝ,(∀i,0≤ B i) ∧
      (∀i,∀ x∈Icc lo hi,∀ y∈Icc low high,
        ‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
          polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2≤ B i) ∧
      (∑ i∈rows,B i)≤(1+2*(hi-lo))*((1+2*(high-low))*E) := by
  let S := scaleSupport hi b
  let T := scaleSupport high d
  let F (i : ι) (p : ℝ×ℝ) :=
    frequencyScaleSum (χ i) false W (freq₁ i) S p.1 * frequencyScaleSum (ψ i) false V (freq₂ i) T p.2 * P i
  have hc (i : ι) : Continuous (F i) :=
    (((frequencyScaleSum_continuous (χ i) false W (freq₁ i) S hW.continuous).comp continuous_fst).mul
      ((frequencyScaleSum_continuous (ψ i) false V (freq₂ i) T hV.continuous).comp continuous_snd)).mul continuous_const
  have heq (i : ι) (x y : ℝ) (hx : x∈Icc lo hi) (hy : y∈Icc low high) :
      ‖F i (x,y)‖^2=‖polynomial (χ i) false W (Real.exp x) 0 (freq₁ i) *
        polynomial (ψ i) false V (Real.exp y) 0 (freq₂ i) * P i‖^2 := by
    dsimp only [F]
    simp only [norm_mul]
    rw [frequencyScaleSum_norm (χ i) false W (freq₁ i) S x
      (scaleSupport_cover W a b hi x hb hWs hx.2),
      frequencyScaleSum_norm (ψ i) false V (freq₂ i) T y
      (scaleSupport_cover V c d high y hd hVs hy.2)]
  have hm (i : ι) : ∃p∈(Icc lo hi)×ˢ(Icc low high),
      ∀q∈(Icc lo hi)×ˢ(Icc low high),‖F i q‖^2≤‖F i p‖^2 := by
    exact (isCompact_Icc.prod isCompact_Icc).exists_isMaxOn
      ((nonempty_Icc.mpr hlh).prod (nonempty_Icc.mpr hlw)) ((hc i).norm.pow 2).continuousOn
  choose p hp hmax using hm
  refine ⟨fun i=>‖F i (p i)‖^2,fun i=> sq_nonneg _,?_,?_⟩
  · intro i x hx y hy
    have hh := hmax i (x,y) ⟨hx,hy⟩
    rwa [heq i x y hx hy] at hh
  · have hh := paired_rowwise_scales rows χ ψ freq₁ freq₂ P W V a b c d hb hd hWs hVs hW hV
      lo hi low high E hlh hlw (fun i=>(p i).1) (fun i=>(p i).2)
      (fun i _=>(hp i).1) (fun i _=>(hp i).2) henergy
    convert hh using 1
    apply Finset.sum_congr rfl
    intro i hi
    rw [←heq i (p i).1 (p i).2 (hp i).1 (hp i).2]

end CenteredMomentFrequencyScaleSupremum

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap
namespace CenteredMomentRadialPolynomialEnergy
open HeckeFamily HeckeDyadic CenteredMomentFrequencyScaleSupremum
open CenteredMomentPositiveSummability 
open HeckeInverseAmplification
local notation "O" => Eisenstein.O

lemma polynomial_bounded (W : ℝ→ℂ) (a b X : ℝ) (hb : 0≤ b) (hX : 0< X)
    (hs : Function.support W⊆Set.Icc a b) :
    ∃B : ℝ,0≤ B ∧ ∀χ : Character,∀t : ℝ,‖polynomial χ false W X 0 t‖≤ B := by
  let l:=Real.log X
  let S:=scaleSupport l b
  have hx : Real.exp l=X := Real.exp_log hX
  have hc : ∀I : Ideal O,I≠0 → W ((I.absNorm:ℝ)/Real.exp l)≠0 → I∈S :=
    scaleSupport_cover W a b l l hb hs le_rfl
  let B:=‖Complex.exp (-(l:ℂ)/2)‖*∑I∈S,‖W ((I.absNorm:ℝ)*Real.exp (-l))‖
  refine ⟨B,by dsimp [B];positivity,?_⟩
  intro χ t
  rw [←hx,frequencyScaleSum_eq_polynomial χ false W t S l hc,norm_mul,
    kernelLogPhase_norm,one_mul]
  unfold frequencyScaleSum
  rw [norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro I hI
  rw [norm_mul,norm_mul,kernelLogPhase_norm,mul_one]
  exact mul_le_of_le_one_left (norm_nonneg _) (coefficient_norm_le χ false I)

lemma pair_radial_summable (χ : O→Character) (P : O→ℂ) (t omega : O→ℝ)
    (W₁ W₂ : ℝ→ℂ) (a b c d X Y Pbound : ℝ)
    (hb : 0≤ b) (hd : 0≤ d) (hX : 0< X) (hY : 0< Y)
    (hs₁ : Function.support W₁⊆Set.Icc a b) (hs₂ : Function.support W₂⊆Set.Icc c d)
    (hP : ∀z,‖P z‖≤ Pbound) (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z:O=> if keep z then
      ‖polynomial (χ z) false W₁ X 0 (t z)*polynomial (χ z) false W₂ Y 0 (omega z)*P z‖^2*
        (Φ (‖ringComplex z‖^2/K)).re else 0) := by
  obtain ⟨B₁,hB₁,h₁⟩:=polynomial_bounded W₁ a b X hb hX hs₁
  obtain ⟨B₂,hB₂,h₂⟩:=polynomial_bounded W₂ c d Y hd hY hs₂
  apply bounded_radial_summable _ (B₁*B₂*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul,norm_mul]
  exact mul_le_mul (mul_le_mul (h₁ _ _) (h₂ _ _) (norm_nonneg _) hB₁)
    (hP z) (norm_nonneg _) (mul_nonneg hB₁ hB₂)

lemma single_radial_summable (χ : O→Character) (P : O→ℂ) (t : O→ℝ)
    (W : ℝ→ℂ) (a b X Pbound : ℝ) (hb : 0≤ b) (hX : 0< X)
    (hs : Function.support W⊆Set.Icc a b) (hP : ∀z,‖P z‖≤ Pbound)
    (keep : O→Prop) (Φ : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0< K) :
    Summable (fun z:O=> if keep z then ‖polynomial (χ z) false W X 0 (t z)*P z‖^2*
      (Φ (‖ringComplex z‖^2/K)).re else 0) := by
  obtain ⟨B,hB,hh⟩:=polynomial_bounded W a b X hb hX hs
  apply bounded_radial_summable _ (B*Pbound) _ keep Φ K hK
  intro z
  rw [norm_mul]
  exact mul_le_mul (hh _ _) (hP z) (norm_nonneg _) hB

end CenteredMomentRadialPolynomialEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentInductionEnergy
open HeckeFamily CenteredMomentAbsoluteEnergy CenteredMomentPositiveSummability
open CenteredMomentCounting CenteredMomentHeckeExpansion CenteredMomentHeckeHeight
open CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open InversePrincipalEnergy 
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def energy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ) (X₁ X₂:ℝ)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) : ℝ :=
  ∑'z:O,if keep z then ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
    (Φ (‖ringComplex z‖^2/K)).re else 0

lemma plain_absolute (η:Character) (m A z:O) (t:ℝ) (W:ℝ→ℂ) (b B X:ℝ)
    (hb:0≤ b) (hB:0≤ B) (hX:0< X) (hs:Function.support W⊆Set.Iic b)
    (hW:∀x,‖W x‖≤ B) : ‖rowTwistedSum η m A z W t X‖≤(128*b*B)*X := by
  rw [rowTwistedSum_eq_weight]
  have hh:=norm_tsum_ideal_ball (fun I:Ideal O=> rowWeight η m A z t I*W ((Ideal.absNorm I:ℝ)/X))
    (b*X) B (mul_nonneg hb hX.le) hB (by change rowWeight η m A z t (0:Ideal O)*_=0; rw [map_zero,zero_mul])
    (fun I=> by rw [norm_mul]; exact (mul_le_mul (rowWeight_norm_le_one_all η m A z t I)
      (hW _) (norm_nonneg _) zero_le_one).trans_eq (one_mul _))
    (fun I hi=>(div_le_iff₀ hX).mp (hs (right_ne_zero_of_mul hi)))
  convert hh using 1 ; ring

omit [DecidableEq ι] in
lemma positive_squared_absolute (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤ b₁) (hb₂:0≤ b₂) (hB₁:0≤ B₁) (hB₂:0≤ B₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤ B₁) (hW₂:∀x,‖W₂ x‖≤ B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0< P i) (hb:∀i,0≤ b i) (hB:∀i,0≤ B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤ B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤ b i*P i) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i) := by
  let L:ℝ:=(128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i)
  let T:ℝ:=X₁*X₂*∏i,P i
  have hL:0≤ L:=mul_nonneg (mul_nonneg (by positivity) (by positivity))
    (Finset.prod_nonneg (fun i _=> mul_nonneg (mul_nonneg (by norm_num) (hb i)) (hB i)))
  have hT:0< T:=mul_pos (mul_pos hX₁ hX₂) (Finset.prod_pos (fun i _=> hP i))
  have hsum:‖(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏i,rowSlot η m A z (S i) (β i) t‖≤ L*T := by
    rw [norm_mul,norm_mul,norm_prod]
    have hp:=Finset.prod_le_prod (s:=Finset.univ) (fun i _=> norm_nonneg (rowSlot η m A z (S i) (β i) t))
      (fun i _=> rowSlot_bound η m A z (S i) (β i) t (b i*P i) (B i)
        (mul_nonneg (hb i) (hP i).le) (hB i) (hβ i) (hN i))
    have hq:=mul_le_mul
      (mul_le_mul (plain_absolute η m A z t W₁ b₁ B₁ X₁ hb₁ hB₁ hX₁ hs₁ hW₁)
        (plain_absolute η m A z t W₂ b₂ B₂ X₂ hb₂ hB₂ hX₂ hs₂ hW₂) (norm_nonneg _) (by positivity))
      hp (by positivity) (by positivity)
    apply hq.trans_eq
    simp only [mul_left_comm (B _) (b _),mul_assoc,Finset.prod_mul_distrib]
    dsimp [L,T]
    simp only [Finset.prod_mul_distrib]
    ring
  unfold positiveSlotRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ hT]
  calc
    _≤(L*T)^2/T:=div_le_div_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hsum 2) hT.le
    _=L^2*T:=by field_simp

omit [DecidableEq ι] in
theorem energy_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤ b₁) (hb₂:0≤ b₂) (hB₁:0≤ B₁) (hB₂:0≤ B₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂) (hW₁:∀x,‖W₁ x‖≤ B₁) (hW₂:∀x,‖W₂ x‖≤ B₂)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P b B:ι→ℝ)
    (hP:∀i,0< P i) (hb:∀i,0≤ b i) (hB:∀i,0≤ B i)
    (hβ:∀i,∀I∈S i,‖β i I‖≤ B i)
    (hN:∀i,∀I∈S i,β i I≠0 → (Ideal.absNorm I:ℝ)≤ b i*P i)
    (keep:O→Prop) (Φ:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0< K) :
    energy η m A t W₁ W₂ S β P X₁ X₂ keep Φ K≤
      diagonalControl Φ*max 1 K*
        (((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)) := by
  let E:ℝ:=((128*b₁*B₁)*(128*b₂*B₂)*(∏i,128*b i*B i))^2*(X₁*X₂*∏i,P i)
  have hE:0≤ E:=mul_nonneg (sq_nonneg _) (mul_nonneg (mul_nonneg hX₁.le hX₂.le)
    (Finset.prod_nonneg (fun i _=>(hP i).le)))
  have hp (z:O):‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2≤ E:=
    positive_squared_absolute η m A z t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂ hb₁ hb₂ hB₁ hB₂
      hX₁ hX₂ hs₁ hs₂ hW₁ hW₂ S β P b B hP hb hB hβ hN
  have hs:=bounded_radial_summable
    (fun z:O=> positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂) (Real.sqrt E)
    (fun z=> Real.le_sqrt_of_sq_le (hp z)) keep Φ K hK
  have hbnd:=hs.tsum_le_tsum (g:=fun z:O=> E*‖Φ (‖ringComplex z‖^2/K)‖) (fun z=> by
    split_ifs
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (hp z) (norm_nonneg _))
    · positivity) ((radial_norm_summable Φ K hK).mul_left E)
  rw [tsum_mul_left] at hbnd
  exact hbnd.trans ((mul_le_mul_of_nonneg_left (radial_weight_lattice_bound_all Φ K hK) hE).trans_eq (mul_comm _ _))

end CenteredMomentInductionEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentBottomStage
open CenteredMomentEligibleEnergy CenteredMomentRadialEligibleEnergy
open CenteredMomentInductionEnergy CenteredMomentAbsoluteEnergy InversePrincipalEnergy
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι]

 def positiveEnergy (s:Data ι) (r:Radial) : ℝ :=
  CenteredMomentInductionEnergy.energy s.η s.m s.A s.t s.W₁ s.W₂ s.slots s.coefficient s.P
    s.X₁ s.X₂ r.keep r.profile r.scale

 def profileMass (s:Data ι) (B₁ B₂:ℝ) : ℝ :=
  ((128*max 0 s.b₁*B₁)*(128*max 0 s.b₂*B₂)*(∏i,128*max 0 (s.hi i)*s.M i))^2

 theorem actual_absolute (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤ B₁) (hB₂:0≤ B₂)
    (hW₁:∀x,‖s.W₁ x‖≤ B₁) (hW₂:∀x,‖s.W₂ x‖≤ B₂) :
    positiveEnergy s r≤ diagonalControl r.profile*max 1 r.scale*profileMass s B₁ B₂*
      (s.X₁*s.X₂*∏i,s.P i) := by
  have hs₁:Function.support s.W₁⊆Set.Iic (max 0 s.b₁):=
    by
      intro x hx
      change x≤ max 0 s.b₁
      have hs:x≤ s.b₁:=s.support₁ hx
      exact hs.trans (le_max_right 0 s.b₁)
  have hs₂:Function.support s.W₂⊆Set.Iic (max 0 s.b₂):=
    by
      intro x hx
      change x≤ max 0 s.b₂
      have hs:x≤ s.b₂:=s.support₂ hx
      exact hs.trans (le_max_right 0 s.b₂)
  have hN:∀i,∀I∈s.slots i,s.coefficient i I≠0 →
      (Ideal.absNorm I:ℝ)≤ max 0 (s.hi i)*s.P i:=by
    intro i I hI hn
    have hw:s.W i ((Ideal.absNorm I:ℝ)/s.P i)≠0:=by
      intro hw
      apply hn
      simp only [Data.coefficient,hw,mul_zero]
    have hs:=s.support i hw
    exact (div_le_iff₀ (s.P_pos i)).mp (hs.2.trans (le_max_right _ _))
  have hh:=energy_absolute s.η s.m s.A s.t s.W₁ s.W₂
    (max 0 s.b₁) (max 0 s.b₂) B₁ B₂ s.X₁ s.X₂ (le_max_left _ _) (le_max_left _ _) hB₁ hB₂
    s.X₁_pos s.X₂_pos hs₁ hs₂ hW₁ hW₂
    s.slots s.coefficient s.P (fun i=> max 0 (s.hi i)) s.M s.P_pos
    (fun i=> le_max_left _ _) (fun i=> zero_le_one.trans (s.M_ge_one i)) s.coefficient_bound
    hN r.keep r.profile r.scale r.scale_pos
  exact hh.trans_eq (by unfold profileMass;ring)

 theorem actual_bottom_band (s:Data ι) (r:Radial) (B₁ B₂:ℝ) (hB₁:0≤ B₁) (hB₂:0≤ B₂)
    (hW₁:∀x,‖s.W₁ x‖≤ B₁) (hW₂:∀x,‖s.W₂ x‖≤ B₂)
    (Z m M σ:ℝ) (hZ:1< Z) (hK:1≤ r.scale) (hm:m≤σ)
    (hrow:r.scale≤ Z^m) (hsource:s.X₁*s.X₂*∏i,s.P i≤ Z^M) :
    positiveEnergy s r≤(diagonalControl r.profile*profileMass s B₁ B₂)*Z^(M+σ) := by
  have hh:=actual_absolute s r B₁ B₂ hB₁ hB₂ hW₁ hW₂
  rw [max_eq_right hK] at hh
  have hp:0≤ profileMass s B₁ B₂:=sq_nonneg _
  have hd:0≤ diagonalControl r.profile:=diagonalControl_nonneg _
  have hs:0≤ s.X₁*s.X₂*∏i,s.P i:=(mul_pos (mul_pos s.X₁_pos s.X₂_pos)
    (Finset.prod_pos (fun i _=> s.P_pos i))).le
  have hpow:r.scale*(s.X₁*s.X₂*∏i,s.P i)≤ Z^(M+σ):=by
    apply (mul_le_mul hrow hsource hs (Real.rpow_nonneg (by linarith) _)).trans
    rw [←Real.rpow_add (zero_lt_one.trans hZ)]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply hh.trans
  calc
    _=(diagonalControl r.profile*profileMass s B₁ B₂)*(r.scale*(s.X₁*s.X₂*∏i,s.P i)):=by ring
    _≤ _:=mul_le_mul_of_nonneg_left hpow (mul_nonneg hd hp)

end CenteredMomentBottomStage

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap

namespace CenteredMomentCoreFloor
open HeckeFamily CenteredMomentHeckeHeight CenteredMomentHeckeSlots
open CenteredMomentRetainedEnergy CenteredMomentInductionEnergy
open CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open InversePrincipalEnergy 
local notation "O" => Eisenstein.O

 def zeroRow (η:Character) (m A z:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ):ℂ :=
  (Real.sqrt (X₁*X₂):ℂ)⁻¹*(rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)

 def zeroEnergy (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):ℝ :=
  ∑'z:O,if r.keep z then ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2*
    (r.profile (‖ringComplex z‖^2/r.scale)).re else 0

 theorem zero_energy_eq (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ) (X₁ X₂:ℝ) (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r=
    energy η m A t W₁ W₂ (fun _:Fin 0=>∅) (fun _:Fin 0=>0) (fun _:Fin 0=>1)
      X₁ X₂ r.keep r.profile r.scale:=by
  simp [zeroEnergy,energy,zeroRow,positiveSlotRow]

 theorem zero_absolute (η:Character) (m A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂ X₁ X₂:ℝ) (hb₁:0≤ b₁)(hb₂:0≤ b₂)(hB₁:0≤ B₁)(hB₂:0≤ B₂)
    (hX₁:0< X₁)(hX₂:0< X₂)(hs₁:Function.support W₁⊆Set.Iic b₁)
    (hs₂:Function.support W₂⊆Set.Iic b₂)(hW₁:∀x,‖W₁ x‖≤ B₁)(hW₂:∀x,‖W₂ x‖≤ B₂)
    (r:Radial):
    zeroEnergy η m A t W₁ W₂ X₁ X₂ r≤
      diagonalControl r.profile*max 1 r.scale*((128*b₁*B₁)*(128*b₂*B₂))^2*(X₁*X₂):=by
  rw [zero_energy_eq]
  have h:=energy_absolute (ι:=Fin 0) η m A t W₁ W₂ b₁ b₂ B₁ B₂ X₁ X₂
    hb₁ hb₂ hB₁ hB₂ hX₁ hX₂ hs₁ hs₂ hW₁ hW₂
    (fun _=>∅) (fun _=>0) (fun _=>1) (fun _=>1) (fun _=>1)
    (by simp) (by simp) (by simp) (by simp) (by simp)
    r.keep r.profile r.scale r.scale_pos
  simpa only [Fin.prod_univ_zero,mul_one,mul_assoc] using h

 theorem zero_padded_core (η:Character) (mask A:O) (t:ℝ) (W₁ W₂:ℝ→ℂ)
    (b₁ b₂ B₁ B₂:ℝ) (hb₁:0≤ b₁)(hb₂:0≤ b₂)(hB₁:0≤ B₁)(hB₂:0≤ B₂)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hW₁:∀x,‖W₁ x‖≤ B₁)(hW₂:∀x,‖W₂ x‖≤ B₂)
    (r:Radial)(Z m q n₁ n₂ ρ δ:ℝ)(hZ:1< Z)(hm:0≤ m)(hq:0≤ q)
    (hscale:r.scale=Z^m)(hfloor:m+q≤ρ)(hcore:n₁+n₂≤ m+q+δ):
    zeroEnergy η mask A t W₁ W₂ (Z^n₁) (Z^n₂) r≤
      (diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*Z^(m+q+ρ+δ):=by
  have hZ0:0< Z:=zero_lt_one.trans hZ
  have h:=zero_absolute η mask A t W₁ W₂ b₁ b₂ B₁ B₂ (Z^n₁) (Z^n₂)
    hb₁ hb₂ hB₁ hB₂ (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _)
    hs₁ hs₂ hW₁ hW₂ r
  rw [hscale,max_eq_right (Real.one_le_rpow hZ.le hm)] at h
  have hp:Z^m*(Z^n₁*Z^n₂)≤ Z^(m+q+ρ+δ):=by
    rw [←Real.rpow_add hZ0,←Real.rpow_add hZ0]
    exact Real.rpow_le_rpow_of_exponent_le hZ.le (by linarith)
  apply h.trans
  calc
    _=(diagonalControl r.profile*((128*b₁*B₁)*(128*b₂*B₂))^2)*(Z^m*(Z^n₁*Z^n₂)):=by ring
    _≤ _:=mul_le_mul_of_nonneg_left hp (mul_nonneg (diagonalControl_nonneg _) (sq_nonneg _))

 theorem whole_slot_norm {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A z:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂)
    (S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)(P:ι→ℝ)(hP:∀i,0< P i):
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2=
      ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖^2 *
        (∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i):=by
  have hp:0<∏i,P i:=Finset.prod_pos (fun i _=> hP i)
  unfold positiveSlotRow zeroRow
  rw [CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos (mul_pos hX₁ hX₂) hp),
    CenteredMomentDivisorRawEnergy.normalized_norm_sq _ (mul_pos hX₁ hX₂)]
  rw [norm_mul,norm_prod,mul_pow,Finset.prod_div_distrib,Finset.prod_pow]
  ring

 theorem slot_energy_reduction {ι:Type*}[Fintype ι][DecidableEq ι]
    (η:Character)(m A:O)(t:ℝ)(W₁ W₂:ℝ→ℂ)(b₁ b₂ X₁ X₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁)(hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0< X₁)(hX₂:0< X₂)(S:ι→Finset (Ideal O))(β:ι→Ideal O→ℂ)
    (P:ι→ℝ)(hP:∀i,0< P i)(r:Radial)(E:ℝ)
    (hslots:∀z,r.keep z→(∏i,‖rowSlot η m A z (S i) (β i) t‖^2/P i)≤ E):
    energy η m A t W₁ W₂ S β P X₁ X₂ r.keep r.profile r.scale≤
      E*zeroEnergy η m A t W₁ W₂ X₁ X₂ r:=by
  obtain ⟨B,hB⟩:=product_bounded (ι:=Fin 0) η m A t (Real.sqrt (X₁*X₂):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ (fun _=>∅) (fun _=>0)
  have hz:∀z,‖zeroRow η m A z t W₁ W₂ X₁ X₂‖≤ B:=by
    simpa [zeroRow] using hB
  have hsum:=bounded_radial_summable _ B hz r.keep r.profile r.scale r.scale_pos
  obtain ⟨B',hB'⟩:=product_bounded η m A t (Real.sqrt (X₁*X₂*∏i,P i):ℂ)⁻¹
    W₁ W₂ b₁ b₂ X₁ X₂ hs₁ hs₂ hX₁ hX₂ S β
  have hspos:=bounded_radial_summable _ B' hB' r.keep r.profile r.scale r.scale_pos
  change Summable (fun z:O=> if r.keep z then
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2*
      (r.profile (‖ringComplex z‖^2/r.scale)).re else 0) at hspos
  unfold energy zeroEnergy
  rw [←tsum_mul_left]
  apply hspos.tsum_le_tsum _ (hsum.mul_left E)
  intro z
  by_cases hk:r.keep z
  · simp only [if_pos hk]
    rw [whole_slot_norm η m A z t W₁ W₂ X₁ X₂ hX₁ hX₂ S β P hP]
    have hb:=mul_le_mul_of_nonneg_left (hslots z hk)
      (sq_nonneg ‖zeroRow η m A z t W₁ W₂ X₁ X₂‖)
    have hh:=mul_le_mul_of_nonneg_right hb (r.nonneg z)
    nlinarith only [hh]
  · simp [hk]

end CenteredMomentCoreFloor

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson
namespace CenteredMomentDetectorDictionary
open HeckeFamily HeckeDyadic HeckeInverseAmplification CenteredMomentHeckeTwist
lemma sqrt_inverse_cpow (X : ℝ) (hX : 0 < X) :
    (Real.sqrt X : ℂ)⁻¹ = (X : ℂ)^(-(1/2 : ℂ)) := by
  rw [Complex.cpow_neg, Real.sqrt_eq_rpow]
  congr 1
  simpa using (Complex.ofReal_cpow hX.le (1/2 : ℝ))

lemma plain_zero_height (χ : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0< X) :
    polynomial χ false W X 0 0 = (Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W 0 X := by
  rw [sqrt_inverse_cpow X hX]
  unfold polynomial twistedIdealSum
  congr 1
  have he := tsum_subtype_eq_of_support_subset
    (s := {I : Ideal O | I≠0})
    (f := fun I : Ideal O=> idealCoeff χ I*W ((I.absNorm:ℝ)/X))
    (by intro I hI hi; subst I; exact hI (by simp only [map_zero,zero_mul]))
  change (∑' I : HeckeDyadic.NonzeroIdeal,idealCoeff χ I.val*W ((I.val.absNorm:ℝ)/X))=
    ∑' I : Ideal O,idealCoeff χ I*W ((I.absNorm:ℝ)/X) at he
  simpa only [HeckeDyadic.summand,coefficient,Bool.false_eq_true,ite_false,HeckeDyadic.norm,HeckeDyadic.shift,
    Complex.ofReal_zero,zero_mul,mul_zero,sub_zero,neg_zero,Complex.cpow_zero,mul_one,
    HeckeDyadic.NonzeroIdeal,CubicEisenstein.NonzeroIdeal] using he


end CenteredMomentDetectorDictionary

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set MeasureTheory Complex
namespace CenteredMomentPlainGlobalBound
open HeckeFamily HeckeDyadic

 theorem weighted_central (χ:Character)(W:ℝ→ℂ)(D freq C K T:ℝ)
    (hD:0< D)(hC:0≤ C)(hK:0≤ K)(hT:0≤ T)
    (hm:∀t:ℝ,(1+|t|)^4*‖mellin W (((1/2:ℝ):ℂ)+t*I)‖≤ C)
    (hs:∀t∈Icc (-T) T,‖series χ false (((1/2:ℝ):ℂ)+t*I+shift 0 freq)‖≤ K*(1+|t|)^2):
    ‖∫t:ℝ in -T..T,integrand χ false W D 0 freq (((1/2:ℝ):ℂ)+t*I)‖≤ C*K*Real.pi:=by
  rw [intervalIntegral.integral_of_le (by linarith : -T≤ T)]
  have hint:=integrable_inv_one_add_sq.const_mul (C*K)
  calc
    _≤∫t:ℝ in Ioc (-T) T,(C*K)*(1+t^2)⁻¹:=by
      apply norm_integral_le_of_norm_le hint.integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      rw [integrand_norm χ false W D 0 freq hD]
      have hm':(1+|t|)^2*(‖mellin W (((1/2:ℝ):ℂ)+t*I)‖*(1+|t|)^2)≤ C:=by
        nlinarith only [hm t]
      have hb:=weighted_two_to_cauchy
        (mul_nonneg (norm_nonneg _) (sq_nonneg _)) t hm'
      have hh:=mul_le_mul_of_nonneg_left (hs t ⟨ht.1.le,ht.2⟩)
        (norm_nonneg (mellin W (((1/2:ℝ):ℂ)+t*I)))
      have hbK:=mul_le_mul_of_nonneg_right hb hK
      simp only [add_re,ofReal_re,mul_re,ofReal_im,I_re,mul_zero,I_im,zero_mul,
        sub_self,add_zero]
      norm_num only [add_zero,sub_self,Real.rpow_zero,mul_one]
      apply hh.trans
      convert hbK using 1 <;> ring
    _≤∫t:ℝ,(C*K)*(1+t^2)⁻¹:=
      integral_mono_measure Measure.restrict_le_self (by filter_upwards [] with t; positivity) hint
    _=_:=by rw [integral_const_mul,integral_univ_inv_one_add_sq]

 theorem finite_strip_bound (χ:Character)(hχ:χ.residue≠1)(W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hWs:Function.support W⊆Icc a b)(hW:ContDiff ℝ ∞ W)
    (D freq C K:ℝ)(hD:1≤ D)(hC:0≤ C)(hK:0≤ K)
    (hm:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,(1+|t|)^6*‖mellin W ((x:ℂ)+t*I)‖≤ C)
    (hs:∀x∈Icc (1/2:ℝ) 2,∀t:ℝ,
      ‖series χ false ((x:ℂ)+t*I+shift 0 freq)‖≤ K*(1+|t|)^2):
    ‖polynomial χ false W D 0 freq‖≤(1/(2*Real.pi))*
      (C*K*Real.pi+3*C*K+C*HeckeReciprocalBound.bound 2*Real.pi):=by
  have hD0:0< D:=zero_lt_one.trans_le hD
  have hm4 (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      (1+|t|)^4*‖mellin W ((x:ℂ)+t*I)‖≤ C:=by
    apply le_trans _ (hm x hx t)
    gcongr
    · exact le_add_of_nonneg_right (abs_nonneg t)
    · norm_num
  have hcent:=weighted_central χ W D freq C K D hD0 hC hK hD0.le
    (hm4 _ (by norm_num)) (fun t _=> hs _ (by norm_num) t)
  have hg (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(y:ℝ)(hy:|y|=D):
      ‖series χ false ((x:ℂ)+y*I+shift 0 freq)‖≤ K*(1+D)^2:=by
    simpa only [hy] using hs x hx y
  have hlo:=horizontal_join_bound χ false W D 0 freq (1/2) 2 (-D) C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=> hm4 x hx (-D))
    (fun x hx=> hg x hx (-D) (by simp [abs_of_nonneg hD0.le]))
  have hhi:=horizontal_join_bound χ false W D 0 freq (1/2) 2 D C (K*(1+D)^2) 4
    hD (by norm_num) hC (by positivity) (fun x hx=> hm4 x hx D)
    (fun x hx=> hg x hx D (abs_of_nonneg hD0.le))
  have htail:=absolute_tail_bound χ false W D 2 0 freq C D 4 hD0 (by norm_num) hC hD0.le
    (hm _ (by norm_num))
  have hpower:D^(3/2:ℝ)≤(1+D)^2:=by
    have hp:D^(3/2:ℝ)≤ D^(2:ℝ):=Real.rpow_le_rpow_of_exponent_le hD (by norm_num)
    rw [Real.rpow_two] at hp
    nlinarith
  have hratio:D^(3/2:ℝ)/(1+D)^2≤1:=(div_le_one (by positivity)).mpr hpower
  have hratio4:D^(3/2:ℝ)/(1+D)^4≤1:=by
    apply (div_le_one (by positivity)).mpr
    apply hpower.trans
    exact pow_le_pow_right₀ (by linarith : 1≤1+D) (by norm_num : 2≤4)
  have hj:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)≤(3/2)*C*K:=by
    have he:(C*D^(3/2:ℝ)*(K*(1+D)^2)/(1+D)^4)*(3/2)=
        ((3/2)*C*K)*(D^(3/2:ℝ)/(1+D)^2):=by field_simp
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio
  have ht:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi≤
      C*HeckeReciprocalBound.bound 2*Real.pi:=by
    have hb:0≤ HeckeReciprocalBound.bound 2:=tsum_nonneg (fun _=> norm_nonneg _)
    have he:(C*D^(3/2:ℝ)*HeckeReciprocalBound.bound 2)/(1+D)^4*Real.pi=
        (C*HeckeReciprocalBound.bound 2*Real.pi)*(D^(3/2:ℝ)/(1+D)^4):=by ring
    rw [he]
    exact mul_le_of_le_one_right (by positivity) hratio4
  norm_num only [add_zero,show (2:ℝ)-1/2=3/2 by norm_num,show |(2:ℝ)-1/2|=3/2 by norm_num,
    abs_neg,abs_of_nonneg hD0.le] at hlo hhi htail
  rw [polynomial_finite_shift χ hχ false W a b ha hWs hW D 0 freq (1/2) 2 D hD0
    (by norm_num) hD0.le (by intro s hs h; cases h),norm_mul]
  have hnorm:‖(1/(2*Real.pi):ℂ)‖=(1/(2*Real.pi):ℝ):=by
    simp [Real.norm_eq_abs,abs_of_pos Real.pi_pos]
  rw [hnorm]
  apply mul_le_mul_of_nonneg_left ((norm_four_sides _ _ _ _).trans ?_) (by positivity)
  simp only [ofReal_neg] at hlo
  linarith [hlo.trans hj,hhi.trans hj,htail.trans ht]

end CenteredMomentPlainGlobalBound

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical Topology ContDiff
open Set Complex
namespace CenteredMomentPlainGlobalActual
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalBound

 theorem global_polynomial_bound (a b:ℝ)(ha:0< a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,1≤ D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,Cm,hCm,hm⟩:=profile_strip_decay a b ha (1/2) 2 6
  obtain ⟨Cg,hCg,hg⟩:=original_upper_strip (3/10) (by norm_num)
  let E:=HeckeReciprocalBound.bound 2
  have hE:0≤ E:=tsum_nonneg (fun _=> norm_nonneg _)
  let C:ℝ:=Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)
  have hC:0< C:=div_pos (mul_pos hCm (add_pos_of_pos_of_nonneg
    (mul_pos hCg (by positivity)) (mul_nonneg hE Real.pi_pos.le))) (by positivity)
  refine ⟨S,C,hC,?_⟩
  intro W hWs χ hχ D freq hD
  let Q:ℝ:=χ.modulus.absNorm
  let V:ℝ:=3+|freq|
  let B:ℝ:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hB:0≤ B:=apply_nonneg _ _
  have hQ:1≤ Q:=by
    dsimp [Q]
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤ V:=by dsimp [V]; linarith [abs_nonneg freq]
  have hQ0:0≤ Q:=zero_le_one.trans hQ
  have hrad:((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)≤ Q:=radical_norm_le_modulus χ
  have hrad0:0≤((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ):=Nat.cast_nonneg _
  have hcost:Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)≤ Q:=by
    calc
      _≤ Q^(3/5:ℝ)*Q^((1/10+(3/10)):ℝ):=mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hrad0 hrad (by norm_num)) (Real.rpow_nonneg hQ0 _)
      _=Q:=by rw [←Real.rpow_add (zero_lt_one.trans_le hQ)]; norm_num
  have hgrowth (x:ℝ)(hx:x∈Icc (1/2:ℝ) 2)(t:ℝ):
      ‖series χ false ((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)‖≤(Cg*Q*V^2)*(1+|t|)^2:=by
    have hs:-(1/10:ℝ)≤(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).re:=by simp [HeckeDyadic.shift]; linarith [hx.1]
    have hh:=hg χ hχ _ hs
    have him:(((x:ℂ)+t*I+HeckeDyadic.shift 0 freq)).im=t-freq:=by simp [HeckeDyadic.shift,sub_eq_add_neg]
    rw [him] at hh
    have ht:3+|t-freq|≤ V*(1+|t|):=by
      dsimp [V]
      have hab:=abs_sub t freq
      nlinarith [abs_nonneg t,abs_nonneg freq,mul_nonneg (abs_nonneg t) (abs_nonneg freq)]
    apply hh.trans
    change Cg*Q^(3/5:ℝ)*((HeckeDeletionBounds.radical χ.modulus).absNorm:ℝ)^((1/10+(3/10)):ℝ)*
      (3+|t-freq|)^2≤ _
    have hc:=mul_le_mul (mul_le_mul_of_nonneg_left hcost hCg.le)
      (pow_le_pow_left₀ (by positivity) ht 2) (by positivity) (mul_nonneg hCg.le hQ0)
    convert hc using 1 <;> first | rfl | ring
  have hb:=finite_strip_bound χ hχ W a b ha hWs (W.smooth ⊤) D freq (Cm*B) (Cg*Q*V^2)
    hD (mul_nonneg hCm.le hB) (by positivity) (hm W hWs) hgrowth
  have hQV:1≤ Q*V^2:=one_le_mul_of_one_le_of_one_le hQ (one_le_pow₀ hV)
  have he:E≤ E*(Q*V^2):=le_mul_of_one_le_right hE hQV
  apply hb.trans
  dsimp only [C]
  change _≤ Cm*(Cg*(Real.pi+3)+E*Real.pi)/(2*Real.pi)*B*Q*V^2
  have hCe: Cm*B*E*Real.pi≤ Cm*B*(E*(Q*V^2))*Real.pi:=by gcongr
  dsimp only [E] at hCe ⊢
  calc
    _≤(1/(2*Real.pi))*
      (Cm*B*(Cg*Q*V^2)*Real.pi+3*(Cm*B)*(Cg*Q*V^2)+
       Cm*B*(HeckeReciprocalBound.bound 2*(Q*V^2))*Real.pi):=
      mul_le_mul_of_nonneg_left (add_le_add_right hCe _) (by positivity)
    _=_:=by ring

end CenteredMomentPlainGlobalActual

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentPlainGlobalEnergy
open HeckeFamily HeckeDyadic CenteredMomentCoreFloor
open CenteredMomentPlainGlobalActual CenteredMomentPositiveSummability
open CenteredMomentRadialEligibleEnergy (Radial)
open InversePrincipalEnergy 
open CenteredMomentHeckeTwist CenteredMomentTwist CenteredMomentDetectorDictionary
open HeckeInverseAmplification CompletedHeight CenteredMomentHeckeHeight
open CenteredMomentLattice CenteredMomentHeckeCancellation CenteredMomentAbsoluteEnergy
local notation "O"=> Eisenstein.O

 theorem plain_height_norm (χ:Character)(W:ℝ→ℂ)(a b:ℝ)(ha:0< a)
    (hs:Function.support W⊆Set.Icc a b)(hW:ContDiff ℝ ∞ W)(t X:ℝ)(hX:0< X):
    ‖(Real.sqrt X:ℂ)⁻¹*twistedIdealSum χ W t X‖=
      ‖polynomial χ false W X 0 t‖:=by
  have hp:(normPowerProfile W a b ha hs hW t:ℝ→ℂ)=twistProfile W 0 t:=by
    funext x
    rw [normPowerProfile_apply]
    unfold twistProfile HeckeDyadic.shift
    simp only [Complex.ofReal_zero,zero_sub,neg_neg]
    rw [mul_comm (Complex.I) (t:ℂ)]
    ring
  rw [twistedIdealSum_scale χ W a b ha hs hW t X hX]
  have hi:idealSum χ (normPowerProfile W a b ha hs hW t) X=
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X:=by
    simp [idealSum,twistedIdealSum]
  rw [hi]
  have he:(Real.sqrt X:ℂ)⁻¹*((X:ℂ)^(Complex.I*t)*
      twistedIdealSum χ (normPowerProfile W a b ha hs hW t) 0 X)=
      (X:ℂ)^(Complex.I*t)*polynomial χ false W X 0 t:=by
    rw [←polynomial_twistProfile,←hp,plain_zero_height _ _ X hX]
    ring
  rw [he,norm_mul,norm_real_imaginary_power X t hX,one_mul]

 theorem zero_row_norm (η χ:Character)(mask A z:O)
    (hrow:∀n,elementCoeff χ n=CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)
    (W₁ W₂:ℝ→ℂ)(a b:ℝ)(ha:0< a)(hs₁:Function.support W₁⊆Set.Icc a b)
    (hs₂:Function.support W₂⊆Set.Icc a b)(hW₁:ContDiff ℝ ∞ W₁)(hW₂:ContDiff ℝ ∞ W₂)
    (t X₁ X₂:ℝ)(hX₁:0< X₁)(hX₂:0< X₂):
    ‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖=
      ‖polynomial χ false W₁ X₁ 0 t‖*‖polynomial χ false W₂ X₂ 0 t‖:=by
  unfold zeroRow
  rw [rowTwistedSum_eq η χ mask A z hrow,rowTwistedSum_eq η χ mask A z hrow,
    Real.sqrt_mul hX₁.le,Complex.ofReal_mul,mul_inv_rev]
  have he:(Real.sqrt X₂:ℂ)⁻¹*(Real.sqrt X₁:ℂ)⁻¹*
      (twistedIdealSum χ W₁ t X₁*twistedIdealSum χ W₂ t X₂)=
      ((Real.sqrt X₁:ℂ)⁻¹*twistedIdealSum χ W₁ t X₁)*
      ((Real.sqrt X₂:ℂ)⁻¹*twistedIdealSum χ W₂ t X₂):=by ring
  rw [he,norm_mul,plain_height_norm χ W₁ a b ha hs₁ hW₁ t X₁ hX₁,
    plain_height_norm χ W₂ a b ha hs₂ hW₂ t X₂ hX₂]

 theorem radial_bound_on_keep (F:O→ℂ)(r:Radial)(B:ℝ)(hB:0≤ B)
    (hF:∀z,r.keep z→‖F z‖≤ B):
    (∑'z:O,if r.keep z then ‖F z‖^2*(r.profile (‖ringComplex z‖^2/r.scale)).re else 0)≤
      diagonalControl r.profile*max 1 r.scale*B^2:=by
  have hb:∀z,‖(if r.keep z then F z else 0)‖≤ B:=by
    intro z
    by_cases h:r.keep z
    · simpa only [if_pos h] using hF z h
    · simpa only [if_neg h,norm_zero] using hB
  have hs:=bounded_radial_summable _ B hb r.keep r.profile r.scale r.scale_pos
  have heq:(fun z:O=> if r.keep z then
      ‖(if r.keep z then F z else 0)‖^2*(r.profile (‖ringComplex z‖^2/r.scale)).re else 0)=
      (fun z:O=> if r.keep z then ‖F z‖^2*(r.profile (‖ringComplex z‖^2/r.scale)).re else 0):=by
    funext z
    split_ifs <;> rfl
  rw [heq] at hs
  have hh:=hs.tsum_le_tsum (g:=fun z:O=> B^2*‖r.profile (‖ringComplex z‖^2/r.scale)‖) (fun z=> by
    split_ifs with hk
    · exact (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) (sq_nonneg _)).trans
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hF z hk) 2) (norm_nonneg _))
    · positivity) ((radial_norm_summable r.profile r.scale r.scale_pos).mul_left (B^2))
  rw [tsum_mul_left] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left
    (radial_weight_lattice_bound_all r.profile r.scale r.scale_pos) (sq_nonneg B)).trans_eq (by ring))

 theorem zero_all_lengths_floor (a b:ℝ)(ha:0< a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
    ∀(W₁ W₂:SchwartzMap ℝ ℂ),Function.support (W₁:ℝ→ℂ)⊆Set.Icc a b→
      Function.support (W₂:ℝ→ℂ)⊆Set.Icc a b→
    ∀(η:Character)(mask A:O)(r:Radial)(χ:O→Character),
      (∀z,r.keep z→(χ z).residue≠1)→
      (∀z,r.keep z→∀n,elementCoeff (χ z) n=
        CanonicalRowCompletion.rowTwist (HeckeRowClosure.elementHom η) mask 1 (A*z) n)→
    ∀(Z m q ρ Cscale t X₁ X₂:ℝ),1≤ Z→0≤ m→0≤ q→0≤ Cscale→
      r.scale=Z^m→m+q≤ρ→1≤ X₁→1≤ X₂→
      (∀z,r.keep z→((χ z).modulus.absNorm:ℝ)≤ Cscale*Z^(m+q))→
    zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤
      C*Cscale^4*diagonalControl r.profile*
        ((S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁)*
         (S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂))^2*(3+|t|)^8*Z^(m+q+4*ρ):=by
  obtain ⟨S,C,hC,hpoly⟩:=global_polynomial_bound a b ha
  refine ⟨S,C ^ 4,pow_pos hC _,?_⟩
  intro W₁ W₂ hs₁ hs₂ η mask A r χ hχ hrow Z m q ρ Cscale t X₁ X₂ hZ hm hq hCs hscale hfloor hX₁ hX₂ hmod
  let B₁:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₁
  let B₂:=S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W₂
  have hB₁:0≤ B₁:=apply_nonneg _ _
  have hB₂:0≤ B₂:=apply_nonneg _ _
  let V:=3+|t|
  let Q:=Cscale*Z^(m+q)
  have hQ:0≤ Q:=mul_nonneg hCs (Real.rpow_nonneg (zero_le_one.trans hZ) _)
  let B:=C ^ 2*(B₁*B₂)*Q^2*V^4
  have hB:0≤ B:=by dsimp [B]; positivity
  have hpoint (z:O)(hz:r.keep z):‖zeroRow η mask A z t W₁ W₂ X₁ X₂‖≤ B:=by
    rw [zero_row_norm η (χ z) mask A z (hrow z hz) W₁ W₂ a b ha hs₁ hs₂
      (W₁.smooth ⊤) (W₂.smooth ⊤) t X₁ X₂ (zero_lt_one.trans_le hX₁) (zero_lt_one.trans_le hX₂)]
    have hb₁:=hpoly W₁ hs₁ (χ z) (hχ z hz) X₁ t hX₁
    have hb₂:=hpoly W₂ hs₂ (χ z) (hχ z hz) X₂ t hX₂
    have h₁:‖polynomial (χ z) false W₁ X₁ 0 t‖≤ C*B₁*Q*V^2:=
      hb₁.trans (by dsimp [V]; gcongr; exact hmod z hz)
    have h₂:‖polynomial (χ z) false W₂ X₂ 0 t‖≤ C*B₂*Q*V^2:=
      hb₂.trans (by dsimp [V]; gcongr; exact hmod z hz)
    exact (mul_le_mul h₁ h₂ (norm_nonneg _) (by positivity)).trans_eq (by dsimp [B];ring)
  have hb:=radial_bound_on_keep (fun z=> zeroRow η mask A z t W₁ W₂ X₁ X₂) r B hB hpoint
  change zeroEnergy η mask A t W₁ W₂ X₁ X₂ r≤ _ at hb
  rw [hscale,max_eq_right (Real.one_le_rpow hZ hm)] at hb
  have hz:0< Z:=zero_lt_one.trans_le hZ
  have hp:Z^m*(Z^(m+q))^4≤ Z^(m+q+4*ρ):=by
    rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
    apply Real.rpow_le_rpow_of_exponent_le hZ
    norm_num
    linarith
  have hd:=diagonalControl_nonneg r.profile
  apply hb.trans
  calc
    _=(C ^ 4*Cscale^4*diagonalControl r.profile*(B₁*B₂)^2*V^8)*(Z^m*(Z^(m+q))^4):=by
      dsimp [B,Q]; ring
    _≤ _:=mul_le_mul_of_nonneg_left hp (by positivity)

end CenteredMomentPlainGlobalEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical SchwartzMap ContDiff
namespace CenteredMomentPlainPositiveScale
open HeckeFamily HeckeDyadic CenteredMomentPlainGlobalActual CenteredMomentPlainGlobalEnergy
open CenteredMomentHeckeTwist CenteredMomentDetectorDictionary

 theorem small_polynomial (χ:Character)(W:SchwartzMap ℝ ℂ)(a b:ℝ)(ha:0< a)
    (hWs:Function.support (W:ℝ→ℂ)⊆Set.Icc a b)(D freq:ℝ)(hD:0< D)(hD1:D≤1):
    ‖polynomial χ false W D 0 freq‖≤
      (128*max 0 b)*(SchwartzMap.seminorm ℝ 0 0 W):=by
  let B:=SchwartzMap.seminorm ℝ 0 0 W
  have hB:0≤ B:=apply_nonneg _ _
  have hWs':Function.support (W:ℝ→ℂ)⊆Set.Icc a (max 0 b):=by
    intro x hx
    exact ⟨(hWs hx).1,(hWs hx).2.trans (le_max_right _ _)⟩
  have hs:=twistedIdealSum_absolute χ W a (max 0 b) B ha (le_max_left _ _) hB hWs' (W.smooth ⊤)
    (fun x=> SchwartzMap.norm_le_seminorm ℝ W x) freq D hD
  rw [←plain_height_norm χ W a b ha hWs (W.smooth ⊤) freq D hD,norm_mul,norm_inv,
    Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg _)]
  apply (mul_le_mul_of_nonneg_left hs (inv_nonneg.mpr (Real.sqrt_nonneg _))).trans
  have hsq:(Real.sqrt D)^2=D:=Real.sq_sqrt hD.le
  have hroot:0< Real.sqrt D:=Real.sqrt_pos.mpr hD
  have hle:Real.sqrt D≤1:=by exact (Real.sqrt_le_one).mpr hD1
  have he:(Real.sqrt D)⁻¹*((128*max 0 b*B)*D)=(128*max 0 b*B)*Real.sqrt D:=by
    calc
      _=(128*max 0 b*B)*((Real.sqrt D)⁻¹*(Real.sqrt D*Real.sqrt D)):=by rw [←pow_two,hsq];ring
      _=_:=by rw [inv_mul_cancel_left₀ hroot.ne']
  rw [he]
  exact mul_le_of_le_one_right (by positivity) hle

 theorem global_positive_scale (a b:ℝ)(ha:0< a):
    ∃S:Finset (ℕ×ℕ),∃C:ℝ,0< C ∧
    ∀W:SchwartzMap ℝ ℂ,Function.support (W:ℝ→ℂ)⊆Set.Icc a b→
    ∀χ:Character,χ.residue≠1→∀D freq:ℝ,0< D→
      ‖polynomial χ false W D 0 freq‖≤
        C*(S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*
          (χ.modulus.absNorm:ℝ)*(3+|freq|)^2:=by
  obtain ⟨S,C,hC,hg⟩:=global_polynomial_bound a b ha
  let S':Finset (ℕ×ℕ):=insert (0,0) S
  let C':ℝ:=C+128*max 0 b
  have hC':0< C':=add_pos_of_pos_of_nonneg hC (by positivity)
  refine ⟨S',C',hC',?_⟩
  intro W hWs χ hχ D freq hD
  have hB:0≤ S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=apply_nonneg _ _
  have hsup:S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W≤ S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_def.mp (Finset.sup_mono (Finset.subset_insert _ _)) W
  have hzero:SchwartzMap.seminorm ℝ 0 0 W≤ S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W:=
    Seminorm.le_finset_sup_apply (p:=schwartzSeminormFamily ℝ ℝ ℂ) (s:=S') (i:=(0,0)) (x:=W) (Finset.mem_insert_self (0,0) S)
  have hQ:1≤(χ.modulus.absNorm:ℝ):=by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr χ.modulus_ne_bot)
  have hV:1≤(3+|freq|)^2:=one_le_pow₀ (by linarith [abs_nonneg freq])
  by_cases hD1:1≤ D
  · apply (hg W hWs χ hχ D freq hD1).trans
    gcongr
    dsimp [C']; linarith [le_max_left (0:ℝ) b]
  · have hh:=small_polynomial χ W a b ha hWs D freq hD (le_of_lt (lt_of_not_ge hD1))
    apply hh.trans
    calc
      _≤ C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W):=by
        apply mul_le_mul _ hzero (apply_nonneg _ _) hC'.le
        dsimp [C'];linarith
      _≤(C'*(S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W))*
          ((χ.modulus.absNorm:ℝ)*(3+|freq|)^2):=
        le_mul_of_one_le_right (mul_nonneg hC'.le hB) (one_le_mul_of_one_le_of_one_le hQ hV)
      _=_:=by ring

end CenteredMomentPlainPositiveScale

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentNaturalPrimitive
open HeckeFamily  UniqueFactorizationMonoid
local notation "O" => Eisenstein.O

def redundantSet (M C : Ideal O) : Finset (Ideal O) := primeSupport M\primeSupport C

def redundantIdeal (M C : Ideal O) : Ideal O := ∏P∈redundantSet M C,P

lemma redundantSet_prime (M C : Ideal O) : ∀P∈redundantSet M C,Prime P :=
  fun _ h=> support_prime (Finset.mem_sdiff.mp h).1

lemma redundantSet_subset (M C : Ideal O) : redundantSet M C⊆primeSupport M :=
  Finset.sdiff_subset

lemma prime_mem_support_iff (M P : Ideal O) (hM : M≠0) (hP : Prime P) :
    P∈primeSupport M ↔ P∣M := by
  simp only [primeSupport,Multiset.mem_toFinset,Ideal.mem_normalizedFactors_iff hM]
  exact ⟨fun h=> Ideal.dvd_iff_le.mpr h.2,fun h=>⟨Ideal.isPrime_of_prime hP,Ideal.dvd_iff_le.mp h⟩⟩

lemma mem_redundantSet (M C P : Ideal O) (hC : C≠0) :
    P∈redundantSet M C ↔ P∈primeSupport M ∧ ¬P∣C := by
  constructor
  · intro h
    obtain ⟨hp,hc⟩ := Finset.mem_sdiff.mp h
    exact ⟨hp,fun hd=> hc ((prime_mem_support_iff C P hC (support_prime hp)).mpr hd)⟩
  · rintro ⟨hp,hc⟩
    exact Finset.mem_sdiff.mpr ⟨hp,fun h=> hc ((prime_mem_support_iff C P hC (support_prime hp)).mp h)⟩

lemma redundantIdeal_squarefree (M C : Ideal O) : Squarefree (redundantIdeal M C) :=
  squarefree_support_product (redundantSet_subset M C)

lemma redundantIdeal_ne_zero (M C : Ideal O) : redundantIdeal M C≠0 :=
  support_product_ne_zero (redundantSet_subset M C)

lemma redundantIdeal_support (M C : Ideal O) : primeSupport (redundantIdeal M C)=redundantSet M C := by
  unfold primeSupport redundantIdeal
  rw [factors_support_product (redundantSet_subset M C)]
  exact Finset.val_toFinset _

lemma redundantIdeal_coprime (M C : Ideal O) (hC : C≠0) : IsCoprime (redundantIdeal M C) C := by
  apply (CenteredMomentSupport.primeSupport_disjoint_iff (redundantIdeal_ne_zero M C) hC).mp
  rw [redundantIdeal_support]
  exact Finset.disjoint_left.mpr (fun P hp hc=>(Finset.mem_sdiff.mp hp).2 hc)

lemma primitive_redundant_dvd (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C*redundantIdeal M C∣M := by
  exact (redundantIdeal_coprime M C hC).symm.mul_dvd hCM
    (support_product_dvd hM (redundantSet_subset M C))

lemma primitive_redundant_norm (M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    C.absNorm*(redundantIdeal M C).absNorm≤ M.absNorm := by
  have h := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hM))
    (map_dvd Ideal.absNorm (primitive_redundant_dvd M C hM hC hCM))
  simpa only [map_mul] using h

lemma coprime_support_iff (I M : Ideal O) (hM : M≠0) :
    IsCoprime I M ↔ ∀P∈primeSupport M,IsCoprime I P := by
  have hprod (s : Multiset (Ideal O)) : IsCoprime I s.prod ↔ ∀P∈s,IsCoprime I P := by
    induction s using Multiset.induction_on with
    | empty => simpa using (isCoprime_one_right : IsCoprime I (1 : Ideal O))
    | cons a s ih => simp only [Multiset.prod_cons,IsCoprime.mul_right_iff,Multiset.mem_cons,
        forall_eq_or_imp,ih]
  calc
    _ ↔ IsCoprime I (normalizedFactors M).prod := by rw [Ideal.prod_normalizedFactors_eq_self hM]
    _ ↔ _ := by simpa only [primeSupport,Multiset.mem_toFinset] using hprod (normalizedFactors M)

lemma coprime_original_iff (I M C : Ideal O) (hM : M≠0) (hC : C≠0) (hCM : C∣M) :
    IsCoprime I M ↔ IsCoprime I C ∧ ∀P∈redundantSet M C,IsCoprime I P := by
  constructor
  · intro h
    refine ⟨h.of_isCoprime_of_dvd_right hCM,?_⟩
    intro P hP
    exact (coprime_support_iff I M hM).mp h P ((redundantSet_subset M C) hP)
  · rintro ⟨hIC,hIR⟩
    apply (coprime_support_iff I M hM).mpr
    intro P hP
    by_cases hPC : P∈primeSupport C
    · exact (coprime_support_iff I C hC).mp hIC P hPC
    · exact hIR P (Finset.mem_sdiff.mpr ⟨hP,hPC⟩)

theorem idealCoeff_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (I : Ideal O) :
    idealCoeff χ I=idealCoeff (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
      (redundantSet_prime χ.modulus ψ.modulus)) I := by
  rw [hmask I,idealCoeff_excludePrimes]
  have hm := coprime_original_iff I χ.modulus ψ.modulus χ.modulus_ne_bot ψ.modulus_ne_bot
    (Ideal.dvd_iff_le.mpr hmod)
  by_cases hC : IsCoprime I ψ.modulus
  · rw [hm]
    simp only [hC,true_and]
  · have hz : idealCoeff ψ I=0 := by simpa only [hC,ite_false] using idealCoeff_source_mask ψ I
    simp only [hz,ite_self]

theorem polynomial_natural_deletion (χ ψ : Character) (hmod : χ.modulus≤ψ.modulus)
    (hmask : ∀I : Ideal O,idealCoeff χ I=if IsCoprime I χ.modulus then idealCoeff ψ I else 0)
    (inverse : Bool) (W : ℝ→ℂ) (D σ t : ℝ) :
    HeckeDyadic.polynomial χ inverse W D σ t=
      HeckeDyadic.polynomial (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
        (redundantSet_prime χ.modulus ψ.modulus)) inverse W D σ t := by
  unfold HeckeDyadic.polynomial
  congr 1
  apply tsum_congr
  intro I
  unfold HeckeDyadic.summand HeckeDyadic.coefficient
  rw [idealCoeff_natural_deletion χ ψ hmod hmask I.val]

theorem exists_natural_primitive (χ : Character) :
    ∃ψ : Character,χ.modulus≤ψ.modulus ∧
      FiniteFourier.IsPrimitiveOnIdeals ψ.residue ∧
      (χ.residue≠1 → ψ.residue≠1) ∧
      Squarefree (redundantIdeal χ.modulus ψ.modulus) ∧
      IsCoprime (redundantIdeal χ.modulus ψ.modulus) ψ.modulus ∧
      ψ.modulus*redundantIdeal χ.modulus ψ.modulus∣χ.modulus ∧
      ψ.modulus.absNorm*(redundantIdeal χ.modulus ψ.modulus).absNorm≤χ.modulus.absNorm ∧
      ∀I : Ideal O,idealCoeff χ I=idealCoeff
        (ψ.excludePrimes (redundantSet χ.modulus ψ.modulus)
          (redundantSet_prime χ.modulus ψ.modulus)) I := by
  obtain ⟨ψ,hmod,hprim,_,hmask⟩ := exists_primitive_character χ
  refine ⟨ψ,hmod,hprim,?_,redundantIdeal_squarefree _ _,redundantIdeal_coprime _ _ ψ.modulus_ne_bot,
    primitive_redundant_dvd _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    primitive_redundant_norm _ _ χ.modulus_ne_bot ψ.modulus_ne_bot (Ideal.dvd_iff_le.mpr hmod),
    idealCoeff_natural_deletion χ ψ hmod hmask⟩
  intro hχ hψ
  exact hχ ((HeckeFiniteDeletion.principal_iff_of_mask χ ψ hmask).mpr hψ)

end CenteredMomentNaturalPrimitive
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentWholeSlotDeletion
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentHeckeHeight
local notation "O" => Eisenstein.O

def normalizedSlot (η:Character) (m A z:O) (S:Finset (Ideal O)) (β:Ideal O→ℂ)
    (t P:ℝ) : ℂ := (Real.sqrt P:ℂ)⁻¹*rowSlot η m A z S β t

def selectedProduct {α:Type*} (J:Finset α) (η:Character) (m A z:O)
    (W₁ W₂:ℝ→ℂ) (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ)
    (t X₁ X₂:ℝ) : ℂ :=
  ((Real.sqrt (X₁*X₂):ℂ)⁻¹*
    (rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂))*
    ∏i∈J,normalizedSlot η m A z (S i) (β i) t (P i)

theorem selectedProduct_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂:ℝ) :
    selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂=
      (∏i∈R,normalizedSlot η m A z (S i) (β i) t (P i))*
        selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct
  rw [←Finset.prod_sdiff hR]
  ring

theorem selectedProduct_energy_remove {α:Type*} (J R:Finset α) (hR:R⊆J)
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:α→Finset (Ideal O)) (β:α→Ideal O→ℂ) (P:α→ℝ) (t X₁ X₂ Z κ:ℝ)
    (hZ:0< Z) (w B:α→ℝ) (_hB:∀i∈R,0≤ B i)
    (hslot:∀i∈R,‖normalizedSlot η m A z (S i) (β i) t (P i)‖^2≤ B i*Z^(κ*w i)) :
    ‖selectedProduct J η m A z W₁ W₂ S β P t X₁ X₂‖^2≤
      ((∏i∈R,B i)*Z^(κ*∑i∈R,w i))*
        ‖selectedProduct (J\R) η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  rw [selectedProduct_remove J R hR,norm_mul,mul_pow,norm_prod,←Finset.prod_pow]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
  calc
    _≤∏i∈R,B i*Z^(κ*w i):=Finset.prod_le_prod (fun i _=> sq_nonneg _) hslot
    _=_:=by rw [Finset.prod_mul_distrib,←Real.rpow_sum_of_pos hZ,Finset.mul_sum]

end CenteredMomentWholeSlotDeletion

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators
namespace CenteredMomentSlotNormalization
open HeckeFamily CenteredMomentHeckeSlots CenteredMomentRetainedEnergy
open CenteredMomentWholeSlotDeletion CenteredMomentHeckeHeight
local notation "O" => Eisenstein.O

lemma sqrt_product_normalizer {ι:Type*} [Fintype ι] (X:ℝ) (P:ι→ℝ)
    (hX:0≤ X) (hP:∀i,0≤ P i) :
    ((Real.sqrt X:ℂ)⁻¹)*(∏i,(Real.sqrt (P i):ℂ)⁻¹)=
      (Real.sqrt (X*∏i,P i):ℂ)⁻¹ := by
  rw [Real.sqrt_mul hX,Real.sqrt_prod _ (fun i _=> hP i),Complex.ofReal_mul,
    Complex.ofReal_prod,mul_inv_rev,Finset.prod_inv_distrib]
  ring

theorem selectedProduct_univ {ι:Type*} [Fintype ι] [DecidableEq ι]
    (η:Character) (m A z:O) (W₁ W₂:ℝ→ℂ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (P:ι→ℝ)
    (t X₁ X₂:ℝ) (hX:0≤ X₁*X₂) (hP:∀i,0≤ P i) :
    selectedProduct Finset.univ η m A z W₁ W₂ S β P t X₁ X₂=
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂ := by
  unfold selectedProduct normalizedSlot positiveSlotRow
  rw [Finset.prod_mul_distrib]
  have he:=sqrt_product_normalizer (X₁*X₂) P hX hP
  calc
    _=((Real.sqrt (X₁*X₂):ℂ)⁻¹*(∏i,(Real.sqrt (P i):ℂ)⁻¹))*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏i,rowSlot η m A z (S i) (β i) t) := by ring
    _=_ := by rw [he]

end CenteredMomentSlotNormalization

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff
namespace CenteredMomentComparisonReflection
open HeckeFamily HeckePrimitive Eisenstein 
open SchwartzPlanePoisson 
local notation "O" => Eisenstein.O
local notation "NI" => CubicEisenstein.NonzeroIdeal

lemma residue_nontrivial (c : O) (χ : MulChar (O⧸Ideal.span {c}) ℂ) (hχ : χ≠1) :
    Nontrivial (O⧸Ideal.span {c}) := by
  by_contra h
  have : Subsingleton (O⧸Ideal.span {c}) := not_nontrivial_iff_subsingleton.mp h
  apply hχ
  ext x
  have hx : x=1 := Subsingleton.elim _ _
  simp [hx]

lemma residue_zero (c : O) [NeZero c] (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1) (hχ : χ≠1) :
    elementCoeff (character c χ hu) 0=0 := by
  let := residue_nontrivial c χ hχ
  change χ (Ideal.Quotient.mk (Ideal.span {c}) 0)=0
  rw [map_zero,χ.map_zero]

theorem radial_ideal_reindex (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hzero : elementCoeff η 0=0)
    (hs : Summable (fun z : O => elementCoeff η z*W (‖ringComplex z‖^2/X))) :
    (∑' z : O,elementCoeff η z*W (‖ringComplex z‖^2/X))=
      6*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  have h := SchwartzPlanePoisson.tsum_unit_invariant_ideals
    (fun z : O => elementCoeff η z*W (‖ringComplex z‖^2/X)) hs
    (by rw [hzero,zero_mul])
    (fun u z => by rw [elementCoeff_unit_mul,map_mul,norm_mul,norm_ringComplex_unit,one_mul])
  rw [EisensteinLatticeCount.natCard_units_eq_six] at h
  rw [h]
  congr 1
  apply tsum_congr
  intro I
  rw [ringComplex_norm_sq_eq_absNorm_span,span_cubicIdealGenerator]
  congr 1
  exact (IdealCharacter.ofResidue_of_generator η.modulus η.residue η.unit_trivial
    I.property (span_cubicIdealGenerator I.val)).symm

lemma bounded_radial_summable (η : Character) (W : ℝ→ℂ) (X : ℝ)
    (hs : Summable (fun z : O => ‖W (‖ringComplex z‖^2/X)‖)) :
    Summable (fun z : O => elementCoeff η z*W (‖ringComplex z‖^2/X)) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) _ hs
  intro z
  rw [norm_mul]
  apply mul_le_of_le_one_left (norm_nonneg _)
  let : Finite (O⧸η.modulus) := Ring.HasFiniteQuotients.finiteQuotient η.modulus_ne_bot
  let : Fintype (O⧸η.modulus) := Fintype.ofFinite _
  exact FiniteRayExpansion.norm_char_le_one η.residue _

theorem primitive_plain_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0< X) :
    (∑' I : NI,idealCoeff (character c χ hu) I.val*W ((I.val.absNorm:ℝ)/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖ringComplex c‖:ℂ))*
      ∑' I : NI,idealCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) I.val*
        paperRadialFourier W ((I.val.absNorm:ℝ)/(‖ringComplex c‖^2/X)) := by
  have hc : 0<‖ringComplex c‖ := norm_pos_iff.mpr (ringComplex_ne_zero (NeZero.ne c))
  have hQ : 0<‖ringComplex c‖^2 := sq_pos_of_pos hc
  have hχi : χ⁻¹≠1 := inv_ne_one.mpr hχ
  have hs : Summable (fun z : O => ‖W (‖ringComplex z‖^2/X)‖) := by
    simpa only [scaledRadialTest_apply] using actual_eisenstein_summable_norm (scaledRadialTest W X hX)
  have hd : Summable (fun z : O => ‖paperRadialFourier W
      (‖ringComplex z‖^2/(‖ringComplex c‖^2/X))‖) := by
    convert paperRadialFourier_lattice_summable_norm W (X/‖ringComplex c‖^2) (div_pos hX hQ) using 1
    funext z
    congr 2
    field_simp
  have he := TraceCharacter.primitive_radial_paper_poisson_normalized c W X hX χ hp
  have he' : (∑' z : O,elementCoeff (character c χ hu) z*W (‖ringComplex z‖^2/X))=
      ((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖ringComplex c‖:ℂ))*
      ∑' z : O,elementCoeff (character c χ⁻¹ (inverse_unit_trivial c χ hu)) z*
        paperRadialFourier W (‖ringComplex z‖^2/(‖ringComplex c‖^2/X)) := by
    change (∑' z : O,χ (Ideal.Quotient.mk (Ideal.span {c}) z)*W (‖ringComplex z‖^2/X))=_
    rw [he]
    congr 1
    apply tsum_congr
    intro z
    congr 2
    field_simp
  rw [radial_ideal_reindex _ W X (residue_zero c χ hu hχ) (bounded_radial_summable _ W X hs),
    radial_ideal_reindex _ (paperRadialFourier W) _ (residue_zero c χ⁻¹ _ hχi)
      (bounded_radial_summable _ (paperRadialFourier W) _ hd)] at he'
  linear_combination he'/6

lemma inverse_half_power (X : ℝ) (hX : 0≤ X) :
    (X:ℂ)^(-(1/2:ℂ))=(Real.sqrt X:ℂ)⁻¹ := by
  rw [Complex.cpow_neg]
  congr 1
  rw [Real.sqrt_eq_rpow]
  simpa only [Complex.ofReal_div,Complex.ofReal_one,Complex.ofReal_ofNat] using (Complex.ofReal_cpow hX (1/2)).symm

lemma polynomial_plain (η : Character) (W : ℝ→ℂ) (X : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial η false W X 0 0=
      (Real.sqrt X:ℂ)⁻¹*∑' I : NI,idealCoeff η I.val*W ((I.val.absNorm:ℝ)/X) := by
  simp only [HeckeDyadic.polynomial,HeckeDyadic.summand,HeckeDyadic.coefficient,
    Bool.false_eq_true,ite_false,HeckeDyadic.shift,Complex.ofReal_zero,zero_mul,
    sub_zero,neg_zero,Complex.cpow_zero,mul_one,HeckeDyadic.norm]
  rw [inverse_half_power X hX.le]

theorem primitive_normalized_reflection (c : O) [NeZero c]
    (χ : MulChar (O⧸Ideal.span {c}) ℂ)
    (hu : ∀u:Oˣ,χ (Ideal.Quotient.mk (Ideal.span {c}) u.val)=1)
    (hp : FiniteFourier.IsPrimitiveOnIdeals χ) (hχ : χ≠1)
    (W : 𝓢(ℝ,ℂ)) (X : ℝ) (hX : 0< X) :
    HeckeDyadic.polynomial (character c χ hu) false W X 0 0=
      TraceCharacter.normalizedGauss c χ*
        HeckeDyadic.polynomial (character c χ⁻¹ (inverse_unit_trivial c χ hu)) false
          (paperRadialFourier W) (‖ringComplex c‖^2/X) 0 0 := by
  have hc : 0<‖ringComplex c‖ := norm_pos_iff.mpr (ringComplex_ne_zero (NeZero.ne c))
  have hY : 0<‖ringComplex c‖^2/X := div_pos (sq_pos_of_pos hc) hX
  rw [polynomial_plain _ _ _ hX,primitive_plain_reflection c χ hu hp hχ W X hX,
    polynomial_plain _ _ _ hY]
  have hs : Real.sqrt (‖ringComplex c‖^2/X)=‖ringComplex c‖/Real.sqrt X := by
    rw [Real.sqrt_div (sq_nonneg _),Real.sqrt_sq hc.le]
  have hx : (Real.sqrt X:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr hX).ne'
  have hcn : (‖ringComplex c‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hc.ne'
  have hsq : (Real.sqrt X:ℂ)^2=(X:ℂ) := by exact_mod_cast Real.sq_sqrt hX.le
  have hfac : (Real.sqrt X:ℂ)⁻¹*((X:ℂ)*TraceCharacter.normalizedGauss c χ/(‖ringComplex c‖:ℂ))=
      TraceCharacter.normalizedGauss c χ*(Real.sqrt (‖ringComplex c‖^2/X):ℂ)⁻¹ := by
    rw [hs,Complex.ofReal_div]
    field_simp
    rw [hsq]
  rw [←mul_assoc,hfac,mul_assoc]

theorem reflected_profile_height_control (a b : ℝ) (ha : 0< a) (A K : ℕ) :
    ∃ n : ℕ,∀ (W : ℝ→ℂ),∀_hs : Function.support W⊆Set.Icc a b,
      ∀_hW : ContDiff ℝ ∞ W,∃C : ℝ,0< C ∧ ∀t : ℝ,∀j : ℕ,j≤ K → ∀x : ℝ,0≤ x →
      (1+x)^A*‖LocalLogFourier.eulerDeriv
        (paperRadialFourier (CompletedHeight.normTwistedSource W t)) j x‖≤ C*(1+‖t‖)^n := by
  obtain ⟨s,C,hC,hbound⟩ := paperRadialFourier_euler_source_weighted_bound A K
  obtain ⟨n,hn⟩ := CompletedHeight.normTwistedSource_uniform_degree a b ha s
  refine ⟨n,?_⟩
  intro W hs hW
  obtain ⟨D,hD,hDbd⟩ := hn W hs hW
  refine ⟨C*D,mul_pos hC hD,?_⟩
  intro t j hj x hx
  have hsame : (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t : ℝ→ℂ)=
      CompletedHeight.normTwistedSource W t := by
    funext y
    exact CompletedHeight.uniformTwistedSchwartz_apply W a b ha hs hW t y
  have hb := hbound (CompletedHeight.uniformTwistedSchwartz W a b ha hs hW t) j hj x hx
  rw [hsame] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_left (hDbd t) hC.le).trans_eq (by ring))
end CenteredMomentComparisonReflection

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
