/-
The first dyadic radius adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.CorrelatedSecondRadius
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.FirstGlobalCaps

/-!
# The first dyadic radius

First dyadic and cell radii, label gates and refined outer data of the live first original
profile; principal mass cores and priority tail and zero parents.
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
namespace InverseMomentFirstLiveCaps
open InverseMoment InverseMomentFirstOriginalProfile Eisenstein FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg:∀i,lambda∉Ideal.span {p i})

theorem original_live_norm_caps
    (pool:Finset ι)(Q:Finset (ι→₀ℕ))(labels:Finset (Ideal O))(Y:ℝ)
    (β:Ideal O→(ι→₀ℕ)→ℂ)(cutoff:CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ:O→*ℂ)(m:O)(mark:(ι→₀ℕ)→Finset ι→ℂ)(W:ℝ→ℂ)(Φ:𝓢(ℝ,ℂ))(K L B:ℝ)
    (hB:0≤ B)(hQ:∀v∈Q,‖ringComplex (primeProduct p v.support v)‖^2≤ B)
    (hlabels:∀I∈labels,I≠0)(hW:∀y,W y≠0→y≤ L)(x:OriginalIndex ι)
    (hx:x∈firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun o=>o.1) Y)
    (j:FirstCommonIndex ι)
    (hn:sourceSummand p hp hg β cutoff Ψ m mark W Φ K x j≠0):
    (∀i:Fin 6,originalNorms p x i≤(![L,L,L,L*B^2,B^2,Y]:Fin 6→ℝ) i) ∧
      primeProductNorm p j.2.1≤ L ∧ InverseFirstGlobalCaps.jNorm p x.1≤ B^2:=by
  obtain ⟨ha₁,ha₂,hcommon,hquot⟩:=original_live_profile_caps p hp hg pool Q labels Y β cutoff Ψ m mark W Φ K L hW x hx j hn
  obtain ⟨ho,hfreq⟩:=Finset.mem_sigma.mp hx
  obtain ⟨hb,hC,hD⟩:=(mem_firstOriginalOuter pool Q x.1).mp ho
  obtain ⟨hf,hrow⟩:=(mem_firstRetainedSource p labels x.1.1 Y x.2).mp hfreq
  have hcube:=reopenedCubeFamily_cube_norms p Q B hQ x.1.1 hb
  have hsup:=cube_whole_support_dyad p hp x.1.1 B hB hcube.1 hcube.2
  have hdiv:primeProductNorm p x.1.2.2≤ L*B^2:=by
    calc
      _≤ primeProductNorm p (x.1.2.1∪cubePrincipalSupport x.1.1.support x.1.1.leftExponent
          x.1.1.rightExponent x.1.1.leftBit x.1.1.rightBit):=
        primeProductNorm_mono p hp (Finset.mem_powerset.mp hD)
      _≤ primeProductNorm p x.1.2.1*primeProductNorm p x.1.1.support:=by
        apply (primeProductNorm_union_le_mul p hp _ _).trans
        exact mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _))
          (primeProductNorm_pos p hp _).le
      _≤ L*B^2:=mul_le_mul hcommon hsup (primeProductNorm_pos p hp _).le
        ((primeProductNorm_pos p hp _).le.trans hcommon)
  have hactive:activeNorm p x≤ B^2:=
    (primeProductNorm_mono p hp (Finset.filter_subset _ _)).trans hsup
  have hE:=firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hlabels _ hf)
  have hh0:x.2.2≠0:=(Finset.mem_erase.mp hrow).1
  have hh:=((mem_nonzeroChildFrequencyBall _ hE Y x.2.2).mp hrow).2
  have hfreqnorm:‖ringComplex x.2.2‖^2≤ Y:=
    (element_norm_le_of_dvd (mul_ne_zero hE hh0) (dvd_mul_left x.2.2 _)).trans hh
  have hj:InverseFirstGlobalCaps.jNorm p x.1≤ B^2:=by
    have hd:=jLabel_dvd_cube_product p x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
      x.1.1.leftBit x.1.1.rightBit x.1.1.support_pos
    have hnorm:=element_norm_le_of_dvd
      (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _)) hd
    simp only [map_mul,norm_mul,mul_pow] at hnorm
    exact hnorm.trans ((mul_le_mul hcube.1 hcube.2 (sq_nonneg _) hB).trans_eq (pow_two B).symm)
  refine ⟨?_,hquot,hj⟩
  intro i
  fin_cases i
  · exact ha₁
  · exact ha₂
  · exact hcommon
  · simpa [originalNorms,InverseMomentFirstChildWindows.sourceNorms,divisorElement,
      primeProductNorm] using hdiv
  · exact hactive
  · exact hfreqnorm

end InverseMomentFirstLiveCaps

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic InverseFirstGlobalCaps
open InverseSecondSourceBlocks
open Eisenstein (ringComplex)
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]

def firstDyadicExponent (Z x:ℝ):ℝ:=dyadicExponent Z (dyadIndex x)

theorem first_dyadic_bounds (Z eta x:ℝ)(hZ:1<Z)(hbin:2≤ Z^eta)(hx:1≤ x):
    0≤ firstDyadicExponent Z x ∧ Z^firstDyadicExponent Z x≤ x ∧ x≤ Z^(firstDyadicExponent Z x+eta):=by
  have hd:=dyadIndex_bounds x hx
  have he:=dyad_power_bounds Z eta x hZ hbin (dyadIndex x) ⟨hd.1,hd.2.le⟩
  refine ⟨?_,he⟩
  apply (Real.rpow_le_rpow_left_iff hZ).mp
  rw [Real.rpow_zero,firstDyadicExponent,rpow_dyadicExponent Z hZ]
  exact one_le_pow₀ (by norm_num : (1:ℝ)≤2)

def firstDyadicRadius (p:ι→O)(b:CubeCoordinates ι)(C D:Finset ι)
    (Z M r ell V eta tau:ℝ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (firstDyadicExponent Z (primeProductNorm p D))
    (firstDyadicExponent Z (primeProductNorm p C))
    (firstDyadicExponent Z (‖ringComplex (jLabel p b.support
      (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2))+12*eta+tau)

def firstDyadicPhysicalCutoff (p:ι→O)(b:CubeCoordinates ι)(C:Finset ι)(I:Ideal O)
    (Z M r ell V eta tau:ℝ)(D:Finset ι):Finset O:=
  childFrequencyBall (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit I)
    (firstDyadicRadius p b C D Z M r ell V eta tau)

theorem first_dyadic_radius_global_cap
    (p:ι→O)(hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι)(C D:Finset ι)
    (hD:D⊆C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)
    (Z M r ell V eta tau Fmax:ℝ)(hZ:1<Z)(hbin:2≤ Z^eta)(hM:0≤ M)
    (hF:r+3*ell+V≤ Fmax)
    (h₁:‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ Z^(ell+eta))
    (h₂:‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ Z^(ell+eta)):
    firstDyadicRadius p b C D Z M r ell V eta tau≤ Z^(2*Fmax+15*eta+tau):=by
  have hz:0<Z:=zero_lt_one.trans hZ
  have hC:=first_dyadic_bounds Z eta (primeProductNorm p C) hZ hbin (primeProductNorm_ge_one p hp C)
  have hd:=first_dyadic_bounds Z eta (primeProductNorm p D) hZ hbin (primeProductNorm_ge_one p hp D)
  have hj:=first_dyadic_bounds Z eta (‖ringComplex (jLabel p b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)‖^2) hZ hbin
    (SecondPassArithmetic.element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hs:=cube_whole_support_dyad p hp b (Z^(ell+eta)) (Real.rpow_nonneg hz.le _) h₁ h₂
  have hn:primeProductNorm p D≤ Z^(firstDyadicExponent Z (primeProductNorm p C)+2*ell+3*eta):=by
    calc
      _≤ primeProductNorm p (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit):=
        primeProductNorm_mono p hp hD
      _≤ primeProductNorm p C*primeProductNorm p b.support:=
        (primeProductNorm_union_le_mul p hp _ _).trans
          (mul_le_mul_of_nonneg_left (primeProductNorm_mono p hp (Finset.filter_subset _ _)) (primeProductNorm_pos p hp _).le)
      _≤ Z^(firstDyadicExponent Z (primeProductNorm p C)+eta)*(Z^(ell+eta))^2:=
        mul_le_mul hC.2.2 hs (primeProductNorm_pos p hp _).le (Real.rpow_nonneg hz.le _)
      _=_:=by
        rw [←Real.rpow_natCast,←Real.rpow_mul hz.le,←Real.rpow_add hz]
        congr 1
        norm_num
        ring
  have hde:= (Real.rpow_le_rpow_left_iff hZ).mp (hd.2.1.trans hn)
  unfold firstDyadicRadius firstPhysicalHeight
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  linarith [hC.1,hj.1]

end InverseMoment

end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment InverseMomentFirstChildWindows Eisenstein
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalNorms_eq_caps : originalNorms p=InverseFirstGlobalCaps.originalNorms p := by
  funext x i
  fin_cases i <;> rfl

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma originalOuterCell_eq_caps (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) :
    originalOuterCell p pool Q k=InverseFirstGlobalCaps.outerCell p pool Q k := by
  unfold originalOuterCell InverseFirstGlobalCaps.outerCell InverseFirstGlobalCaps.outerGate
  ext x
  simp only [Finset.mem_filter,originalNorms_eq_caps,InverseFirstGlobalCaps.originalNorms_outer]

lemma originalChildEnergy_eq_caps (hp : ∀i,p i≠0)
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) :
    originalChildEnergy p hp hg hinj pool Q k l negative Ψ m mark omega T t Y=
      ∑x∈InverseFirstGlobalCaps.outerCell p pool Q k,
        firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
          (mark (if negative then x.1.rightExponent else x.1.leftExponent))
          (commonSelector p (fun _=>1) l) omega T t Y := by
  rw [originalChildEnergy,originalOuterCell_eq_caps]

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]

def refinedOuter (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex)
    (gate : FirstOriginalOuter ι→Prop) : Finset (FirstOriginalOuter ι) :=
  (originalOuterCell p pool Q k).filter gate

def refinedSource (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) : Finset (OriginalIndex ι) :=
  (sourceCell (originalNorms p)
    (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k).filter
      (fun x=>gate x.1 ∧ firstOriginalWeight p β cutoff x.1 x.2≠0)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedSource_subset (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Y : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop) :
    refinedSource p pool Q labels β cutoff Y k gate⊆sourceCell (originalNorms p)
      (firstGlobalRetainedSource p (firstOriginalOuter pool Q) (fun _=>labels) (fun x=>x.1) Y) k :=
  Finset.filter_subset _ _

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma original_weight_frequency (β : Ideal O→(ι→₀ℕ)→ℂ)
    (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (x : OriginalIndex ι) (hx : firstOriginalWeight p β cutoff x.1 x.2≠0) :
    x.2.2∈reopenedPhysicalCutoff p x.1.1 x.2.1 (cutoff x.1.1 x.1.2.1 x.2.1) x.1.2.2 := by
  by_contra hh
  exact hx (by simp [firstOriginalWeight,hh])

theorem refined_source_radius (hp : ∀i,p i≠0)
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ysource Ychild : ℝ) (k : SourceIndex) (gate : FirstOriginalOuter ι→Prop)
    (hn : ∀I∈labels,I≠0)
    (hcut : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤ Ychild) :
    refinedSource p pool Q labels β cutoff Ysource k gate⊆
      firstGlobalRetainedSource p (refinedOuter p pool Q k gate) (fun _=>labels) (fun x=>x.1) Ychild := by
  intro x hx
  obtain ⟨hxcell,hgate,hweight⟩ := Finset.mem_filter.mp hx
  have hxold := original_cell_subset p pool Q labels Ysource k hxcell
  obtain ⟨ho,hf⟩ := Finset.mem_sigma.mp hxold
  have hm := (mem_firstRetainedSource p labels x.1.1 Ysource x.2).mp hf
  have houter : x.1∈refinedOuter p pool Q k gate := Finset.mem_filter.mpr ⟨ho,hgate⟩
  have hE := firstPhysicalMultiplier_ne_zero p hp x.1.1.support x.1.1.leftExponent x.1.1.rightExponent
    x.1.1.leftBit x.1.1.rightBit x.2.1 (hn x.2.1 hm.1)
  apply Finset.mem_sigma.mpr
  refine ⟨houter,(mem_firstRetainedSource p labels x.1.1 Ychild x.2).mpr ⟨hm.1,?_⟩⟩
  apply Finset.mem_erase.mpr
  refine ⟨(Finset.mem_erase.mp hm.2).1,?_⟩
  apply (mem_childFrequencyBall _ hE Ychild x.2.2).mpr
  exact ((mem_childFrequencyBall _ hE _ x.2.2).mp
    (original_weight_frequency p β cutoff x hweight)).trans (hcut x.1 houter x.2.1 hm.1)

def labelGate (j : ℕ) (x : FirstOriginalOuter ι) : Prop :=
  InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma refinedOuter_label (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (j : ℕ) :
    refinedOuter p pool Q k (labelGate p j)=
      (InverseFirstGlobalCaps.outerCell p pool Q k).filter
        (fun x=>InverseSecondSourceBlocks.dyadIndex (InverseFirstGlobalCaps.jNorm p x)=j) := by
  rw [refinedOuter,originalOuterCell_eq_caps]
  ext x
  simp [labelGate]

end InverseMomentFirstOriginalProfile
end

noncomputable section
namespace InverseMomentFirstOriginalProfile
open InverseMoment Eisenstein FirstPassCubeLabels SecondPassArithmetic
open InverseMomentFirstChildWindows InverseMomentFirstProfileUniform
open InverseAmbientProfileTower JointLogSeparation
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]

def refinedChildEnergy (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i})
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (k : SourceIndex) (l : ℕ)
    (gate : FirstOriginalOuter ι→Prop) (negative : Bool) (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (omega : ℝ→ℂ) (T t Y : ℝ) : ℝ :=
  ∑x∈refinedOuter p pool Q k gate,
    firstCanonicalSecondEnergy p hp hg hinj pool x.1 x.2.1 negative Ψ m (divisorElement p x)
      (mark (if negative then x.1.rightExponent else x.1.leftExponent))
      (commonSelector p (fun _=>1) l) omega T t Y

def refinedCellRows (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hg : ∀i,lambda∉Ideal.span {p i})
    (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
    (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
    (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ)
    (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop) (W₁ W₂ : ℝ→ℂ) (Φ : 𝓢(ℝ,ℂ)) (K Y : ℝ) (s : Fin 9→ℝ) : ℂ :=
  firstFamilyPhysicalRows p hg
    (refinedSource p pool Q labels β cutoff Y k gate)
    pool (fun _=>commonSelector p (fun _=>1) l)
    (coefficient p hg Ψ m mark true) (coefficient p hg Ψ m mark false)
    (weight p hp hg β cutoff Ψ m) W₁ W₂ Φ
    (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p) K
    (fun x=>divisorElement p x.1) (fun x=>x.2.2) s

theorem original_refined_cell_physical_budget (g₁ g₂ Φ : 𝓢(ℝ,ℂ)) (m₁ m₂ : ℝ)
    (hm₁ : 0≤ m₁) (hm₂ : 0≤ m₂)
    (hg₁ : Function.support g₁⊆Set.Icc (-m₁) m₁)
    (hg₂ : Function.support g₂⊆Set.Icc (-m₂) m₂) :
    ∃(omega₁ omega₂ : 𝓢(ℝ,ℂ))(lo hi : ℝ),0<lo ∧ lo≤ hi ∧
      HasCompactSupport (omega₁ : ℝ→ℂ) ∧ HasCompactSupport (omega₂ : ℝ→ℂ) ∧
      tsupport (omega₁ : ℝ→ℂ)⊆Set.Icc lo hi ∧ tsupport (omega₂ : ℝ→ℂ)⊆Set.Icc lo hi ∧
    ∀(ε : ℝ),0<ε→∀(Aker J : ℕ),∃ Cprofile Kpush : ℝ,0≤ Cprofile ∧ 0<Kpush ∧
    ∀{ι : Type*}[DecidableEq ι](p : ι→O)(hp : ∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀i,lambda^2∣p i-1)
      (pool : Finset ι) (Q : Finset (ι→₀ℕ)) (labels : Finset (Ideal O))
      (β : Ideal O→(ι→₀ℕ)→ℂ) (cutoff : CubeCoordinates ι→Finset ι→Ideal O→Finset ι→ℝ)
      (Ψ : O→*ℂ) (m : O) (mark : (ι→₀ℕ)→Finset ι→ℂ) (Γ Ysource Y : ℝ)
      (_hΨ : ∀u,‖Ψ u‖≤1) (_hΓ : 0≤Γ) (_hY : 0<Y)
      (_hsf : ∀I∈labels,Squarefree I) (_hn : ∀I∈labels,I≠0)
      (_hβ : ∀I∈labels,∀v∈Q,‖β I v‖≤Γ)
      (k : SourceIndex) (l : ℕ) (gate : FirstOriginalOuter ι→Prop)
      (_hcutoff : ∀x∈refinedOuter p pool Q k gate,∀I∈labels,cutoff x.1 x.2.1 I x.2.2≤ Y)
      (T₁ T₂ K theta L : ℝ)
      (_hT₁ : 0<T₁) (_hT₂ : 0<T₂) (_hK : 0<K) (_hL : 0≤ L)
      (Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta : ℝ)
      (_hB : 0≤ Benergy) (_hZ : 0<Z)
      (_hscale : rawScales k l T₁ T₂=fun i=>Z^(![aa₁,aa₂,bb,delta,rr,tq,hh,r-aa₁-bb-tq,r-aa₂-bb-tq] i))
      (_hLe : L=eta*Real.log Z)
      (_hleft : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₁ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate true Ψ m mark omega₁ T₁
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2))
      (_hright : ∀z : Frequency×(Fin 9→ℝ),
        (Z^(firstKappa M r ell V delta aa₂ bb rr)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
          refinedChildEnergy p hp hg hinj pool Q k l gate false Ψ m mark omega₂ T₂
            (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) Y≤
          Benergy*(tripleHeight J z.1*coordinateHeight J z.2)),
      (Z^(-r-2*ell-V)*Z^M)*‖refinedCellRows p hp hcop hg pool Q labels β cutoff Ψ m mark k l gate
        (positiveSource g₁ 1 (-theta)) (positiveSource g₂ 1 theta) Φ K Ysource (rawScales k l T₁ T₂)‖≤
        ((Γ^2*Kpush*Y^ε*Benergy)*(Cprofile*((1+‖-theta‖)^InverseClippingProfiles.momentOrder J*
          (1+‖theta‖)^InverseClippingProfiles.momentOrder J)/
          (1+K*(rawScales k l T₁ T₂) 6/((rawScales k l T₁ T₂) 3*(rawScales k l T₁ T₂) 4*
            ((rawScales k l T₁ T₂) 5)^2*T₁*T₂))^Aker)) := by
  obtain ⟨w₁,w₂,U,M₀,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,hM,hUc,hUs,hwin⟩ :=
    original_cell_windows g₁ g₂ m₁ m₂ 1 (fun _=>0) hm₁ hm₂ hg₁ hg₂ (fun _=>le_rfl)
  refine ⟨w₁,w₂,lo,hi,hlo,hlh,hw₁,hw₂,hs₁,hs₂,?_⟩
  intro ε hε Aker J
  obtain ⟨Cprofile,Kpush,hC,hKp,he⟩ := actual_first_original_subset_physical_budget
    ε hε U g₁ g₂ Φ M₀ (fun _=>0) m₁ m₂ 1
    hM (fun _=>le_rfl) hUs hg₁ hg₂ Aker J
  refine ⟨Cprofile,Kpush,hC,hKp,?_⟩
  intro ι _ p hp _ hg hinj hcop hc hpr pool Q labels β cutoff Ψ m mark Γ Ysource Y hΨ hΓ hY hsf hn hβ
    k l gate hcutoff T₁ T₂ K theta L hT₁ hT₂ hK hL Benergy Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hB hZ hscale hLe hleft hright
  let source := refinedSource p pool Q labels β cutoff Ysource k gate
  have hgates := hwin p hp hg pool Q labels Ysource (coefficient p hg Ψ m mark true)
    (coefficient p hg Ψ m mark false) k l T₁ T₂ (fun _=>0) 1 1 (-theta) theta
    hT₁ hT₂ (by intro i;simp) le_rfl le_rfl le_rfl le_rfl
  have hb := he p hp hg hinj hcop hc hpr pool (refinedOuter p pool Q k gate) (fun x=>x.1) (fun x=>x.2.1)
    Ψ Ψ m m (divisorElement p) (fun x=>mark x.1.rightExponent) (fun x=>mark x.1.leftExponent)
    (fun _=>commonSelector p (fun _=>1) l) (fun _=>labels) (firstOriginalWeight p β cutoff) (Γ^2) Y
    hΨ hΨ (sq_nonneg _) hY (fun _ _=>hsf) (fun _ _=>hn)
    (fun x hx=>original_weight_bound p pool Q labels β cutoff Γ Y hΓ hβ x (original_outer_cell_subset p pool Q k (Finset.mem_filter.mp hx).1))
    w₁ w₂ (fun _=>0) 1 1 (-theta) theta (leftNorm p) (rightNorm p) (commonNorm p) (activeNorm p)
    K L hK (rawScales k l T₁ T₂) (rawScales_pos k l T₁ T₂ hT₁ hT₂)
    source (refined_source_radius p hp pool Q labels β cutoff Ysource Y k gate hn hcutoff)
    (fun x hx=>original_source_positive p hp pool Q labels Ysource x (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1)
    (by intro i;simp) le_rfl le_rfl le_rfl le_rfl hL
    (fun x hx=>hgates.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.1 x (Finset.mem_filter.mp hx).1)
    (fun x hx=>hgates.2.2 x (Finset.mem_filter.mp hx).1)
    Benergy hB Z M r ell V delta aa₁ aa₂ bb rr tq hh eta hZ hscale hLe
    (by simpa [refinedChildEnergy,rawScales] using hleft)
    (by simpa [refinedChildEnergy,rawScales] using hright)
  unfold refinedCellRows
  unfold InverseMomentFirstOriginalProfile.coefficient InverseMomentFirstOriginalProfile.weight
  simpa [source,rawScales] using hb

end InverseMomentFirstOriginalProfile
end

namespace InverseMoment
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment

lemma second_tail_fixed_cap (Y L cap B P H : ℝ) (order : ℕ)
    (hY : 0<Y) (hL : 0≤ L) (hc : 1≤ cap) (_hB : 0≤ B) (hP : 0≤ P) (hH : 0≤ H)
    (hy : Y≤ cap) (hyi : Y⁻¹≤ cap) (hl : L≤ cap) :
    ((1+diagonalControl sieveCutoff)*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+H)^order))≤
      (4*(1+diagonalControl sieveCutoff)^4)*B^2*P*cap^13/(1+H)^order := by
  have hdc := diagonalControl_nonneg sieveCutoff
  have hc0 : 0≤ cap := zero_le_one.trans hc
  have hscale : 1+L^3/Y≤2*cap^4 := by
    calc
      _ ≤ 1+cap^3*cap := by rw [div_eq_mul_inv]; gcongr
      _ ≤ _ := by have hh : 1≤ cap^4 := one_le_pow₀ hc; nlinarith
  calc
    _ = ((1+diagonalControl sieveCutoff)*L)^4*B^2*Y*P*(1+L^3/Y)^2/(1+H)^order := by ring
    _ ≤ ((1+diagonalControl sieveCutoff)*cap)^4*B^2*cap*P*(2*cap^4)^2/(1+H)^order := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      gcongr
    _ = _ := by ring

theorem choose_second_tail_order (Lcap tau saving : ℝ) (hL : 0≤ Lcap) (htau : 0<tau) :
    ∃ order : ℕ,∀ Z Y L B P : ℝ,1≤ Z → 0<Y → 0≤ L → 0≤ B → 0≤ P →
      Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → L≤ Z^Lcap →
      ((1+diagonalControl sieveCutoff)*L)^4*(B^2*(Y*P*(1+L^3/Y)^2/(1+Z^tau)^order))≤
        (4*(1+diagonalControl sieveCutoff)^4)*B^2*P*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨order,ho⟩ := exists_nat_gt ((13*Lcap+saving)/tau)
  refine ⟨order,?_⟩
  intro Z Y L B P hZ hY hL0 hB hP hy hyi hl
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hb := second_tail_fixed_cap Y L (Z^Lcap) B P (Z^tau) order hY hL0
    (Real.one_le_rpow hZ hL) hB hP (Real.rpow_pos_of_pos hz _).le hy hyi hl
  have hdecay : (Z^Lcap)^13/(1+Z^tau)^order≤ Z^(-saving) := by
    calc
      _ ≤ (Z^Lcap)^13/(Z^tau)^order := div_le_div_of_nonneg_left (by positivity)
        (by positivity) (pow_le_pow_left₀ (by positivity) (by linarith) order)
      _ = Z^(13*Lcap-tau*(order:ℝ)) := by
        rw [←Real.rpow_mul_natCast hz.le,←Real.rpow_mul_natCast hz.le,←Real.rpow_sub hz]
        congr 1
        norm_num
        ring
      _ ≤ _ := by
        apply Real.rpow_le_rpow_of_exponent_le hZ
        have hh := (div_lt_iff₀ htau).mp ho
        nlinarith
  apply hb.trans
  calc
    _ = ((4*(1+diagonalControl sieveCutoff)^4)*B^2*P)*((Z^Lcap)^13/(1+Z^tau)^order) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hdecay (by positivity)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem full_second_rapid_correlated_tail (Lcap tau saving : ℝ)
    (hLcap : 0≤ Lcap) (htau : 0<tau) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg : ∀i,lambda∉Ideal.span {p i})
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F : Finset ι) (Ψ : O→*ℂ), (∀ a,‖Ψ a‖≤1) →
      ∀ (m c d : O),d≠0 → ∀ (Hcol : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ))
      (Z B Y L : ℝ) (R : Finset ι→Finset ι→ℝ),
      1≤ Z → 0≤ B → 0<Y → 1≤ L → Y≤ Z^Lcap → Y⁻¹≤ Z^Lcap → L≤ Z^Lcap →
      (∀ U,‖Hcol U‖≤ B) → (∀ U,Hcol U≠0 → primeProductNorm p U≤ L) →
      (∀ G∈F.powerset,∀ E : G.powerset,correlatedSecondRadius p d G E.val L Y (Z^tau)≤ R G E.val) →
      ‖secondSourceTail p hp hg F Ψ m c d Hcol W Y
        (fun G E=>childFrequencyBall (d*(∏ i ∈ E,p i)) (R G E))‖≤
      C*B^2*(s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)*Z^(-saving) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨order,horder⟩ := choose_second_tail_order Lcap tau saving hLcap htau
  obtain ⟨s,Ct,hCt,htail⟩ := full_second_correlated_tail order
  refine ⟨s,(4*(1+diagonalControl sieveCutoff)^4)*Ct,by positivity,?_⟩
  intro ι _ p hp _ hg hinj hc F Ψ hΨ m c d hd Hcol W Z B Y L R hZ hB hY hL hy hyi hl hcol hsupp hR
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have he := htail p hp hg hinj hc F Ψ hΨ m c d hd Hcol W B Y (Z^tau) L R
    hB hY (Real.rpow_pos_of_pos hz _).le hL hcol hsupp hR
  apply he.trans
  have hh := horder Z Y L B (Ct*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    hZ hY (zero_le_one.trans hL) hB (mul_nonneg hCt.le (apply_nonneg _ _)) hy hyi hl
  convert hh using 1 <;> first | rfl | ring

end
end InverseMoment

noncomputable section
namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem first_selector_weighted_mass {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (pool A:Finset ι) (selector:Finset ι→ℂ) (E T S ε:ℝ)
    (hE:0≤ E) (hT:0<T) (hS:0≤ S) (hε:0≤ε)
    (hA:primeProductNorm p A≤ E)
    (hselector:∀D∈pool.powerset,‖selector D‖≤ S)
    (hsupport:∀D∈pool.powerset,selector D≠0→primeProductNorm p D≤ T) :
    (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)≤
      (1+diagonalControl sieveCutoff)*T*S*(E*T)^ε := by
  have hfilter:(∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^ε)=
      ∑D∈boundedPrimeSupports p pool T,‖selector D‖*(primeProductNorm p (A∪D))^ε:=by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro D hD hnot
    have hz:selector D=0:=by
      by_contra h
      exact hnot (Finset.mem_filter.mpr ⟨hD,hsupport D hD h⟩)
    simp [hz]
  rw [hfilter]
  calc
    _≤∑D∈boundedPrimeSupports p pool T,S*(E*T)^ε:=by
      apply Finset.sum_le_sum
      intro D hD
      have hnorm:primeProductNorm p (A∪D)≤ E*T:=
        (primeProductNorm_union_le_mul p hp A D).trans
          (mul_le_mul hA (Finset.mem_filter.mp hD).2 (primeProductNorm_pos p hp D).le hE)
      exact mul_le_mul (hselector D (Finset.mem_filter.mp hD).1)
        (Real.rpow_le_rpow (primeProductNorm_pos p hp _).le hnorm hε)
        (Real.rpow_nonneg (primeProductNorm_pos p hp _).le _) hS
    _= ((boundedPrimeSupports p pool T).card:ℝ)*S*(E*T)^ε:=by simp;ring
    _≤_:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj pool T hT) hS)
      (Real.rpow_nonneg (mul_nonneg hE hT.le) _)

theorem first_whole_extracted_norm {ι:Type*} [DecidableEq ι]
    (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (b:CubeCoordinates ι) (hb:b.Admissible) (C extra:Finset ι) (he:extra⊆b.support)
    (negative:Bool) (B:ℝ) (hB:0≤ B)
    (h₁:‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤ B)
    (h₂:‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤ B) :
    primeProductNorm p (extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))≤
      B^2*primeProductNorm p C := by
  have hbits:(if negative then b.rightDivisor else b.leftDivisor)⊆b.support:=by
    cases negative
    · exact hb.1
    · exact hb.2
  have hs:extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)⊆b.support∪C:=by
    exact Finset.union_subset (he.trans Finset.subset_union_left)
      (Finset.union_subset_union hbits (Finset.Subset.refl C))
  apply (primeProductNorm_mono p hp hs).trans
  apply (primeProductNorm_union_le_mul p hp b.support C).trans
  exact mul_le_mul_of_nonneg_right (cubeCoordinates_radical_bound p hp b B hB h₁ h₂)
    (primeProductNorm_pos p hp C).le

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem whole_assigned_source_original
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→InverseInitialFibers.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    (∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y))=
    ∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      H (parent p (fixedPoint cube C E old D)) := by
  rw [activeParents,←wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj,
    sum_activeFixedSource]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro D hD
  by_cases hs:selector D≠0
  · rw [if_pos hs]
    simp only [fixedPoint,wholeExtractedSupport,extractedSupport,Finset.union_assoc]
  · rw [if_neg hs,priorityOuter_zero p hg cube negative Ψ m selector ray core D (not_ne_iff.mp hs)]
    simp

theorem whole_assigned_source_norm
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→InverseInitialFibers.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (H:SecondParentSource ι Jo→ℂ):
    ‖∑y∈activeParents p extra pool cube C E old selector negative assigned lists,
      coefficient p assigned a (fun x=>(priorityOuter p hg cube negative Ψ m selector ray core x.quotientSupport:ℂ)) y *
        H (forgetAppended y)‖≤
    ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖H (parent p (fixedPoint cube C E old D))‖ := by
  rw [whole_assigned_source_original p hg hinj]
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro D hD
  rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
    Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

def priorityZeroParent (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  truncatedSecondZero p hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

def priorityTailParent (hp:∀i,p i≠0) (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis) (slots assigned:Finset σ)
    (lists:σ→Finset ι) (a:σ→ι→ℂ) (V:𝓢(ℝ,ℂ)) (X Y:ℝ)
    (R:Finset ι→Finset ι→ℝ) (y:SecondParentSource ι Jo):ℂ:=
  secondSourceTail p hp hg pool Ψ (secondParentPuncture p m y)
    (secondParentLabel p y) (secondParentDivisor p y)
    (InversePrincipalEnergy.markedRadial p (slots\assigned)
      (residualLists p negative (fun i=>lists i\extra y.cube) y) a ∅ V X)
    rowMajorant Y (secondVariableCutoff p y R)

theorem whole_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→InverseInitialFibers.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D)=
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D)))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))) := by
  intro V Ψ₀ parents source
  rw [whole_priority_complex_slice p hp hg hcop hinj hc hpr pool cube C E extra old negative Ψ m
    slots assigned lists a selector om lo hi hlo hs X t Y hX hY ray core R (fun _ _=>())]
  rw [fullPhysical_unified p hg hp hcop hinj extra pool]
  dsimp only
  rw [←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    ←whole_assigned_source_original p hg hinj extra pool cube C E old selector negative Ψ m ray core assigned lists a
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem whole_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (cube:CubeCoordinates ι) (C E:Finset ι) (old:Fin Jo→InverseInitialFibers.PrimeIdeal)
    (selector:Finset ι→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=activeParents p extra pool cube C E old selector negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
      (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*
      wholePriorityPoisson p hp hg hinj pool cube C E (extra cube) negative Ψ m slots assigned lists a om X t Y ray core D‖≤
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      sourceWeight p hg cube negative Ψ m selector ray core assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
      ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p (fixedPoint cube C E old D))‖) := by
  intro V Ψ₀ parents source
  rw [whole_priority_signed_branches p hg hp hcop hinj hc hpr extra pool cube C E old selector negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Finset ι→ℂ):
      ‖∑D∈pool.powerset,(priorityOuter p hg cube negative Ψ m selector ray core D:ℂ)*
        (‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2:ℝ)*H D‖≤
      ∑D∈pool.powerset,priorityOuter p hg cube negative Ψ m selector ray core D*
        ‖primeMark assigned lists a ((extra cube∪((if negative then cube.rightDivisor else cube.leftDivisor)∪C))∪D)‖^2*‖H D‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro D hD
    rw [norm_mul,norm_mul,Complex.norm_real,Complex.norm_real,
      Real.norm_of_nonneg (by unfold priorityOuter;positivity),Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem global_priority_signed_branches
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x))=
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x))+
    (∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x)+
    (∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)) := by
  intro V Ψ₀ parents source
  rw [global_priority_physical_source p hp hcop hg hinj hc hpr extra pool original negative Ψ m ray core w
    slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R),
    wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj original negative assigned lists a
      (globalPriorityOuter p hg negative Ψ m ray core w)
      (priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R)]
  rfl

theorem global_priority_slice_bound
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖) := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (hn _))

end InverseMoment

end

noncomputable section
namespace InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

abbrev Core (ι : Type*) := CubeCoordinates ι×Finset ι×Finset ι

def core {ι : Type*} {Jo : ℕ} (x : Source ι Jo) : Core ι :=
  (x.cube,x.firstCommon,x.quotientSupport)

def divisorTarget {ι : Type*} [DecidableEq ι] (p : ι→O) (q : Core ι) : Ideal O :=
  sourceIdeal p q.1.support*sourceIdeal p q.2.1*sourceIdeal p q.2.2

lemma divisorTarget_ne_zero {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) : divisorTarget p q≠0 :=
  mul_ne_zero (mul_ne_zero (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _))
    (sourceIdeal_ne_zero p hp _)

lemma firstDivisor_dvd_target {ι : Type*} [DecidableEq ι] (p : ι→O)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ} (x : Source ι Jo) (hx : SourceValid p x) :
    sourceIdeal p x.firstDivisor∣divisorTarget p (core x) := by
  have hd := sourceIdeal_dvd p _ _ hx.first_divisor
  rw [sourceIdeal_union p _ _ hx.common_disjoint] at hd
  apply hd.trans
  change sourceIdeal p x.firstCommon*sourceIdeal p x.cube.support∣
    sourceIdeal p x.cube.support*sourceIdeal p x.firstCommon*sourceIdeal p x.quotientSupport
  rw [mul_comm (sourceIdeal p x.firstCommon)]
  exact dvd_mul_right _ _

theorem core_fiber_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i})) {Jo : ℕ}
    (S : Finset (Source ι Jo)) (q : Core ι)
    (hS : ∀x∈S,SourceValid p x) (hq : ∀x∈S,core x=q) :
    S.card≤(idealDivisors (divisorTarget p q)).card^(Jo+1) := by
  let D := idealDivisors (divisorTarget p q)
  have hD := divisorTarget_ne_zero p hp q
  let encode (x : S) : D×(Fin Jo→D) :=
    (⟨sourceIdeal p x.val.firstDivisor,(mem_idealDivisors hD).mpr (by
      simpa only [hq x.val x.property] using firstDivisor_dvd_target p x.val (hS x.val x.property))⟩,
      fun i=>⟨(x.val.oldAssigned i).val,(mem_idealDivisors hD).mpr (by
        have hh := (hS x.val x.property).old_support i
        change (x.val.oldAssigned i).val∣divisorTarget p (core x.val) at hh
        simpa only [hq x.val x.property] using hh)⟩)
  have hi : Function.Injective encode := by
    intro x y he
    have hk := (hq x.val x.property).trans (hq y.val y.property).symm
    have hd : x.val.firstDivisor=y.val.firstDivisor :=
      sourceIdeal_injective p hinj (congrArg (fun z=>z.1.val) he)
    have ho : x.val.oldAssigned=y.val.oldAssigned := by
      funext i
      apply Subtype.ext
      exact congrArg (fun z=>(z.2 i).val) he
    apply Subtype.ext
    exact Source.ext (congrArg Prod.fst hk) (congrArg (fun q=>q.2.1) hk) hd
      (congrArg (fun q=>q.2.2) hk) ho
  have hh := Fintype.card_le_of_injective encode hi
  simpa only [Fintype.card_coe,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,D,pow_succ,mul_comm] using hh

theorem core_fiber_small_power (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))(q : Core ι),
    (∀x∈S,SourceValid p x) → (∀x∈S,core x=q) →
    (S.card:ℝ)≤ C*(Ideal.absNorm (divisorTarget p q):ℝ)^eps := by
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power
    (eps/(Jmax+1)) (by positivity)
  refine ⟨D^(Jmax+1),by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S q hS hq
  have h0 := divisorTarget_ne_zero p hp q
  have hcard : S.card≤(idealDivisors (divisorTarget p q)).card^(Jmax+1) :=
    (core_fiber_card p hp hinj S q hS hq).trans
      (Nat.pow_le_pow_right (InverseInitialFibers.divisor_card_pos _ h0) (Nat.add_le_add_right hJo 1))
  have hb := pow_le_pow_left₀ (Nat.cast_nonneg _) (hdiv _ h0) (Jmax+1)
  apply (show (S.card:ℝ)≤((idealDivisors (divisorTarget p q)).card:ℝ)^(Jmax+1) by exact_mod_cast hcard).trans
  apply hb.trans_eq
  rw [mul_pow]
  congr 1
  rw [←Real.rpow_natCast,←Real.rpow_mul (Nat.cast_nonneg _)]
  congr 1
  push_cast
  field_simp

lemma divisorTarget_norm_bound {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] (q : Core ι) (B V T : ℝ)
    (hB : 0≤ B) (hV : 0≤ V) (_hT : 0≤ T)
    (hb₁ : ‖ringComplex (primeProduct p q.1.support q.1.leftExponent)‖^2≤ B)
    (hb₂ : ‖ringComplex (primeProduct p q.1.support q.1.rightExponent)‖^2≤ B)
    (hC : primeProductNorm p q.2.1≤ V) (ht : primeProductNorm p q.2.2≤ T) :
    (Ideal.absNorm (divisorTarget p q):ℝ)≤ B^2*V*T := by
  unfold divisorTarget
  simp only [map_mul,Nat.cast_mul,sourceIdeal,←ringComplex_norm_sq_eq_absNorm_span]
  change primeProductNorm p q.1.support*primeProductNorm p q.2.1*primeProductNorm p q.2.2≤_
  exact mul_le_mul (mul_le_mul (cubeCoordinates_radical_bound p hp q.1 B hB hb₁ hb₂)
    hC (primeProductNorm_pos p hp _).le (sq_nonneg _)) ht (primeProductNorm_pos p hp _).le
    (mul_nonneg (sq_nonneg _) hV)

end InverseMomentGlobalPrincipalMass
end

noncomputable section
namespace InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

lemma support_family_card {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset (Finset ι)) (U : ℝ) (hU : 0<U) (hS : ∀A∈S,primeProductNorm p A≤ U) :
    (S.card:ℝ)≤(1+diagonalControl sieveCutoff)*U := by
  have hdc := diagonalControl_nonneg sieveCutoff
  by_cases h1 : 1≤ U
  · have hh := SchwartzPlanePoisson.finite_ideal_card_bound (S.image (sourceIdeal p)) U h1
      (by
        intro I hI
        obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hI
        simpa only [sourceIdeal,←ringComplex_norm_sq_eq_absNorm_span,primeProductNorm] using hS A hA)
    simpa only [Finset.card_image_of_injective S (sourceIdeal_injective p hinj)] using hh.trans (mul_le_mul_of_nonneg_right (show diagonalControl sieveCutoff ≤ 1+diagonalControl sieveCutoff by linarith) hU.le)

  · have he : S=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro A hA
      exact h1 ((primeProductNorm_ge_one p hp A).trans (hS A hA))
    rw [he]
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

theorem original_source_card (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))(B H V T : ℝ),
    1≤ B → 0≤ H → 0<V → 0<T → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ B) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ B) →
    (∀x∈S,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤ V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤ T) →
    (S.card:ℝ)≤ C*B^(1+eps)*H*V*T*(B^2*V*T)^eps := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨Cf,hCf,hfiber⟩ := core_fiber_small_power Jmax eps heps
  obtain ⟨Cb,hCb,hcube⟩ := cube_coordinates_parity_count eps heps
  refine ⟨Cf*Cb*(1+diagonalControl sieveCutoff)^2,by positivity,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T hB hH hV hT hS hleft hright hactive hcommon hquot
  let Q := S.image core
  let bs := S.image Source.cube
  let cs := S.image Source.firstCommon
  let ts := S.image Source.quotientSupport
  have hbcount : (bs.card:ℝ)≤ Cb*B^(1+eps)*H := hcube p hp hinj bs B H hB hH
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact (hS x hx).admissible)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hleft x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hright x hx)
    (by intro b hb;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hb;exact hactive x hx)
  have hccount : (cs.card:ℝ)≤(1+diagonalControl sieveCutoff)*V := support_family_card p hp hinj cs V hV
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hcommon x hx)
  have htcount : (ts.card:ℝ)≤(1+diagonalControl sieveCutoff)*T := support_family_card p hp hinj ts T hT
    (by intro A hA;obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hA;exact hquot x hx)
  have hsub : Q⊆bs×ˢ(cs×ˢts) := by
    intro q hq
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,
      Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hx,Finset.mem_image_of_mem _ hx⟩⟩
  have hQcard : (Q.card:ℝ)≤(Cb*B^(1+eps)*H)*((1+diagonalControl sieveCutoff)*V)*((1+diagonalControl sieveCutoff)*T) := by
    have hh : (Q.card:ℝ)≤(bs.card:ℝ)*((cs.card:ℝ)*(ts.card:ℝ)) := by
      exact_mod_cast (Finset.card_le_card hsub).trans_eq (by simp only [Finset.card_product])
    apply hh.trans
    calc
      _ ≤ (Cb*B^(1+eps)*H)*(((1+diagonalControl sieveCutoff)*V)*((1+diagonalControl sieveCutoff)*T)) := by gcongr
      _ = _ := by ring
  have hF (q : Core ι) (hq : q∈Q) :
      ((S.filter (fun x=>core x=q)).card:ℝ)≤ Cf*(B^2*V*T)^eps := by
    have hf := hfiber p hp hinj Jo hJo (S.filter (fun x=>core x=q)) q
      (fun x hx=>hS x (Finset.mem_filter.mp hx).1) (fun x hx=>(Finset.mem_filter.mp hx).2)
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hq
    apply hf.trans
    apply mul_le_mul_of_nonneg_left _ hCf.le
    exact Real.rpow_le_rpow (Nat.cast_nonneg _)
      (divisorTarget_norm_bound p hp (core x) B V T (zero_le_one.trans hB) hV.le hT.le
        (hleft x hx) (hright x hx) (hcommon x hx) (hquot x hx)) heps.le
  have he : (S.card:ℝ)=∑q∈Q,((S.filter (fun x=>core x=q)).card:ℝ) := by
    calc
      _ = ∑_x∈S,(1:ℝ) := by simp
      _ = ∑q∈Q,∑_x∈S.filter (fun x=>core x=q),(1:ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun x hx=>Finset.mem_image_of_mem core hx) _).symm
      _ = _ := by simp
  rw [he]
  calc
    _ ≤ ∑_q∈Q,Cf*(B^2*V*T)^eps := Finset.sum_le_sum hF
    _ = (Q.card:ℝ)*(Cf*(B^2*V*T)^eps) := by simp
    _ ≤ ((Cb*B^(1+eps)*H)*((1+diagonalControl sieveCutoff)*V)*((1+diagonalControl sieveCutoff)*T))*(Cf*(B^2*V*T)^eps) :=
      mul_le_mul_of_nonneg_right hQcard (by positivity)
    _ = _ := by ring

end InverseMomentGlobalPrincipalMass
end

noncomputable section
namespace InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def principalSupport {ι : Type*} [DecidableEq ι] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo) : Finset ι :=
  (extra x.cube∪((if negative then x.cube.rightDivisor else x.cube.leftDivisor)∪x.firstCommon))∪x.quotientSupport

lemma principalSupport_norm {ι : Type*} [DecidableEq ι] (p : ι→O) (hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal] {Jo : ℕ}
    (extra : CubeCoordinates ι→Finset ι) (negative : Bool) (x : Source ι Jo)
    (hx : SourceValid p x) (hextra : extra x.cube⊆x.cube.support)
    (B V T : ℝ) (hB : 0≤ B) (hV : 0≤ V)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ B)
    (hC : primeProductNorm p x.firstCommon≤ V) (ht : primeProductNorm p x.quotientSupport≤ T) :
    primeProductNorm p (principalSupport extra negative x)≤ B^2*V*T := by
  have hh := first_whole_extracted_norm p hp x.cube hx.admissible x.firstCommon (extra x.cube)
    hextra negative B hB hb₁ hb₂
  unfold principalSupport
  apply (primeProductNorm_union_le_mul p hp _ _).trans
  exact mul_le_mul (hh.trans (mul_le_mul_of_nonneg_left hC (sq_nonneg _))) ht
    (primeProductNorm_pos p hp _).le (mul_nonneg (sq_nonneg _) hV)

theorem original_weighted_mass (Jmax : ℕ) (eps : ℝ) (heps : 0<eps) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))(B H V T a : ℝ),
    1≤ B → 0≤ H → 0<V → 0<T → 0≤ a → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ B) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ B) →
    (∀x∈S,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ H) →
    (∀x∈S,primeProductNorm p x.firstCommon≤ V) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤ T) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*B^(1+eps)*H*V*T*(B^2*V*T)^(eps+a) := by
  obtain ⟨C,hC,hcount⟩ := original_source_card Jmax eps heps
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S B H V T a hB hH hV hT ha hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hcard := hcount p hp hinj Jo hJo S B H V T hB hH hV hT hS hb₁ hb₂ hactive hcommon hquot
  have hBp : 0<B := zero_lt_one.trans_le hB
  calc
    _ ≤ ∑_x∈S,(B^2*V*T)^a := Finset.sum_le_sum (fun x hx=>
      Real.rpow_le_rpow (primeProductNorm_pos p hp _).le
        (principalSupport_norm p hp extra negative x (hS x hx) (hextra x hx) B V T hBp.le hV.le
          (hb₁ x hx) (hb₂ x hx) (hcommon x hx) (hquot x hx)) ha)
    _ = (S.card:ℝ)*(B^2*V*T)^a := by simp
    _ ≤ (C*B^(1+eps)*H*V*T*(B^2*V*T)^eps)*(B^2*V*T)^a :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by rw [mul_assoc,←Real.rpow_add (by positivity : 0<B^2*V*T)]

lemma weighted_mass_power (Z ell R Bfirst t eta eps a : ℝ) (hZ : 0<Z) :
    (Z^(ell+eta))^(1+eps)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(eps+a)=
    Z^(ell+R/2+Bfirst+t+7*eta/2+eps*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
  rw [←Real.rpow_mul hZ.le,←Real.rpow_mul_natCast hZ.le]
  repeat rw [←Real.rpow_add hZ]
  rw [←Real.rpow_mul hZ.le,←Real.rpow_add hZ]
  congr 1
  norm_num
  ring

end InverseMomentGlobalPrincipalMass
end

noncomputable section
namespace InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

lemma active_norm_of_square {ι : Type*} [DecidableEq ι] (p : ι→O)
    (A : Finset ι) (Z R eta : ℝ) (hZ : 0<Z)
    (hA : primeProductNorm p A≤ Z^(R+eta)) :
    ‖ringComplex (∏i∈A,p i)‖≤ Z^((R+eta)/2) := by
  apply (sq_le_sq₀ (norm_nonneg _) (Real.rpow_nonneg hZ.le _)).mp
  have hh : (Z^((R+eta)/2))^2=Z^(R+eta) := by
    rw [←Real.rpow_mul_natCast hZ.le]
    congr 1
    norm_num
  rw [hh]
  exact hA

theorem original_weighted_source (Jmax : ℕ) (delta : ℝ) (hdelta : 0<delta) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))(Z ell R Bfirst t eta a loss : ℝ),
    1≤ Z → 0≤ ell+eta → 0≤ a →
    7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)≤ loss →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta)) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤ Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤ Z^(Bfirst+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤ Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^a)≤
      C*Z^(ell+R/2+Bfirst+t+loss) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax delta hdelta
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z ell R Bfirst t eta a loss hZ hell ha hloss hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^(ell+eta)) (Z^((R+eta)/2))
    (Z^(Bfirst+eta)) (Z^(t+eta)) a (Real.one_le_rpow hZ hell)
    (Real.rpow_nonneg hZp.le _) (Real.rpow_pos_of_pos hZp _)
    (Real.rpow_pos_of_pos hZp _) ha hS hb₁ hb₂
    (fun x hx=>active_norm_of_square p _ Z R eta hZp (hactive x hx))
    hcommon hquot extra negative hextra
  apply hh.trans
  calc
    _ = C*( (Z^(ell+eta))^(1+delta)*Z^((R+eta)/2)*Z^(Bfirst+eta)*Z^(t+eta)*
      ((Z^(ell+eta))^2*Z^(Bfirst+eta)*Z^(t+eta))^(delta+a)) := by ring
    _ = C*Z^(ell+R/2+Bfirst+t+7*eta/2+delta*(3*ell+Bfirst+t+5*eta)+a*(2*ell+Bfirst+t+4*eta)) := by
      rw [weighted_mass_power Z ell R Bfirst t eta delta a hZp]
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ (by linarith)) hC.le

end InverseMomentGlobalPrincipalMass
end

noncomputable section
namespace InverseMomentGlobalPrincipalMass
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

def physicalPrincipalFactor (Z M r ell V delta A B R j t eta tau eps window : ℝ) : ℝ :=
  (Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
    Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau)*
    (Z^(r-A-B-t)*Real.exp window)^(1+eps)

lemma principal_nominal_identity (M r ell V delta A B R j t : ℝ) :
    firstKappa M r ell V delta A B R+firstPhysicalHeight M r ell V delta B j+
      (r-A-B-t)+(ell+R/2+B+t)=r+3*ell+V-B-j := by
  unfold firstKappa firstPhysicalHeight
  ring

lemma physical_principal_exact (Z M r ell V delta A B R j t eta tau eps window loss : ℝ)
    (hZ : 0<Z) :
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)=
    Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss) := by
  have he : Real.exp ((9/2:ℝ)*(eta*Real.log Z))=Z^((9/2:ℝ)*eta) := by
    rw [Real.rpow_def_of_pos hZ]
    congr 1
    ring
  have hw : (Real.exp window)^(1+eps)=Real.exp (window*(1+eps)) := by
    rw [Real.rpow_def_of_pos (Real.exp_pos _),Real.log_exp]
  unfold physicalPrincipalFactor
  rw [he,Real.mul_rpow (Real.rpow_nonneg hZ.le _) (Real.exp_pos _).le,
    ←Real.rpow_mul hZ.le,hw]
  have hx : r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss=
    firstKappa M r ell V delta A B R+(9/2:ℝ)*eta+
    (firstPhysicalHeight M r ell V delta B j+12*eta+tau)+
    (r-A-B-t)*(1+eps)+(ell+R/2+B+t+loss) := by
    unfold firstKappa firstPhysicalHeight
    ring
  rw [hx]
  simp only [Real.rpow_add hZ]
  ring

theorem original_physical_weighted_source (Jmax : ℕ) (dsmall : ℝ) (hdsmall : 0<dsmall) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))
    (Z M r ell V delta A B R j t eta tau eps window pi : ℝ),
    1≤ Z → 0≤ ell+eta → 0≤ eps → 0≤ B → 0≤ j →
    eps*(r-A-B-t)+7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)≤ pi+eta/2 →
    (∀x∈S,SourceValid p x) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^(ell+eta)) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^(ell+eta)) →
    (∀x∈S,primeProductNorm p (cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)≤ Z^(R+eta)) →
    (∀x∈S,primeProductNorm p x.firstCommon≤ Z^(B+eta)) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤ Z^(t+eta)) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (∑x∈S,(primeProductNorm p (principalSupport extra negative x))^(2*eps))≤
      C*Real.exp (window*(1+eps))*Z^(r+3*ell+V+17*eta+tau+pi) := by
  obtain ⟨C,hC,hsource⟩ := original_weighted_source Jmax dsmall hdsmall
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z M r ell V delta A B R j t eta tau eps window pi hZ hell heps hB hj hcost hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  let loss := 7*eta/2+dsmall*(3*ell+B+t+5*eta)+2*eps*(2*ell+B+t+4*eta)
  have hZp : 0<Z := zero_lt_one.trans_le hZ
  have hh := hsource p hp hinj Jo hJo S Z ell R B t eta (2*eps) loss hZ hell
    (by positivity) (le_refl _) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hP : 0≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window := by
    unfold physicalPrincipalFactor
    positivity
  calc
    _ ≤ physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      (C*Z^(ell+R/2+B+t+loss)) := mul_le_mul_of_nonneg_left hh hP
    _ = C*(physicalPrincipalFactor Z M r ell V delta A B R j t eta tau eps window*
      Z^(ell+R/2+B+t+loss)) := by ring
    _ = C*(Real.exp (window*(1+eps))*
      Z^(r+3*ell+V-B-j+(33/2:ℝ)*eta+tau+eps*(r-A-B-t)+loss)) := by
      rw [physical_principal_exact Z M r ell V delta A B R j t eta tau eps window loss hZp]
    _ ≤ _ := by
      rw [←mul_assoc]
      apply mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hZ _) (by positivity)
      dsimp [loss]
      linarith

end InverseMomentGlobalPrincipalMass
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseFirstPriorityParents InverseMomentWholePriorityParents InverseWholePriorityRetainedSource
open InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem global_priority_weighted_branch (ε:ℝ)(hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*}[DecidableEq ι][DecidableEq σ]
      (p:ι→O)(_hp:∀i,p i≠0)[∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      {Jo:ℕ}(original:Finset (Source ι Jo))(extra:CubeCoordinates ι→Finset ι)
      (negative:Bool)(Ψ:O→*ℂ)(m:O)(w:Source ι Jo→ℂ)
      (slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)(B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists→(∀i∈slots,∀k∈lists i,‖a i k‖≤1)→
      (∀u,‖Ψ u‖≤1)→(∀x∈original,‖w x‖≤1)→0≤ B→
      ∀U:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→Source ι Jo→ℝ,
      (∀r core J,J∈slots.powerset→∀x∈original,0≤ U r core J x)→
      (∀r core J,J∈slots.powerset→∀x∈original,U r core J x≤ B)→
      firstCoreMassBound*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,‖globalPriorityOuter p hg negative Ψ m r core w x‖*
          ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*U r core J x≤
      Cb*(4:ℝ)^slots.card*B*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  let Cr:ℝ:=Fintype.card (RayCharacter×RayCharacter)
  let Cc:ℝ:=Fintype.card FirstCoreIndex
  refine ⟨max (firstCoreMassBound*Cr*Cc*coefficientBound*Cm^2) 1,
    zero_lt_one.trans_le (le_max_right _ _),?_⟩
  have hmass := firstCoreMassBound_nonneg
  intro ι σ _ _ p hp _ hg hcop Jo original extra negative Ψ m w slots lists a B hslots ha hΨ hw hB U hU0 hU
  let N:=fun x:Source ι Jo=>(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε)
  have hn(x:Source ι Jo):0≤ N x:=Real.rpow_nonneg (primeProductNorm_pos p hp _).le _
  have hm(J:Finset σ)(hJ:J∈slots.powerset)(x:Source ι Jo):
      ‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2≤ Cm^2*N x:=by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij)
      (fun i hi=>ha i (hj hi)) (wholeExtractedSupport (fun x=>extra x.cube) negative x)
    have he:((primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^ε)^2=N x:=by
      dsimp [N]
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    exact (pow_le_pow_left₀ (norm_nonneg _) hh 2).trans_eq (by rw [mul_pow,he])
  have hw'(r:RayCharacter×RayCharacter)(core:FirstCoreIndex)(x:Source ι Jo)(hx:x∈original):
      ‖globalPriorityOuter p hg negative Ψ m r core w x‖≤ coefficientBound:=by
    rw [globalPriorityOuter,norm_mul]
    have ht:=priorityOuter_norm p hg x.cube negative Ψ m (fun _=>1) r core x.quotientSupport (by simp) (hΨ _)
    exact (mul_le_mul (hw x hx) ht (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  calc
    _≤firstCoreMassBound*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
        ∑x∈original,coefficientBound*(Cm^2*N x)*B:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro core hc
      apply Finset.sum_le_sum
      intro J hJ
      apply Finset.sum_le_sum
      intro x hx
      exact mul_le_mul (mul_le_mul (hw' r core x hx) (hm J hJ x) (sq_nonneg _) coefficientBound_pos.le)
        (hU r core J hJ x hx) (hU0 r core J hJ x hx) (mul_nonneg coefficientBound_pos.le (mul_nonneg (sq_nonneg Cm) (hn x)))
    _= (firstCoreMassBound*Cr*Cc*coefficientBound*Cm^2)*(4:ℝ)^slots.card*B*
        ∑x∈original,(primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε):=by
      have hsum:(∑x∈original,coefficientBound*(Cm^2*N x)*B)=
          coefficientBound*Cm^2*B*∑x∈original,N x:=by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intros;ring
      rw [hsum]
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [←he]
      dsimp only [Cr,Cc,N]
      ring
    _≤_ := by
      have hsum : 0 ≤ ∑ x ∈ original,
          (primeProductNorm p (wholeExtractedSupport (fun x=>extra x.cube) negative x))^(2*ε) :=
        Finset.sum_nonneg (fun x _ => hn x)
      gcongr
      exact le_max_left _ _
end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O

theorem whole_priority_weighted_branch (ε:ℝ) (hε:0<ε):
    ∃Cb:ℝ,0<Cb ∧ ∀{ι σ:Type*} [DecidableEq ι] [DecidableEq σ]
      (p:ι→O) (_hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hg:∀i,lambda∉Ideal.span {p i})
      (_hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (pool:Finset ι) (b:CubeCoordinates ι) (C extra:Finset ι) (negative:Bool)
      (Ψ:O→*ℂ) (m:O) (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
      (selector:Finset ι→ℂ) (B:ℝ),
      (slots:Set σ).PairwiseDisjoint lists → (∀i∈slots,∀k∈lists i,‖a i k‖≤1) →
      (∀u,‖Ψ u‖≤1) → 0≤ B →
      ∀U:(RayCharacter×RayCharacter)→Finset ι→FirstCoreIndex→Finset σ→ℝ,
      (∀r D core J,J∈slots.powerset → 0≤ U r D core J) →
      (∀r D core J,J∈slots.powerset → U r D core J≤ B) →
      firstCoreMassBound*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative Ψ m D core‖*
          ∑J∈slots.powerset,‖primeMark J lists a
            ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D)‖^2*U r D core J ≤
      Cb*(4:ℝ)^slots.card*B*
        (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p
          ((extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C))∪D))^(2*ε)):=by
  obtain ⟨Cm,hCm,hmark⟩:=finite_primeMark_small_power ε hε
  refine ⟨max ((firstCoreMassBound^2*(∑ r : RayCharacter × RayCharacter, ‖crossCoeff r.1 r.2‖))*Cm^2) 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
  have hmass := firstCoreMassBound_nonneg
  intro ι σ _ _ p hp _ hg hcop pool b C extra negative Ψ m slots lists a selector B hslots ha hΨ hB U hU0 hU
  let A:=extra∪((if negative then b.rightDivisor else b.leftDivisor)∪C)
  have hm (J:Finset σ) (hJ:J∈slots.powerset) (D:Finset ι) :
      ‖primeMark J lists a (A∪D)‖^2≤ Cm^2*(primeProductNorm p (A∪D))^(2*ε) := by
    have hj:=Finset.mem_powerset.mp hJ
    have hh:=hmark p hp hcop J lists a (fun i hi j hj' hij=>hslots (hj hi) (hj hj') hij) (fun i hi=>ha i (hj hi)) (A∪D)
    have he:((primeProductNorm p (A∪D))^ε)^2=(primeProductNorm p (A∪D))^(2*ε):=by
      rw [←Real.rpow_natCast,←Real.rpow_mul (primeProductNorm_pos p hp _).le]
      congr 1;ring
    calc
      _≤(Cm*(primeProductNorm p (A∪D))^ε)^2:=pow_le_pow_left₀ (norm_nonneg _) hh 2
      _= _:=by rw [mul_pow,he]
  have hn (D:Finset ι) : 0≤ primeProductNorm p (A∪D):=(primeProductNorm_pos p hp _).le
  calc
    _≤firstCoreMassBound*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑core:FirstCoreIndex,
        ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative Ψ m D core‖*
        ((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B)) := by
      gcongr with r hr D hD core hc
      calc
        _≤∑J∈slots.powerset,Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B := by
          apply Finset.sum_le_sum
          intro J hJ
          exact mul_le_mul (hm J hJ D) (hU r D core J hJ) (hU0 r D core J hJ) (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _))
        _= _:=by simp only [Finset.sum_const,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤firstCoreMassBound*(2:ℝ)^slots.card*∑r:RayCharacter×RayCharacter,∑D∈pool.powerset,
      (‖crossCoeff r.1 r.2‖*‖selector D‖)*
        (firstCoreMassBound*((2:ℝ)^slots.card*(Cm^2*(primeProductNorm p (A∪D))^(2*ε)*B))) := by
      gcongr with r hr D hD
      rw [←Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right (firstCoreOuter_mass p hg b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D (hΨ _)) (mul_nonneg (pow_nonneg (by norm_num) _)
          (mul_nonneg (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hn D) _)) hB))
    _= (firstCoreMassBound^2)*((2:ℝ)^slots.card)^2*Cm^2*B*
      (∑r:RayCharacter×RayCharacter,‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      simp only [Finset.mul_sum,Finset.sum_mul]
      rw [Finset.sum_comm (s:=pool.powerset)]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring
    _≤ (firstCoreMassBound^2)*((2:ℝ)^slots.card)^2*Cm^2*B*(∑ r : RayCharacter × RayCharacter, ‖crossCoeff r.1 r.2‖)*
      (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      apply mul_le_mul_of_nonneg_right
      · apply mul_le_mul_of_nonneg_left
        · exact le_refl _
        · positivity
      · exact Finset.sum_nonneg (fun D hD=>mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (hn D) _))
    _= ((firstCoreMassBound^2*(∑ r : RayCharacter × RayCharacter, ‖crossCoeff r.1 r.2‖))*Cm^2)*(4:ℝ)^slots.card*B*
        (∑D∈pool.powerset,‖selector D‖*(primeProductNorm p (A∪D))^(2*ε)) := by
      have he:((2:ℝ)^slots.card)^2=(4:ℝ)^slots.card:=by rw [←pow_mul,pow_mul'];norm_num
      rw [he]
      dsimp only [A]
      ring
    _≤_ := by
      have hsum : 0 ≤ ∑ D ∈ pool.powerset,
          ‖selector D‖*(primeProductNorm p (A∪D))^(2*ε) :=
        Finset.sum_nonneg (fun D _ => mul_nonneg (norm_nonneg (selector D))
          (Real.rpow_nonneg (hn D) (2*ε)))
      gcongr
      exact le_max_left _ _

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
theorem global_priority_retained_all_rays
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (omega₁ omega₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis) (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:SecondParentSource ι (Jo+(assigned.card+assigned.card))→Finset ι→Finset ι→ℝ)
,
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) cutoff
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    ∀
        (Y:ℝ) (R:BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) →
      (∀ i,|ρ i| ≤ B₀ i) → 0 ≤ L →
      1 < Z → 0 < X → 0 < Y → 0≤ eta → 2≤ Z^eta →
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R (index p x))) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) →
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) →
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) →
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) →
      (∀ a,‖Ψ a‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) →
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels d) →
      Jo+(assigned.card+assigned.card) ≤ 2*K → (slots\assigned).card ≤ K → (slots\assigned).card ≤ K → 0 ≤ A →
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) →
      X=Z^(r-Acol-Bfirst-tcount) → L=eta*Real.log Z →
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) →
      2≤ Z → 1≤ b → b≤ Z^(6*eta) →
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) →
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) →
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6 → ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R d)) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
      ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
        ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖ ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_moving_radius (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C*(∑ z : SecondRayIndex, ‖secondRayCoefficient z‖),Cbin,by positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m ray core slots assigned lists a cutoff source Ψ₀
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
    haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
    ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:= (1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*(1+Cbin*Real.log Z)^4*
    Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  let S:SecondRayIndex→ℂ:=fun z=>(Y:ℂ)*secondRayCoefficient z *
      ∑x∈source,globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a
          (principalWindow om lo hi hlo hsupport negative t) X Y z x
  have hP:0≤ P:=by dsimp [P];positivity
  have hH:0≤ H:=by dsimp [H];positivity
  have hz (z:SecondRayIndex):P*‖S z‖≤ C*A*H*‖secondRayCoefficient z‖:=by
    have h:=he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a cutoff z
      Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass
      (hleft z) (hright z)
    convert h using 1 ; dsimp only [P,S,H] ; ring
  calc
    _≤ P*∑z:SecondRayIndex,‖S z‖:=mul_le_mul_of_nonneg_left (norm_sum_le _ _) hP
    _=∑z:SecondRayIndex,P*‖S z‖:=Finset.mul_sum _ _ _
    _≤∑z:SecondRayIndex,C*A*H*‖secondRayCoefficient z‖:=Finset.sum_le_sum (fun z _=>hz z)
    _=C*A*H*(∑z:SecondRayIndex,‖secondRayCoefficient z‖):=(Finset.mul_sum _ _ _).symm
    _≤ C*A*H*(∑ z : SecondRayIndex, ‖secondRayCoefficient z‖):= le_refl _
    _= _:=by dsimp [H];ring

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseSecondSourceBlocks InverseSecondPrincipalCaller InverseSecondProfileUniform
open CompletedHeight SecondPassIntegration JointLogSeparation
open InverseInitialClippedColumns InverseSecondFibers InverseInitialArithmetic
open InverseWholePriorityRetainedSource RayFourExpansion
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type} [DecidableEq ι] [DecidableEq σ]
def globalPriorityRetainedAggregate
    (p:ι→Eis)[∀i,(Ideal.span {p i}).IsMaximal]
    (hg:∀i,lambda∉Ideal.span {p i})
    (hp:∀i,p i≠0)(hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    {Jo:ℕ}(extra:CubeCoordinates ι→Finset ι)(pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))(w:InverseFirstPriorityParents.Source ι Jo→ℂ)
    (negative:Bool)(Ψ:Eis→*ℂ)(m:Eis)(slots:Finset σ)(lists:σ→Finset ι)(a:σ→ι→ℂ)
    (V:𝓢(ℝ,ℂ))(X Y:ℝ)(R:Finset ι→Finset ι→ℝ):ℝ:=
  firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑J∈slots.powerset,
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z*
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative J lists) (fun _=>R),
        globalPriorityWeight p hg negative Ψ m ray core w J a x*
        wholeRow p hp hcop hg extra pool negative (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core)
          m slots J lists a V X Y z x‖

theorem global_priority_retained_aggregate
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo)
    (hsupport:Function.support om⊆Set.Icc lo hi) (negative:Bool)
    (caps:Fin 4→ℝ) (hcaps:∀i,0≤ caps i) (B₀:Fin 6→ℝ) (hB₀:∀i,0≤ B₀ i) (J K:ℕ) (εmass:ℝ) (hεmass:0<εmass) :
    ∃ (omega₁ omega₂ : 𝓢(ℝ,ℂ)) (loFresh hiFresh : ℝ),
      0<loFresh ∧ loFresh≤ hiFresh ∧ HasCompactSupport (omega₁:ℝ→ℂ) ∧ HasCompactSupport (omega₂:ℝ→ℂ) ∧
      tsupport (omega₁:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧ tsupport (omega₂:ℝ→ℂ)⊆Set.Icc loFresh hiFresh ∧
      ∃ C Cbin : ℝ,0 ≤ C ∧ 0≤ Cbin ∧ ∀ (p : ι → Eis) (hp : ∀ i,p i ≠ 0)
    [∀ i,(Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (_hpr : ∀ i, lambda^2 ∣ p i-1)
    (_hinj : Function.Injective (fun i => Ideal.span {p i}))
    (_hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (InverseFirstPriorityParents.Source ι Jo))
    (_hvalid:∀x∈original,InverseFirstPriorityParents.SourceValid p x)
    (_hextra:∀x∈original,extra x.cube⊆x.cube.support)
    (w:InverseFirstPriorityParents.Source ι Jo→ℂ) (_hw:∀x∈original,‖w x‖≤1)
    (Ψ:Eis→*ℂ) (m:Eis)
    (slots:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (cutoff:Finset ι→Finset ι→ℝ)
,
    ∀
        (Y:ℝ) (R:Finset σ→BlockIndex→ℝ) (L Z X εchild : ℝ) (Vlabel:BlockIndex→ℝ)
        (ell Ractive j tcount eta : ℝ) (M r V delta Acol Bfirst tau pi b : ℝ) (ρ : Fin 6 → ℝ) (t : ℝ)
        (labels : Finset σ→BlockIndex→Finset (Ideal Eis)) (A : ℝ),
      slots.card≤ K → 0≤ A → (∀(ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ), assigned⊆slots →
    let source:=unifiedSource p pool
      (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff);
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core;
      (∀i∈assigned,∀k∈lists i,‖a i k‖≤1) ∧
      (∀ i,|ρ i| ≤ B₀ i) ∧
      0 ≤ L ∧
      1 < Z ∧
      0 < X ∧
      0 < Y ∧
      0≤ eta ∧
      2≤ Z^eta ∧
      (∀ x ∈ source,x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) (R assigned (index p x))) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ Z^(ell+eta)) ∧
      (∀ x∈source,primeProductNorm p (cubeActiveSupport x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit) ≤ Z^(Ractive+eta)) ∧
      (∀ x∈source,Z^(j-eta) ≤ ‖ringComplex (jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)‖^2) ∧
      (∀ x∈source,(Ideal.absNorm x.quotient : ℝ) ≤ Z^(tcount+eta)) ∧
      (∀ a,‖Ψ a‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ i∈(slots\assigned),∀ q∈lists i,‖a i q‖ ≤ 1) ∧
      (∀ d∈keys p source,∀ x∈cell p source d,(actualSecondChild p 1 1 x).2.1 ∈ labels assigned d) ∧
      Jo+(assigned.card+assigned.card) ≤ 2*K ∧
      (slots\assigned).card ≤ K ∧
      (slots\assigned).card ≤ K ∧
      0 ≤ A ∧
      Y=Z^(firstPhysicalHeight M r ell V delta Bfirst j+12*eta+tau) ∧
      X=Z^(r-Acol-Bfirst-tcount) ∧
      L=eta*Real.log Z ∧
      (∀d,Vlabel d=secondFormalLabel Bfirst (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta) ∧
      2≤ Z ∧
      1≤ b ∧
      b≤ Z^(6*eta) ∧
      (∀x∈source,∀i,outerNorms p x i≤ Z^(caps i)) ∧
      (∀x∈source,primeProductNorm p x.second.sourceCommon*primeProductNorm p x.second.overlap≤ b*X) ∧
      (∀d∈keys p source,εmass*(secondCount ell Ractive j tcount (secondCellExponent Z d 0)
        (secondCellExponent Z d 1)+11*eta/2)≤ pi) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₁∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayMinus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₁) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest omega₁ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2)) ∧
      (∀ z:SecondRayIndex,∀ d∈keys p source,∀ t : Frequency × (Fin 6→ℝ),∀ J₂∈(slots\assigned).powerset,∀ γ∈actualSecondTriples p 1 1 (cell p source d),
        normalizedColumnEnergy p hg pool (secondRayPlus Ψ₀ z)
          (actualSecondInheritedRadicalPuncture m γ) ((slots\assigned)\J₂) lists a
          ((labels assigned d).filter Squarefree) (nonzeroChildFrequencyBall 1 (R assigned d)) (secondLabelWeight K)
          (clippedTest omega₂ (Z^(max 0 (secondCellColumnExponent Z X d)-(secondCellColumnExponent Z X d))) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
          (Z^(max 0 (secondCellColumnExponent Z X d))) Z (max 0 (secondCellColumnExponent Z X d)+(Vlabel d)) ≤
          A*Z^(max 0 (secondCellColumnExponent Z X d)+(Vlabel d)+εchild)*(tripleHeight J t.1*coordinateHeight J t.2))) →
      (Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z)))*
        globalPriorityRetainedAggregate p hg hp hcop extra pool original w
          negative Ψ m slots lists a (principalWindow om lo hi hlo hsupport negative t) X Y cutoff ≤
      C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild) := by
  obtain ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,C,Cbin,hC,hCbin,he⟩:=
    global_priority_retained_all_rays (ι:=ι) (σ:=σ) om lo hi hlo hsupport negative
      caps hcaps B₀ hB₀ J K εmass hεmass
  have hmass := firstCoreMassBound_nonneg
  let Ctot:=firstCoreMassBound*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*
    (Fintype.card FirstCoreIndex:ℝ)*C
  refine ⟨omega₁,omega₂,af,bf,haf,hab,hc₁,hc₂,hs₁,hs₂,Ctot,Cbin,by dsimp [Ctot];positivity,hCbin,?_⟩
  intro p hp _ hcop hg hpr hinj hc Jo extra pool original hvalid hextra w hwOriginal
    Ψ m slots lists a cutoff
    Y R L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t labels A hslots hA hdata
  let P:=Z^(firstKappa M r ell V delta Acol Bfirst Ractive)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))
  let H:=C*A*(1+‖t‖)^(2*InverseClippingProfiles.momentOrder J)*
        (1+Cbin*Real.log Z)^4*Z^(r+3*ell+V+48*eta+tau+pi+εchild)
  have hb (ray:RayCharacter×RayCharacter)(core:FirstCoreIndex)(assigned:Finset σ)(ha:assigned⊆slots):
    P*‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖≤ H:=by
    obtain ⟨haassigned,hρ,hL,hZ,hX,hY,heta,hbin,hrows,hcube₁,hcube₂,hactive,hj,hquot,hΨ,
      ha₁,ha₂,hlabels,ho,hslots₁,hslots₂,hA',hYe,hXe,hLe,hVe,hZ2,hb,hthreshold,hnorm,hgeom,hmass,hleft,hright⟩:=hdata ray core assigned ha
    exact he p hp hcop hg hpr hinj hc extra pool original hvalid hextra w hwOriginal
      Ψ m ray core slots assigned lists a (fun _=>cutoff)
      Y (R assigned) L Z X εchild Vlabel ell Ractive j tcount eta M r V delta Acol Bfirst tau pi b ρ t (labels assigned) A
      haassigned hρ hL hZ hX hY heta hbin hrows hcube₁ hcube₂ hactive hj hquot hΨ
      ha₁ ha₂ hlabels ho hslots₁ hslots₂ hA' hYe hXe hLe hVe hZ2 hb hthreshold hnorm hgeom hmass hleft hright
  have hZ:1<Z:=(hdata 1 1 ∅ (Finset.empty_subset _)).2.2.2.1
  have hH:0≤ H:=by dsimp [H];positivity
  have hpow:(4:ℝ)^slots.card≤4^K:=pow_le_pow_right₀ (by norm_num) hslots
  let S:(RayCharacter×RayCharacter)→FirstCoreIndex→Finset σ→ℝ:=fun ray core assigned=>‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z *
      ∑x∈unifiedSource p pool (InverseMomentWholePriorityParents.wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists) (fun _=>cutoff),
        globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
          wholeRow p hp hcop hg extra pool negative
            (firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core) m slots assigned lists a
            (principalWindow om lo hi hlo hsupport negative t) X Y z x‖
  change ∀ray core assigned, assigned⊆slots → P*S ray core assigned≤ H at hb
  change P*(firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,S ray core assigned)≤_
  calc
    _=firstCoreMassBound*(2:ℝ)^slots.card*∑ray:RayCharacter×RayCharacter,∑core:FirstCoreIndex,∑assigned∈slots.powerset,P*S ray core assigned:=by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro ray hr
      apply Finset.sum_congr rfl
      intro core hc
      apply Finset.sum_congr rfl
      intro assigned ha
      ring
    _≤firstCoreMassBound*(2:ℝ)^slots.card*∑_ray:RayCharacter×RayCharacter,∑_core:FirstCoreIndex,∑_assigned∈slots.powerset,H:=by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact Finset.sum_le_sum fun ray _=>Finset.sum_le_sum fun core _=>Finset.sum_le_sum fun assigned ha=>hb ray core assigned (Finset.mem_powerset.mp ha)
    _=firstCoreMassBound*(4:ℝ)^slots.card*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by
      simp only [Finset.sum_const,Finset.card_univ,Finset.card_powerset,nsmul_eq_mul,Nat.cast_pow,Nat.cast_ofNat]
      rw [show (4:ℝ)^slots.card=(2:ℝ)^slots.card*(2:ℝ)^slots.card by rw [←mul_pow];norm_num]
      ring
    _≤firstCoreMassBound*(4:ℝ)^K*(Fintype.card (RayCharacter×RayCharacter):ℝ)*(Fintype.card FirstCoreIndex:ℝ)*H:=by gcongr
    _= _:=by dsimp [Ctot,H];ring
end InverseMoment

end

noncomputable section
namespace InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseInitialArithmetic
open InverseMomentGlobalPrincipalMass
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O

theorem original_tail_mass (Jmax : ℕ) :
    ∃C : ℝ,0<C ∧ ∀{ι : Type*}[DecidableEq ι](p : ι→O)(_hp : ∀i,p i≠0)
    [∀i,(Ideal.span {p i}).IsMaximal]
    (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (Jo : ℕ),Jo≤ Jmax → ∀(S : Finset (Source ι Jo))(Z L : ℝ),
    1≤ Z → 0≤ L → (∀x∈S,SourceValid p x) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2≤ Z^L) →
    (∀x∈S,‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2≤ Z^L) →
    (∀x∈S,‖ringComplex (∏i∈cubeActiveSupport x.cube.support
      (fun i=>x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖≤ Z^L) →
    (∀x∈S,primeProductNorm p x.firstCommon≤ Z^L) →
    (∀x∈S,primeProductNorm p x.quotientSupport≤ Z^L) →
    ∀(extra : CubeCoordinates ι→Finset ι)(negative : Bool),
    (∀x∈S,extra x.cube⊆x.cube.support) →
    (∑x∈S,primeProductNorm p (principalSupport extra negative x))≤ C*Z^(13*L) := by
  obtain ⟨C,hC,hraw⟩ := original_weighted_mass Jmax 1 (by norm_num)
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj Jo hJo S Z L hZ hL hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  have hz : 0<Z := zero_lt_one.trans_le hZ
  have hh := hraw p hp hinj Jo hJo S (Z^L) (Z^L) (Z^L) (Z^L) 1
    (Real.one_le_rpow hZ hL) (by positivity) (by positivity) (by positivity)
    (by norm_num) hS hb₁ hb₂ hactive hcommon hquot extra negative hextra
  simp only [Real.rpow_one] at hh
  apply hh.trans_eq
  have he : Z^(13*L)=(Z^L)^13 := by
    rw [←Real.rpow_mul_natCast hz.le]
    congr 1
    norm_num
    ring
  rw [he]
  norm_num
  ring

end InverseMomentGlobalPriorityTail
end

noncomputable section
namespace InverseMomentGlobalPriorityTail
open InverseMoment InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open InversePrioritySecondSource InverseSecondPrincipalCaller InversePrincipalEnergy
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ] {Jo : ℕ}
variable (p : ι→O) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀i,lambda∉Ideal.span {p i})

lemma tail_forget (hp : ∀i,p i≠0) (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (negative : Bool)
    (Ψ : O→*ℂ) (m : O) (slots J : Finset σ) (lists : σ→Finset ι) (a : σ→ι→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ)
    (y : SecondParentSource ι (Jo+(J.card+J.card))) :
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R
      (forgetAppended (Jo:=Jo) y)=
    priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y := rfl

theorem original_paired_tail (hp : ∀i,p i≠0)
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (extra : CubeCoordinates ι→Finset ι) (pool : Finset ι) (source : Finset (Source ι Jo))
    (negative : Bool) (Ψ : O→*ℂ) (m : O) (slots J : Finset σ)
    (lists : σ→Finset ι) (a : σ→ι→ℂ) (w : Source ι Jo→ℂ)
    (V : 𝓢(ℝ,ℂ)) (X Y : ℝ) (R : Finset ι→Finset ι→ℝ) :
    (∑y∈wholeAssignedParents p (fun x=>extra x.cube) source negative J lists,
      coefficient p J a w y*priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R y)=
    ∑x∈source,w x*(‖primeMark J lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ m slots J lists a V X Y R (parent p x) := by
  rw [wholePaired_parent_sq_sum p (fun x=>extra x.cube) hinj]
  simp only [tail_forget]

end InverseMomentGlobalPriorityTail
end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseInitialArithmetic InverseFirstPriorityParents InverseMomentWholePriorityParents
open InverseWholePriorityValidSource InverseWholePriorityRetainedSource RayFourExpansion
open InverseMomentWholePriorityPhysical InversePrioritySecondSource InverseSecondPrincipalCaller
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "Eis"=>Eisenstein.O
variable {ι σ:Type*} [DecidableEq ι] [DecidableEq σ] {Jo:ℕ}
variable (p:ι→Eis) [∀i,(Ideal.span {p i}).IsMaximal]
  (hg:∀i,lambda∉Ideal.span {p i})

theorem global_priority_slice_full_tail
    (hp:∀i,p i≠0) (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (Eis⧸Ideal.span {p i})≠2)
    (hpr:∀i,lambda^2∣p i-1)
    (extra:CubeCoordinates ι→Finset ι) (pool:Finset ι)
    (original:Finset (Source ι Jo)) (w:Source ι Jo→ℂ) (negative:Bool) (Ψ:Eis→*ℂ) (m:Eis)
    (ray:RayCharacter×RayCharacter) (core:FirstCoreIndex)
    (slots assigned:Finset σ) (lists:σ→Finset ι) (a:σ→ι→ℂ)
    (om:𝓢(ℝ,ℂ)) (lo hi:ℝ) (hlo:0<lo) (hs:Function.support om⊆Set.Icc lo hi)
    (X t Y:ℝ) (hX:0<X) (hY:0<Y) (R:Finset ι→Finset ι→ℝ):
    let V:=principalWindow om lo hi hlo hs negative t
    let Ψ₀:=firstCoreTwist negative (if negative then ray.1 else ray.2) Ψ core
    let parents:=wholeAssignedParents p (fun x=>extra x.cube) original negative assigned lists
    let source:=unifiedSource p pool parents (fun _=>R)
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      parentPoisson p hp hg hinj pool negative Ψ m slots assigned (fun i=>lists i\extra x.cube) a om X t Y ray core (parent p x)‖≤
    (∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
      ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*
      ‖priorityZeroParent p hg extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖)+
    ‖∑z:SecondRayIndex,(Y:ℂ)*secondRayCoefficient z * ∑x∈source,
      globalPriorityWeight p hg negative Ψ m ray core w assigned a x *
        wholeRow p hp hcop hg extra pool negative Ψ₀ m slots assigned lists a V X Y z x‖+
    ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
      (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*
      priorityTailParent p hg hp hinj extra pool negative Ψ₀ m slots assigned lists a V X Y R (parent p x)‖ := by
  intro V Ψ₀ parents source
  rw [global_priority_signed_branches p hg hp hcop hinj hc hpr extra pool original w negative
    Ψ m ray core slots assigned lists a om lo hi hlo hs X t Y hX hY R]
  have hn (H:Source ι Jo→ℂ):
      ‖∑x∈original,globalPriorityOuter p hg negative Ψ m ray core w x*
        (‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2:ℝ)*H x‖≤
      ∑x∈original,‖globalPriorityOuter p hg negative Ψ m ray core w x‖*
        ‖primeMark assigned lists a (wholeExtractedSupport (fun x=>extra x.cube) negative x)‖^2*‖H x‖:=by
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro x hx
    rw [norm_mul,norm_mul,Complex.norm_real,Real.norm_of_nonneg (sq_nonneg _)]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans (add_le_add (hn _) (le_refl _))) (le_refl _))

end InverseMoment

end

noncomputable section
namespace InverseMoment
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open InverseFirstGlobalCaps InverseSecondSourceBlocks InverseMomentFirstChildWindows
open InverseMomentFirstOriginalProfile
open Eisenstein (ringComplex)
open InverseInitialRayAttachment InverseFirstRayAttachment
local notation "O"=>Eisenstein.O
variable {ι:Type*}[DecidableEq ι]
variable (p:ι→O)

def firstCellRadius (Z M r ell V eta tau:ℝ)(k:SourceIndex)(j:ℕ):ℝ:=
  Z^(firstPhysicalHeight M r ell V (dyadicExponent Z (k 3))
    (dyadicExponent Z (k 2)) (dyadicExponent Z j)+12*eta+tau)

theorem first_dyadic_radius_cell (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(x:FirstOriginalOuter ι)
    (hx:x∈refinedOuter p pool Q k (labelGate p j))
    (Z M r ell V eta tau:ℝ):
    firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau=
      firstCellRadius Z M r ell V eta tau k j:=by
  rw [refinedOuter_label] at hx
  obtain ⟨hx,hj⟩:=Finset.mem_filter.mp hx
  have hg:outerGate p k x:=(Finset.mem_filter.mp hx).2
  have hC:=hg 2
  have hD:=hg 3
  change dyadIndex (primeProductNorm p x.2.1)=k 2 at hC
  change dyadIndex (‖ringComplex ((∏ i ∈ x.2.2,p i))‖^2)=k 3 at hD
  change dyadIndex (primeProductNorm p x.2.2)=k 3 at hD
  unfold firstDyadicRadius firstCellRadius firstDyadicExponent
  rw [hD,hC]
  change dyadIndex (‖ringComplex (jLabel p x.1.support
    (fun i=>x.1.leftExponent i+x.1.rightExponent i) x.1.leftBit x.1.rightBit)‖^2)=j at hj
  rw [hj]

theorem first_dyadic_refined_cutoff (pool:Finset ι)(Q:Finset (ι→₀ℕ))
    (k:SourceIndex)(j:ℕ)(Z M r ell V eta tau:ℝ):
    ∀x∈refinedOuter p pool Q k (labelGate p j),∀_I:Ideal O,
      firstDyadicRadius p x.1 x.2.1 x.2.2 Z M r ell V eta tau≤
        firstCellRadius Z M r ell V eta tau k j:=by
  intro x hx I
  exact (first_dyadic_radius_cell p pool Q k j x hx Z M r ell V eta tau).le

end InverseMoment

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
