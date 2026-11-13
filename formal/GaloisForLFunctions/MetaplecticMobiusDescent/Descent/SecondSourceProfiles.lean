/-
Second source profiles adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.MarkedSecondSources

/-!
# Second source profiles

Multipliers, signed weights and inherited radical punctures of the actual second sources;
left, right and branch second modes; normalized child energies and twisted descent profile
separation.
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

namespace InverseMoment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open scoped BigOperators Classical
variable {ι:Type*} [DecidableEq ι] (p:ι→O)

/-- The complementary primary product in a common-prime divisor. -/
def secondMaskQuotient (E G:Finset ι) (_h:E⊆G) : O := ∏ i∈G\E,p i

lemma secondMaskQuotient_spec (E G:Finset ι) (h:E⊆G) :
    (∏i∈G,p i)=(∏i∈E,p i)*secondMaskQuotient p E G h := by
  rw [secondMaskQuotient,←Finset.prod_union Finset.disjoint_sdiff,Finset.union_sdiff_of_subset h]

lemma secondMaskQuotient_span (E G:Finset ι) (h:E⊆G) :
    Ideal.span {secondMaskQuotient p E G h} = InverseInitialArithmetic.sourceIdeal p (G\E) := rfl

lemma poisson_mask_generator_dvd (E G:Finset ι) (h:E⊆G) : (∏i∈E,p i)∣∏i∈G,p i :=
  ⟨secondMaskQuotient p E G h,secondMaskQuotient_spec p E G h⟩

def secondExpansionQuotient (x:SecondExpansionData ι) : O :=
  if h:x.divisor⊆x.sourceCommon then secondMaskQuotient p x.divisor x.sourceCommon h else 0

@[simp] lemma secondExpansionQuotient_of_subset (x:SecondExpansionData ι)
    (h:x.divisor⊆x.sourceCommon) :
    secondExpansionQuotient p x=secondMaskQuotient p x.divisor x.sourceCommon h := by
  simp only [secondExpansionQuotient,dif_pos h]
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_drop_puncture (Ψ : Eis →* ℂ) (m d f k : Eis)
    (hd : d ∣ m*f) (H : Finset ι → ℂ) (S : Finset ι) :
    secondChildColumn p hg Ψ (m*d) f k H S =
      secondChildColumn p hg Ψ m f k H S := by
  by_cases hz : ∃ i ∈ S, d ∈ Ideal.span {p i}
  · obtain ⟨i,hi,hdI⟩ := hz
    have hr : m*f ∈ Ideal.span {p i} := by
      obtain ⟨a,ha⟩ := hd
      rw [ha]
      exact Ideal.mul_mem_right _ _ hdI
    have hl : (m*d)*f ∈ Ideal.span {p i} := by
      exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hdI)
    rw [secondChildColumn_zero_of_mask_label_mem p hg Ψ (m*d) f k H S i hi hl,
      secondChildColumn_zero_of_mask_label_mem p hg Ψ m f k H S i hi hr]
  · have hm : primeCoprimeMask p S d = 1 := by
      rw [primeCoprimeMask_indicator]
      exact if_pos (fun i hi hd=>hz ⟨i,hi,Ideal.mem_span_singleton.mpr hd⟩)
    simp only [secondChildColumn,FirstPassCubeLabels.mask_mul p hg S,hm,mul_one]

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_drop_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m d f k : Eis) (hd : d ∣ m*f)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ (m*d) f k slots lists a W X =
      finiteCanonicalMarkedRow p hg F Ψ m f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn_drop_puncture p hg Ψ m d f k hd]

theorem canonicalMarkedSplit_original_lists (F V A : Finset ι) (Ψ : Eis →* ℂ)
    (m r c d e k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ)
    (hA : ∀ i ∈ A, (m*r)*(c*e*∏ j ∈ V,p j) ∈ Ideal.span {p i}) :
    canonicalMarkedSplit p hg F V A Ψ m r c d e k slots lists a W X =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hg F Ψ (m*r)
          (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) := by
  unfold canonicalMarkedSplit
  apply Finset.sum_congr rfl
  intro J hJ
  exact congrArg (fun y => primeMark J lists a (A∪V)*y)
    (finiteCanonicalMarkedRow_restore_lists p hg F A Ψ (m*r)
      (c*e*∏ j ∈ V,p j) (d*e*k) (slots\J) lists a W (X/primeProductNorm p V) hA)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_first_divisor_dvd_child
    (B C D V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (m r e : Eis) :
    (∏ i∈D,p i) ∣
      ((m*b0Label p B v ε₁ ε₂)*r)*
        (((∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂)*e*∏ i ∈ V,p i) := by
  have hd := poisson_mask_generator_dvd p D (C∪B) hD
  rw [Finset.prod_union hCB] at hd
  have hb := cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv
  change (∏ i ∈ B,p i) ∣ jLabel p B v ε₁ ε₂*b0Label p B v ε₁ ε₂ at hb
  apply (hd.trans (mul_dvd_mul_left (∏ i ∈ C,p i) hb)).trans
  refine ⟨m*r*e*∏ i ∈ V,p i,?_⟩
  ring

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actual_second_extracted_support_killed
    (B C G E V A : Finset ι) (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i) (m : Eis) :
    ∀ i ∈ A,
      ((m*b0Label p B v ε₁ ε₂)*secondMaskQuotient p E G hEG)*
        (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*
          (∏ i∈E,p i)*∏ j ∈ V,p j) ∈ Ideal.span {p i} := by
  let r := secondMaskQuotient p E G hEG
  let e := (∏ i∈E,p i)
  let T := ((m*b0Label p B v ε₁ ε₂)*r)*
    (((∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂)*e*∏ j ∈ V,p j)
  have hb : (∏ j ∈ B,p j) ∣ T := by
    apply (cubeRadical_dvd_jLabel_b0 p B v ε₁ ε₂ hv).trans
    refine ⟨m*r*(∏ j ∈ C,p j)*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hc : (∏ j ∈ C,p j) ∣ T := by
    refine ⟨m*b0Label p B v ε₁ ε₂*r*jLabel p B v ε₁ ε₂*e*∏ j ∈ V,p j,?_⟩
    dsimp [T]
    ring
  have hg' : (∏ j ∈ G,p j) ∣ T := by
    rw [secondMaskQuotient_spec p E G hEG]
    refine ⟨m*b0Label p B v ε₁ ε₂*(∏ j ∈ C,p j)*jLabel p B v ε₁ ε₂*∏ j ∈ V,p j,?_⟩
    dsimp [T,r,e]
    ring
  intro i hi
  apply Ideal.mem_span_singleton.mpr
  change p i ∣ T
  rcases Finset.mem_union.mp (hA hi) with hi|hi
  · rcases Finset.mem_union.mp hi with hi|hi
    · exact (Finset.dvd_prod_of_mem p hi).trans hb
    · exact (Finset.dvd_prod_of_mem p hi).trans hc
  · exact (Finset.dvd_prod_of_mem p hi).trans hg'

include hp in
theorem actual_second_split_fixed_family
    (F B C D G E V A : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C∪B)
    (hEG : E ⊆ G) (hA : A ⊆ (B∪C)∪G)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v i)
    (Ψ : Eis →* ℂ) (m k : Eis) (slots : Finset σ) (lists : σ → Finset ι)
    (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    let d := (∏ i∈D,p i)
    let e := (∏ i∈E,p i)
    let r := secondMaskQuotient p E G hEG
    let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
    canonicalMarkedSplit p hg F V A Ψ
      (m*b0Label p B v ε₁ ε₂*d) r c d e k slots lists a W (primeProductNorm p V*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪V) *
        finiteCanonicalMarkedRow p hg F Ψ ((m*b0Label p B v ε₁ ε₂)*r)
          (c*e*∏ i ∈ V,p i) (d*e*k) (slots\J) lists a W X := by
  dsimp only
  let d := (∏ i∈D,p i)
  let e := (∏ i∈E,p i)
  let r := secondMaskQuotient p E G hEG
  let c := (∏ i ∈ C,p i)*jLabel p B v ε₁ ε₂
  have hd := actual_first_divisor_dvd_child p B C D V hCB hD v ε₁ ε₂ hv m r e
  have hk := actual_second_extracted_support_killed p B C G E V A hEG hA v ε₁ ε₂ hv m
  have hm : (m*b0Label p B v ε₁ ε₂*d)*r = ((m*b0Label p B v ε₁ ε₂)*r)*d := by ring
  have hX : primeProductNorm p V*X/primeProductNorm p V = X := by
    field_simp [(primeProductNorm_pos p hp V).ne']
  unfold canonicalMarkedSplit
  rw [show m*b0Label p B v ε₁ ε₂*(∏ i∈D,p i) *
      secondMaskQuotient p E G hEG = ((m*b0Label p B v ε₁ ε₂)*r)*d from hm]
  rw [hX]
  apply Finset.sum_congr rfl
  intro J hJ
  rw [finiteCanonicalMarkedRow_drop_puncture p hg F Ψ _ d _ _ hd]
  exact congrArg (fun y => primeMark J lists a (A∪V)*y)
    (finiteCanonicalMarkedRow_restore_lists p hg F A Ψ _ _ _ (slots\J) lists a W X hk)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
variable (hinj : Function.Injective (fun i => Ideal.span {p i}))
include hinj

theorem secondPreColumn_zero_of_common_overlap
    (Ψ : O →* ℂ) (m c d e k : O) (H : Finset ι → ℂ) (G S : Finset ι)
    (hSG : ¬ Disjoint S G) :
    secondPreColumn p hg Ψ (m * ∏ i ∈ G, p i) c d e k H S = 0 := by
  have hm : primeCoprimeMask p S (m * ∏ i ∈ G, p i) = 0 := by
    rw [FirstPassCubeLabels.mask_mul p hg S,
      commonProduct_mask p hinj S G, if_neg hSG, mul_zero]
  simp only [secondPreColumn, hm, mul_zero, zero_mul]

include hp in
theorem weighted_secondChildKernelPair_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := (∏ i ∈ E,p i)
    let r := secondMaskQuotient p E G hEG
    secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ K =
    secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
      secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ lengthScale := by
  have hcopElements : Pairwise (Function.onFun IsCoprime p) := fun i j hij =>
    (Ideal.isCoprime_span_singleton_iff _ _).mp (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  dsimp only
  let e := (∏ i ∈ E,p i)
  let r := secondMaskQuotient p E G hEG
  let w := secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V
  unfold secondChildKernelPair
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hVN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hVM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  have hcoeff :
      w * (star (secondChildColumn p hg Ψ₁ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₁) (fun _ => 1) N) *
        secondChildColumn p hg Ψ₂ (m*r) (c*e*∏ i ∈ V, p i)
          (d*e*k₂) (fun _ => 1) M) =
      supportMobius V *
        star (secondPreColumn p hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N)) *
        secondPreColumn p hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) := by
    rw [secondPreColumn_union p hg hp hcopElements hpr Ψ₁ m r c d e k₁ (fun _ => 1) V N hVN,
      secondPreColumn_union p hg hp hcopElements hpr Ψ₂ m r c d e k₂ (fun _ => 1) V M hVM]
    simp only [w, secondCommonWeight, star_mul]
    ring
  change w * (_ * K (V∪N) (V∪M)) = w * (_ * lengthScale (V∪N) (V∪M))
  conv_lhs => rw [← mul_assoc w, hcoeff]
  conv_rhs => rw [← mul_assoc w, hcoeff]
  by_cases hGN : Disjoint G (V∪N)
  · by_cases hGM : Disjoint G (V∪M)
    · rw [hKL _ _ hGN hGM]
    · have hz := secondPreColumn_zero_of_common_overlap p hg hinj Ψ₂ m c d e k₂
        (fun _ => 1) G (V∪M) (fun h => hGM h.symm)
      rw [secondMaskQuotient_spec p E G hEG] at hz
      change secondPreColumn p hg Ψ₂ (m*(e*r)) c d e k₂ (fun _ => 1) (V∪M) = 0 at hz
      rw [hz]
      ring
  · have hz := secondPreColumn_zero_of_common_overlap p hg hinj Ψ₁ m c d e k₁
      (fun _ => 1) G (V∪N) (fun h => hGN h.symm)
    rw [secondMaskQuotient_spec p E G hEG] at hz
    change secondPreColumn p hg Ψ₁ (m*(e*r)) c d e k₁ (fun _ => 1) (V∪N) = 0 at hz
    rw [hz, star_zero]
    ring

include hp in
theorem weighted_secondRayChild_congr_off_common
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (G E : Finset ι) (hEG : E ⊆ G) (F V : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (z : SecondRayIndex)
    (K lengthScale : Finset ι → Finset ι → ℂ)
    (hKL : ∀ S T, Disjoint G S → Disjoint G T → K S T = lengthScale S T) :
    let e := (∏ i ∈ E,p i)
    let r := secondMaskQuotient p E G hEG
    secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) K =
    secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V) *
      secondChildKernelPair p hg F V (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z)
        m r c d e k (-k) lengthScale := by
  dsimp only
  simp only [secondTotalWeight, mul_assoc]
  congr 1
  exact weighted_secondChildKernelPair_congr_off_common p hp hg hinj hpr G E hEG F V
    (secondRayMinus Ψ₁ z) (secondRayPlus Ψ₂ z) m c d k (-k) K lengthScale hKL

def secondExpansionSource
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (z : SecondRayIndex)
    (s : Finset (SecondExpansionData ι)) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ x ∈ s,
    ((Y : ℂ) * secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor) *
    (secondTotalWeight p hg Ψ Ψ m (secondExpansionQuotient p x) c d
      ((∏ i ∈ x.divisor,p i)) x.frequency (z,x.overlap) *
    secondChildKernelPair p hg F x.overlap (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d
      ((∏ i ∈ x.divisor,p i)) x.frequency (-x.frequency)
      (secondSourcePairKernel p ((∏ i ∈ x.divisor,p i))
        x.frequency (fun A => H₁ (x.sourceCommon∪A)) (fun A => H₂ (x.sourceCommon∪A)) W Y))

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def expansionProfileData (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (A₁ A₂ : Finset ι) (x : SecondExpansionData ι) : SecondProfileData ι where
  common := x.sourceCommon
  overlap := x.overlap
  extractedLeft := A₁ ∪ x.sourceCommon
  extractedRight := A₂ ∪ x.sourceCommon
  rayLeft := secondRayMinus Ψ z
  rayRight := secondRayPlus Ψ z
  puncture := m
  quotient := secondExpansionQuotient p x
  oldLabel := c
  oldDivisor := d
  divisor := (∏ i ∈ x.divisor,p i)
  frequency := x.frequency

def expansionProfileWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (Y : ℝ) (x : SecondExpansionData ι) : ℂ :=
  (Y : ℂ) * (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    supportMobius x.divisor *
    secondTotalWeight p hg Ψ Ψ m (secondExpansionQuotient p x) c d
      ((∏ i ∈ x.divisor,p i)) x.frequency (z,x.overlap)

include hp in
theorem secondExpansionSource_marked_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι))
    (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    ∑ x ∈ source, expansionProfileWeight p hg Ψ m c d z Y x *
      actualSecondProfileRow p hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  unfold secondExpansionSource
  apply Finset.sum_congr rfl
  intro x hx
  have he := hE x hx
  have hc := weighted_secondRayChild_congr_off_common p hp hg hinj hpr
    x.sourceCommon x.divisor he F x.overlap Ψ Ψ m c d x.frequency z
    (secondSourcePairKernel p ((∏ i ∈ x.divisor,p i)) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ (x.sourceCommon ∪ U)) *
        W₁ (primeProductNorm p (x.sourceCommon ∪ U)/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ (x.sourceCommon ∪ U)) *
        W₂ (primeProductNorm p (x.sourceCommon ∪ U)/X)) Φ Y)
    (secondSourcePairKernel p ((∏ i ∈ x.divisor,p i)) x.frequency
      (fun U => primeMark slots₁ lists₁ a₁ ((A₁ ∪ x.sourceCommon) ∪ U) *
        W₁ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ ((A₂ ∪ x.sourceCommon) ∪ U) *
        W₂ (primeProductNorm p x.sourceCommon * primeProductNorm p U/X)) Φ Y)
    (by
      intro S T hGS hGT
      simp only [secondSourcePairKernel,primeProductNorm_union p x.sourceCommon S hGS,
        primeProductNorm_union p x.sourceCommon T hGT,Finset.union_assoc])
  dsimp only at hc
  rw [← secondExpansionQuotient_of_subset p x he] at hc
  rw [hc]
  simp only [expansionProfileWeight,actualSecondProfileRow,expansionProfileData,
    secondSourceCommonCoefficient,Complex.ofReal_pow]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
def secondSignedSourceWeight (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) : ℂ :=
  (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) x.sourceCommon‖^2 : ℝ) *
    supportMobius x.divisor *
    secondCommonWeight p hg (secondRayMinus Ψ z) (secondRayPlus Ψ z)
      m (secondExpansionQuotient p x) c d ((∏ i ∈ x.divisor,p i))
      x.frequency (-x.frequency) x.overlap

theorem expansionProfileWeight_eq_signed (Ψ : Eis →* ℂ) (m c d : Eis)
    (z : SecondRayIndex) (Y : ℝ) (x : SecondExpansionData ι) :
    expansionProfileWeight p hg Ψ m c d z Y x =
      (Y : ℂ)*secondRayCoefficient z*secondSignedSourceWeight p hg Ψ m c d z x := by
  simp only [expansionProfileWeight,secondSignedSourceWeight,secondTotalWeight]
  ring

include hp in
theorem secondSignedSourceWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m c d : Eis) (z : SecondRayIndex)
    (x : SecondExpansionData ι) :
    ‖secondSignedSourceWeight p hg Ψ m c d z x‖ ≤ 1 := by
  have hinput : ‖secondInputCoefficient p
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) x.sourceCommon‖^2 ≤ 1 := by
    have h := secondInputCoefficient_norm_le_test p hg Ψ hΨ m c d (fun _ => 1) x.sourceCommon
    simpa only [norm_one,one_pow] using pow_le_pow_left₀ (norm_nonneg _) h 2
  have hminus : ∀ a, ‖secondRayMinus Ψ z a‖ ≤ 1 := fun a =>
    (secondRayMinus_norm_le Ψ z a).trans (hΨ a)
  have hplus : ∀ a, ‖secondRayPlus Ψ z a‖ ≤ 1 := fun a =>
    (secondRayPlus_norm_le Ψ z a).trans (hΨ a)
  have pre (Ξ : Eis →* ℂ) (hΞ : ∀ a, ‖Ξ a‖ ≤ 1) (m c d e k : Eis) (S : Finset ι) :
      ‖secondPreColumn p hg Ξ m c d e k (fun _ => 1) S‖ ≤ 1 := by
    have hcol := secondColumnCoefficient_norm_one_of_good p hp hinj hg hc S
    have hm := primeCoprimeMask_norm_le_one p S m
    have hr (a : Eis) := primeSubsetRow_norm_le_one p
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S a
    simp only [secondPreColumn,norm_mul,norm_pow,norm_star,norm_one,hcol,one_mul,mul_one]
    calc
      ‖Ξ (∏ i∈S,p i)‖*‖primeCoprimeMask p S m‖*
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c‖^4*
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d‖*
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S e‖*
        ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S k‖
        ≤ 1 * 1 * 1^4 * 1 * 1 * 1 := by
        gcongr <;> first | exact hΞ _ | exact hm | exact hr _
      _ = 1 := by norm_num
  have hm := pre (secondRayMinus Ψ z) hminus
    (m*((∏ i∈x.divisor,p i)*secondExpansionQuotient p x)) c d (∏ i∈x.divisor,p i) x.frequency x.overlap
  have hp' := pre (secondRayPlus Ψ z) hplus
    (m*((∏ i∈x.divisor,p i)*secondExpansionQuotient p x)) c d (∏ i∈x.divisor,p i) (-x.frequency) x.overlap
  simp only [secondSignedSourceWeight,secondCommonWeight,norm_mul,norm_star,
    supportMobius_norm,Complex.norm_real,Real.norm_eq_abs,mul_one,one_mul]
  rw [abs_of_nonneg (sq_nonneg (‖secondInputCoefficient p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d (fun _ => 1) x.sourceCommon‖))]
  exact (mul_le_mul hinput ((mul_le_mul hm hp' (norm_nonneg _) zero_le_one).trans_eq (one_mul 1))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one).trans_eq (one_mul 1)

include hp in
theorem secondExpansionSource_signed_profile
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hpr : ∀ i, lambda^2 ∣ p i - 1)
    (F : Finset ι) (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex)
    (source : Finset (SecondExpansionData ι)) (hE : ∀ x ∈ source, x.divisor ⊆ x.sourceCommon)
    (A₁ A₂ : Finset ι) (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι)
    (a₁ a₂ : σ → ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ)) (X Y : ℝ) :
    secondExpansionSource p hg F Ψ m c d z source
      (fun U => primeMark slots₁ lists₁ a₁ (A₁ ∪ U) * W₁ (primeProductNorm p U/X))
      (fun U => primeMark slots₂ lists₂ a₂ (A₂ ∪ U) * W₂ (primeProductNorm p U/X)) Φ Y =
    (Y : ℂ)*secondRayCoefficient z *
      ∑ x ∈ source, secondSignedSourceWeight p hg Ψ m c d z x *
        actualSecondProfileRow p hg F (expansionProfileData p Ψ m c d z A₁ A₂ x)
          slots₁ slots₂ lists₁ lists₂ a₁ a₂ W₁ W₂ Φ Y X := by
  rw [secondExpansionSource_marked_profile p hp hg hinj hpr (hE := hE)]
  simp only [expansionProfileWeight_eq_signed,Finset.mul_sum,mul_assoc]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment
open InverseInitialArithmetic (sourceIdeal sourcePrime sourceIdeal_dvd)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hcop in
omit [DecidableEq ι] in
theorem sourceIdeal_squarefree (S : Finset ι) : Squarefree (sourceIdeal p S) := by
  rw [sourceIdeal,span_finset_prime_product]
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro i hi j hj hij
    exact (hcop hij).isRelPrime
  · intro i hi
    exact (sourcePrime p i).property.squarefree

include hcop in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_coprime_of_disjoint (S T : Finset ι) (hST : Disjoint S T) :
    IsCoprime (sourceIdeal p S) (sourceIdeal p T) := by
  simp only [sourceIdeal,span_finset_prime_product]
  apply IsCoprime.prod_left
  intro i hi
  apply IsCoprime.prod_right
  intro j hj
  exact hcop (fun he => Finset.disjoint_left.mp hST hi (he.symm ▸ hj))

omit [DecidableEq ι] in
lemma prime_span_coprime_of_not_mem (i : ι) (c : Eis) (hc : c ∉ Ideal.span {p i}) :
    IsCoprime (Ideal.span {p i}) (Ideal.span {c} : Ideal Eis) := by
  apply Ideal.isCoprime_iff_sup_eq.mpr
  by_contra hne
  have he := (inferInstance : (Ideal.span {p i}).IsMaximal).eq_of_le hne le_sup_left
  apply hc
  rw [he]
  exact (show Ideal.span {c} ≤ (Ideal.span {p i} : Ideal Eis) ⊔ Ideal.span {c} from le_sup_right)
    (Ideal.subset_span (by simp))

omit [DecidableEq ι] in
theorem sourceIdeal_coprime_of_not_mem (S : Finset ι) (c : Eis)
    (hc : ∀ i ∈ S, c ∉ Ideal.span {p i}) :
    IsCoprime (sourceIdeal p S) (Ideal.span {c} : Ideal Eis) := by
  rw [sourceIdeal,span_finset_prime_product]
  exact IsCoprime.prod_left (fun i hi => prime_span_coprime_of_not_mem p i c (hc i hi))

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem jLabel_span_dvd_source (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (Ideal.span {jLabel p B v ε₁ ε₂} : Ideal Eis) ∣ sourceIdeal p B := by
  apply span_dvd_of_element_dvd
  change (∏ i ∈ B,p i^bit (retained (parity (v i)) (ε₁ i) (ε₂ i))) ∣ ∏ i ∈ B,p i
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  cases retained (parity (v i)) (ε₁ i) (ε₂ i) <;> simp [bit]

omit [DecidableEq ι] in
theorem secondInputCoefficient_zero_of_label_mem (Ψ : Eis →* ℂ) (m c d : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S) (hc : c ∈ Ideal.span {p i}) :
    secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) Ψ m c d H S = 0 := by
  have hr : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c = 0 := by
    apply Finset.prod_eq_zero hi
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc,MulChar.map_zero]
  simp only [secondInputCoefficient,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondPreColumn_zero_of_mask_label_mem (Ψ : Eis →* ℂ) (m c d e k : Eis)
    (H : Finset ι → ℂ) (S : Finset ι) (i : ι) (hi : i ∈ S)
    (hc : m*c ∈ Ideal.span {p i}) : secondPreColumn p hg Ψ m c d e k H S = 0 := by
  rcases (inferInstance : (Ideal.span {p i}).IsPrime).mem_or_mem hc with hm|hc
  · have hz : primeCoprimeMask p S m = 0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (fun h => h i hi (Ideal.mem_span_singleton.mp hm))
    simp only [secondPreColumn,hz,mul_zero,zero_mul]
  · have hr : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S c = 0 := by
      apply Finset.prod_eq_zero hi
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hc,MulChar.map_zero]
    simp only [secondPreColumn,hr,zero_pow (by decide : (4:ℕ) ≠ 0),mul_zero,zero_mul]

theorem secondSignedSourceWeight_nonzero_masks
    (Ψ : Eis →* ℂ) (m c d : Eis) (z : SecondRayIndex) (x : SecondExpansionData ι)
    (hE : x.divisor ⊆ x.sourceCommon)
    (hw : secondSignedSourceWeight p hg Ψ m c d z x ≠ 0) :
    IsCoprime (sourceIdeal p x.sourceCommon) (Ideal.span {c}) ∧
    IsCoprime (sourceIdeal p x.overlap) (sourceIdeal p x.sourceCommon * Ideal.span {c}) := by
  constructor
  · apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    have hz := secondInputCoefficient_zero_of_label_mem p hg Ψ m c d (fun _ => 1) x.sourceCommon i hi hc
    apply hw
    simp only [secondSignedSourceWeight,hz,norm_zero,zero_pow (by decide : (2:ℕ) ≠ 0),
      Complex.ofReal_zero,zero_mul]
  · change IsCoprime (sourceIdeal p x.overlap) (Ideal.span {∏ i ∈ x.sourceCommon,p i} * Ideal.span {c})
    rw [Ideal.span_singleton_mul_span_singleton]
    apply sourceIdeal_coprime_of_not_mem p
    intro i hi hc
    let e := (∏ i ∈ x.divisor,p i)
    let r := secondExpansionQuotient p x
    have her : e*r = ∏ j ∈ x.sourceCommon,p j := by
      dsimp only [r]
      rw [secondExpansionQuotient_of_subset p x hE]
      exact (secondMaskQuotient_spec p _ _ hE).symm
    have hmc : (m*(e*r))*c ∈ Ideal.span {p i} := by
      rw [her,mul_assoc]
      exact Ideal.mul_mem_left _ m hc
    have hz := secondPreColumn_zero_of_mask_label_mem p hg (secondRayPlus Ψ z)
      (m*(e*r)) c d e (-x.frequency) (fun _ => 1) x.overlap i hi hmc
    dsimp only [e,r] at hz
    apply hw
    simp only [secondSignedSourceWeight,secondCommonWeight,hz,mul_zero]

def actualSecondSignedWeight {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ℂ :=
  let d := (∏ i ∈ x.firstDivisor,p i)
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  secondSignedSourceWeight p hg Ψ
    (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit*d) c d z x.second

include hp in
theorem actualSecondSignedWeight_norm_le_one
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn) : ‖actualSecondSignedWeight p hg Ψ m z x‖ ≤ 1 :=
  secondSignedSourceWeight_norm_le_one p hp hg hinj hc Ψ hΨ _ _ _ z x.second

include hcop in
theorem actual_second_nonzero_weight_squarefree
    {Jo Jn : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon)
    (hw : actualSecondSignedWeight p hg Ψ m z x ≠ 0) (u v : Eisˣ) :
    Squarefree (actualSecondChild p u v x).2.1 := by
  let J : Ideal Eis := Ideal.span {jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}
  let C := sourceIdeal p x.firstCommon
  let E := sourceIdeal p x.second.divisor
  let G := sourceIdeal p x.second.sourceCommon
  let V := sourceIdeal p x.second.overlap
  have hj : J ∣ sourceIdeal p x.cube.support := jLabel_span_dvd_source p _ _ _ _
  have hJ : Squarefree J := (sourceIdeal_squarefree p hcop x.cube.support).squarefree_of_dvd hj
  have hC : Squarefree C := sourceIdeal_squarefree p hcop _
  have hG : Squarefree G := sourceIdeal_squarefree p hcop _
  have hV : Squarefree V := sourceIdeal_squarefree p hcop _
  have hJC : IsCoprime J C :=
    (sourceIdeal_coprime_of_disjoint p hcop x.cube.support x.firstCommon hCB.symm).of_isCoprime_of_dvd_left hj
  have hdg : E ∣ G := sourceIdeal_dvd p _ _ hE
  have hcspan : Ideal.span {(∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit} = C*J :=
    (Ideal.span_singleton_mul_span_singleton _ _).symm
  obtain ⟨hgmask,hvmask⟩ := secondSignedSourceWeight_nonzero_masks p hg Ψ _ _ _ z x.second hE hw
  rw [hcspan] at hgmask hvmask
  change IsCoprime G (C*J) at hgmask
  change IsCoprime V (G*(C*J)) at hvmask
  have heJC : IsCoprime E (J*C) := by
    simpa only [mul_comm] using hgmask.of_isCoprime_of_dvd_left hdg
  have hdiv : J*C*E ∣ G*(C*J) := by
    obtain ⟨r,hr⟩ := hdg
    refine ⟨r,?_⟩
    rw [hr]
    ring
  have hvJCE := hvmask.of_isCoprime_of_dvd_right hdiv
  change Squarefree (J*C*E*V)
  exact squarefree_mul_iff.mpr ⟨hvJCE.symm.isRelPrime,
    squarefree_mul_iff.mpr ⟨heJC.symm.isRelPrime,
      squarefree_mul_iff.mpr ⟨hJC.isRelPrime,hJ,hC⟩,hG.squarefree_of_dvd hdg⟩,hV⟩

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment InverseSecondFibers
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem primaryIdealGenerator_primeProduct
    (hpr : ∀ i, lambda^2 ∣ p i-1) (S : Finset ι) (v : ι → ℕ) :
    primaryIdealGenerator (Ideal.span {primeProduct p S v}) = primeProduct p S v := by
  apply primaryIdealGenerator_span _ (primeProduct_ne_zero p hp S v)
  unfold primeProduct
  induction S using Finset.induction_on with
  | empty => simp
  | @insert i S hi ih =>
    rw [Finset.prod_insert hi]
    have hpow : lambda^2 ∣ p i^v i-1 := by
      simpa only [one_pow] using (hpr i).trans (sub_dvd_pow_sub_pow (p i) 1 (v i))
    have he : p i^v i*(∏ j ∈ S,p j^v j)-1 =
        (p i^v i-1)*(∏ j ∈ S,p j^v j)+((∏ j ∈ S,p j^v j)-1) := by ring
    rw [he]
    exact dvd_add (dvd_mul_of_dvd_left hpow _) ih

def actualSecondPuncture (m : Eis) (γ : OuterTriple) : Eis :=
  (m*primaryIdealGenerator γ.q0)*primaryIdealGenerator γ.residual

def actualSecondRawLabel {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  ((∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
    (∏ i ∈ x.second.divisor,p i) * ∏ i ∈ x.second.overlap,p i

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_mask_span (F : Finset ι) (Ψ : Eis →* ℂ)
    (m₁ m₂ f k : Eis) (he : Ideal.span {m₁}=Ideal.span {m₂})
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ m₁ f k slots lists a W X =
      finiteCanonicalMarkedRow p hg F Ψ m₂ f k slots lists a W X :=
  fixedChildRow_congr_mask_span p hg F Ψ he _ f k

theorem actual_second_puncture_span
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) :
    Ideal.span {((m*b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit)*
      secondExpansionQuotient p x.second)} =
    Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} := by
  change Ideal.span {(m*b0Label p _ _ _ _)*secondExpansionQuotient p x.second} =
    Ideal.span {(m*primaryIdealGenerator (Ideal.span {b0Label p _ _ _ _}))*
      primaryIdealGenerator (sourceIdeal p (x.second.sourceCommon\x.second.divisor))}
  rw [show primaryIdealGenerator (Ideal.span {b0Label p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryIdealGenerator_primeProduct p hp hpr _ _,
    sourceIdeal_gen p hp hpr,secondExpansionQuotient_of_subset p x.second hE]
  simp only [←Ideal.span_singleton_mul_span_singleton,secondMaskQuotient_span,sourceIdeal,
    span_finset_prime_product]

theorem actual_second_generator_sectors
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    ∃ u v : Eisˣ,
      actualSecondRawLabel p x = (u:Eis)*primaryIdealGenerator (actualSecondChild p u v x).2.1 ∧
      (∏ i ∈ x.firstDivisor,p i) *
        (∏ i ∈ x.second.divisor,p i) =
        (v:Eis)*(primaryIdealGenerator (sourceIdeal p x.firstDivisor)*primaryIdealGenerator (sourceIdeal p x.second.divisor)) := by
  let L := (markedSecondOriginal p x).J * sourceIdeal p x.firstCommon *
    sourceIdeal p x.second.divisor * sourceIdeal p x.second.overlap
  have hs (S : Finset ι) : Ideal.span {∏ i ∈ S,p i} = sourceIdeal p S := rfl
  have hl : Ideal.span {actualSecondRawLabel p x} = L := by
    unfold actualSecondRawLabel L
    simp only [←Ideal.span_singleton_mul_span_singleton,sourceIdeal,markedSecondOriginal,cubeSecondSource]
    ring
  have hgp (S : Finset ι) : primaryIdealGenerator (sourceIdeal p S) ≠ 0 := by
    rw [sourceIdeal_gen p hp hpr]
    exact Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hL : primaryIdealGenerator L ≠ 0 := by
    dsimp only [L]
    rw [primaryIdealGenerator_mul,primaryIdealGenerator_mul,primaryIdealGenerator_mul]
    apply mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ (hgp _)) (hgp _)) (hgp _)
    change primaryIdealGenerator (Ideal.span {jLabel p _ _ _ _}) ≠ 0
    rw [show primaryIdealGenerator (Ideal.span {jLabel p x.cube.support
      (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}) =
      jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit from primaryIdealGenerator_primeProduct p hp hpr _ _]
    exact primeProduct_ne_zero p hp _ _
  obtain ⟨u,v,hu,hv⟩ := exists_second_generator_sectors (actualSecondRawLabel p x)
    ((∏ i ∈ x.firstDivisor,p i))
    ((∏ i ∈ x.second.divisor,p i))
    L (sourceIdeal p x.firstDivisor) (sourceIdeal p x.second.divisor)
    hl (hs _) (hs _) hL (hgp _) (hgp _)
  exact ⟨u,v,hu,hv⟩

theorem actual_second_canonical_child
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
    finiteCanonicalMarkedRow p hg F Ψ
      ((m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit)*secondExpansionQuotient p x.second)
      (actualSecondRawLabel p x)
      ((∏ i ∈ x.firstDivisor,p i) *
        (∏ i ∈ x.second.divisor,p i) * k)
      slots lists a W X =
    secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
      slots lists a (fun _ => W) X
      (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hu,hv⟩ := actual_second_generator_sectors p hp hpr x
  refine ⟨u,v,?_⟩
  intro F Ψ m k slots lists a W X
  rw [secondCanonical_generator_transport p hg F Ψ _ _ _ _ _ _ _ _ u v hu hv]
  exact finiteCanonicalMarkedRow_mask_span p hp hg F Ψ _ _ _ _
    (actual_second_puncture_span p hp hpr x hE u v m) slots lists a W X

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment InverseSecondFibers
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def actualMarkedSecondProfileData {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) (A₁ A₂ : Finset ι) : SecondProfileData ι :=
  let d := (∏ i ∈ x.firstDivisor,p i)
  let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
  expansionProfileData p Ψ (m*b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit*d)
    c d z A₁ A₂ x.second

theorem actual_second_split_child_uniform
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m k : Eis)
      (A : Finset ι), A ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon →
      ∀ (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (W : ℝ → ℂ) (X : ℝ),
      let d := (∏ i ∈ x.firstDivisor,p i)
      let e := (∏ i ∈ x.second.divisor,p i)
      let c := (∏ i ∈ x.firstCommon,p i)*jLabel p x.cube.support
        (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
      canonicalMarkedSplit p hg F x.second.overlap A Ψ
        (m*b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
          x.cube.leftBit x.cube.rightBit*d)
        (secondExpansionQuotient p x.second) c d e k slots lists a W
        (primeProductNorm p x.second.overlap*X) =
      ∑ J ∈ slots.powerset, primeMark J lists a (A∪x.second.overlap) *
        secondCanonicalPolynomial p hp hcop hg F (fun _ => Ψ) (actualSecondPuncture m)
          (slots\J) lists a (fun _ => W) X
          (actualSecondChild p u v {x with second := {x.second with frequency := k}}) := by
  obtain ⟨u,v,hchild⟩ := actual_second_canonical_child p hp hcop hg hpr (σ:=σ) x hE
  refine ⟨u,v,?_⟩
  intro F Ψ m k A hA slots lists a W X
  dsimp only
  rw [secondExpansionQuotient_of_subset p x.second hE]
  rw [actual_second_split_fixed_family p hp hg F x.cube.support x.firstCommon
    x.firstDivisor x.second.sourceCommon x.second.divisor x.second.overlap A hCB hD hE hA
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit
    x.cube.support_pos Ψ m k slots lists a W X]
  apply Finset.sum_congr rfl
  intro J hJ
  congr 1
  simpa only [actualSecondRawLabel,secondExpansionQuotient_of_subset p x.second hE] using
    hchild F Ψ m k (slots\J) lists a W X

theorem actual_second_separated_pair_canonical
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hCB : Disjoint x.firstCommon x.cube.support)
    (hD : x.firstDivisor ⊆ x.firstCommon∪x.cube.support)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) :
    ∃ u v : Eisˣ, ∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}}) := by
  obtain ⟨u,v,hsplit⟩ := actual_second_split_child_uniform p hp hcop hg hpr (σ:=σ) x hCB hD hE
  refine ⟨u,v,?_⟩
  intro F Ψ m z A₁ A₂ hA₁ hA₂ slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t
  dsimp only
  have hA (A : Finset ι) (ha : A ⊆ x.cube.support∪x.firstCommon) :
      A∪x.second.sourceCommon ⊆ (x.cube.support∪x.firstCommon)∪x.second.sourceCommon :=
    Finset.union_subset_union_left ha
  unfold secondSeparatedPair
  dsimp only [actualMarkedSecondProfileData,expansionProfileData]
  rw [hsplit F (secondRayMinus Ψ z) m x.second.frequency _ (hA A₁ hA₁),
    hsplit F (secondRayPlus Ψ z) m (-x.second.frequency) _ (hA A₂ hA₂)]
  simp only [star_sum,star_mul,Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J₁ hJ₁
  apply Finset.sum_congr rfl
  intro J₂ hJ₂
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0)
    (newAssigned : Fin Jn → ι) : MarkedSecondSource ι Jo Jn where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := newAssigned

omit [DecidableEq ι] in
theorem attachSecondSlots_injective {Jo Jn : ℕ} :
    Function.Injective (fun q : MarkedSecondSource ι Jo 0 × (Fin Jn → ι) => attachSecondSlots q.1 q.2) := by
  intro q r h
  apply Prod.ext
  · apply MarkedSecondSource.ext
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.cube) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstCommon) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.firstDivisor) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.second) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.quotient) h
    · exact congrArg (fun z : MarkedSecondSource ι Jo Jn => z.oldAssigned) h
    · funext i; exact Fin.elim0 i
  · exact congrArg MarkedSecondSource.newAssigned h

def attachPairedSlots {Jo : ℕ} (J₁ J₂ : Finset σ)
    (q : MarkedSecondSource ι Jo 0 × ((∀ i ∈ J₁, ι) × (∀ i ∈ J₂, ι))) :
    MarkedSecondSource ι Jo (J₁.card+J₂.card) :=
  attachSecondSlots q.1 (pairedSlotAssignment J₁ J₂ q.2)

omit [DecidableEq ι] [DecidableEq σ] in
theorem attachPairedSlots_injective {Jo : ℕ} (J₁ J₂ : Finset σ) :
    Function.Injective (attachPairedSlots (ι:=ι) (Jo:=Jo) J₁ J₂) := by
  intro q r h
  have he := @attachSecondSlots_injective ι Jo (J₁.card+J₂.card)
    (q.1,pairedSlotAssignment J₁ J₂ q.2) (r.1,pairedSlotAssignment J₁ J₂ r.2) h
  exact Prod.ext (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.1) he)
    (pairedSlotAssignment_injective J₁ J₂
      (congrArg (fun z : MarkedSecondSource ι Jo 0 × (Fin (J₁.card+J₂.card) → ι) => z.2) he))

def assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    Finset (MarkedSecondSource ι Jo (J₁.card+J₂.card)) :=
  ((source ×ˢ ((J₁.pi (fun i => L₁ i)) ×ˢ (J₂.pi (fun i => L₂ i)))).filter
    (fun q => ∀ j, pairedSlotAssignment J₁ J₂ q.2 j ∈ q.1.second.sourceCommon∪q.1.second.overlap)).image
      (attachPairedSlots J₁ J₂)

theorem mem_assignedSecondSource {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) :
    x ∈ assignedSecondSource source J₁ J₂ L₁ L₂ ↔
      ∃ y ∈ source, ∃ q₁ ∈ J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap)),
      ∃ q₂ ∈ J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap)),
        attachPairedSlots J₁ J₂ (y,(q₁,q₂)) = x := by
  constructor
  · intro hx
    obtain ⟨⟨y,q₁,q₂⟩,hmem,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hs⟩ := Finset.mem_filter.mp hmem
    obtain ⟨hy,hq⟩ := Finset.mem_product.mp hmem
    obtain ⟨hq₁,hq₂⟩ := Finset.mem_product.mp hq
    refine ⟨y,hy,q₁,Finset.mem_pi.mpr ?_,q₂,Finset.mem_pi.mpr ?_,rfl⟩
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₁ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩))
    · intro i hi
      refine Finset.mem_inter.mpr ⟨Finset.mem_pi.mp hq₂ i hi,?_⟩
      simpa [pairedSlotAssignment,indexedSlotAssignment] using hs (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩))
  · rintro ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩
    apply Finset.mem_image.mpr
    refine ⟨(y,(q₁,q₂)),Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hy,Finset.mem_product.mpr ⟨?_,?_⟩⟩,?_⟩,rfl⟩
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₁ i hi)).1)
    · exact Finset.mem_pi.mpr (fun i hi => (Finset.mem_inter.mp (Finset.mem_pi.mp hq₂ i hi)).1)
    · intro j
      refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simpa only [pairedSlotAssignment,Fin.addCases_left] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₁ L₁ _ q₁ hq₁ k)).2
      · simpa only [pairedSlotAssignment,Fin.addCases_right] using
          (Finset.mem_inter.mp (indexedSlotAssignment_support J₂ L₂ _ q₂ hq₂ k)).2

theorem assignedSecondSource_conditions (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    ActualSecondSourceConditions p (assignedSecondSource source J₁ J₂ L₁ L₂) := by
  have hmem : ∀ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      ∃ y ∈ source, ∃ q, attachPairedSlots J₁ J₂ (y,q)=x ∧
        ∀ j, pairedSlotAssignment J₁ J₂ q j ∈ y.second.sourceCommon∪y.second.overlap := by
    intro x hx
    obtain ⟨⟨y,q⟩,hmem,he⟩ := Finset.mem_image.mp hx
    obtain ⟨hmem,hq⟩ := Finset.mem_filter.mp hmem
    exact ⟨y,(Finset.mem_product.mp hmem).1,q,he,hq⟩
  constructor
  all_goals
    intro x hx
    obtain ⟨y,hy,q,rfl,hq⟩ := hmem x hx
  · exact hs.admissible y hy
  · exact hs.common_disjoint y hy
  · exact hs.first_divisor y hy
  · exact hs.second_divisor y hy
  · exact hs.old_support y hy
  · exact hq
  · exact hs.quotient_nonzero y hy

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]

def eraseSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : MarkedSecondSource ι Jo 0 where
  cube := x.cube
  firstCommon := x.firstCommon
  firstDivisor := x.firstDivisor
  second := x.second
  quotient := x.quotient
  oldAssigned := x.oldAssigned
  newAssigned := Fin.elim0

omit [DecidableEq ι] in
@[simp] theorem erase_attachSecondSlots {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo 0) (a : Fin Jn → ι) :
    eraseSecondSlots (attachSecondSlots x a) = x := by
  apply MarkedSecondSource.ext <;> try rfl
  funext i
  exact Fin.elim0 i

def assignedSecondCoefficient {Jo : ℕ} (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card)) : ℂ :=
  star (slotAssignmentWeight J₁ a₁
    (fun i hi => x.newAssigned (Fin.castAdd J₂.card (J₁.equivFin ⟨i,hi⟩)))) *
    slotAssignmentWeight J₂ a₂
    (fun i hi => x.newAssigned (Fin.natAdd J₁.card (J₂.equivFin ⟨i,hi⟩)))

omit [DecidableEq ι] [DecidableEq σ] in
@[simp] theorem assignedSecondCoefficient_attach {Jo : ℕ}
    (J₁ J₂ : Finset σ) (a₁ a₂ : σ → ι → ℂ)
    (x : MarkedSecondSource ι Jo 0) (q : (∀ i ∈ J₁,ι) × (∀ i ∈ J₂,ι)) :
    assignedSecondCoefficient J₁ J₂ a₁ a₂ (attachPairedSlots J₁ J₂ (x,q)) =
      pairedSlotWeight J₁ J₂ a₁ a₂ q := by
  simp only [assignedSecondCoefficient,attachPairedSlots,attachSecondSlots,
    pairedSlotAssignment,Fin.addCases_left,Fin.addCases_right,indexedSlotAssignment_apply,pairedSlotWeight]

theorem assignedSecondSource_sum {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι)
    (F : MarkedSecondSource ι Jo (J₁.card+J₂.card) → ℂ) :
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂, F x =
      ∑ y ∈ source, ∑ q ∈
        (J₁.pi (fun i => L₁ i∩(y.second.sourceCommon∪y.second.overlap))) ×ˢ
        (J₂.pi (fun i => L₂ i∩(y.second.sourceCommon∪y.second.overlap))),
          F (attachPairedSlots J₁ J₂ (y,q)) := by
  rw [assignedSecondSource,Finset.sum_image (fun q _ r _ h => attachPairedSlots_injective J₁ J₂ h),
    Finset.sum_filter,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro y hy
  rw [←Finset.sum_filter]
  dsimp only
  rw [paired_assignment_filter]

theorem assignedSecondSource_sum_marks {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (w P : MarkedSecondSource ι Jo 0 → ℂ) :
    (∑ y ∈ source, w y * (star (primeMark J₁ L₁ a₁ (y.second.sourceCommon∪y.second.overlap)) *
      primeMark J₂ L₂ a₂ (y.second.sourceCommon∪y.second.overlap)) * P y) =
    ∑ x ∈ assignedSecondSource source J₁ J₂ L₁ L₂,
      (w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x) * P (eraseSecondSlots x) := by
  rw [assignedSecondSource_sum]
  apply Finset.sum_congr rfl
  intro y hy
  rw [paired_primeMark_assignments]
  simp only [Finset.mul_sum,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro q hq
  rw [assignedSecondCoefficient_attach]
  simp only [attachPairedSlots,erase_attachSecondSlots]

theorem assignedSecondCoefficient_norm_le_one {Jo : ℕ}
    (source : Finset (MarkedSecondSource ι Jo 0)) (J₁ J₂ : Finset σ)
    (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ p ∈ L₁ i, ‖a₁ i p‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ p ∈ L₂ i, ‖a₂ i p‖ ≤ 1)
    (x : MarkedSecondSource ι Jo (J₁.card+J₂.card))
    (hx : x ∈ assignedSecondSource source J₁ J₂ L₁ L₂) :
    ‖assignedSecondCoefficient J₁ J₂ a₁ a₂ x‖ ≤ 1 := by
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
  rw [assignedSecondCoefficient_attach]
  exact pairedSlotWeight_norm_le_one J₁ J₂ L₁ L₂ a₁ a₂ _ (q₁,q₂)
    (Finset.mem_product.mpr ⟨hq₁,hq₂⟩) ha₁ ha₂

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open Eisenstein SchwartzPlanePoisson InverseInitialRayAttachment InverseSecondFibers
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem actualSecondChild_erase {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v (eraseSecondSlots x) = actualSecondChild p u v x := rfl

theorem actualSecondChild_neg_frequency {Jo Jn : ℕ} (u v : Eisˣ) (x : MarkedSecondSource ι Jo Jn) :
    actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}} =
      ((actualSecondChild p u v x).1,(actualSecondChild p u v x).2.1,-(actualSecondChild p u v x).2.2) := by
  simp only [actualSecondChild,secondChild,originalSecondTuple,markedSecondOriginal,cubeSecondSource,
    secondUnitFrequency_neg,mul_neg]

include hp hcop in
theorem actual_second_marked_weighted_count
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source, ‖w x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, w x *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K labels rows G γ) := by
  let S := assignedSecondSource source J₁ J₂ L₁ L₂
  let w' := fun x : MarkedSecondSource ι Jo (J₁.card+J₂.card) =>
    w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x
  have hs' : ActualSecondSourceConditions p S := assignedSecondSource_conditions p source hs J₁ J₂ L₁ L₂
  have herase : ∀ x ∈ S, eraseSecondSlots x ∈ source := by
    intro x hx
    obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,rfl⟩ := (mem_assignedSecondSource source J₁ J₂ L₁ L₂ x).mp hx
    simpa only [attachPairedSlots,erase_attachSecondSlots] using hy
  have hw' : ∀ x ∈ S, ‖w' x‖ ≤ 1 := by
    intro x hx
    rw [show w' x = w (eraseSecondSlots x)*assignedSecondCoefficient J₁ J₂ a₁ a₂ x from rfl,norm_mul]
    exact (mul_le_of_le_one_left (norm_nonneg _) (hw _ (herase x hx))).trans
      (assignedSecondCoefficient_norm_le_one source J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ x hx)
  have hc' : ∀ x ∈ S, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows := by
    intro x hx
    simpa only [actualSecondChild_erase] using hchild (eraseSecondSlots x) (herase x hx)
  have he := assignedSecondSource_sum_marks source J₁ J₂ L₁ L₂ a₁ a₂ w
    (fun x => F (actualSecondChild p u v x)*star (G (actualSecondChild p u v x)))
  simp only [actualSecondChild_erase,←mul_assoc] at he
  simp only [←mul_assoc]
  rw [he]
  exact actual_second_weighted_count p hp hpr hcop hinj u v S hs' labels rows hc' K ho
    (by omega) w' hw' F G

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem ActualSecondSourceConditions.mono {Jo Jn : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (h : ActualSecondSourceConditions p S)
    (hTS : T ⊆ S) : ActualSecondSourceConditions p T where
  admissible x hx := h.admissible x (hTS hx)
  common_disjoint x hx := h.common_disjoint x (hTS hx)
  first_divisor x hx := h.first_divisor x (hTS hx)
  second_divisor x hx := h.second_divisor x (hTS hx)
  old_support x hx := h.old_support x (hTS hx)
  new_support x hx := h.new_support x (hTS hx)
  quotient_nonzero x hx := h.quotient_nonzero x (hTS hx)

def actualSecondSurvivingSource {Jo : ℕ} (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (source : Finset (MarkedSecondSource ι Jo 0)) : Finset (MarkedSecondSource ι Jo 0) :=
  source.filter (fun x => actualSecondSignedWeight p hg Ψ m z x ≠ 0)

theorem assignedSecondSource_mono {Jo : ℕ}
    {S T : Finset (MarkedSecondSource ι Jo 0)} (hST : S ⊆ T)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) :
    assignedSecondSource S J₁ J₂ L₁ L₂ ⊆ assignedSecondSource T J₁ J₂ L₁ L₂ := by
  intro x hx
  obtain ⟨y,hy,q₁,hq₁,q₂,hq₂,he⟩ := (mem_assignedSecondSource S J₁ J₂ L₁ L₂ x).mp hx
  exact (mem_assignedSecondSource T J₁ J₂ L₁ L₂ x).mpr ⟨y,hST hy,q₁,hq₁,q₂,hq₂,he⟩

theorem actualSecondTriples_mono {Jo Jn : ℕ} (u v : Eisˣ)
    {S T : Finset (MarkedSecondSource ι Jo Jn)} (hST : S ⊆ T) :
    actualSecondTriples p u v S ⊆ actualSecondTriples p u v T :=
  Finset.image_subset_image hST

include hp hcop in
theorem actual_second_supported_marked_energy
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := actualSecondSurvivingSource p hg Ψ m z source
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hg Ψ m z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hg Ψ m z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hcop hg Ψ m z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hg Ψ m z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hg hinj hc Ψ hΨ m z x)).trans
          (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers
noncomputable section
local notation "Eis" => Eisenstein.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def SecondPairCanonicalAt {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) : Prop :=
∀ (F : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
      (A₁ A₂ : Finset ι), A₁ ⊆ x.cube.support∪x.firstCommon → A₂ ⊆ x.cube.support∪x.firstCommon →
      ∀ (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
      (ω₁ ω₂ : ℝ → ℂ) (G₀ E₀ V₀ K₀ X₀ : ℝ) (t : JointLogSeparation.Frequency × (Fin 6 → ℝ)),
      let h := profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2
      let data := actualMarkedSecondProfileData p x Ψ m z A₁ A₂
      secondSeparatedPair p hg F data slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G₀ E₀ V₀ K₀ X₀ t =
      secondOuterPhase h (secondRelativeLog (secondActualNorms p data ∅ ∅) G₀ E₀ V₀ K₀ X₀) *
        ∑ J₁ ∈ slots₁.powerset, ∑ J₂ ∈ slots₂.powerset,
          (star (primeMark J₁ lists₁ a₁ ((A₁∪x.second.sourceCommon)∪x.second.overlap)) *
            primeMark J₂ lists₂ a₂ ((A₂∪x.second.sourceCommon)∪x.second.overlap)) *
          star (secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayMinus Ψ z)
            (actualSecondPuncture m) (slots₁\J₁) lists₁ a₁ (fun _ => childLogTest ω₁ (-h 4)) X₀
            (actualSecondChild p u v x)) *
          secondCanonicalPolynomial p hp hcop hg F (fun _ => secondRayPlus Ψ z)
            (actualSecondPuncture m) (slots₂\J₂) lists₂ a₂ (fun _ => childLogTest ω₂ (h 5)) X₀
            (actualSecondChild p u v {x with second := {x.second with frequency := -x.second.frequency}})

theorem exists_second_uniform_sectors
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ x ∈ source, SecondPairCanonicalAt (σ:=σ) p hp hcop hg x (sector x).1 (sector x).2 := by
  have he (x : {x // x ∈ source}) :=
    actual_second_separated_pair_canonical p hp hcop hg hpr (σ:=σ) x.val
      (hs.common_disjoint x.val x.property) (hs.first_divisor x.val x.property)
      (hs.second_divisor x.val x.property)
  choose u v hu using he
  let sector := fun x => if hx : x ∈ source then (u ⟨x,hx⟩,v ⟨x,hx⟩) else (1,1)
  refine ⟨sector,?_⟩
  intro x hx
  simpa only [sector,dif_pos hx,SecondPairCanonicalAt] using hu ⟨x,hx⟩

def secondSourceSector {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (uv : Eisˣ × Eisˣ) :
    Finset (MarkedSecondSource ι Jo Jn) := source.filter (fun x => sector x = uv)

omit [DecidableEq ι] in
theorem secondSourceSector_partition {Jo Jn : ℕ}
    (source : Finset (MarkedSecondSource ι Jo Jn))
    (sector : MarkedSecondSource ι Jo Jn → Eisˣ × Eisˣ) (H : MarkedSecondSource ι Jo Jn → ℂ) :
    ∑ x ∈ source,H x = ∑ uv : Eisˣ × Eisˣ,∑ x ∈ secondSourceSector source sector uv,H x :=
  (Finset.sum_fiberwise source sector H).symm


end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen sourceIdeal_ne_zero)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem primeCoprimeMask_radical_generator (S : Finset ι) (a : Eis) :
    primeCoprimeMask p S a =
      primeCoprimeMask p S
        (cubicIdealGenerator (Ideal.span {a}).radical) := by
  have he (i : ι) : a ∈ Ideal.span {p i} ↔
      cubicIdealGenerator (Ideal.span {a}).radical ∈ Ideal.span {p i} := by
    rw [←Ideal.span_singleton_le_iff_mem,←Ideal.span_singleton_le_iff_mem,
      span_cubicIdealGenerator]
    exact (inferInstance : (Ideal.span {p i}).IsPrime).radical_le_iff.symm
  simp only [primeCoprimeMask_indicator]
  congr 1
  apply propext
  apply forall_congr'
  intro i
  apply forall_congr'
  intro _
  exact not_congr (by simpa only [←Ideal.mem_span_singleton] using he i)

omit [DecidableEq σ] in
theorem finiteCanonicalMarkedRow_radical_puncture (F : Finset ι) (Ψ : Eis →* ℂ)
    (m f k : Eis) (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : ℝ → ℂ) (X : ℝ) :
    finiteCanonicalMarkedRow p hg F Ψ m f k slots lists a W X =
      finiteCanonicalMarkedRow p hg F Ψ
        (cubicIdealGenerator (Ideal.span {m}).radical) f k slots lists a W X := by
  simp only [finiteCanonicalMarkedRow,fixedChildRow,secondChildColumn,
    ←primeCoprimeMask_radical_generator p]

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem sourceIdeal_le_radical_primeProduct (B : Finset ι) (v : ι → ℕ) :
    sourceIdeal p B ≤ (Ideal.span {primeProduct p B v} : Ideal Eis).radical := by
  simp only [sourceIdeal,primeProduct,span_finset_prime_product,←Ideal.span_singleton_pow]
  induction B using Finset.induction_on with
  | empty => simp
  | @insert i B hi ih =>
    rw [Finset.prod_insert hi,Finset.prod_insert hi,Ideal.radical_mul]
    apply le_inf
    · apply (show Ideal.span {p i} * (∏ j ∈ B, Ideal.span {p j}) ≤ Ideal.span {p i} from Ideal.mul_le_right).trans
      by_cases hv : v i = 0
      · rw [hv,pow_zero,Ideal.one_eq_top]
        exact le_trans le_top Ideal.le_radical
      · rw [Ideal.radical_pow _ hv]
        exact Ideal.le_radical
    · exact Ideal.mul_le_left.trans ih

theorem actual_second_q0_radical_norm (hp : ∀ i, p i ≠ 0)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    (Ideal.absNorm (actualSecondChild p u v x).1.q0.radical : ℝ) ≤
      primeProductNorm p x.cube.support := by
  have hd := Ideal.absNorm_dvd_absNorm_of_le (sourceIdeal_le_radical_primeProduct p x.cube.support
    (fun i => b0Exponent (x.cube.leftExponent i+x.cube.rightExponent i) (x.cube.leftBit i) (x.cube.rightBit i)))
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (sourceIdeal_ne_zero p hp x.cube.support))) hd
  change (Ideal.absNorm (Ideal.span {b0Label p x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit}).radical : ℝ) ≤ _
  have he : (Ideal.absNorm (sourceIdeal p x.cube.support) : ℝ) = primeProductNorm p x.cube.support := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ x.cube.support,p i)).symm
  rw [←he]
  exact_mod_cast hb

def actualSecondRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  cubicIdealGenerator (Ideal.span {actualSecondPuncture m γ}).radical

theorem secondCanonicalPolynomial_radical_puncture
    (F : Finset ι) (Ψ : InverseSecondFibers.OuterTriple → Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (W : InverseSecondFibers.OuterTriple → ℝ → ℂ) (X : ℝ) (c : SecondChild) :
    secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondPuncture m) slots lists a W X c =
      secondCanonicalPolynomial p hp hcop hg F Ψ (actualSecondRadicalPuncture m) slots lists a W X c :=
  finiteCanonicalMarkedRow_radical_puncture p hg F (Ψ c.1) _ _ _ slots lists a (W c.1) X

theorem radical_product_norm_le (I J B R : Ideal Eis) (hI : I ≠ 0) (hB : B ≠ 0)
    (hR : R ≠ 0) (hBJ : B ≤ J.radical) :
    (Ideal.absNorm (I*J*R).radical : ℝ) ≤
      (Ideal.absNorm I.radical : ℝ)*Ideal.absNorm B*Ideal.absNorm R := by
  have hi : I.radical ≠ 0 := by
    intro he
    apply hI
    exact le_antisymm (he ▸ Ideal.le_radical) bot_le
  have hle : I.radical*B*R ≤ (I*J*R).radical := by
    rw [Ideal.radical_mul,Ideal.radical_mul]
    refine le_inf (le_inf ?_ ?_) ?_
    · exact (show I.radical*B*R ≤ I.radical*B from Ideal.mul_le_right).trans Ideal.mul_le_right
    · exact ((show I.radical*B*R ≤ I.radical*B from Ideal.mul_le_right).trans Ideal.mul_le_left).trans hBJ
    · exact (show I.radical*B*R ≤ R from Ideal.mul_le_left).trans Ideal.le_radical
  have hb := Nat.le_of_dvd (Nat.pos_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr
    (mul_ne_zero (mul_ne_zero hi hB) hR))) (Ideal.absNorm_dvd_absNorm_of_le hle)
  simpa only [map_mul,Nat.cast_mul] using (show (Ideal.absNorm (I*J*R).radical : ℝ) ≤
    Ideal.absNorm (I.radical*B*R) from by exact_mod_cast hb)

include hp in

theorem actual_second_radical_puncture_norm
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ringComplex (actualSecondRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hspan : Ideal.span {actualSecondPuncture m (actualSecondChild p u v x).1} =
      (Ideal.span {m} : Ideal Eis) *
      Ideal.span {b0Label p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
        x.cube.leftBit x.cube.rightBit} * sourceIdeal p (x.second.sourceCommon\x.second.divisor) := by
    rw [←actual_second_puncture_span p hp hpr x hE u v m]
    simp only [←Ideal.span_singleton_mul_span_singleton,secondExpansionQuotient_of_subset p x.second hE,
      secondMaskQuotient_span,sourceIdeal,span_finset_prime_product]
  rw [ringComplex_norm_sq_eq_absNorm_span]
  simp only [actualSecondRadicalPuncture,span_cubicIdealGenerator,hspan]
  have hn (S : Finset ι) : (Ideal.absNorm (sourceIdeal p S) : ℝ)=primeProductNorm p S := by
    simpa only [sourceIdeal,primeProductNorm,map_prod] using
      (ringComplex_norm_sq_eq_absNorm_span (∏ i ∈ S,p i)).symm
  rw [←hn x.cube.support,←hn (x.second.sourceCommon\x.second.divisor)]
  exact radical_product_norm_le _ _ _ _ (Ideal.span_singleton_eq_bot.not.mpr hm)
    (sourceIdeal_ne_zero p hp _) (sourceIdeal_ne_zero p hp _)
    (sourceIdeal_le_radical_primeProduct p _ _)

def actualSecondInheritedPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondPuncture (m*cubicIdealGenerator γ.quotient) γ

def actualSecondInheritedRadicalPuncture (m : Eis) (γ : InverseSecondFibers.OuterTriple) : Eis :=
  actualSecondRadicalPuncture (m*cubicIdealGenerator γ.quotient) γ

include hp in

theorem actual_second_inherited_puncture_norm
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (hE : x.second.divisor ⊆ x.second.sourceCommon) (ht : x.quotient ≠ 0)
    (u v : Eisˣ) (m : Eis) (hm : m ≠ 0) :
    ‖ringComplex (actualSecondInheritedRadicalPuncture m (actualSecondChild p u v x).1)‖^2 ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ) * Ideal.absNorm x.quotient *
        primeProductNorm p x.cube.support * primeProductNorm p (x.second.sourceCommon\x.second.divisor) := by
  have hm' := mul_ne_zero hm (cubicIdealGenerator_ne_zero x.quotient ht)
  have hb := actual_second_radical_puncture_norm p hp hpr x hE u v
    (m*cubicIdealGenerator x.quotient) hm'
  change ‖ringComplex (actualSecondRadicalPuncture
    (m*cubicIdealGenerator x.quotient) (actualSecondChild p u v x).1)‖^2 ≤ _
  apply hb.trans
  have ho : (Ideal.absNorm (Ideal.span {m*cubicIdealGenerator x.quotient}).radical : ℝ) ≤
      (Ideal.absNorm (Ideal.span {m} : Ideal Eis).radical : ℝ)*Ideal.absNorm x.quotient := by
    rw [←Ideal.span_singleton_mul_span_singleton,span_cubicIdealGenerator]
    simpa only [mul_one,map_one,Nat.cast_one] using radical_product_norm_le (Ideal.span {m}) 1 1 x.quotient
      (Ideal.span_singleton_eq_bot.not.mpr hm) one_ne_zero ht Ideal.le_radical
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right ho (primeProductNorm_pos p hp _).le) (primeProductNorm_pos p hp _).le

include hp in

theorem actualSecondTriples_q0_radical_bound
    {Jo Jn : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo Jn)) (B : ℝ)
    (hB : ∀ x ∈ source, primeProductNorm p x.cube.support ≤ B) :
    ∀ γ ∈ actualSecondTriples p u v source, (Ideal.absNorm γ.q0.radical : ℝ) ≤ B := by
  intro γ hγ
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hγ
  exact (actual_second_q0_radical_norm p hp x u v).trans (hB x hx)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers SecondPassArithmetic
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp hcop in
theorem actual_second_supported_marked_energy_varying_puncture
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : MarkedSecondSource ι Jo 0 → Eis) (z : SecondRayIndex)
    (J₁ J₂ : Finset σ) (L₁ L₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ L₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ L₂ i, ‖a₂ i q‖ ≤ 1)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis)
    (hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ rows)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (phase : MarkedSecondSource ι Jo 0 → ℂ) (hphase : ∀ x ∈ source, ‖phase x‖ ≤ 1)
    (F G : SecondChild → ℂ) :
    ‖∑ x ∈ source, (actualSecondSignedWeight p hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows F γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource
          source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows G γ) := by
  let S := source.filter (fun x => actualSecondSignedWeight p hg Ψ (m x) z x ≠ 0)
  have hsub : S ⊆ source := Finset.filter_subset _ _
  have he : (∑ x ∈ source, (actualSecondSignedWeight p hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x))) =
    ∑ x ∈ S, (actualSecondSignedWeight p hg Ψ (m x) z x * phase x) *
      (star (primeMark J₁ L₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
        primeMark J₂ L₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
      F (actualSecondChild p u v x) * star (G (actualSecondChild p u v x)) := by
    symm
    apply Finset.sum_subset hsub
    intro x hx hnx
    have hz : actualSecondSignedWeight p hg Ψ (m x) z x = 0 := by
      by_contra hh
      exact hnx (Finset.mem_filter.mpr ⟨hx,hh⟩)
    simp only [hz,zero_mul]
  rw [he]
  have hb := actual_second_marked_weighted_count p hp hcop hpr hinj u v S
    (hs.mono p hsub) J₁ J₂ L₁ L₂ a₁ a₂ ha₁ ha₂ (labels.filter Squarefree) rows
    (by
      intro x hx
      have hx0 := hsub hx
      refine ⟨Finset.mem_filter.mpr ⟨(hchild x hx0).1,?_⟩,(hchild x hx0).2⟩
      exact actual_second_nonzero_weight_squarefree p hcop hg Ψ (m x) z x
        (hs.common_disjoint x hx0) (hs.second_divisor x hx0) (Finset.mem_filter.mp hx).2 u v)
    K ho hJ₁ hJ₂ (fun x => actualSecondSignedWeight p hg Ψ (m x) z x*phase x)
    (by
      intro x hx
      rw [norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _)
        (actualSecondSignedWeight_norm_le_one p hp hg hinj hc Ψ hΨ (m x) z x)).trans
        (hphase x (hsub hx))) F G
  apply hb.trans
  have hΓ := actualSecondTriples_mono p u v (assignedSecondSource_mono hsub J₁ J₂ L₁ L₂)
  have hsum (P : SecondChild → ℂ) :
      (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource S J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ) ≤
      ∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ L₁ L₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) rows P γ := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hΓ
    intro γ _ _
    exact mul_nonneg (tripleDivisorWeight_nonneg K γ) (secondLabelEnergy_nonneg _ _ _ _ _)
  exact mul_le_mul (Real.sqrt_le_sqrt (hsum F)) (Real.sqrt_le_sqrt (hsum G))
    (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers JointLogSeparation
noncomputable section
local notation "Eis" => Eisenstein.O
local instance : Fintype Eisˣ := @Fintype.ofFinite _ cubic_units_finite
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondInheritedProfile {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex) : SecondProfileData ι :=
  actualMarkedSecondProfileData p x Ψ (m*cubicIdealGenerator x.quotient) z ∅ ∅

def secondModeLeft (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (omega : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : SecondChild → ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest omega (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4)) X

def secondModeRight (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (omega : ℝ → ℂ) (X : ℝ) (t : Frequency × (Fin 6 → ℝ)) (c : SecondChild) : ℂ :=
  secondCanonicalPolynomial p hp hcop hg pool (fun _ => secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m) slots lists a
    (fun _ => childLogTest omega ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) X
    (c.1,c.2.1,-c.2.2)

def secondModeOuter {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn)
    (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondOuterPhase (profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2)
    (secondRelativeLog (secondActualNorms p (secondInheritedProfile p x Ψ m z) ∅ ∅) G E V B X)

def secondModeBranch {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) : ℂ :=
  secondModeOuter p x Ψ m z G E V B X t *
    (star (primeMark J₁ lists₁ a₁ (x.second.sourceCommon∪x.second.overlap)) *
      primeMark J₂ lists₂ a₂ (x.second.sourceCommon∪x.second.overlap)) *
    star (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t (actualSecondChild p u v x)) *
    secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t (actualSecondChild p u v x)

theorem second_inherited_mode_canonical {Jo Jn : ℕ}
    (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ)
    (hx : SecondPairCanonicalAt (σ:=σ) p hp hcop hg x u v)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ)) :
    secondSeparatedPair p hg pool (secondInheritedProfile p x Ψ m z)
      slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t =
    ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t := by
  have he := hx pool Ψ (m*cubicIdealGenerator x.quotient) z ∅ ∅
    (Finset.empty_subset _) (Finset.empty_subset _) slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t
  dsimp only at he
  have hq : (actualSecondChild p u v x).1.quotient = x.quotient := rfl
  simpa only [secondInheritedProfile,secondModeBranch,secondModeOuter,secondModeLeft,secondModeRight,
    secondCanonicalPolynomial,actualSecondInheritedPuncture,actualSecondChild_neg_frequency,
    Finset.empty_union,Finset.mul_sum,mul_assoc,hq] using he

theorem actual_second_modes_common_sectors
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo : ℕ} (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source) :
    ∃ sector : MarkedSecondSource ι Jo 0 → Eisˣ × Eisˣ,
      ∀ (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
        (slots₁ slots₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
        (ω₁ ω₂ : ℝ → ℂ) (G E V B X : ℝ) (t : Frequency × (Fin 6 → ℝ))
        (w : MarkedSecondSource ι Jo 0 → ℂ),
      (∑ x ∈ source,w x * secondSeparatedPair p hg pool (secondInheritedProfile p x Ψ m z)
        slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t) =
      ∑ uv : Eisˣ × Eisˣ, ∑ x ∈ secondSourceSector source sector uv, w x *
        ∑ J₁ ∈ slots₁.powerset,∑ J₂ ∈ slots₂.powerset,
          secondModeBranch p hp hcop hg x uv.1 uv.2 pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
            ω₁ ω₂ G E V B X t := by
  obtain ⟨sector,hsector⟩ := exists_second_uniform_sectors p hp hcop hg hpr (σ:=σ) source hs
  refine ⟨sector,?_⟩
  intro pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t w
  rw [secondSourceSector_partition source sector]
  apply Finset.sum_congr rfl
  intro uv huv
  apply Finset.sum_congr rfl
  intro x hx
  obtain ⟨hx,hxs⟩ := Finset.mem_filter.mp hx
  congr 1
  have hh := hsector x hx
  rw [hxs] at hh
  exact second_inherited_mode_canonical p hp hcop hg x uv.1 uv.2 hh
    pool Ψ m z slots₁ slots₂ lists₁ lists₂ a₁ a₂ ω₁ ω₂ G E V B X t

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open InverseInitialArithmetic (sourceIdeal sourceIdeal_gen)
open Eisenstein (ringComplex)
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι] (p : ι → Eis)
  (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

def actualSecondMultiplier {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) : Eis :=
  (∏ i ∈ x.firstDivisor,p i) *
    (∏ i ∈ x.second.divisor,p i)

include hp in
omit [DecidableEq ι] in
theorem actualSecondMultiplier_ne_zero {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) :
    actualSecondMultiplier p x ≠ 0 := by
  exact mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

include hp in

theorem actual_second_row_norm_sq
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) :
    ‖ringComplex (actualSecondChild p u v x).2.2‖^2 =
      ‖ringComplex (actualSecondMultiplier p x*x.second.frequency)‖^2 := by
  change ‖ringComplex (primaryIdealGenerator (sourceIdeal p x.firstDivisor)*
      primaryIdealGenerator (sourceIdeal p x.second.divisor)*secondUnitFrequency u v x.second.frequency)‖^2 = _
  rw [sourceIdeal_gen p hp hpr,sourceIdeal_gen p hp hpr]
  simp only [map_mul,norm_mul,mul_pow,secondUnitFrequency_norm,actualSecondMultiplier,
    primeProductNorm]

include hp in

theorem actual_second_row_ball
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    {Jo Jn : ℕ} (x : MarkedSecondSource ι Jo Jn) (u v : Eisˣ) (R : ℝ) :
    x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R ↔
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
  rw [mem_nonzeroChildFrequencyBall _ (actualSecondMultiplier_ne_zero p hp x),
    mem_nonzeroChildFrequencyBall _ one_ne_zero,one_mul,actual_second_row_norm_sq p hp hpr]

include hp in
omit [DecidableEq ι] in
theorem actual_second_row_radius_one
    {Jo Jn : ℕ} (source : Finset (MarkedSecondSource ι Jo Jn)) (R : ℝ)
    (hsource : source.Nonempty)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R) : 1 ≤ R := by
  obtain ⟨x,hx⟩ := hsource
  by_contra hR
  have he := nonzeroChildFrequencyBall_empty _ (actualSecondMultiplier_ne_zero p hp x) R (lt_of_not_ge hR)
  simpa [he] using hrows x hx

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers Eisenstein FirstPassCubeLabels SecondPassArithmetic
open JointLogSeparation
noncomputable section
local notation "Eis" => Eisenstein.O
variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem actual_second_mode_branch_energy
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    {Jo : ℕ} (u v : Eisˣ) (source : Finset (MarkedSecondSource ι Jo 0))
    (hs : ActualSecondSourceConditions p source)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (hΨ : ∀ a, ‖Ψ a‖ ≤ 1) (m : Eis) (z : SecondRayIndex)
    (slots₁ slots₂ J₁ J₂ : Finset σ) (lists₁ lists₂ : σ → Finset ι) (a₁ a₂ : σ → ι → ℂ)
    (ha₁ : ∀ i ∈ J₁, ∀ q ∈ lists₁ i, ‖a₁ i q‖ ≤ 1)
    (ha₂ : ∀ i ∈ J₂, ∀ q ∈ lists₂ i, ‖a₂ i q‖ ≤ 1)
    (ω₁ ω₂ : ℝ → ℂ) (G E V B X R : ℝ) (t : Frequency × (Fin 6 → ℝ))
    (labels : Finset (Ideal Eis))
    (hlabels : ∀ x ∈ source,(actualSecondChild p u v x).2.1 ∈ labels)
    (hrows : ∀ x ∈ source,
      x.second.frequency ∈ nonzeroChildFrequencyBall (actualSecondMultiplier p x) R)
    (K : ℕ) (ho : Jo ≤ 2*K) (hJ₁ : J₁.card ≤ K) (hJ₂ : J₂.card ≤ K)
    (w : MarkedSecondSource ι Jo 0 → ℂ) (hw : ∀ x ∈ source,‖w x‖ ≤ 1) :
    ‖∑ x ∈ source,actualSecondSignedWeight p hg Ψ
        (m*cubicIdealGenerator x.quotient) z x * w x *
      secondModeBranch p hp hcop hg x u v pool Ψ m z slots₁ slots₂ J₁ J₂ lists₁ lists₂ a₁ a₂
        ω₁ ω₂ G E V B X t‖ ≤
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t) γ) *
      Real.sqrt (∑ γ ∈ actualSecondTriples p u v (assignedSecondSource source J₁ J₂ lists₁ lists₂),
        tripleDivisorWeight K γ * secondLabelEnergy K (labels.filter Squarefree) (nonzeroChildFrequencyBall 1 R)
          (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t) γ) := by
  let phase := fun x => w x * secondModeOuter p x Ψ m z G E V B X t
  have hphase : ∀ x ∈ source,‖phase x‖ ≤ 1 := by
    intro x hx
    simpa only [phase,norm_mul,secondModeOuter,secondOuterPhase_norm,mul_one] using hw x hx
  have hchild : ∀ x ∈ source, (actualSecondChild p u v x).2.1 ∈ labels ∧
      (actualSecondChild p u v x).2.2 ∈ nonzeroChildFrequencyBall 1 R := by
    intro x hx
    exact ⟨hlabels x hx,(actual_second_row_ball p hp hpr x u v R).mp (hrows x hx)⟩
  have he := actual_second_supported_marked_energy_varying_puncture p hp hcop hg hpr hinj hc
    u v source hs Ψ hΨ (fun x => m*cubicIdealGenerator x.quotient) z
    J₁ J₂ lists₁ lists₂ a₁ a₂ ha₁ ha₂ labels (nonzeroChildFrequencyBall 1 R) hchild
    K ho hJ₁ hJ₂ phase hphase
    (secondModeRight p hp hcop hg pool Ψ m z (slots₂\J₂) lists₂ a₂ ω₂ X t)
    (secondModeLeft p hp hcop hg pool Ψ m z (slots₁\J₁) lists₁ a₁ ω₁ X t)
  apply le_trans (le_of_eq ?_) he
  congr 1
  apply Finset.sum_congr rfl
  intro x hx
  dsimp only [secondModeBranch,phase]
  ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson InverseSecondFibers Eisenstein FirstPassCubeLabels SecondPassArithmetic CompletedGauss
open JointLogSeparation InverseInitialClippedColumns
noncomputable section
local notation "Eis" => Eisenstein.O

variable {ι σ : Type*} [DecidableEq ι] [DecidableEq σ]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem second_left_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (rows : Finset Eis) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (omega : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels rows (secondModeLeft p hp hcop hg pool Ψ m z slots lists a omega (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hg pool (secondRayMinus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K)
        (clippedTest omega (Z^(max 0 N-N)) (-(profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 4))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  exact initial_columnEnergy_clipping_normalized p hg hp pool (secondRayMinus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels rows (secondLabelWeight K) omega hZ N V _

theorem second_right_normalized_energy
    (K : ℕ) (labels : Finset (Ideal Eis)) (R : ℝ) (γ : OuterTriple)
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis) (z : SecondRayIndex)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (omega : ℝ → ℂ) (Z N V : ℝ) (hZ : 0 < Z) (t : Frequency × (Fin 6 → ℝ)) :
    secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a omega (Z^N) t) γ =
      Z^(max 0 N+V) * normalizedColumnEnergy p hg pool (secondRayPlus Ψ z)
        (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (clippedTest omega (Z^(max 0 N-N)) ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5))
        (Z^(max 0 N)) Z (max 0 N+V) := by
  have he : secondLabelEnergy K labels (nonzeroChildFrequencyBall 1 R)
      (secondModeRight p hp hcop hg pool Ψ m z slots lists a omega (Z^N) t) γ =
      columnEnergy p hg pool (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ)
        slots lists a labels (nonzeroChildFrequencyBall 1 R) (secondLabelWeight K)
        (childLogTest omega ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N) := by
    unfold secondLabelEnergy columnEnergy
    apply Finset.sum_congr rfl
    intro f hf
    simp only [secondLabelWeight,secondModeRight,secondCanonicalPolynomial]
    apply congrArg (fun a : ℝ => ((idealDivisors f).card : ℝ)^(9+4*K)*a)
    exact child_ball_sum_neg (β:=ℝ) R (fun k => ‖finiteCanonicalMarkedRow p hg pool
      (secondRayPlus Ψ z) (actualSecondInheritedPuncture m γ) (primaryIdealGenerator f) k
      slots lists a (childLogTest omega ((profileHeight secondLeftSlope secondRightSlope secondKernelSlope t.1 t.2) 5)) (Z^N)‖^2)
  rw [he]
  exact initial_columnEnergy_clipping_normalized p hg hp pool (secondRayPlus Ψ z)
    (actualSecondInheritedPuncture m γ) slots lists a labels (nonzeroChildFrequencyBall 1 R)
    (secondLabelWeight K) omega hZ N V _

omit [DecidableEq σ] in
theorem normalized_child_energy_radical_puncture
    (pool : Finset ι) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ)
    (labels : Finset (Ideal Eis)) (rows : Finset Eis) (D : Ideal Eis → ℝ)
    (W : ℝ → ℂ) (X Z F : ℝ) :
    normalizedColumnEnergy p hg pool Ψ m slots lists a labels rows D W X Z F =
    normalizedColumnEnergy p hg pool Ψ
      (cubicIdealGenerator (Ideal.span {m}).radical)
      slots lists a labels rows D W X Z F := by
  unfold normalizedColumnEnergy
  apply Finset.sum_congr rfl
  intro f hf
  apply congrArg (fun x : ℝ => D f*x)
  apply Finset.sum_congr rfl
  intro k hk
  rw [finiteCanonicalMarkedRow_radical_puncture p hg pool Ψ m (primaryIdealGenerator f) k slots lists a W X]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation SchwartzPlanePoisson
noncomputable section
theorem twisted_descent_profile_separation {ι : Type*} [Fintype ι]
    (g₁ g₂ Φ : 𝓢(ℝ, ℂ)) (V : ι → ℝ → ℂ) (a₁ a₂ ak M : ι → ℝ)
    (hM : ∀ i, 0 ≤ M i) (hV : ∀ i y, V i y ≠ 0 → |y| ≤ M i)
    (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ θ₁ θ₂ : ℝ,
      (∀ y : ι → ℝ,
        (∏ i, V i (y i)) * frequencyTwist g₁ θ₁ (∑ i, a₁ i * y i) *
          frequencyTwist g₂ θ₂ (∑ i, a₂ i * y i) *
          paperRadialFourier Φ (R * Real.exp (∑ i, ak i * y i)) =
        ∫ t₁ : ℝ, ∫ t₂ : ℝ, ∫ t₃ : ℝ,
          tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ (t₁,t₂,t₃) *
            (∏ i, V i (y i) * kernelLogPhase t₁ (a₁ i * y i) *
              kernelLogPhase t₂ (a₂ i * y i) * kernelLogPhase t₃ (ak i * y i))) ∧
      Integrable (fun t : Frequency =>
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ∧
      (1 + R)^A * (∫ t : Frequency,
        ((1 + ‖t.1‖)^J * (1 + ‖t.2.1‖)^J * (1 + ‖t.2.2‖)^J) *
          ‖tripleCoefficient (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ t‖) ≤
        C * (1 + ‖θ₁‖)^(J + (volume : Measure ℝ).integrablePower) *
          (1 + ‖θ₂‖)^(J + (volume : Measure ℝ).integrablePower) := by
  obtain ⟨Ck, hCk, hk⟩ := radial_profile_envelope Φ V ak M hM hV A J
  obtain ⟨C₁, hC₁, h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂, hC₂, h₂⟩ := frequencyTwist_fourier_moment J g₂
  refine ⟨C₁ * C₂ * Ck, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃, he, hi, hb, hp⟩ := hk R hR
  refine ⟨b₃, ?_⟩
  intro θ₁ θ₂
  refine ⟨descent_profile_identity _ _ Φ V a₁ a₂ ak R b₃ he,
    tripleCoefficient_weighted_integrable _ _ _ J, ?_⟩
  rw [tripleCoefficient_weighted_integral]
  have hh := mul_le_mul (mul_le_mul (h₁ θ₁) (h₂ θ₂)
    (integral_nonneg (fun t => by positivity)) (by positivity)) hb
    (by positivity : 0 ≤ (1 + R)^A * ∫ t : ℝ, (1 + ‖t‖)^J * ‖b₃ t‖) (by positivity)
  convert hh using 1 <;> first | rfl | ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open MeasureTheory JointLogSeparation
noncomputable section

theorem integrable_density_mode {ι : Type*} [Fintype ι]
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak y : ι → ℝ) :
    Integrable (fun z : Frequency × (ι → ℝ) => D z *
      pureProfileMode a₁ a₂ ak y z.1 z.2) := by
  have hc : Continuous (fun z : Frequency × (ι → ℝ) => pureProfileMode a₁ a₂ ak y z.1 z.2) := by
    unfold pureProfileMode kernelLogPhase
    fun_prop
  exact hD.mul_bdd hc.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun z => (pureProfileMode_norm a₁ a₂ ak y z.1 z.2).le))

theorem density_finite_sum {ι κ : Type*} [Fintype ι] (s : Finset κ)
    (D : Frequency × (ι → ℝ) → ℂ) (hD : Integrable D) (a₁ a₂ ak : ι → ℝ)
    (c : κ → ℂ) (y : κ → ι → ℝ) :
    (∑ k ∈ s,c k * ∫ z : Frequency × (ι → ℝ),D z*pureProfileMode a₁ a₂ ak (y k) z.1 z.2) =
    ∫ z : Frequency × (ι → ℝ),D z * ∑ k ∈ s,c k*pureProfileMode a₁ a₂ ak (y k) z.1 z.2 := by
  simp only [← integral_const_mul]
  rw [← integral_finsetSum s (fun k hk => (integrable_density_mode D hD a₁ a₂ ak (y k)).const_mul (c k))]
  apply integral_congr_ae
  filter_upwards with z
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

end
end InverseMoment

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
