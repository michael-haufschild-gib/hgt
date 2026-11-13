/-
Logarithmic bins and cube blocks adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.FirstPassRowMajorants

/-!
# Logarithmic bins and cube blocks

Global logarithmic indices and pooled row scales, first-pass block data `GlobalFirstData` and
cube blocks. First passage summed over cube blocks with one constant; two-pass residue
weights of the child kernel pairs.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
def secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) : Finset (SecondExpansionData ι) :=
  F.powerset.biUnion (fun G => G.powerset.biUnion (fun E =>
    F.powerset.biUnion (fun V => (K G E).image (fun k => ⟨G,E,V,k⟩))))

theorem mem_secondExpansionPool {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (x : SecondExpansionData ι) :
    x ∈ secondExpansionPool F K ↔
      x.sourceCommon ⊆ F ∧ x.divisor ⊆ x.sourceCommon ∧ x.overlap ⊆ F ∧
        x.frequency ∈ K x.sourceCommon x.divisor := by
  simp only [secondExpansionPool, Finset.mem_biUnion, Finset.mem_powerset, Finset.mem_image]
  constructor
  · rintro ⟨G,hG,E,hE,V,hV,k,hk,hx⟩
    subst x
    exact ⟨hG,hE,hV,hk⟩
  · rintro ⟨hG,hE,hV,hk⟩
    exact ⟨x.sourceCommon,hG,x.divisor,hE,x.overlap,hV,x.frequency,hk,rfl⟩

theorem sum_secondExpansionPool {M : Type*} [AddCommMonoid M] {ι : Type*} [DecidableEq ι] (F : Finset ι)
    (K : Finset ι → Finset ι → Finset O) (H : SecondExpansionData ι → M) :
    (∑ x ∈ secondExpansionPool F K, H x) =
      ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ V ∈ F.powerset, ∑ k ∈ K G E, H ⟨G,E,V,k⟩ := by
  unfold secondExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro G hG
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro E hE
      rw [Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro V hV
        rw [Finset.sum_image]
        intro k hk k' hk' heq
        exact congrArg SecondExpansionData.frequency heq
      · intro V hV V' hV' hne
        apply Finset.disjoint_left.mpr
        intro x hx hx'
        obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
        obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
        exact hne (congrArg SecondExpansionData.overlap heq).symm
    · intro E hE E' hE' hne
      apply Finset.disjoint_left.mpr
      intro x hx hx'
      obtain ⟨V,hV,hx⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨V',hV',hx'⟩ := Finset.mem_biUnion.mp hx'
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
      exact hne (congrArg SecondExpansionData.divisor heq).symm
  · intro G hG G' hG' hne
    apply Finset.disjoint_left.mpr
    intro x hx hx'
    obtain ⟨E,hE,V,hV,hx⟩ := (by simpa only [Finset.mem_biUnion] using hx)
    obtain ⟨E',hE',V',hV',hx'⟩ := (by simpa only [Finset.mem_biUnion] using hx')
    obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨k',hk',heq⟩ := Finset.mem_image.mp hx'
    exact hne (congrArg SecondExpansionData.sourceCommon heq).symm

@[ext] structure GlobalFirstData (ι : Type*) where
  cube : CubeCoordinates ι
  firstCommon : Finset ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalFirstData
variable {ι : Type*}
def append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : GlobalSecondData ι :=
  ⟨b.cube,b.firstCommon,b.common,b.firstDivisor,x⟩
end GlobalFirstData

namespace GlobalSecondData
variable {ι : Type*}
def first (x : GlobalSecondData ι) : GlobalFirstData ι :=
  ⟨x.cube,x.firstCommon,x.common,x.firstDivisor⟩
@[simp] theorem append_first (x : GlobalSecondData ι) : x.first.append x.source=x := by cases x; rfl
@[simp] theorem first_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).first=b := rfl
@[simp] theorem source_append (b : GlobalFirstData ι) (x : SecondExpansionData ι) : (b.append x).source=x := rfl
end GlobalSecondData

section
variable {ι : Type*} [DecidableEq ι]

def globalFirstRawPool (pool : Finset ι) (b : GlobalFirstData ι) : Finset ι :=
  (pool\(b.cube.support∪b.common))\b.firstCommon

def globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : Finset (GlobalSecondData ι) :=
  s.biUnion (fun b => (secondExpansionPool (globalFirstRawPool pool b) (cutoff b)).image b.append)

theorem mem_globalFirstExpansionPool (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (x : GlobalSecondData ι) :
    x∈globalFirstExpansionPool pool s cutoff ↔
      x.first∈s ∧ x.source∈secondExpansionPool (globalFirstRawPool pool x.first) (cutoff x.first) := by
  simp only [globalFirstExpansionPool,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨b,hb,z,hz,rfl⟩
    exact ⟨hb,hz⟩
  · rintro ⟨hb,hx⟩
    exact ⟨x.first,hb,x.source,hx,x.append_first⟩

theorem sum_globalFirstExpansionPool {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) (f : GlobalSecondData ι → M) :
    ∑ x∈globalFirstExpansionPool pool s cutoff,f x =
    ∑ b∈s,∑ x∈secondExpansionPool (globalFirstRawPool pool b) (cutoff b),f (b.append x) := by
  unfold globalFirstExpansionPool
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro x hx y hy heq
    exact congrArg GlobalSecondData.source heq
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨v,hv,heq⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalSecondData.first heq).symm

end
@[ext] structure GlobalCubeBlock (ι : Type*) where
  cube : CubeCoordinates ι
  common : Finset ι
  firstDivisor : Finset ι

namespace GlobalCubeBlock
variable {ι : Type*}
def withCommon (b : GlobalCubeBlock ι) (A : Finset ι) : GlobalFirstData ι :=
  ⟨b.cube,A,b.common,b.firstDivisor⟩
end GlobalCubeBlock

namespace GlobalFirstData
variable {ι : Type*}
def block (b : GlobalFirstData ι) : GlobalCubeBlock ι := ⟨b.cube,b.common,b.firstDivisor⟩
@[simp] theorem block_withCommon (b : GlobalCubeBlock ι) (A : Finset ι) : (b.withCommon A).block=b := rfl
@[simp] theorem withCommon_block (b : GlobalFirstData ι) : b.block.withCommon b.firstCommon=b := by cases b; rfl
end GlobalFirstData

variable {ι : Type*} [DecidableEq ι]

def globalCubePool (pool : Finset ι) (b : GlobalCubeBlock ι) : Finset ι := pool\(b.cube.support∪b.common)

def globalFirstFamilySet (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) : Finset (GlobalFirstData ι) :=
  blocks.biUnion (fun b => (globalCubePool pool b).powerset.image b.withCommon)

theorem sum_globalFirstFamilySet {M : Type*} [AddCommMonoid M]
    (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (f : GlobalFirstData ι → M) :
    ∑ d∈globalFirstFamilySet pool blocks,f d =
      ∑ b∈blocks,∑ A∈(globalCubePool pool b).powerset,f (b.withCommon A) := by
  unfold globalFirstFamilySet
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_image]
    intro A hA B hB he
    exact congrArg GlobalFirstData.firstCommon he
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro x hx hy
    obtain ⟨A,hA,rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨B,hB,he⟩ := Finset.mem_image.mp hy
    exact hne (congrArg GlobalFirstData.block he).symm

theorem mem_globalFirstFamilySet (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι)) (d : GlobalFirstData ι) :
    d∈globalFirstFamilySet pool blocks ↔ d.block∈blocks ∧ d.firstCommon⊆globalCubePool pool d.block := by
  simp only [globalFirstFamilySet,Finset.mem_biUnion,Finset.mem_image,Finset.mem_powerset]
  constructor
  · rintro ⟨b,hb,A,hA,rfl⟩;exact ⟨hb,hA⟩
  · rintro ⟨hb,hA⟩;exact ⟨d.block,hb,d.firstCommon,hA,d.withCommon_block⟩

/-- Arithmetic compatibility of a first-pass block. -/
def GlobalFirstAdmissible (b : GlobalFirstData ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common ∪ b.cube.support

def GlobalCubeAdmissible (b : GlobalCubeBlock ι) : Prop :=
  b.cube.Admissible ∧ Disjoint b.common b.cube.support ∧ b.firstDivisor ⊆ b.common ∪ b.cube.support

theorem globalFirstExpansionPool_admissible (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (hs : ∀ b ∈ s, GlobalFirstAdmissible b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (x : GlobalSecondData ι) (hx : x ∈ globalFirstExpansionPool pool s cutoff) :
    GlobalSecondAdmissible x := by
  have hm := (mem_globalFirstExpansionPool pool s cutoff x).mp hx
  have hb := hs x.first hm.1
  have he := ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.1
  exact ⟨hb.1, he, hb.2.1, hb.2.2⟩

theorem globalFirstExpansionPool_frequency_ne_zero (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O)
    (x : GlobalSecondData ι)
    (hx : x ∈ globalFirstExpansionPool pool s (fun b G E => (cutoff b G E).erase 0)) :
    x.source.frequency ≠ 0 := by
  have hm := (mem_globalFirstExpansionPool _ _ _ x).mp hx
  exact (Finset.mem_erase.mp ((mem_secondExpansionPool _ _ x.source).mp hm.2).2.2.2).1

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap

namespace CubeCoordinates
def sideDivisor {ι : Type*} (x : CubeCoordinates ι) (side : Bool) : Finset ι :=
  if side then x.leftDivisor else x.rightDivisor
end CubeCoordinates

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

def globalFirstBlockColumnScale (ell : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  ell / (primeProductNorm p (b.cube.sideDivisor side) * primeProductNorm p b.common)

def globalCubeColumnScale (ell : ℝ) (side : Bool) (b : GlobalCubeBlock ι) : ℝ :=
  globalFirstBlockColumnScale p ell side (b.withCommon ∅)

theorem globalCubeColumnScale_pos (hp : ∀ i, p i ≠ 0) (ell : ℝ) (hell : 0 < ell)
    (side : Bool) (b : GlobalCubeBlock ι) : 0 < globalCubeColumnScale p ell side b :=
  div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))

variable [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalCubeInputFamilyEnergy (pool : Finset ι) (b : GlobalCubeBlock ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (J : ℕ) (T : Finset O) : ℝ :=
  firstInputFamilyEnergy p hg (globalCubePool pool b) b.cube.support
    (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit side Ψ m
    (fun S => g (columnLog p (globalCubeColumnScale p ell side b) S)) V
    (globalCubeColumnScale p ell side b) (∏ i ∈ b.common, p i) (∏ i ∈ b.firstDivisor, p i) J T

theorem globalCubeInputFamilyEnergy_nonneg (pool : Finset ι) (b : GlobalCubeBlock ι)
    (Ψ : O →* ℂ) (m : O) (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (J : ℕ) (T : Finset O) :
    0 ≤ globalCubeInputFamilyEnergy p hg pool b Ψ m g V ell side J T :=
  firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

def globalFirstCoreRow (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (r : QuadraticRayRing)
    (t : ℝ) (b : GlobalFirstData ι) (z : O) : ℂ :=
  firstCoreInputRow p hg (pool \ (b.cube.support ∪ b.common)) b.firstCommon b.cube.support
    (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
    side r Ψ m (normalizedColumn p (fun S => g (columnLog p (globalFirstBlockColumnScale p ell side b) S)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b))
    (∏ i ∈ b.common, p i) (∏ i ∈ b.firstDivisor, p i) t z

/-- The inverse divisor norm and first Poisson scaling remain outside both column energies. -/
def globalCubeFirstCoefficient (K : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  K / (primeProductNorm p b.firstDivisor *
    ‖ringComplex (∏ i ∈ cubeActiveSupport b.cube.support
      (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit, p i)‖)

def globalCubeFirstBlock (hp : ∀ i, p i ≠ 0) (pool : Finset ι) (b : GlobalCubeBlock ι)
    (s : Finset (Ideal O × O)) (a : Ideal O × O → ℂ)
    (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ W V₁ V₂ : 𝓢(ℝ, ℂ)) (K ell : ℝ) : ℂ :=
  (primeProductNorm p b.firstDivisor : ℂ)⁻¹ * ∑ x ∈ s, a x *
    actualFirstKernel p hp hg (globalCubePool pool b) b.cube.support
      (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit true
        (multiplicativeCoreColumn p Ψ₁ m₁ (fun S => g₁ (columnLog p (globalCubeColumnScale p ell true b) S)))
        (∏ i ∈ b.common, p i) (cubicIdealGenerator x.1))
      (originalLabelColumn p hg b.cube.support b.cube.leftBit b.cube.rightBit false
        (multiplicativeCoreColumn p Ψ₂ m₂ (fun S => g₂ (columnLog p (globalCubeColumnScale p ell false b) S)))
        (∏ i ∈ b.common, p i) (cubicIdealGenerator x.1))
      W V₁ V₂ (globalCubeColumnScale p ell true b) (globalCubeColumnScale p ell false b) K
      (∏ i ∈ b.firstDivisor, p i) x.2

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

/-- First passage summed over cube blocks, with one constant for all arithmetic data. -/
theorem globalCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ, ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ t, V₁ t ≠ 0 → |t| ≤ M₁) (hV₂ : ∀ t, V₂ t ≠ 0 → |t| ≤ M₂)
    (J : ℕ) (δ : ℝ) (hδ : 0 < δ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ, ℂ)) (K ell Y : ℝ),
      0 < K → 0 < ell → 0 ≤ Y →
      (∀ u, ‖Ψ₁ u‖ ≤ 1) → (∀ u, ‖Ψ₂ u‖ ≤ 1) →
      (∀ b ∈ blocks, 0 ≤ w b) → (∀ b ∈ blocks, ∀ x ∈ s b, ‖a b x‖ ≤ w b) →
      (∀ b ∈ blocks, ∀ x ∈ s b, x.2 ≠ 0) →
      (∀ b ∈ blocks, ∀ x ∈ s b, DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i + b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x ∈ T b) →
      (∀ b ∈ blocks, ∀ z ∈ T b, z ≠ 0) →
      (∀ b ∈ blocks, ∀ z ∈ T b, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      ‖∑ b ∈ blocks, globalCubeFirstBlock p hg hp pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
      C * Y ^ δ *
        Real.sqrt (∑ b ∈ blocks, w b * globalCubeFirstCoefficient p K b *
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b ∈ blocks, w b * globalCubeFirstCoefficient p K b *
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C, hC, hfirst⟩ := first_passage_to_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J δ hδ
  refine ⟨C, hC, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ K ell Y
    hK hell hY hΨ₁ hΨ₂ hw ha hs0 hmap hT0 hT
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b * globalCubeFirstCoefficient p K b
  have hv (b) (hb : b ∈ blocks) : 0 ≤ v b :=
    mul_nonneg (hw b hb) (div_nonneg hK.le (mul_nonneg (primeProductNorm_pos p hp _).le (norm_nonneg _)))
  have hE₁ (b) : 0 ≤ E₁ b := globalCubeInputFamilyEnergy_nonneg p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  have hE₂ (b) : 0 ≤ E₂ b := globalCubeInputFamilyEnergy_nonneg p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  have hb (b) (hb : b ∈ blocks) :
      ‖globalCubeFirstBlock p hg hp pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ ≤
        (C * Y ^ δ) * (Real.sqrt (v b * E₁ b) * Real.sqrt (v b * E₂ b)) := by
    have hpool : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hb
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb)
    have h := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hpool
      (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
      b.cube.support_pos Ψ₁ Ψ₂ m₁ m₂
      (fun S => g₁ (columnLog p (globalCubeColumnScale p ell true b) S))
      (fun S => g₂ (columnLog p (globalCubeColumnScale p ell false b) S))
      (fun D _ => hΨ₁ _) (fun D _ => hΨ₂ _)
      (globalCubeColumnScale p ell true b) (globalCubeColumnScale p ell false b)
      (globalCubeColumnScale_pos p hp ell hell true b) (globalCubeColumnScale_pos p hp ell hell false b)
      K hK (∏ i ∈ b.common, p i) (∏ i ∈ b.firstDivisor, p i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
      (s b) (T b) (a b) (w b) Y (hw b hb) hY (hs0 b hb) (hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    unfold globalCubeFirstBlock
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (primeProductNorm_pos p hp b.firstDivisor)]
    apply (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr (primeProductNorm_pos p hp _).le)).trans_eq
    rw [Real.sqrt_mul (hv b hb), Real.sqrt_mul (hv b hb)]
    calc
      _ = (C * Y ^ δ) * (v b * (Real.sqrt (E₁ b) * Real.sqrt (E₂ b))) := by
        dsimp only [v, E₁, E₂, globalCubeFirstCoefficient, globalCubeInputFamilyEnergy]
        ring
      _ = (C * Y ^ δ) * (Real.sqrt (v b)) ^ 2 * Real.sqrt (E₁ b) * Real.sqrt (E₂ b) := by
        rw [Real.sq_sqrt (hv b hb)]
        ring
      _ = _ := by ring
  calc
    _ ≤ ∑ b ∈ blocks, ‖globalCubeFirstBlock p hg hp pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ K ell‖ := norm_sum_le _ _
    _ ≤ ∑ b ∈ blocks, (C * Y ^ δ) * (Real.sqrt (v b * E₁ b) * Real.sqrt (v b * E₂ b)) :=
      Finset.sum_le_sum hb
    _ = (C * Y ^ δ) * (∑ b ∈ blocks, Real.sqrt (v b * E₁ b) * Real.sqrt (v b * E₂ b)) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (C * Y ^ δ) * (Real.sqrt (∑ b ∈ blocks, v b * E₁ b) *
        Real.sqrt (∑ b ∈ blocks, v b * E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        rw [← Finset.sum_coe_sort blocks (fun b => Real.sqrt (v b * E₁ b) * Real.sqrt (v b * E₂ b)),
          ← Finset.sum_coe_sort blocks (fun b => v b * E₁ b),
          ← Finset.sum_coe_sort blocks (fun b => v b * E₂ b)]
        exact Real.sum_sqrt_mul_sqrt_le Finset.univ
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val)))
        (mul_nonneg hC (Real.rpow_nonneg hY δ))
    _ = _ := by dsimp only [v, E₁, E₂]; ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
def normLogBin (u : ℝ) : ℕ := ⌊Real.log u⌋₊
def normLogScale (j : ℕ) : ℝ := Real.exp (j : ℝ)

lemma normLogScale_pos (j : ℕ) : 0 < normLogScale j := Real.exp_pos _
lemma normLogScale_ge_one (j : ℕ) : 1 ≤ normLogScale j :=
  Real.one_le_exp (by positivity)

lemma normLogBin_error (u : ℝ) (hu : 1 ≤ u) :
    0 ≤ Real.log (u / normLogScale (normLogBin u)) ∧
      Real.log (u / normLogScale (normLogBin u)) ≤ 1 := by
  rw [Real.log_div (by linarith) (normLogScale_pos _).ne', normLogScale, Real.log_exp]
  exact ⟨sub_nonneg.mpr (Nat.floor_le (Real.log_nonneg hu)),
    by have h := Nat.lt_floor_add_one (Real.log u); dsimp [normLogBin]; linarith⟩

lemma normLogBin_scale_bounds (u : ℝ) (hu : 1 ≤ u) :
    normLogScale (normLogBin u) ≤ u ∧
      u ≤ normLogScale (normLogBin u) * Real.exp 1 := by
  have hu0 : 0 < u := by linarith
  constructor
  · have h := Real.exp_le_exp.mpr (Nat.floor_le (Real.log_nonneg hu))
    simpa only [Real.exp_log hu0, normLogScale, normLogBin] using h
  · have h := Real.exp_le_exp.mpr (Nat.lt_floor_add_one (Real.log u)).le
    simpa only [Real.exp_log hu0, Real.exp_add, normLogScale, normLogBin] using h

lemma normLogBin_mono {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    normLogBin u ≤ normLogBin v := Nat.floor_mono (Real.log_le_log hu huv)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalCubeJNorm (x : GlobalSecondData ι) : ℝ :=
  ‖ringComplex (jLabel p x.cube.support (fun i => x.cube.leftExponent i+x.cube.rightExponent i)
    x.cube.leftBit x.cube.rightBit)‖^2

def globalCubeActiveRoot (x : GlobalSecondData ι) : ℝ :=
  ‖ringComplex (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)‖

def globalFirstColumnScale (ell : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  ell/(primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.common)

def globalFirstRowScale (K ell B F : ℝ) (x : GlobalSecondData ι) : ℝ :=
  ell^2*B^4*F^2*primeProductNorm p x.firstDivisor/
    (K*(primeProductNorm p x.common)^2*globalCubeJNorm p x)

def globalSecondDelta (B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  B*F*primeProductNorm p (x.cube.sideDivisor side)*primeProductNorm p x.firstCommon*
    primeProductNorm p (x.source.sourceCommon\x.source.divisor)

def globalNominalChildRow (K B F : ℝ) (x : GlobalSecondData ι) (side : Bool) : ℝ :=
  K*globalCubeJNorm p x/((globalSecondDelta p B F x side)^2*B^2)

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalCubeJNorm_pos (x : GlobalSecondData ι) : 0 < globalCubeJNorm p x :=
  zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalCubeActiveRoot_pos (x : GlobalSecondData ι) : 0 < globalCubeActiveRoot p x := by
  have hh := element_norm_ge_one (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i)
    (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))
  change 0 < ‖ringComplex _‖
  nlinarith [norm_nonneg (ringComplex (∏ i∈cubeActiveSupport x.cube.support
    (fun i => x.cube.leftExponent i+x.cube.rightExponent i) x.cube.leftBit x.cube.rightBit,p i))]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalFirstColumnScale_pos (ell : ℝ) (hell : 0 < ell) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalFirstColumnScale p ell x side :=
  div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSecondDelta_ge (B F : ℝ) (hB : 0 ≤ B) (hF : 1 ≤ F) (x : GlobalSecondData ι) (side : Bool) :
    B ≤ globalSecondDelta p B F x side := by
  have hA := primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  have ht := primeProductNorm_ge_one p hp x.firstCommon
  have hR := primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  unfold globalSecondDelta
  calc
    B = B*1*1*1*1 := by ring
    _ ≤ _ := by gcongr

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSecondDelta_pos (B F : ℝ) (hB : 0 < B) (hF : 0 < F) (x : GlobalSecondData ι) (side : Bool) :
    0 < globalSecondDelta p B F x side := by
  unfold globalSecondDelta
  exact mul_pos (mul_pos (mul_pos (mul_pos hB hF)
    (primeProductNorm_pos p hp _))
    (primeProductNorm_pos p hp _)) (primeProductNorm_pos p hp _)

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actualSecondRow_ne_zero (D E : Finset ι) (k : O) (hk : k ≠ 0) :
    actualSecondRow p D E k ≠ 0 :=
  mul_ne_zero (mul_ne_zero
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
    (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))) hk

/-- The descendant element label generates the ideal recorded by the divisor encoding. -/
def globalSecondLabel (x : GlobalSecondData ι) : O :=
  (∏ i ∈ x.common, p i) *
    jLabel p x.cube.support (fun i => x.cube.leftExponent i + x.cube.rightExponent i)
      x.cube.leftBit x.cube.rightBit * (∏ i ∈ x.source.divisor, p i) * (∏ i ∈ x.source.overlap, p i)

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalSecondLabel_span (x : GlobalSecondData ι) :
    Ideal.span {globalSecondLabel p x} = SecondPassFiber.newLabel (globalSecondTuple p x) :=
  actualSecondLabel_span p x.cube.support x.common x.source.divisor x.source.overlap
    x.cube.leftExponent x.cube.rightExponent x.cube.leftBit x.cube.rightBit

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
abbrev GlobalLogIndex := Fin 10 → ℕ

def globalLogRep (j : GlobalLogIndex) (i : Fin 10) : ℝ := normLogScale (j i)

theorem globalLogRep_pos (j : GlobalLogIndex) (i : Fin 10) : 0 < globalLogRep j i := normLogScale_pos _

theorem globalLogRep_ge_one (j : GlobalLogIndex) (i : Fin 10) : 1 ≤ globalLogRep j i := normLogScale_ge_one _

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalScaleVector (side : Bool) (x : GlobalSecondData ι) : Fin 10 → ℝ :=
  ![primeProductNorm p (x.cube.sideDivisor side),primeProductNorm p x.common,
    primeProductNorm p x.firstCommon,primeProductNorm p (x.source.sourceCommon\x.source.divisor),
    globalCubeJNorm p x,primeProductNorm p x.firstDivisor,primeProductNorm p x.source.divisor,
    primeProductNorm p x.source.overlap,‖ringComplex (SecondPassFiber.newRow (globalSecondTuple p x))‖^2,
    (globalCubeActiveRoot p x)^2]

def globalScaleIndex (side : Bool) (x : GlobalSecondData ι) : GlobalLogIndex :=
  fun i => normLogBin (globalScaleVector p side x i)

include hp in
theorem globalScaleVector_ge_one (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) :
    ∀ i,1 ≤ globalScaleVector p side x i := by
  intro i
  fin_cases i
  · exact primeProductNorm_ge_one p hp (x.cube.sideDivisor side)
  · exact primeProductNorm_ge_one p hp x.common
  · exact primeProductNorm_ge_one p hp x.firstCommon
  · exact primeProductNorm_ge_one p hp (x.source.sourceCommon\x.source.divisor)
  · change 1 ≤ globalCubeJNorm p x
    exact element_norm_ge_one _ (primeProduct_ne_zero p hp x.cube.support _)
  · exact primeProductNorm_ge_one p hp x.firstDivisor
  · exact primeProductNorm_ge_one p hp x.source.divisor
  · exact primeProductNorm_ge_one p hp x.source.overlap
  · change 1 ≤ ‖ringComplex (SecondPassFiber.newRow (globalSecondTuple p x))‖ ^ 2
    unfold globalSecondTuple
    rw [actualSecondTuple_newRow]
    exact element_norm_ge_one _ (actualSecondRow_ne_zero p hp _ _ _ hk)
  · change 1 ≤ (globalCubeActiveRoot p x)^2
    exact element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i))

include hp in
theorem globalScaleIndex_bounds (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    globalLogRep (globalScaleIndex p side x) i ≤ globalScaleVector p side x i ∧
    globalScaleVector p side x i ≤ globalLogRep (globalScaleIndex p side x) i*Real.exp 1 :=
  normLogBin_scale_bounds _ (globalScaleVector_ge_one p hp side x hk i)

include hp in
theorem globalScaleIndex_error (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0)
    (i : Fin 10) :
    0 ≤ Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ∧
    Real.log (globalScaleVector p side x i/globalLogRep (globalScaleIndex p side x) i) ≤ 1 :=
  normLogBin_error _ (globalScaleVector_ge_one p hp side x hk i)

def globalLogSector (s : Finset (GlobalSecondData ι)) (side : Bool) (j : GlobalLogIndex) : Finset (GlobalSecondData ι) :=
  s.filter (fun x => globalScaleIndex p side x=j)

end

def globalLogBox (U : Fin 10 → ℝ) : Finset GlobalLogIndex :=
  Fintype.piFinset (fun i => Finset.range (normLogBin (U i)+1))

theorem globalLogBox_card (U : Fin 10 → ℝ) :
    (globalLogBox U).card=∏ i : Fin 10,(normLogBin (U i)+1) := by
  simp only [globalLogBox,Fintype.card_piFinset,Finset.card_range]

theorem globalScaleIndex_mem_box {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (side : Bool) (x : GlobalSecondData ι) (hk : x.source.frequency ≠ 0) (U : Fin 10 → ℝ)
    (hU : ∀ i,globalScaleVector p side x i ≤ U i) :
    globalScaleIndex p side x∈globalLogBox U := by
  apply Fintype.mem_piFinset.mpr
  intro i
  apply Finset.mem_range.mpr
  exact Nat.lt_succ_of_le (normLogBin_mono (zero_lt_one.trans_le (globalScaleVector_ge_one p hp side x hk i)) (hU i))

theorem sum_globalLogSector {ι M : Type*} [DecidableEq ι] [AddCommMonoid M]
    (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
    (s : Finset (GlobalSecondData ι)) (side : Bool) (U : Fin 10 → ℝ)
    (hk : ∀ x∈s,x.source.frequency ≠ 0)
    (hU : ∀ x∈s,∀ i,globalScaleVector p side x i ≤ U i) (f : GlobalSecondData ι → M) :
    ∑ x∈s,f x=∑ j∈globalLogBox U,∑ x∈globalLogSector p s side j,f x := by
  symm
  exact Finset.sum_fiberwise_of_maps_to (fun x hx => globalScaleIndex_mem_box p hp side x (hk x hx) U (hU x hx)) f

def globalPooledColumnScale (ell : ℝ) (j : GlobalLogIndex) : ℝ :=
  ell/(globalLogRep j 0*globalLogRep j 1*globalLogRep j 2*globalLogRep j 3*globalLogRep j 6*globalLogRep j 7)

def globalPooledLabelScale (j : GlobalLogIndex) : ℝ :=
  globalLogRep j 1*globalLogRep j 4*globalLogRep j 6*globalLogRep j 7*Real.exp 4

def globalPooledRowScale (K ell B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)

def globalPooledDelta (B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  B*F*globalLogRep j 0*globalLogRep j 2*globalLogRep j 3

def globalPooledNaturalRow (K B F : ℝ) (j : GlobalLogIndex) : ℝ :=
  K*globalLogRep j 4/((globalPooledDelta B F j)^2*B^2)

theorem globalPooledColumnScale_pos (ell : ℝ) (hell : 0 < ell) (j : GlobalLogIndex) :
    0 < globalPooledColumnScale ell j := by
  unfold globalPooledColumnScale
  apply div_pos hell
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos (globalLogRep_pos j 0)
    (globalLogRep_pos j 1)) (globalLogRep_pos j 2)) (globalLogRep_pos j 3))
    (globalLogRep_pos j 6)) (globalLogRep_pos j 7)

theorem globalPooledLabelScale_ge_one (j : GlobalLogIndex) : 1 ≤ globalPooledLabelScale j := by
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le (globalLogRep_ge_one j 1) (globalLogRep_ge_one j 4))
        (globalLogRep_ge_one j 6)) (globalLogRep_ge_one j 7)) (Real.one_le_exp (by norm_num))

theorem globalPooled_mass (ell B F : ℝ) (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledColumnScale ell j*globalPooledLabelScale j =
      Real.exp 4*((ell*B^3)*F)*globalLogRep j 4/(globalPooledDelta B F j*B^2) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledColumnScale globalPooledLabelScale globalPooledDelta
  field_simp [h]

theorem globalPooled_radial_ratio (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) :
    globalPooledRowScale K ell B F j*globalLogRep j 8/
      (globalLogRep j 5*(globalLogRep j 6)^2*(globalLogRep j 7)^2*(globalPooledColumnScale ell j)^2) =
    Real.exp 1*(globalLogRep j 8/globalPooledNaturalRow K B F j) := by
  have h (i : Fin 10) := (globalLogRep_pos j i).ne'
  unfold globalPooledRowScale globalPooledColumnScale globalPooledNaturalRow globalPooledDelta
  field_simp [h]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
theorem local_first_conductor_balance (parityBit e₁ e₂ : Bool) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      2*bit (!parityBit && e₁ && e₂)=bit e₁+bit e₂+bit parityBit := by
  cases parityBit <;> cases e₁ <;> cases e₂ <;> decide

theorem local_first_conductor_bound (parityBit e₁ e₂ : Bool) (n : ℕ) (hn : 0<n) :
    (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2*n := by
  have h : (if conductorExponent parityBit e₁ e₂=0 then 0 else 1)+dilationExponent parityBit e₁ e₂+
      bit (retained parityBit e₁ e₂)≤bit e₁+bit e₂+2 := by
    cases parityBit <;> cases e₁ <;> cases e₂ <;> decide
  omega

variable {ι : Type*} [DecidableEq ι] (p : ι → O)

omit [DecidableEq ι] in
theorem firstActiveProduct_as_primeProduct (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)=
      primeProduct p S (fun i => if conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 then 0 else 1) := by
  unfold cubeActiveSupport primeProduct
  rw [Finset.prod_filter]
  apply Finset.prod_congr rfl
  intro i hi
  by_cases h : conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)=0 <;> simp [h]

omit [DecidableEq ι] in
/-- The active conductor and dilation have an exact primewise exponent balance. -/
theorem first_conductor_product_balance (S : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    (∏ i∈cubeActiveSupport S v ε₁ ε₂,p i)*dilationLabel p S v ε₁ ε₂*j2Label p S v ε₁ ε₂^2 =
      aLabel p S ε₁*aLabel p S ε₂*squarefreeLabel p S v := by
  rw [firstActiveProduct_as_primeProduct]
  simp only [dilationLabel,j2Label,aLabel,squarefreeLabel,primeProduct,← Finset.prod_pow,
    ← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_congr rfl
  intro i hi
  congr 1
  simpa only [evenDouble,mul_comm] using local_first_conductor_balance (parity (v i)) (ε₁ i) (ε₂ i)

variable [∀ i,(Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_conductor_product_dvd (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) :
    (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)*
      dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂*jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣
      aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2 := by
  rw [firstActiveProduct_as_primeProduct,← primeProduct_add]
  simp only [dilationLabel,jLabel,aLabel,primeProduct,← Finset.prod_pow,← Finset.prod_mul_distrib,← pow_mul,← pow_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  simpa only [mul_comm] using local_first_conductor_bound (parity (v₁ i+v₂ i)) (ε₁ i) (ε₂ i) (v₁ i+v₂ i) (hv i hi)

variable (hp : ∀ i,p i≠0)
include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_conductor_norm_bound (S : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i∈S,0<v₁ i+v₂ i) (B : ℝ) (hB : 0≤B)
    (hb₁ : ‖ringComplex (primeProduct p S v₁)‖^2≤B)
    (hb₂ : ‖ringComplex (primeProduct p S v₂)‖^2≤B) :
    ‖ringComplex (∏ i∈cubeActiveSupport S (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2*
      ‖ringComplex (dilationLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2*
      ‖ringComplex (jLabel p S (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤
    ‖ringComplex (aLabel p S ε₁)‖^2*‖ringComplex (aLabel p S ε₂)‖^2*B^4 := by
  have hn : aLabel p S ε₁*aLabel p S ε₂*(primeProduct p S v₁*primeProduct p S v₂)^2≠0 := by
    apply mul_ne_zero (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
    exact pow_ne_zero _ (mul_ne_zero (primeProduct_ne_zero p hp _ _) (primeProduct_ne_zero p hp _ _))
  have h := element_norm_le_of_dvd hn (first_conductor_product_dvd p S v₁ v₂ ε₁ ε₂ hv)
  simp only [map_mul,map_pow,norm_mul,norm_pow,mul_pow] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hm := mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hs := pow_le_pow_left₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _)) hm 2
  convert hs using 1 <;> ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

theorem globalPooledRowScale_pos (K ell B F : ℝ) (hK : 0 < K) (hell : 0 < ell)
    (hB : 0 < B) (hF : 0 < F) (j : GlobalLogIndex) : 0 < globalPooledRowScale K ell B F j := by
  have h1 := globalLogRep_pos j 1
  have h4 := globalLogRep_pos j 4
  have h5 := globalLogRep_pos j 5
  unfold globalPooledRowScale
  positivity

def globalFirstIndex {ι : Type*} [DecidableEq ι] (p : ι → O)
    (side : Bool) (b : GlobalFirstData ι) : GlobalLogIndex :=
  globalScaleIndex p side (b.append ⟨∅, ∅, ∅, 1⟩)

def globalFirstPooledRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    (K ell B F : ℝ) (side : Bool) (b : GlobalFirstData ι) : ℝ :=
  globalPooledRowScale K ell B F (globalFirstIndex p side b)

lemma first_row_numeric_bound (an en jn a1 a2 cn dn hn fn ell K B F : ℝ)
    (ha : 0≤an) (he : 0≤en) (hj : 0<jn) (h1 : 0<a1) (h2 : 0<a2) (hc : 0<cn)
    (hd : 0≤dn) (_hh : 0≤hn) (hf : 0≤fn) (hell : 0<ell) (hK : 0<K) (_hB : 0<B) (hF : 0<F)
    (hcon : an*en*jn≤a1*a2*B^4) (hfreq : hn≤ell^2*an*dn/(K*a1*a2*cn^2)) (hlabel : fn≤F) :
    hn*fn^2*en≤ell^2*B^4*F^2*dn/(K*cn^2*jn) := by
  have hratio : an*en/(a1*a2)≤B^4/jn := by
    apply (div_le_div_iff₀ (mul_pos h1 h2) hj).mpr
    nlinarith only [hcon]
  calc
    hn*fn^2*en ≤ (ell^2*an*dn/(K*a1*a2*cn^2))*F^2*en := by
      apply mul_le_mul_of_nonneg_right _ he
      exact mul_le_mul hfreq (pow_le_pow_left₀ hf hlabel 2) (sq_nonneg _) (by positivity)
    _ = (ell^2*dn*F^2/(K*cn^2))*(an*en/(a1*a2)) := by
      field_simp

    _ ≤ (ell^2*dn*F^2/(K*cn^2))*(B^4/jn) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstRowScale_le_pooled (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) (b : GlobalCubeBlock ι) :
    globalFirstRowScale p K ell B F ((b.withCommon ∅).append ⟨∅,∅,∅,1⟩) ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).2
  have hc := (hbds 1).1
  have hJ := (hbds 4).1
  change primeProductNorm p b.firstDivisor≤globalLogRep j 5*Real.exp 1 at hd
  change globalLogRep j 1≤primeProductNorm p b.common at hc
  change globalLogRep j 4≤globalCubeJNorm p x at hJ
  change ell^2*B^4*F^2*primeProductNorm p b.firstDivisor/
      (K*(primeProductNorm p b.common)^2*globalCubeJNorm p x) ≤
    Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)
  have hdpos := (primeProductNorm_pos p hp b.firstDivisor).le
  have h5 := (globalLogRep_pos j 5).le
  apply div_le_div₀ (by positivity)
  · calc
      _ ≤ ell^2*B^4*F^2*(globalLogRep j 5*Real.exp 1) := by gcongr
      _ = _ := by ring
  · exact mul_pos (mul_pos hK (sq_pos_of_pos (globalLogRep_pos j 1))) (globalLogRep_pos j 4)
  · exact mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (globalLogRep_pos j 1).le hc 2) hK.le)
      hJ (globalLogRep_pos j 4).le (by positivity)

include hp in

/-- The first frequency cutoff and cube norm bounds give one common row range. -/
theorem first_row_enlargement (b : GlobalCubeBlock ι) (x : Ideal O × O)
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : (Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ‖ringComplex x.2‖^2 ≤
      ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
        (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
      primeProductNorm p b.firstDivisor/
      (K*‖ringComplex (aLabel p b.cube.support b.cube.leftBit)‖^2*
        ‖ringComplex (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)) :
    ‖ringComplex (DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x)‖^2 ≤
      globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  let active := cubeActiveSupport b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let e := dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let j := jLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit
  let a1 := aLabel p b.cube.support b.cube.leftBit
  let a2 := aLabel p b.cube.support b.cube.rightBit
  have hpos (v : ι → ℕ) : 0<‖ringComplex (primeProduct p b.cube.support v)‖^2 :=
    zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp _ _))
  have hcon := first_conductor_norm_bound p hp b.cube.support b.cube.leftExponent b.cube.rightExponent
    b.cube.leftBit b.cube.rightBit b.cube.support_pos B hB.le hb₁ hb₂
  have hnum := first_row_numeric_bound (primeProductNorm p active) (‖ringComplex e‖^2) (‖ringComplex j‖^2)
    (‖ringComplex a1‖^2) (‖ringComplex a2‖^2) (primeProductNorm p b.common) (primeProductNorm p b.firstDivisor)
    (‖ringComplex x.2‖^2) (Ideal.absNorm x.1) ell K B F
    (primeProductNorm_pos p hp active).le (sq_nonneg _) (hpos _) (hpos _) (hpos _)
    (primeProductNorm_pos p hp b.common) (primeProductNorm_pos p hp b.firstDivisor).le
    (sq_nonneg _) (Nat.cast_nonneg _) hell hK hB hF hcon hh hf
  have hgen : ‖ringComplex (cubicIdealGenerator x.1)‖^2=(Ideal.absNorm x.1 : ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span,span_cubicIdealGenerator]
  have hrow : ‖ringComplex (DescentWeightedCauchy.firstElementRowMap e x)‖^2 =
      ‖ringComplex x.2‖^2*(Ideal.absNorm x.1 : ℝ)^2*‖ringComplex e‖^2 := by
    simp only [DescentWeightedCauchy.firstElementRowMap,map_mul,map_pow,norm_mul,norm_pow,mul_pow]
    rw [show (‖ringComplex (cubicIdealGenerator x.1)‖^2)^2 =
        (Ideal.absNorm x.1 : ℝ)^2 by rw [hgen]]
  rw [hrow]
  exact hnum.trans (globalFirstRowScale_le_pooled p hp K ell B F hK hell hB hF b)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

def globalFirstFrequencyScale (K ell : ℝ) (b : GlobalCubeBlock ι) : ℝ :=
  ell^2*primeProductNorm p (cubeActiveSupport b.cube.support
    (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit)*
    primeProductNorm p b.firstDivisor/
    (K*‖ringComplex (aLabel p b.cube.support b.cube.leftBit)‖^2*
      ‖ringComplex (aLabel p b.cube.support b.cube.rightBit)‖^2*(primeProductNorm p b.common)^2)

def globalCubeFirstTargets (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O)) : Finset O :=
  s.image (DescentWeightedCauchy.firstElementRowMap
    (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
      b.cube.leftBit b.cube.rightBit))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_mem (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (x : Ideal O × O) (hx : x∈s) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
        b.cube.leftBit b.cube.rightBit) x∈globalCubeFirstTargets p b s :=
  Finset.mem_image.mpr ⟨x,hx,rfl⟩

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem globalCubeFirstTargets_ne_zero (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (hn : ∀ x∈s,x.1 ≠ ⊥) (hs0 : ∀ x∈s,x.2≠0)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) : z≠0 := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  apply mul_ne_zero
  · apply mul_ne_zero (hs0 x hx)
    exact pow_ne_zero _ (cubicIdealGenerator_ne_zero _ (hn x hx))
  · exact primeProduct_ne_zero p hp _ _

include hp in
theorem globalCubeFirstTargets_norm_bound (b : GlobalCubeBlock ι) (s : Finset (Ideal O × O))
    (K ell B F : ℝ) (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (hb₁ : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B)
    (hf : ∀ x∈s,(Ideal.absNorm x.1 : ℝ)≤F)
    (hh : ∀ x∈s,‖ringComplex x.2‖^2≤globalFirstFrequencyScale p K ell b)
    (z : O) (hz : z∈globalCubeFirstTargets p b s) :
    (Ideal.absNorm (Ideal.span {z}) : ℝ)≤globalFirstPooledRow p K ell B F true (b.withCommon ∅) := by
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hz
  rw [← ringComplex_norm_sq_eq_absNorm_span]
  exact first_row_enlargement p hp b x K ell B F hK hell hB hF hb₁ hb₂ (hf x hx) (hh x hx)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical
section

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)

include hp in
theorem globalCube_radical_bound (B : ℝ) (hB : 0 ≤ B) (x : GlobalSecondData ι)
    (hb₁ : ‖ringComplex (primeProduct p x.cube.support x.cube.leftExponent)‖^2 ≤ B)
    (hb₂ : ‖ringComplex (primeProduct p x.cube.support x.cube.rightExponent)‖^2 ≤ B) :
    primeProductNorm p x.cube.support ≤ B^2 := by
  have hd : (∏ i∈x.cube.support,p i) ∣ primeProduct p x.cube.support x.cube.leftExponent *
      primeProduct p x.cube.support x.cube.rightExponent := by
    rw [← primeProduct_add]
    apply Finset.prod_dvd_prod_of_dvd
    intro i hi
    simpa only [pow_one] using pow_dvd_pow (p i) (x.cube.support_pos i hi)
  have hb0 := mul_ne_zero (primeProduct_ne_zero p hp x.cube.support x.cube.leftExponent)
    (primeProduct_ne_zero p hp x.cube.support x.cube.rightExponent)
  have hn := element_norm_le_of_dvd hb0 hd
  simp only [map_mul,norm_mul,mul_pow] at hn
  exact hn.trans (by simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB)

end
def globalFirstRowCap (K ell B F : ℝ) : ℝ :=
  (Real.exp 1)^2*ell^2*B^6*F^2/K

theorem globalFirstRowCap_pos (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F) :
    0<globalFirstRowCap K ell B F := by
  unfold globalFirstRowCap
  positivity

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]

include hp in
theorem globalFirstPooledRow_le_cap (K ell B F : ℝ)
    (hK : 0<K) (hell : 0<ell) (hB : 0<B) (hF : 0<F)
    (b : GlobalCubeBlock ι) (hadm : GlobalCubeAdmissible b)
    (hb₁ : ‖ringComplex (primeProduct p b.cube.support b.cube.leftExponent)‖^2≤B)
    (hb₂ : ‖ringComplex (primeProduct p b.cube.support b.cube.rightExponent)‖^2≤B) :
    globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤globalFirstRowCap K ell B F := by
  let x := (b.withCommon ∅).append (⟨∅,∅,∅,1⟩ : SecondExpansionData ι)
  let j := globalScaleIndex p true x
  have hbds := globalScaleIndex_bounds p hp true x (by exact one_ne_zero)
  have hd := (hbds 5).1
  have hc := (hbds 1).2
  change globalLogRep j 5≤primeProductNorm p b.firstDivisor at hd
  change primeProductNorm p b.common≤globalLogRep j 1*Real.exp 1 at hc
  have hrad := globalCube_radical_bound p hp B hB.le x hb₁ hb₂
  have h1p := globalLogRep_pos j 1
  have hd' : globalLogRep j 5≤globalLogRep j 1*Real.exp 1*B^2 := by
    calc
      _ ≤ primeProductNorm p b.firstDivisor := hd
      _ ≤ primeProductNorm p (b.common∪b.cube.support) := primeProductNorm_mono p hp hadm.2.2
      _ = primeProductNorm p b.common*primeProductNorm p b.cube.support :=
        primeProductNorm_union p _ _ hadm.2.1
      _ ≤ (globalLogRep j 1*Real.exp 1)*B^2 :=
        mul_le_mul hc hrad (primeProductNorm_pos p hp _).le (by positivity)
  have h1 := globalLogRep_ge_one j 1
  have h4 := globalLogRep_ge_one j 4
  have h4p := globalLogRep_pos j 4
  have hm : globalLogRep j 1≤(globalLogRep j 1)^2*globalLogRep j 4 := by
    calc
      globalLogRep j 1 = globalLogRep j 1*1*1 := by ring
      _ ≤ globalLogRep j 1*globalLogRep j 1*globalLogRep j 4 := by gcongr
      _ = _ := by ring
  have hr : globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)≤Real.exp 1*B^2 := by
    apply (div_le_iff₀ (mul_pos (sq_pos_of_pos h1p) h4p)).mpr
    calc
      _ ≤ globalLogRep j 1*Real.exp 1*B^2 := hd'
      _ ≤ ((globalLogRep j 1)^2*globalLogRep j 4)*Real.exp 1*B^2 := by gcongr
      _ = _ := by ring
  change Real.exp 1*ell^2*B^4*F^2*globalLogRep j 5/(K*(globalLogRep j 1)^2*globalLogRep j 4)≤_
  calc
    _ = (Real.exp 1*ell^2*B^4*F^2/K)*(globalLogRep j 5/((globalLogRep j 1)^2*globalLogRep j 4)) := by ring
    _ ≤ (Real.exp 1*ell^2*B^4*F^2/K)*(Real.exp 1*B^2) :=
      mul_le_mul_of_nonneg_left hr (by positivity)
    _ = globalFirstRowCap K ell B F := by unfold globalFirstRowCap; ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def secondSourceCommonCoefficient (Ψ : O →* ℂ) (m c d : O) (G E : Finset ι) : ℂ :=
  (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
    Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
    (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ))

def truncatedSecondSource (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E ∈ G.powerset, ∑ k ∈ K G E,
    secondSourceCommonCoefficient p hg Ψ m c d G E *
      secondFrequencyKernel p hp hg F Ψ Ψ m (∏ i ∈ G \ E, p i) c d
        (∏ i ∈ E, p i) k (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

def secondSourceTail (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ G ∈ F.powerset, ∑ E ∈ G.powerset,
    secondSourceCommonCoefficient p hg Ψ m c d G E *
      ∑' k : {k : O // k ∉ K G E},
        secondFrequencyKernel p hp hg F Ψ Ψ m (∏ i ∈ G \ E, p i) c d
          (∏ i ∈ E, p i) k.val (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y

/-- The frequency cutoff retains its complete complementary lattice tail. -/
theorem inputConjugateRow_eq_truncated_add_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) (K : Finset ι → Finset ι → Finset O) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ m c d H z‖ ^ 2 : ℝ)) =
      truncatedSecondSource p hp hg F Ψ m c d H W Y K + secondSourceTail p hp hg F Ψ m c d H W Y K := by
  rw [inputConjugateRow_second_frequency_expansion p hp hg hinj F Ψ m c d H W Y hY]
  unfold truncatedSecondSource secondSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro G _
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro E hE
  have hs : Summable (fun k : O => secondFrequencyKernel p hp hg F Ψ Ψ m
      (∏ i ∈ G \ E, p i) c d (∏ i ∈ E, p i) k
      (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y) := by
    simp_rw [← residualSecondMode_eq_frequencyKernel p hp hg hinj F G E
      (Finset.mem_powerset.mp hE) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))]
    exact residualSecondMode_summable p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp
      F G Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
      (∏ i ∈ E, p i) (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) W Y hY
  rw [← hs.sum_add_tsum_subtype_compl (K G E)]
  simp only [secondSourceCommonCoefficient, mul_add, Finset.mul_sum]
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

abbrev secondFrequencyTest (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (S T : Finset ι) : ℂ :=
  ((Y : ℂ) / ((‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) *
    (‖ringComplex (∏ i ∈ T, p i)‖ : ℂ))) *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * primeProductNorm p S * primeProductNorm p T))

/-- Product norms extend the disjoint-pair kernel to the overlap expansion. -/
theorem secondFrequencyKernel_eq_product_test
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg F Ψ₁ Ψ₂ m r c d e k H₁ H₂ W Y =
      secondKernelPair p hg hp F Ψ₁ Ψ₂ m r c d e k H₁ H₂
        (secondFrequencyTest p e k W Y) := by
  unfold secondFrequencyKernel secondKernelPair
  apply Finset.sum_congr rfl
  intro S _
  apply Finset.sum_congr rfl
  intro T _
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, secondFrequencyTest, primeProductNorm_union p S T hd,
      Finset.prod_union hd, map_mul, norm_mul, Complex.ofReal_mul, mul_assoc]
  · simp only [if_neg hd]

/-- One finite expansion datum retains both residue phases and the full radial kernel. -/
def secondExpansionTerm (F : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ)
    (ray : QuadraticRayRing × QuadraticRayRing) (x : SecondExpansionData ι) : ℂ :=
  let r := ∏ i ∈ x.sourceCommon \ x.divisor, p i
  let e := ∏ i ∈ x.divisor, p i
  let Q := fun U => H (x.sourceCommon ∪ U)
  secondSourceCommonCoefficient p hg Ψ m c d x.sourceCommon x.divisor *
    secondTotalWeight p hg Ψ Ψ m r c d e x.frequency (ray, x.overlap) *
      secondChildKernelPair p hg F x.overlap Ψ Ψ m r c d e x.frequency (-x.frequency)
        (secondRayMask p hg ray.1 Q) (secondRayMask p hg ray.2 Q)
        (secondFrequencyTest p e x.frequency W Y)

/-- The finite source is exactly a sum over its arithmetic expansion data. -/
theorem truncatedSecondSource_eq_expansionPool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (K : Finset ι → Finset ι → Finset O) :
    truncatedSecondSource p hp hg F Ψ m c d H W Y K =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ x ∈ secondExpansionPool F K, secondExpansionTerm p hg F Ψ m c d H W Y ray x := by
  simp_rw [sum_secondExpansionPool]
  unfold truncatedSecondSource secondExpansionTerm
  simp only [secondFrequencyKernel_eq_product_test,
    secondKernelPair_eq_children p hg hp hinj hc hpr, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro G _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro E _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray _
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro V _
  apply Finset.sum_congr rfl
  intro k _
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def globalFirstBadLabel (b : GlobalFirstData ι) : O :=
  b0Label p b.cube.support (fun i => b.cube.leftExponent i + b.cube.rightExponent i)
    b.cube.leftBit b.cube.rightBit

def globalFirstRetainedLabel (b : GlobalFirstData ι) : O :=
  (∏ i ∈ b.common, p i) * jLabel p b.cube.support
    (fun i => b.cube.leftExponent i + b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit

def globalFirstInputTest (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (b : GlobalFirstData ι) : Finset ι → ℂ :=
  firstFixedColumn p hg side r (firstCoreTest
    (normalizedColumn p (fun S => g (columnLog p (globalFirstBlockColumnScale p ell side b) S)))
    V (columnLog p (globalFirstBlockColumnScale p ell side b)) side t b.firstCommon)

theorem globalFirstCoreRow_eq_input (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (r : QuadraticRayRing)
    (t : ℝ) (b : GlobalFirstData ι) (z : O) :
    globalFirstCoreRow p hg pool Ψ m g V ell side r t b z =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        (globalFirstRawPool pool b) Ψ (m * globalFirstBadLabel p b)
        (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
        (globalFirstInputTest p hg g V ell side r t b) z := rfl

def globalFirstTruncatedSource (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ b ∈ s, w b * truncatedSecondSource p hp hg (globalFirstRawPool pool b) Ψ
    (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
    (globalFirstInputTest p hg g V ell side r t b) W (Y b) (cutoff b)

def globalFirstSourceTail (pool : Finset ι) (s : Finset (GlobalFirstData ι))
    (w : GlobalFirstData ι → ℂ) (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ))
    (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) : ℂ :=
  ∑ b ∈ s, w b * secondSourceTail p hp hg (globalFirstRawPool pool b) Ψ
    (m * globalFirstBadLabel p b) (globalFirstRetainedLabel p b) (∏ i ∈ b.firstDivisor, p i)
    (globalFirstInputTest p hg g V ell side r t b) W (Y b) (cutoff b)

/-- The global reflected source splits into its finite frequency part and complete tail. -/
theorem globalFirstCoreRows_eq_truncated_add_tail
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ) (hY : ∀ b ∈ s, 0 < Y b)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    (∑ b ∈ s, w b * ∑' z : O, W (‖ringComplex z‖ ^ 2 / Y b) *
      (‖globalFirstCoreRow p hg pool Ψ m g V ell side r t b z‖ ^ 2 : ℝ)) =
      globalFirstTruncatedSource p hp hg pool s w Ψ m g V W ell side r t Y cutoff +
        globalFirstSourceTail p hp hg pool s w Ψ m g V W ell side r t Y cutoff := by
  unfold globalFirstTruncatedSource globalFirstSourceTail
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b hb
  simp_rw [globalFirstCoreRow_eq_input]
  rw [inputConjugateRow_eq_truncated_add_tail p hp hg hinj _ _ _ _ _ _ W (Y b) (hY b hb) (cutoff b)]
  exact mul_add _ _ _

def globalSecondLiteralTerm (pool : Finset ι) (Ψ : O →* ℂ) (m : O)
    (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool) (r : QuadraticRayRing) (t : ℝ)
    (Y : GlobalFirstData ι → ℝ) (ray : QuadraticRayRing × QuadraticRayRing)
    (x : GlobalSecondData ι) : ℂ :=
  secondExpansionTerm p hg (globalFirstRawPool pool x.first) Ψ
    (m * globalFirstBadLabel p x.first) (globalFirstRetainedLabel p x.first)
    (∏ i ∈ x.firstDivisor, p i) (globalFirstInputTest p hg g V ell side r t x.first) W (Y x.first) ray x.source

/-- The truncated first-pass source uses exactly the data counted by global divisor fibers. -/
theorem globalFirstTruncatedSource_eq_literal
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (pool : Finset ι) (s : Finset (GlobalFirstData ι)) (w : GlobalFirstData ι → ℂ)
    (Ψ : O →* ℂ) (m : O) (g V W : 𝓢(ℝ, ℂ)) (ell : ℝ) (side : Bool)
    (r : QuadraticRayRing) (t : ℝ) (Y : GlobalFirstData ι → ℝ)
    (cutoff : GlobalFirstData ι → Finset ι → Finset ι → Finset O) :
    globalFirstTruncatedSource p hp hg pool s w Ψ m g V W ell side r t Y cutoff =
      ∑ ray : QuadraticRayRing × QuadraticRayRing,
        ∑ x ∈ globalFirstExpansionPool pool s cutoff,
          w x.first * globalSecondLiteralTerm p hg pool Ψ m g V W ell side r t Y ray x := by
  unfold globalFirstTruncatedSource
  simp_rw [truncatedSecondSource_eq_expansionPool p hp hg hinj hc hpr]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro ray _
  rw [sum_globalFirstExpansionPool]
  rfl

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- A source prime kills a child column through either its mask or its retained label. -/
theorem secondChildColumn_zero_of_source_overlap
    (Ψ : O →* ℂ) (m c y : O) (H : Finset ι → ℂ)
    (G E V N : Finset ι) (hd : ¬ Disjoint G N) :
    secondChildColumn p hg Ψ (m * ∏ i ∈ G \ E, p i)
      (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y H N = 0 := by
  obtain ⟨i, hiG, hiN⟩ := Finset.not_disjoint_iff.mp hd
  by_cases hiE : i ∈ E
  · have hdiv : p i ∣ c * (∏ j ∈ E, p j) * ∏ j ∈ V, p j :=
      dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiE) c) _
    have hz : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N
        (c * (∏ j ∈ E, p j) * ∏ j ∈ V, p j) = 0 := by
      apply Finset.prod_eq_zero hiN
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv), MulChar.map_zero]
    simp only [secondChildColumn, hz, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]
  · have hdiv : p i ∣ m * ∏ j ∈ G \ E, p j :=
      dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p (Finset.mem_sdiff.mpr ⟨hiG, hiE⟩)) m
    have hz : primeCoprimeMask p N (m * ∏ j ∈ G \ E, p j) = 0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (fun h => h i hiN hdiv)
    simp only [secondChildColumn, hz, mul_zero, zero_mul]

theorem fixedChildKernelPair_remove_source
    (F G E V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg (F \ G) Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
      (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K := by
  have hz (N : Finset ι) (hNF : N ∈ F.powerset) (hNG : N ∉ (F \ G).powerset) :
      ¬ Disjoint G N := by
    intro hd
    apply hNG
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hNF) hi,
      fun hiG => Finset.disjoint_left.mp hd hiG hi⟩
  unfold fixedChildKernelPair
  calc
    _ = ∑ N ∈ (F \ G).powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hg Ψ₁ (m * ∏ i ∈ G \ E, p i)
          (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ H₁ N) *
        secondChildColumn p hg Ψ₂ (m * ∏ i ∈ G \ E, p i)
          (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₂ H₂ M * K N M := by
      apply Finset.sum_congr rfl
      intro N _
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro M hMF hMG
      rw [secondChildColumn_zero_of_source_overlap p hg Ψ₂ m c y₂ H₂ G E V M (hz M hMF hMG),
        mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro N hNF hNG
      rw [secondChildColumn_zero_of_source_overlap p hg Ψ₁ m c y₁ H₁ G E V N (hz N hNF hNG), star_zero]
      simp only [zero_mul, Finset.sum_const_zero]

theorem secondTotalWeight_zero_of_source_overlap
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d k : O) (G E V : Finset ι) (hEG : E ⊆ G)
    (ray : QuadraticRayRing × QuadraticRayRing) (hd : ¬ Disjoint G V) :
    secondTotalWeight p hg Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d
      (∏ i ∈ E, p i) k (ray, V) = 0 := by
  have hprod : (∏ i ∈ E, p i) * (∏ i ∈ G \ E, p i) = ∏ i ∈ G, p i := by
    rw [← Finset.prod_union disjoint_sdiff_self_right, Finset.union_sdiff_of_subset hEG]
  obtain ⟨i, hiG, hiV⟩ := Finset.not_disjoint_iff.mp hd
  have hz : primeCoprimeMask p V (m * ∏ i ∈ G, p i) = 0 := by
    rw [primeCoprimeMask_indicator]
    exact if_neg (fun h => h i hiV (dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiG) m))
  simp only [secondTotalWeight, secondCommonWeight, secondPreColumn, hprod, hz, mul_zero, zero_mul, star_zero]

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The retained label and mask remove both common prime supports. -/
theorem fixedChildKernelPair_remove_source_union
    (F G E V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c y₁ y₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg (F \ (G ∪ V)) Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
      (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K := by
  have hpool : F \ (G ∪ V) = (F \ V) \ G := by
    ext i
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto
  rw [hpool, fixedChildKernelPair_remove_source, fixedChildKernelPair_fixed_pool]

/-- Both residue families have fixed columns on the original prime pool. -/
theorem fixedChildKernelPair_first_residue_fixed_pool
    (F G E V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c y₁ y₂ : O)
    (negative₁ negative₂ : Bool) (r₁ r₂ s₁ s₂ : QuadraticRayRing)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
      (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂
      (secondRayColumn p hg s₁ (fun U => firstFixedColumn p hg negative₁ r₁ H₁ ((G ∪ V) ∪ U)))
      (secondRayColumn p hg s₂ (fun U => firstFixedColumn p hg negative₂ r₂ H₂ ((G ∪ V) ∪ U))) K =
      ∑ q : QuadraticRayRing × QuadraticRayRing,
        (star (firstFixedTransition p hg negative₁ (G ∪ V) r₁ q.1) *
          firstFixedTransition p hg negative₂ (G ∪ V) r₂ q.2) *
          fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
            (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂
            (combinedFixedColumn p hg negative₁ q.1 s₁ (fun U => H₁ ((G ∪ V) ∪ U)))
            (combinedFixedColumn p hg negative₂ q.2 s₂ (fun U => H₂ ((G ∪ V) ∪ U))) K := by
  calc
    _ = fixedChildKernelPair p hg (F \ (G ∪ V)) Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
        (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i) y₁ y₂
        (secondRayColumn p hg s₁ (fun U => firstFixedColumn p hg negative₁ r₁ H₁ ((G ∪ V) ∪ U)))
        (secondRayColumn p hg s₂ (fun U => firstFixedColumn p hg negative₂ r₂ H₂ ((G ∪ V) ∪ U))) K :=
      (fixedChildKernelPair_remove_source_union p hg F G E V Ψ₁ Ψ₂ m c y₁ y₂ _ _ K).symm
    _ = _ := by
      rw [fixedChildKernelPair_first_residue_separation]
      simp only [fixedChildKernelPair_remove_source_union]

def twoPassResidueWeight (negative₁ negative₂ : Bool) (G V : Finset ι)
    (r₁ r₂ : QuadraticRayRing) (ray s q : QuadraticRayRing × QuadraticRayRing) : ℂ :=
  (star (secondRayTransition p hg V ray.1 s.1) * secondRayTransition p hg V ray.2 s.2) *
    (star (firstFixedTransition p hg negative₁ (G ∪ V) r₁ q.1) *
      firstFixedTransition p hg negative₂ (G ∪ V) r₂ q.2)

theorem twoPassResidueWeight_norm_le (negative₁ negative₂ : Bool) (G V : Finset ι)
    (r₁ r₂ : QuadraticRayRing) (ray s q : QuadraticRayRing × QuadraticRayRing) :
    ‖twoPassResidueWeight p hg negative₁ negative₂ G V r₁ r₂ ray s q‖ ≤ 1 := by
  simp only [twoPassResidueWeight, norm_mul, norm_star]
  exact mul_le_one₀
    (mul_le_one₀ (secondRayTransition_norm_le p hg V ray.1 s.1) (norm_nonneg _)
      (secondRayTransition_norm_le p hg V ray.2 s.2))
    (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (mul_le_one₀ (firstFixedTransition_norm_le p hg negative₁ (G ∪ V) r₁ q.1) (norm_nonneg _)
      (firstFixedTransition_norm_le p hg negative₂ (G ∪ V) r₂ q.2))

/-- Successive common-factor decompositions preserve the two finite residue families. -/
theorem secondChildKernelPair_two_pass_residues
    (F G E V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d k₁ k₂ : O)
    (negative₁ negative₂ : Bool) (r₁ r₂ : QuadraticRayRing)
    (ray : QuadraticRayRing × QuadraticRayRing) (H₁ H₂ : Finset ι → ℂ)
    (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d
      (∏ i ∈ E, p i) k₁ k₂
      (secondRayMask p hg ray.1 (fun U => firstFixedColumn p hg negative₁ r₁ H₁ (G ∪ U)))
      (secondRayMask p hg ray.2 (fun U => firstFixedColumn p hg negative₂ r₂ H₂ (G ∪ U))) K =
      ∑ s : QuadraticRayRing × QuadraticRayRing, ∑ q : QuadraticRayRing × QuadraticRayRing,
        twoPassResidueWeight p hg negative₁ negative₂ G V r₁ r₂ ray s q *
          fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * ∏ i ∈ G \ E, p i)
            (c * (∏ i ∈ E, p i) * ∏ i ∈ V, p i)
            (d * (∏ i ∈ E, p i) * k₁) (d * (∏ i ∈ E, p i) * k₂)
            (combinedFixedColumn p hg negative₁ q.1 s.1 (fun U => H₁ ((G ∪ V) ∪ U)))
            (combinedFixedColumn p hg negative₂ q.2 s.2 (fun U => H₂ ((G ∪ V) ∪ U)))
            (fun N M => K (V ∪ N) (V ∪ M)) := by
  rw [secondChildKernelPair_ray_fixed_pool_weighted]
  simp only [← Finset.union_assoc]
  simp_rw [fixedChildKernelPair_first_residue_fixed_pool]
  simp only [Finset.mul_sum, twoPassResidueWeight, mul_assoc]

end FirstPassCubeLabels

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
