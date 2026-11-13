/-
Canonical dual zero modes adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalLogEnergy

/-!
# Canonical dual zero modes

Zero and tail parts of the canonical cube dual and of the canonical source blocks, with
uniform kernel tails and the padded transfer of oriented first blocks.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
def canonicalCubeDualZero (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      supportMobius D/(primeProductNorm p D:ℂ)*
      actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        ((∏i∈D,p i)) 0

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
def canonicalCubeDualFinite (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      supportMobius D/(primeProductNorm p D:ℂ)*
      ∑h∈(T D).erase 0,actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        ((∏i∈D,p i)) h

def canonicalCubeDualTail (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (T:Finset ι→Finset O):ℂ:=
  canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      supportMobius D/(primeProductNorm p D:ℂ)*
      ∑'h:{h:O // h∉T D},actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f H₁)
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f H₂)
        W (fun _=>1) (fun _=>1) 1 1 K
        ((∏i∈D,p i)) h.val

theorem canonicalCubeBeforePoisson_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂ f:O) (H₁ H₂:Finset ι→ℂ)
    (W:𝓢(ℝ,ℂ)) (K:ℝ) (hK:0<K) (T:Finset ι→Finset O)
    (hT:∀D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,(0:O)∈T D):
    canonicalCubeBeforePoisson p hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K+
      canonicalCubeDualFinite p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T+
      canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K T := by
  rw [canonicalCubeBeforePoisson_eq_all_modes p hp hg hinj hc]
  · unfold canonicalCubeDualZero canonicalCubeDualFinite canonicalCubeDualTail
    rw [←mul_add,←mul_add,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply congrArg
    apply Finset.sum_congr rfl
    intro D hD
    rw [actualFirstKernel_truncate p hp hg _ _ _ _ _ _ _ _ _ _ _ _ _ hK _
      (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)) (T D)]
    rw [←Finset.sum_erase_add _ _ (hT D hD)]
    ring
  · exact hK

theorem canonicalCubeDualFinite_eq_raw_blocks
    (pool:Finset ι) (b:CubeCoordinates ι) (C:Finset ι) (labels:Finset (Ideal O))
    (a:Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ))
    (K ell:ℝ) (T:Finset ι→Finset O):
    (∑I∈labels,a I*canonicalCubeDualFinite p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W K T)=
    ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
      rawCanonicalBlock p hp hg pool (sourceGlobalBlock b C D) (labels.product ((T D).erase 0))
        (fun x=>a x.1*canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator x.1)) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W K ell := by
  simp only [canonicalCubeDualFinite,rawCanonicalBlock,sourceGlobalBlock,
    CubeCoordinates.swap_swap,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro D hD
  rw [Finset.product_eq_sprod,Finset.sum_product]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro h hh
  ring

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
def canonicalSourceBlocks (pool:Finset ι) (bs:Finset (CubeCoordinates ι)):Finset (GlobalCubeBlock ι):=
  bs.biUnion (fun b=>(pool\b.support).powerset.biUnion (fun C=>
    (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset.image
      (sourceGlobalBlock b C)))

theorem canonicalSourceBlocks_mem (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (q:GlobalCubeBlock ι):
    q∈canonicalSourceBlocks pool bs ↔ ∃b∈bs,∃C∈(pool\b.support).powerset,
      ∃D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
        sourceGlobalBlock b C D=q := by
  simp only [canonicalSourceBlocks,Finset.mem_biUnion,Finset.mem_image]

theorem sum_canonicalSourceBlocks {M:Type*} [AddCommMonoid M]
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (f:GlobalCubeBlock ι→M):
    (∑q∈canonicalSourceBlocks pool bs,f q)=
      ∑b∈bs,∑C∈(pool\b.support).powerset,
        ∑D∈(C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit).powerset,
          f (sourceGlobalBlock b C D) := by
  unfold canonicalSourceBlocks
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro b hb
    rw [Finset.sum_biUnion]
    · apply Finset.sum_congr rfl
      intro C hC
      rw [Finset.sum_image]
      intro D hD E hE he
      exact congrArg GlobalCubeBlock.firstDivisor he
    · intro C hC D hD hne
      apply Finset.disjoint_left.mpr
      intro q hq hq'
      obtain ⟨E,hE,he⟩:=Finset.mem_image.mp hq
      obtain ⟨F,hF,hf⟩:=Finset.mem_image.mp hq'
      exact hne (congrArg GlobalCubeBlock.common (he.trans hf.symm))
  · intro b hb c hc hne
    apply Finset.disjoint_left.mpr
    intro q hq hq'
    obtain ⟨C,hC,E,hE,he⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq
    obtain ⟨D,hD,F,hF,hf⟩:=by
      simpa only [Finset.mem_biUnion,Finset.mem_image] using hq'
    have hswap:=congrArg (fun q:GlobalCubeBlock ι=>q.cube.swap) (he.trans hf.symm)
    exact hne (by simpa only [sourceGlobalBlock,CubeCoordinates.swap_swap] using hswap)

theorem canonicalSourceBlocks_admissible (pool:Finset ι) (bs:Finset (CubeCoordinates ι))
    (hadm:∀b∈bs,b.Admissible) (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    GlobalCubeAdmissible q := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  have ha:=hadm b hb
  constructor
  · constructor
    · change b.rightDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.2
    · change b.leftDivisor⊆b.swap.support
      rw [cube_swap_support]
      exact ha.1
  constructor
  · change Disjoint C b.swap.support
    rw [cube_swap_support]
    exact Finset.disjoint_left.mpr (fun i hi hbi=>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hC) hi)).2 hbi)
  · change D⊆C∪b.swap.support
    rw [cube_swap_support]
    exact (Finset.mem_powerset.mp hD).trans
      (Finset.union_subset_union_right (Finset.filter_subset _ _))

theorem canonicalSourceBlocks_cube_norms
    (p:ι→O) (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (B:ℝ)
    (hleft:∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B)
    (hright:∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs):
    ‖ringComplex (primeProduct p q.cube.support q.cube.leftExponent)‖^2≤B ∧
      ‖ringComplex (primeProduct p q.cube.support q.cube.rightExponent)‖^2≤B := by
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  change ‖ringComplex (primeProduct p b.swap.support b.rightExponent)‖^2≤B ∧
    ‖ringComplex (primeProduct p b.swap.support b.leftExponent)‖^2≤B
  rw [cube_swap_support]
  exact ⟨hright b hb,hleft b hb⟩

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
def canonicalSourceCutoff (K ell:ℝ) (b:CubeCoordinates ι) (C D:Finset ι):Finset O:=
  firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma canonicalSourceCutoff_zero (K ell:ℝ) (hK:0≤K) (b:CubeCoordinates ι) (C D:Finset ι):
    (0:O)∈canonicalSourceCutoff p K ell b C D := by
  apply (mem_firstFrequencyDisk _ 0).mpr
  simp only [map_zero,norm_zero,zero_pow (by decide : (2:ℕ)≠0)]
  unfold globalFirstFrequencyScale
  simp only [primeProductNorm]
  positivity

def canonicalSourceTotal (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeBeforePoisson p hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceZero (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc

def canonicalSourceFinite (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualFinite p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalSourceTail (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):ℂ:=
  ∑b∈bs,∑C∈(pool\b.support).powerset,∑I∈labels,a b C I*
    canonicalCubeDualTail p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc (canonicalSourceCutoff p K ell b C)

def canonicalBlockFrequencies (K ell:ℝ) (labels:Finset (Ideal O)) (q:GlobalCubeBlock ι):Finset (Ideal O×O):=
  labels.product ((firstFrequencyDisk (globalFirstFrequencyScale p K ell q)).erase 0)

def canonicalBlockCoefficient (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ)
    (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O) (q:GlobalCubeBlock ι) (x:Ideal O×O):ℂ:=
  a q.cube.swap q.common x.1*canonicalCubeOuter p hg q.cube.swap q.common
    Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)

theorem canonicalSourceFinite_eq_raw
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ):
    canonicalSourceFinite p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell=
      ∑q∈canonicalSourceBlocks pool bs,rawCanonicalBlock p hp hg pool q
        (canonicalBlockFrequencies p K ell labels q)
        (canonicalBlockCoefficient p hg a Ψ₁ Ψ₂ m₁ m₂ q)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell := by
  rw [sum_canonicalSourceBlocks]
  unfold canonicalSourceFinite
  apply Finset.sum_congr rfl
  intro b hb
  apply Finset.sum_congr rfl
  intro C hC
  rw [canonicalCubeDualFinite_eq_raw_blocks]
  apply Finset.sum_congr rfl
  intro D hD
  simp only [canonicalBlockFrequencies,canonicalSourceCutoff,
    sourceGlobalBlock]
  rfl

theorem canonicalSourceTotal_split
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (g₁ g₂ W:𝓢(ℝ,ℂ)) (Ksrc K ell:ℝ) (hKsrc:0<Ksrc) (hK:0≤K):
    canonicalSourceTotal p hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell=
      canonicalSourceZero p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc ell+
      canonicalSourceFinite p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell+
      canonicalSourceTail p hp hg pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Ksrc K ell := by
  unfold canonicalSourceTotal canonicalSourceZero canonicalSourceFinite canonicalSourceTail
  have hsplit (b:CubeCoordinates ι) (C:Finset ι) (I:Ideal O):=
    canonicalCubeBeforePoisson_split p hp hg hinj hc pool b C Ψ₁ Ψ₂ m₁ m₂
      (cubicIdealGenerator I) (fun S=>g₁ (columnLog p ell S))
      (fun S=>g₂ (columnLog p ell S)) W Ksrc hKsrc (canonicalSourceCutoff p K ell b C)
      (fun D hD=>canonicalSourceCutoff_zero p K ell hK b C D)
  simp_rw [hsplit]
  simp only [mul_add,Finset.sum_add_distrib]

include hp in
theorem canonicalBlockCoefficient_bound
    (hinj:Function.Injective (fun i=>Ideal.span {p i}))
    (hpr:∀i,lambda^2∣p i-1)
    (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
    (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ) (m₁ m₂:O)
    (Γ K ell:ℝ) (hΓ:0≤Γ) (hΨ₁:∀u,‖Ψ₁ u‖≤1) (hΨ₂:∀u,‖Ψ₂ u‖≤1)
    (ha:∀b∈bs,∀C∈(pool\b.support).powerset,∀I∈labels,‖a b C I‖≤Γ)
    (q:GlobalCubeBlock ι) (hq:q∈canonicalSourceBlocks pool bs)
    (x:Ideal O×O) (hx:x∈canonicalBlockFrequencies p K ell labels q):
    ‖canonicalBlockCoefficient p hg a Ψ₁ Ψ₂ m₁ m₂ q x‖≤Γ := by
  have hI:x.1∈labels:=(Finset.mem_product.mp hx).1
  obtain ⟨b,hb,C,hC,D,hD,rfl⟩:=(canonicalSourceBlocks_mem pool bs q).mp hq
  simp only [canonicalBlockCoefficient,sourceGlobalBlock,CubeCoordinates.swap_swap,norm_mul]
  exact (mul_le_mul (ha b hb C hC x.1 hI)
    (canonicalCubeOuter_norm_le_one p hp hg hinj hpr b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ _)
    (norm_nonneg _) hΓ).trans_eq (mul_one Γ)

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
lemma blockRow_at_zero (S:Finset ι) (e:ι→ℕ) :
    blockRow p hg S e 0=if S=∅ then 1 else 0 := by
  by_cases hS:S=∅
  · simp [hS,blockRow_eq_product]
  · rw [if_neg hS,blockRow_eq_product]
    obtain ⟨i,hi⟩:=Finset.nonempty_iff_ne_empty.mpr hS
    apply Finset.prod_eq_zero hi
    simp only [map_zero,MulChar.map_zero]

lemma threeGaussRowFactor_zero_nonempty
    (N P B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (d:O)
    (hne:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d 0=0 := by
  simp only [threeGaussRowFactor,blockRow_at_zero,if_neg hne,star_zero,mul_zero]

theorem actualFirstKernel_zero
    (F B:Finset ι) (v:ι→ℕ) (ε₁ ε₂:ι→Bool)
    (C₁ C₂:Finset ι→ℂ) (W:𝓢(ℝ,ℂ)) (V₁ V₂:ℝ→ℂ)
    (X₁ X₂ K:ℝ) (d:O) :
    actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d 0 =
      if cubeActiveSupport B v ε₁ ε₂=∅ then
        (V₁ (columnLog p X₁ ∅)*V₂ (columnLog p X₂ ∅))*(K:ℂ)*paperRadialFourier W 0*
          threeGaussRowFactor p hp hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d 0 else 0 := by
  unfold actualFirstKernel
  by_cases hB:cubeActiveSupport B v ε₁ ε₂=∅
  · rw [if_pos hB,Finset.sum_eq_single ∅]
    · rw [Finset.sum_eq_single ∅]
      · simp only [Finset.disjoint_empty_left,ite_true,Finset.empty_union,hB,
          Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,map_zero,norm_zero,
          zero_pow (by decide:2≠0),mul_zero,zero_div]
      · intro P hP hP0
        have hn:(∅∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by simpa only [Finset.empty_union,hB,Finset.union_empty] using hP0
        simp only [threeGaussRowFactor_zero_nonempty p hp hg ∅ P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
      · simp
    · intro N hN hN0
      apply Finset.sum_eq_zero
      intro P hP
      have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
        intro he
        exact hN0 (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
          have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_left _ (Finset.mem_union_left _ hi)
          simp only [he, Finset.notMem_empty] at this))
      simp only [threeGaussRowFactor_zero_nonempty p hp hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]
    · simp
  · rw [if_neg hB]
    apply Finset.sum_eq_zero
    intro N hN
    apply Finset.sum_eq_zero
    intro P hP
    have hn:(N∪P)∪cubeActiveSupport B v ε₁ ε₂≠∅ := by
      intro he
      exact hB (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi=>by
        have : i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂:=Finset.mem_union_right _ hi
        simp only [he, Finset.notMem_empty] at this))
    simp only [threeGaussRowFactor_zero_nonempty p hp hg N P B v ε₁ ε₂ C₁ C₂ d hn,mul_zero,ite_self]

lemma threeGaussRowFactor_empty
    (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O)
    (hB : cubeActiveSupport B v ε₁ ε₂=∅) :
    threeGaussRowFactor p hp hg ∅ ∅ B v ε₁ ε₂ C₁ C₂ d h=
      star (C₁ ∅)*C₂ ∅ := by
  have hG (χ : ∀i,MulChar (O⧸Ideal.span {p i}) ℂ) :
      normalizedSubsetTraceGauss p hp χ ∅=1 := by
    simp only [normalizedSubsetTraceGauss,subsetTraceGauss,primeRowTraceGauss_empty,
      Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one]
  simp only [threeGaussRowFactor,Finset.empty_union,hB,hG,secondColumnCoefficient,
    Finset.prod_empty,map_one,norm_one,Complex.ofReal_one,div_one,
    normalizedCubicUnitGauss_one,star_one,one_mul,mul_one,blockRow,primeSubsetRow]


end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels TruncatedPrincipalPoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
lemma canonicalCubeResidual_empty (b : CubeCoordinates ι) (C : Finset ι)
    (negative : Bool) (Ψ : O→*ℂ) (m f : O) (H : Finset ι→ℂ) :
    canonicalCubeResidual p hg b C negative Ψ m f H ∅=
      H ((if negative then b.rightDivisor else b.leftDivisor)∪C) := by
  simp [canonicalCubeResidual,originalLabelColumn,multiplicativeCoreColumn,
    primeSubsetRow,primeCoprimeMask]

lemma supportMobius_norm_sum (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (S : Finset ι) :
    (∑D∈S.powerset,supportMobius D/(primeProductNorm p D:ℂ)) =
      ∏i∈S,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})) := by
  have hprime (i : ι) : Prime (Ideal.span {p i}) :=
    Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance
  rw [← primeSubset_moebius_norm_sum (fun i=>Ideal.span {p i}) hprime hinj S]
  apply Finset.sum_congr rfl
  intro D hD
  rw [prime_product_moebius _ hprime hinj]
  simp only [supportMobius,primeProductNorm,ringComplex_norm_sq_eq_absNorm_span,
    span_finset_prime_product,Complex.ofReal_natCast]
theorem canonicalCubeDualZero_eq_density
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ)
    (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K=
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ f*
          (star (H₁ (b.rightDivisor∪C))*H₂ (b.leftDivisor∪C))*
          (K:ℂ)*paperRadialFourier W 0*
          ∏i∈C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit,
            (1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i}))
      else 0 := by
  unfold canonicalCubeDualZero
  simp_rw [actualFirstKernel_zero]
  split_ifs with hB
  · simp only [threeGaussRowFactor_empty p hp hg _ _ _ _ _ _ _ _ hB,
      canonicalCubeResidual_empty,Bool.false_eq_true,ite_true,ite_false,one_mul]
    rw [←Finset.sum_mul]
    rw [supportMobius_norm_sum p hinj]
    ring
  · simp only [mul_zero,Finset.sum_const_zero]

theorem canonicalCubeDualZero_norm_le
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (hpr : ∀i,lambda^2∣p i-1)
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (H₁ H₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    ‖canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f H₁ H₂ W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖*|K| *‖paperRadialFourier W 0‖ else 0 := by
  rw [canonicalCubeDualZero_eq_density p hp hg hinj]
  split_ifs with hB
  · let M := C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit
    have hprod : (∏i∈M,(1-(1:ℂ)/Ideal.absNorm (Ideal.span {p i})))=
        ((∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i}))):ℝ) := by
      simp only [Complex.ofReal_prod,Complex.ofReal_sub,Complex.ofReal_one,
        Complex.ofReal_div,Complex.ofReal_natCast]
    rw [show (C∪cubePrincipalSupport b.support b.leftExponent b.rightExponent b.leftBit b.rightBit)=M from rfl,hprod]
    simp only [norm_mul,norm_star,Complex.norm_real,Real.norm_eq_abs,
      abs_of_nonneg (primeDensity_nonneg_le_one p M).1]
    calc
      _ ≤ 1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖*
          ∏i∈M,(1-(1:ℝ)/Ideal.absNorm (Ideal.span {p i})) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_right
                (canonicalCubeOuter_norm_le_one p hp hg hinj hpr b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f)
                (mul_nonneg (norm_nonneg _) (norm_nonneg _))) (abs_nonneg _)) (norm_nonneg _))
          (primeDensity_nonneg_le_one p M).1
      _ ≤ _ := by
        simpa only [one_mul] using mul_le_of_le_one_right
          (show 0≤(1*(‖H₁ (b.rightDivisor∪C)‖*‖H₂ (b.leftDivisor∪C)‖)*|K| *‖paperRadialFourier W 0‖) by positivity)
          (primeDensity_nonneg_le_one p M).2
  · simp

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

theorem boundedPrimeSupports_card_positive {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i=>Ideal.span {p i}))
    (F : Finset ι) (X : ℝ) (hX : 0<X) :
    ((boundedPrimeSupports p F X).card:ℝ)≤(1+diagonalControl sieveCutoff)*X := by
  have hdc := diagonalControl_nonneg sieveCutoff
  by_cases hx : 1≤X
  · exact (boundedPrimeSupports_card p hinj F X hx).trans
      (mul_le_mul_of_nonneg_right (by linarith) hX.le)
  · have he : boundedPrimeSupports p F X=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro S hS
      exact hx ((primeProductNorm_ge_one p hp S).trans (Finset.mem_filter.mp hS).2)
    rw [he,Finset.card_empty,Nat.cast_zero]
    positivity

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
  (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hpr : ∀i,lambda^2∣p i-1)
include hinj
theorem canonicalCubeDualZero_support
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (ell K M : ℝ) (hell : 0<ell) (hgM : ∀t,g₁ t≠0→t≤M)
    (hC : ¬primeProductNorm p C≤ell*Real.exp M) :
    canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K=0 := by
  have hz : g₁ (columnLog p ell (b.rightDivisor∪C))=0 := by
    by_contra h
    exact hC ((primeProductNorm_mono p hp (Finset.subset_union_right)).trans
      (columnLog_norm_upper p hp ell M hell _ (hgM _ h)))
  rw [canonicalCubeDualZero_eq_density p hp hg hinj]
  split_ifs <;> simp [hz]

include hpr

theorem canonicalCubeDualZero_fixed_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
    (Ψ₁ Ψ₂ : O→*ℂ) (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ f : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (G₁ G₂ ell K : ℝ) (hG₁ : 0≤G₁) (_hG₂ : 0≤G₂)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) :
    ‖canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂ f
      (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        G₁*G₂*|K| *‖paperRadialFourier W 0‖ else 0 := by
  apply (canonicalCubeDualZero_norm_le p hp hg hinj hpr pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f _ _ W K).trans
  split_ifs
  · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul (hg₁ _) (hg₂ _) (norm_nonneg _) hG₁) (abs_nonneg _)) (norm_nonneg _)
  · exact le_rfl

theorem canonicalCubeZero_common_sum_bound
    (pool : Finset ι) (b : CubeCoordinates ι) (labels : Finset (Ideal O))
    (a : Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀u,‖Ψ₂ u‖≤1)
    (m₁ m₂ : O) (g₁ g₂ W : 𝓢(ℝ,ℂ))
    (Γ G₁ G₂ ell K M : ℝ) (hΓ : 0≤Γ) (hG₁ : 0≤G₁) (hG₂ : 0≤G₂) (hell : 0<ell)
    (ha : ∀C∈(pool\b.support).powerset,∀I∈labels,‖a C I‖≤Γ)
    (hg₁ : ∀t,‖g₁ t‖≤G₁) (hg₂ : ∀t,‖g₂ t‖≤G₂) (hgM : ∀t,g₁ t≠0→t≤M) :
    ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*
      canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
        (cubicIdealGenerator I)
        (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      if cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ then
        ((1+diagonalControl sieveCutoff)*(ell*Real.exp M))*(labels.card:ℝ)*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) else 0 := by
  let z (C:Finset ι) (I:Ideal O):ℂ:=canonicalCubeDualZero p hp hg pool b C Ψ₁ Ψ₂ m₁ m₂
    (cubicIdealGenerator I)
    (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K
  let Q:ℝ:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  have hdc := diagonalControl_nonneg sieveCutoff
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hL:0<ell*Real.exp M:=mul_pos hell (Real.exp_pos _)
  have heq : (∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I)=
      ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,a C I*z C I := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro C hC hnot
    have hbnd : ¬primeProductNorm p C≤ell*Real.exp M:=fun h=>hnot (Finset.mem_filter.mpr ⟨hC,h⟩)
    apply Finset.sum_eq_zero
    intro I hI
    rw [show z C I=0 from canonicalCubeDualZero_support p hp hg hinj pool b C Ψ₁ Ψ₂ m₁ m₂ _ g₁ g₂ W ell K M hell hgM hbnd,mul_zero]
  change ‖∑C∈(pool\b.support).powerset,∑I∈labels,a C I*z C I‖≤_
  rw [heq]
  by_cases hb : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  · rw [if_pos hb]
    have hpnt (C:Finset ι) (hC:C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)) (I:Ideal O) (hI:I∈labels):‖a C I*z C I‖≤Q:=by
      rw [norm_mul]
      have hz:=canonicalCubeDualZero_fixed_bound p hp hg hinj hpr pool b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ (cubicIdealGenerator I) g₁ g₂ W G₁ G₂ ell K hG₁ hG₂ hg₁ hg₂
      rw [if_pos hb] at hz
      exact mul_le_mul (ha C (Finset.mem_filter.mp hC).1 I hI) hz (norm_nonneg _) hΓ
    calc
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,‖a C I*z C I‖:=
        (norm_sum_le _ _).trans (Finset.sum_le_sum (fun C hC=>norm_sum_le _ _))
      _ ≤ ∑C∈boundedPrimeSupports p (pool\b.support) (ell*Real.exp M),∑I∈labels,Q:=
        Finset.sum_le_sum (fun C hC=>Finset.sum_le_sum (fun I hI=>hpnt C hC I hI))
      _ = ((boundedPrimeSupports p (pool\b.support) (ell*Real.exp M)).card:ℝ)*(labels.card:ℝ)*Q:=by simp;ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (boundedPrimeSupports_card_positive p hp hinj _ _ hL) (Nat.cast_nonneg _)) hQ
  · rw [if_neg hb]
    have hz (C:Finset ι) (I:Ideal O):z C I=0:=by
      dsimp [z]
      rw [canonicalCubeDualZero_eq_density p hp hg hinj,if_neg hb]
    simp only [hz,mul_zero,Finset.sum_const_zero,norm_zero,le_refl]

end

theorem full_uniform_canonicalFirstZero_bound (ε : ℝ) (hε : 0<ε) :
    ∃C:ℝ,0<C ∧ ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hpr:∀i,lambda^2∣p i-1)
      (pool:Finset ι) (bs:Finset (CubeCoordinates ι)) (labels:Finset (Ideal O))
      (a:CubeCoordinates ι→Finset ι→Ideal O→ℂ) (Ψ₁ Ψ₂:O→*ℂ)
      (m₁ m₂:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (Γ G₁ G₂ ell K M B F:ℝ),
      0≤Γ → 0≤G₁ → 0≤G₂ → 0<ell → 1≤B → 1≤F →
      (∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      (∀b∈bs,b.Admissible) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.leftExponent)‖^2≤B) →
      (∀b∈bs,‖ringComplex (primeProduct p b.support b.rightExponent)‖^2≤B) →
      (∀I∈labels,I≠0) → (∀I∈labels,(Ideal.absNorm I:ℝ)≤F) →
      (∀b∈bs,∀D∈(pool\b.support).powerset,∀I∈labels,‖a b D I‖≤Γ) →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) → (∀t,g₁ t≠0→t≤M) →
      ‖∑b∈bs,∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖≤
      C*B^(1+ε)*(ell*Real.exp M)*F*(Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨C,hC,hcount⟩:=cube_coordinates_parity_count ε hε
  refine ⟨C*(1+diagonalControl sieveCutoff)*(1+diagonalControl sieveCutoff),by positivity,?_⟩
  intro ι _ p hp _ hcop hg hinj hpr pool bs labels a Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M B F hΓ hG₁ hG₂ hell hB hF hΨ₁ hΨ₂ hadm hb1 hb2 hI0 hIF ha hg₁ hg₂ hgM
  let Q:=Γ*(G₁*G₂*|K| *‖paperRadialFourier W 0‖)
  let good:=fun b:CubeCoordinates ι=>cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅
  have hdc := diagonalControl_nonneg sieveCutoff
  have hQ:0≤Q:=by dsimp [Q];positivity
  have hlabel:(labels.card:ℝ)≤(1+diagonalControl sieveCutoff)*F:=(finite_ideal_card_bound labels F hF hIF).trans
    (mul_le_mul_of_nonneg_right (by linarith) (zero_le_one.trans hF))
  have hbcount:((bs.filter good).card:ℝ)≤C*B^(1+ε):=by
    have h:=hcount p hp hinj (bs.filter good) B 1 hB (by norm_num)
      (fun b hb=>hadm b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb1 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>hb2 b (Finset.mem_filter.mp hb).1)
      (fun b hb=>by
        have he : cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit=∅ := (Finset.mem_filter.mp hb).2
        rw [he]
        simp)
    simpa only [mul_one] using h
  calc
    _ ≤ ∑b∈bs,‖∑D∈(pool\b.support).powerset,∑I∈labels,a b D I*
        canonicalCubeDualZero p hp hg pool b D Ψ₁ Ψ₂ m₁ m₂
          (cubicIdealGenerator I)
          (fun S=>g₁ (columnLog p ell S)) (fun S=>g₂ (columnLog p ell S)) W K‖:=norm_sum_le _ _
    _ ≤ ∑b∈bs,if good b then ((1+diagonalControl sieveCutoff)*(ell*Real.exp M))*(labels.card:ℝ)*Q else 0:=by
      apply Finset.sum_le_sum
      intro b hb
      exact canonicalCubeZero_common_sum_bound p hp hg hinj hpr pool b labels (a b) Ψ₁ Ψ₂ hΨ₁ hΨ₂
        m₁ m₂ g₁ g₂ W Γ G₁ G₂ ell K M hΓ hG₁ hG₂ hell (ha b hb) hg₁ hg₂ hgM
    _ = ((bs.filter good).card:ℝ)*(((1+diagonalControl sieveCutoff)*(ell*Real.exp M))*(labels.card:ℝ)*Q):=by
      rw [←Finset.sum_filter];simp
    _ ≤ (C*B^(1+ε))*(((1+diagonalControl sieveCutoff)*(ell*Real.exp M))*((1+diagonalControl sieveCutoff)*F)*Q):=by
      apply mul_le_mul hbcount _ (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hlabel (by positivity)) hQ
    _ = _ := by dsimp [Q];ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i=>Ideal.span {p i})) (hg : ∀i,lambda∉Ideal.span {p i})
lemma threeBlockExponent_ne_zero_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i≠0 := by
  intro i hi
  by_cases hn:i∈N
  · simp [threeBlockExponent,hn]
  by_cases hp':i∈P
  · simp [threeBlockExponent,hn,hp']
  · have hiC:i∈cubeActiveSupport B v ε₁ ε₂ := by simpa [hn,hp'] using hi
    simp only [threeBlockExponent,if_neg hn,if_neg hp']
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2

lemma threeBlockExponent_lt_six_on (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool) :
    ∀i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,threeBlockExponent N P v ε₁ ε₂ i<6 := by
  intro i hi
  unfold threeBlockExponent
  split_ifs <;> first | omega | exact ZMod.val_lt _

include hp hinj hg in
lemma secondColumnCoefficient_norm_one_of_good
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2) (S : Finset ι) :
    ‖secondColumnCoefficient p S‖=1 := by
  have hn : ‖ringComplex (∏i∈S,p i)‖≠0 :=
    norm_ne_zero_iff.mpr (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)))
  rw [secondColumnCoefficient_eq_gaussBlock p hp hinj hg S, norm_mul, norm_star,
    norm_div, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _), div_self hn, one_mul]
  exact gaussBlock_norm_one p hp hinj hg hc S (fun _=>2)
    (fun _ _=>by decide) (fun _ _=>by decide)

include hinj in
lemma threeGaussRowFactor_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (d h : O) :
    ‖threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h‖≤‖C₁ N‖*‖C₂ P‖ := by
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hG := normalizedSubsetTraceGauss_norm_one p hp hinj
    (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)^e i) S (fun i hi=>
      complexSexticChar_pow_ne_one (Ideal.span {p i}) (hg i) (hc i) (e i)
        (threeBlockExponent_lt_six_on N P B v ε₁ ε₂ i hi)
        (threeBlockExponent_ne_zero_on N P B v ε₁ ε₂ i hi))
  change ‖star (secondColumnCoefficient p N*C₁ N)*(secondColumnCoefficient p P*C₂ P)*
    normalizedSubsetTraceGauss p hp (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)^e i) S*
    (blockRow p hg S e d*star (blockRow p hg S e h))‖≤_
  simp only [norm_mul,norm_star,secondColumnCoefficient_norm_one_of_good p hp hinj hg hc,
    hG,one_mul,mul_one]
  apply mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg S e d)).trans (blockRow_norm_le_one p hg S e h)

include hinj in
lemma canonicalPairMode_norm_le
    (hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
    (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d h : O) :
    ‖canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖ringComplex (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖)*
        (‖C₁ N‖*‖C₂ P‖))*
      ‖paperRadialFourier W ((K/(‖ringComplex d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖ringComplex h‖^2)‖ := by
  have hn : 0<‖ringComplex (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖ :=
    norm_pos_iff.mpr (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i hi=>hp i)))
  have ha : K*‖ringComplex h‖^2/(‖ringComplex d‖^2*
      primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)) =
      (K/(‖ringComplex d‖^2*primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖ringComplex h‖^2 := by ring
  simp only [canonicalPairMode,norm_mul,norm_div,Complex.norm_real,Real.norm_eq_abs,
    abs_of_pos hK,abs_of_pos hn,ha]
  calc
    _ ≤ (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖ringComplex (∏i∈(N∪P)∪cubeActiveSupport B v ε₁ ε₂,p i)‖))*
      ‖paperRadialFourier W ((K/(‖ringComplex d‖^2*
        primeProductNorm p ((N∪P)∪cubeActiveSupport B v ε₁ ε₂)))*‖ringComplex h‖^2)‖*
      (‖C₁ N‖*‖C₂ P‖) := mul_le_mul_of_nonneg_left
        (threeGaussRowFactor_norm_le p hp hinj hg hc N P B v ε₁ ε₂ C₁ C₂ d h) (by positivity)
    _ = _ := by ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap
theorem full_uniform_canonicalPairMode_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N P B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
      (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K H : ℝ),0<K → 0≤H → ∀(d : O),d≠0 → ∀T:Finset O,
      let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖ringComplex d‖^2*primeProductNorm p S)
      (∀h:O,h∉T → H≤ scale*‖ringComplex h‖^2) →
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖ringComplex (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/((min 1 scale)^2*(1+H)^A)) := by
  obtain ⟨s,C,hC,hb⟩ := paperRadialFourier_lattice_tail A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K H hK hH d hd T
  dsimp only
  intro hT
  let S := (N∪P)∪cubeActiveSupport B v ε₁ ε₂
  let scale := K/(‖ringComplex d‖^2*primeProductNorm p S)
  let c := ‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ P)‖*
        (K/‖ringComplex (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ P‖)
  have hscale : 0<scale := div_pos hK (mul_pos
    (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))) (primeProductNorm_pos p hp S))
  have hc0 : 0≤c := by dsimp [c]; positivity
  let small : Set O := {h|h∉T}
  let large : Set O := {h|H≤ scale*‖ringComplex h‖^2}
  let f : small→large := fun h=>⟨h.val,hT h.val h.property⟩
  have hfi : Function.Injective f := by
    intro a b hab
    exact Subtype.ext (congrArg (fun x:large=>x.val) hab)
  have hrad := paperRadialFourier_lattice_summable_norm W scale hscale
  have hmajor := (hrad.subtype small).mul_left c
  have hpnt (h:small) :
      ‖canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      c*‖paperRadialFourier W (scale*‖ringComplex h.val‖^2)‖ :=
    canonicalPairMode_norm_le p hp hinj hg hc N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d h.val
  have hsmall := Summable.of_nonneg_of_le (fun _=>norm_nonneg _) hpnt hmajor
  calc
    _ ≤ ∑'h:small,‖canonicalPairMode p hp hg N P B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖ :=
      norm_tsum_le_tsum_norm hsmall
    _ ≤ ∑'h:small,c*‖paperRadialFourier W (scale*‖ringComplex h.val‖^2)‖ :=
      hsmall.tsum_le_tsum hpnt hmajor
    _ = c*∑'h:small,‖paperRadialFourier W (scale*‖ringComplex h.val‖^2)‖ := tsum_mul_left
    _ ≤ c*∑'h:large,‖paperRadialFourier W (scale*‖ringComplex h.val‖^2)‖ :=
      mul_le_mul_of_nonneg_left ((hrad.subtype small).tsum_le_tsum_of_inj f hfi
        (fun _ _=>norm_nonneg _) (fun _=>le_rfl) (hrad.subtype large)) hc0
    _ ≤ _ := mul_le_mul_of_nonneg_left (hb W scale H hscale hH) hc0

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap
def canonicalFirstFrequencyRadius {ι : Type*} [DecidableEq ι]
    (p : ι→O) (B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (d : O) (X₁ X₂ K P : ℝ) : ℝ :=
  P*(‖ringComplex d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*X₁*X₂)/K

theorem firstFrequencyDisk_uniform {ι : Type*} [DecidableEq ι]
    (p : ι→O) (hp : ∀i,p i≠0)
    (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (hNQ : Disjoint N Q) (hNB : Disjoint N B) (hQB : Disjoint Q B)
    (d : O) (hd : d≠0) (X₁ X₂ K P M₁ M₂ : ℝ)
    (hX₁ : 0<X₁) (hX₂ : 0<X₂) (hK : 0<K)
    (hN : columnLog p X₁ N≤M₁) (hQ : columnLog p X₂ Q≤M₂)
    (h : O) (hh : h∉firstFrequencyDisk
      (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)) :
    P/Real.exp (M₁+M₂)≤
      (K/(‖ringComplex d‖^2*primeProductNorm p ((N∪Q)∪cubeActiveSupport B v ε₁ ε₂)))*
        ‖ringComplex h‖^2 := by
  let S := cubeActiveSupport B v ε₁ ε₂
  have hNS : Disjoint N S := hNB.mono_right (Finset.filter_subset _ _)
  have hQS : Disjoint Q S := hQB.mono_right (Finset.filter_subset _ _)
  have hNQS : Disjoint (N∪Q) S := Finset.disjoint_union_left.mpr ⟨hNS,hQS⟩
  have hnorm : primeProductNorm p ((N∪Q)∪S)=
      primeProductNorm p N*primeProductNorm p Q*primeProductNorm p S := by
    rw [primeProductNorm_union p _ _ hNQS,primeProductNorm_union p _ _ hNQ]
  have hNd : 0<‖ringComplex d‖^2 := sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  have hU₁ : 0<X₁*Real.exp M₁ := mul_pos hX₁ (Real.exp_pos _)
  have hU₂ : 0<X₂*Real.exp M₂ := mul_pos hX₂ (Real.exp_pos _)
  let slow := K/(‖ringComplex d‖^2*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S)
  have hs : 0<slow := div_pos hK (mul_pos (mul_pos (mul_pos hNd hU₁) hU₂) (primeProductNorm_pos p hp S))
  have hn := columnLog_norm_upper p hp X₁ M₁ hX₁ N hN
  have hq := columnLog_norm_upper p hp X₂ M₂ hX₂ Q hQ
  have hprod : primeProductNorm p N*primeProductNorm p Q≤(X₁*Real.exp M₁)*(X₂*Real.exp M₂) :=
    mul_le_mul hn hq (primeProductNorm_pos p hp Q).le hU₁.le
  have hscale : slow≤K/(‖ringComplex d‖^2*primeProductNorm p ((N∪Q)∪S)) := by
    apply div_le_div_of_nonneg_left hK.le
      (mul_pos hNd (primeProductNorm_pos p hp _))
    rw [hnorm]
    calc
      _ ≤ ‖ringComplex d‖^2*((X₁*Real.exp M₁)*(X₂*Real.exp M₂)*primeProductNorm p S) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
      _ = _ := by ring
  have hr : (P/Real.exp (M₁+M₂))/slow=
      canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P := by
    dsimp [slow,canonicalFirstFrequencyRadius,S]
    rw [Real.exp_add]
    field_simp

  have ho := outside_firstFrequencyDisk _ h hh
  rw [←hr] at ho
  have hbase : P/Real.exp (M₁+M₂)≤ slow*‖ringComplex h‖^2 := by
    have hz := (div_lt_iff₀ hs).mp ho
    simpa only [mul_comm] using hz.le
  exact hbase.trans (mul_le_mul_of_nonneg_right hscale (sq_nonneg _))

theorem full_uniform_canonicalPairMode_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (N Q B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),
      Disjoint N Q → Disjoint N B → Disjoint Q B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
      (X₁ X₂ K P M₁ M₂ : ℝ),0<X₁ → 0<X₂ → 0<K → 0≤P →
      columnLog p X₁ N≤M₁ → columnLog p X₂ Q≤M₂ → ∀(d : O),d≠0 →
      let S := (N∪Q)∪cubeActiveSupport B v ε₁ ε₂
      let scale := K/(‖ringComplex d‖^2*primeProductNorm p S)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},canonicalPairMode p hp hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val‖≤
      (‖V₁ (columnLog p X₁ N)‖*‖V₂ (columnLog p X₂ Q)‖*
        (K/‖ringComplex (∏i∈S,p i)‖)*(‖C₁ N‖*‖C₂ Q‖))*
      ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 scale)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hg hc N Q B v ε₁ ε₂ hNQ hNB hQB C₁ C₂ W V₁ V₂ X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP hN hQ d hd
  apply hb p hp hinj hg hc N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K _ hK
    (div_nonneg hP (Real.exp_pos _).le) d hd
  intro h hh
  exact firstFrequencyDisk_uniform p hp N Q B v ε₁ ε₂ hNQ hNB hQB d hd
    X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hN hQ h hh

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
theorem actualFirstKernel_complement_eq_pairs
    (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool)
    (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (V₁ V₂ : ℝ→ℂ)
    (X₁ X₂ K : ℝ) (hK : 0<K) (d : O) (hd : d≠0) (T : Finset O) :
    (∑'h:{h:O // h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val)=
      ∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
        ∑'h:{h:O // h∉T},canonicalPairMode p hp hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val
        else 0 := by
  have hs (N Q : Finset ι) : Summable (fun h:{h:O // h∉T}=>if Disjoint N Q then
      canonicalPairMode p hp hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0) := by
    by_cases hNQ : Disjoint N Q
    · simp only [hNQ,ite_true]
      exact (canonicalPairMode_summable p hp hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K hK d hd).subtype _
    · simp only [hNQ,ite_false]
      exact summable_zero
  change (∑'h:{h:O // h∉T},∑N∈F.powerset,∑Q∈F.powerset,if Disjoint N Q then
    canonicalPairMode p hp hg N Q B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ K d h.val else 0)=_
  rw [Summable.tsum_finsetSum (fun N hN=>summable_sum (fun Q hQ=>hs N Q))]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Summable.tsum_finsetSum (fun Q hQ=>hs N Q)]
  apply Finset.sum_congr rfl
  intro Q hQ
  split_ifs <;> simp

end

theorem full_uniform_actualFirstKernel_disk_remainder (A : ℕ) :
    ∃ (s : Finset (ℕ×ℕ)) (C : ℝ),0<C ∧
    ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀i,lambda∉Ideal.span {p i}) (_hc : ∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (F B : Finset ι) (v : ι→ℕ) (ε₁ ε₂ : ι→Bool),Disjoint F B →
      ∀ (C₁ C₂ : Finset ι→ℂ) (W : 𝓢(ℝ,ℂ)) (G₁ G₂ X₁ X₂ K P M₁ M₂ : ℝ),
      0≤G₁ → 0≤G₂ → 0<X₁ → 0<X₂ → 0<K → 0≤P →
      (∀N∈F.powerset,‖C₁ N‖≤G₁) → (∀N∈F.powerset,‖C₂ N‖≤G₂) →
      (∀N∈F.powerset,C₁ N≠0 → columnLog p X₁ N≤M₁) →
      (∀N∈F.powerset,C₂ N≠0 → columnLog p X₂ N≤M₂) →
      ∀(d : O),d≠0 →
      let U₁ := X₁*Real.exp M₁
      let U₂ := X₂*Real.exp M₂
      let slow := K/(‖ringComplex d‖^2*primeProductNorm p (cubeActiveSupport B v ε₁ ε₂)*U₁*U₂)
      let T := firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val‖≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*K)*
        ((C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)) := by
  have hdc := diagonalControl_nonneg sieveCutoff
  obtain ⟨s,C,hC,hb⟩:=full_uniform_canonicalPairMode_disk_remainder A
  refine ⟨s,C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc F B v ε₁ ε₂ hFB C₁ C₂ W G₁ G₂ X₁ X₂ K P M₁ M₂ hG₁ hG₂ hX₁ hX₂ hK hP hC₁ hC₂ hS₁ hS₂ d hd
  dsimp only
  let U₁:=X₁*Real.exp M₁
  let U₂:=X₂*Real.exp M₂
  let S:=cubeActiveSupport B v ε₁ ε₂
  let T:=firstFrequencyDisk (canonicalFirstFrequencyRadius p B v ε₁ ε₂ d X₁ X₂ K P)
  let slow:=K/(‖ringComplex d‖^2*primeProductNorm p S*U₁*U₂)
  let tail:ℝ:=(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
    ((min 1 slow)^2*(1+P/Real.exp (M₁+M₂))^A)
  let Q:ℝ:=G₁*G₂*K*tail
  have hU₁:0<U₁:=mul_pos hX₁ (Real.exp_pos _)
  have hU₂:0<U₂:=mul_pos hX₂ (Real.exp_pos _)
  have hNd:0<‖ringComplex d‖^2:=sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  have hslow:0<slow:=div_pos hK (mul_pos (mul_pos (mul_pos hNd (primeProductNorm_pos p hp S)) hU₁) hU₂)
  have hH:0≤P/Real.exp (M₁+M₂):=div_nonneg hP (Real.exp_pos _).le
  have htail:0≤tail:=by dsimp [tail]; positivity
  have hQ:0≤Q:=mul_nonneg (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le) htail
  let rem (N R:Finset ι):ℂ:=if Disjoint N R then
    ∑'h:{h:O // h∉T},canonicalPairMode p hp hg N R B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val else 0
  have hnzero (N R:Finset ι) (hn:C₁ N=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hn]
  have hrzero (N R:Finset ι) (hr:C₂ R=0):rem N R=0:=by
    simp [rem,canonicalPairMode,threeGaussRowFactor,hr]
  have heq : (∑'h:{h:O // h∉T},actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K d h.val)=
      ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,rem N R := by
    rw [actualFirstKernel_complement_eq_pairs p hp hg F B v ε₁ ε₂ C₁ C₂ W (fun _=>1) (fun _=>1) X₁ X₂ K hK d hd T]
    change (∑N∈F.powerset,∑R∈F.powerset,rem N R)=_
    calc
      _ = ∑N∈boundedPrimeSupports p F U₁,∑R∈F.powerset,rem N R := by
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro N hN hn
        have hz:C₁ N=0:=by
          by_contra h
          exact hn (Finset.mem_filter.mpr ⟨hN,columnLog_norm_upper p hp X₁ M₁ hX₁ N (hS₁ N hN h)⟩)
        simp only [hnzero N _ hz,Finset.sum_const_zero]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro N hN
        symm
        apply Finset.sum_subset (Finset.filter_subset _ _)
        intro R hR hr
        have hz:C₂ R=0:=by
          by_contra h
          exact hr (Finset.mem_filter.mpr ⟨hR,columnLog_norm_upper p hp X₂ M₂ hX₂ R (hS₂ R hR h)⟩)
        exact hrzero N R hz
  have hrem (N:Finset ι) (hN:N∈boundedPrimeSupports p F U₁) (R:Finset ι) (hR:R∈boundedPrimeSupports p F U₂):‖rem N R‖≤Q:=by
    have hNF: N∈F.powerset:=(Finset.mem_filter.mp hN).1
    have hRF: R∈F.powerset:=(Finset.mem_filter.mp hR).1
    by_cases hn:C₁ N=0
    · rw [hnzero N R hn,norm_zero]; exact hQ
    by_cases hr:C₂ R=0
    · rw [hrzero N R hr,norm_zero]; exact hQ
    by_cases hNR:Disjoint N R
    · have hNB:=hFB.mono_left (Finset.mem_powerset.mp hNF)
      have hRB:=hFB.mono_left (Finset.mem_powerset.mp hRF)
      have hNS:Disjoint N S:=hNB.mono_right (Finset.filter_subset _ _)
      have hRS:Disjoint R S:=hRB.mono_right (Finset.filter_subset _ _)
      have hnorm:primeProductNorm p ((N∪R)∪S)=primeProductNorm p N*primeProductNorm p R*primeProductNorm p S:=by
        rw [primeProductNorm_union p _ _ (Finset.disjoint_union_left.mpr ⟨hNS,hRS⟩),primeProductNorm_union p _ _ hNR]
      have hprod:=mul_le_mul (Finset.mem_filter.mp hN).2 (Finset.mem_filter.mp hR).2
        (primeProductNorm_pos p hp R).le hU₁.le
      have hscale:slow≤K/(‖ringComplex d‖^2*primeProductNorm p ((N∪R)∪S)):=by
        apply div_le_div_of_nonneg_left hK.le (mul_pos hNd (primeProductNorm_pos p hp _))
        rw [hnorm]
        calc
          _ ≤ ‖ringComplex d‖^2*(U₁*U₂*primeProductNorm p S):=mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hprod (primeProductNorm_pos p hp S).le) hNd.le
          _ = _ := by ring
      have hnroot:1≤‖ringComplex (∏i∈(N∪R)∪S,p i)‖:=by
        have hx:=primeProductNorm_ge_one p hp ((N∪R)∪S)
        change 1≤‖ringComplex (∏i∈(N∪R)∪S,p i)‖^2 at hx
        nlinarith [norm_nonneg (ringComplex (∏i∈(N∪R)∪S,p i))]
      have hpre:(K/‖ringComplex (∏i∈(N∪R)∪S,p i)‖)*(‖C₁ N‖*‖C₂ R‖)≤G₁*G₂*K:=by
        calc
          _ ≤ K*(G₁*G₂):=mul_le_mul (div_le_self hK.le hnroot)
            (mul_le_mul (hC₁ N hNF) (hC₂ R hRF) (norm_nonneg _) hG₁)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hK.le
          _ = _ := by ring
      have hfrac:(C*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 (K/(‖ringComplex d‖^2*primeProductNorm p ((N∪R)∪S))))^2*(1+P/Real.exp (M₁+M₂))^A)≤tail:=by
        apply div_le_div_of_nonneg_left (by positivity)
          (mul_pos (sq_pos_of_pos (lt_min (by norm_num) hslow)) (pow_pos (by linarith) _))
        exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (le_min zero_le_one hslow.le)
          (min_le_min_left 1 hscale) 2) (pow_nonneg (by linarith) _)
      have hpair:=hb p hp hinj hg hc N R B v ε₁ ε₂ hNR hNB hRB C₁ C₂ W (fun _=>1) (fun _=>1)
        X₁ X₂ K P M₁ M₂ hX₁ hX₂ hK hP (hS₁ N hNF hn) (hS₂ R hRF hr) d hd
      simp only [norm_one,one_mul] at hpair
      dsimp only [rem]
      rw [if_pos hNR]
      exact hpair.trans (mul_le_mul hpre hfrac (by positivity) (mul_nonneg (mul_nonneg hG₁ hG₂) hK.le))
    · simp only [rem,if_neg hNR,norm_zero];exact hQ
  rw [heq]
  calc
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,‖rem N R‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun N hN=>norm_sum_le _ _))
    _ ≤ ∑N∈boundedPrimeSupports p F U₁,∑R∈boundedPrimeSupports p F U₂,Q:=
      Finset.sum_le_sum (fun N hN=>Finset.sum_le_sum (fun R hR=>hrem N hN R hR))
    _ = ((boundedPrimeSupports p F U₁).card:ℝ)*((boundedPrimeSupports p F U₂).card:ℝ)*Q:=by simp;ring
    _ ≤ ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*Q:=mul_le_mul_of_nonneg_right
      (mul_le_mul (boundedPrimeSupports_card_positive p hp hinj F U₁ hU₁)
        (boundedPrimeSupports_card_positive p hp hinj F U₂ hU₂) (Nat.cast_nonneg _) (by positivity)) hQ
    _ = _ := by dsimp [Q,tail,slow,U₁,U₂,S];ring

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical SchwartzMap

section
variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀i,p i≠0)
  [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})

omit [DecidableEq ι] in
lemma originalLabelColumn_core_norm_le
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (hΨ : ∀u,‖Ψ u‖≤1) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι) :
    ‖originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H) c f S‖≤‖H S‖ := by
  have hm (z:O):‖primeCoprimeMask p S z‖≤1:=by
    exact primeCoprimeMask_norm_le_one p S z
  have hrow (z:O):‖primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z‖^4≤1:=by
    simpa using pow_le_pow_left₀ (norm_nonneg _)
      (primeSubsetRow_norm_le_one p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z) 4
  simp only [originalLabelColumn,multiplicativeCoreColumn,norm_mul,norm_pow]
  calc
    _ ≤ 1*‖H S‖*1*1*1 := by
      exact mul_le_mul
        (mul_le_mul
          (mul_le_mul
            (mul_le_mul_of_nonneg_right
              ((mul_le_mul (hΨ _) (hm m) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)) (norm_nonneg _))
            (hm _) (norm_nonneg _) (by positivity))
          (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity))
        (hrow _) (pow_nonneg (norm_nonneg _) _) (by positivity)
    _ = _ := by ring

omit [DecidableEq ι] in
lemma originalLabelColumn_core_test_ne_zero
    (B : Finset ι) (ε₁ ε₂ : ι→Bool) (negative : Bool)
    (Ψ : O→*ℂ) (m c f : O) (H : Finset ι→ℂ) (S : Finset ι)
    (h : originalLabelColumn p hg B ε₁ ε₂ negative
      (multiplicativeCoreColumn p Ψ m H) c f S≠0) : H S≠0 := by
  intro hz
  apply h
  simp only [originalLabelColumn,multiplicativeCoreColumn,hz,mul_zero,zero_mul]

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem canonicalFirstFrequencyRadius_eq_global
    (b : CubeCoordinates ι) (hb : b.Admissible) (C D : Finset ι)
    (Ksrc K ell : ℝ) (hKsrc : 0<Ksrc) (hK : 0<K) :
    canonicalFirstFrequencyRadius p b.support (fun i=>b.leftExponent i+b.rightExponent i)
      b.leftBit b.rightBit ((∏i∈D,p i))
      (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))
      (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)) Ksrc (Ksrc/K)=
    globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D) := by
  have hl:b.swap.leftBit=b.rightBit:=rfl
  have hr:b.swap.rightBit=b.leftBit:=rfl
  simp only [canonicalFirstFrequencyRadius,globalFirstFrequencyScale,sourceGlobalBlock,
    cube_swap_support,cube_swap_sum,hl,hr,
    cubeActiveSupport_swap,
    CubeCoordinates.aLabel_left p b hb,CubeCoordinates.aLabel_right p b hb]
  change (Ksrc/K)*(primeProductNorm p D*primeProductNorm p
    (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*
    (ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C))*
    (ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)))/Ksrc = _
  have hC:primeProductNorm p C≠0:=(primeProductNorm_pos p hp C).ne'
  have hL:primeProductNorm p b.leftDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  have hR:primeProductNorm p b.rightDivisor≠0:=(primeProductNorm_pos p hp _).ne'
  simp only [primeProductNorm]
  simp only [primeProductNorm] at hC hL hR
  field_simp

end

theorem full_uniform_canonicalSource_kernel_tail (A : ℕ) :
    ∃(s:Finset (ℕ×ℕ)) (Ctail:ℝ),0<Ctail ∧
    ∀{ι:Type*} [DecidableEq ι]
      (p:ι→O) (hp:∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
      (_hinj:Function.Injective (fun i=>Ideal.span {p i}))
      (hcop:Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg:∀i,lambda∉Ideal.span {p i}) (_hc:∀i,ringChar (O⧸Ideal.span {p i})≠2)
      (pool:Finset ι) (b:CubeCoordinates ι),b.Admissible → ∀ C D:Finset ι,Disjoint C b.support →
      ∀(Ψ₁ Ψ₂:O→*ℂ),(∀u,‖Ψ₁ u‖≤1) → (∀u,‖Ψ₂ u‖≤1) →
      ∀(m₁ m₂ f:O) (g₁ g₂ W:𝓢(ℝ,ℂ)) (G₁ G₂ M₁ M₂ Ksrc K ell:ℝ),
      0≤G₁ → 0≤G₂ → 0<Ksrc → 0<K → 0<ell →
      (∀t,‖g₁ t‖≤G₁) → (∀t,‖g₂ t‖≤G₂) →
      (∀t,g₁ t≠0→t≤M₁) → (∀t,g₂ t≠0→t≤M₂) →
      let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
      let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
      let U₁:=X₁*Real.exp M₁
      let U₂:=X₂*Real.exp M₂
      let slow:=Ksrc/(primeProductNorm p D*primeProductNorm p
        (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit)*U₁*U₂)
      let T:=firstFrequencyDisk (globalFirstFrequencyScale p K ell (sourceGlobalBlock b C D))
      ‖∑'h:{h:O // h∉T},actualFirstKernel p hp hg (pool\(b.support∪C)) b.support
        (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit
        (canonicalCubeResidual p hg b C true Ψ₁ m₁ f (fun S=>g₁ (columnLog p ell S)))
        (canonicalCubeResidual p hg b C false Ψ₂ m₂ f (fun S=>g₂ (columnLog p ell S)))
        W (fun _=>1) (fun _=>1) 1 1 Ksrc
        ((∏i∈D,p i)) h.val‖≤
      ((1+diagonalControl sieveCutoff)*U₁)*((1+diagonalControl sieveCutoff)*U₂)*(G₁*G₂*Ksrc)*
        ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
          ((min 1 slow)^2*(1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) := by
  obtain ⟨s,Ctail,hCtail,hbound⟩:=full_uniform_actualFirstKernel_disk_remainder A
  refine ⟨s,Ctail,hCtail,?_⟩
  intro ι _ p hp _ hinj hcop hg hc pool b hb C D hCB Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ f g₁ g₂ W G₁ G₂ M₁ M₂ Ksrc K ell hG₁ hG₂ hKsrc hK hell hg₁ hg₂ hM₁ hM₂
  dsimp only
  let X₁:=ell/(primeProductNorm p b.rightDivisor*primeProductNorm p C)
  let X₂:=ell/(primeProductNorm p b.leftDivisor*primeProductNorm p C)
  have hX₁:0<X₁:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hX₂:0<X₂:=div_pos hell (mul_pos (primeProductNorm_pos p hp _) (primeProductNorm_pos p hp _))
  have hFB:Disjoint (pool\(b.support∪C)) b.support:=Finset.disjoint_left.mpr (fun i hi hb=>
    (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hb))
  let C₁:=originalLabelColumn p hg b.support b.leftBit b.rightBit true
    (multiplicativeCoreColumn p Ψ₁ m₁ (fun S=>g₁ (columnLog p X₁ S))) (∏i∈C,p i) f
  let C₂:=originalLabelColumn p hg b.support b.leftBit b.rightBit false
    (multiplicativeCoreColumn p Ψ₂ m₂ (fun S=>g₂ (columnLog p X₂ S))) (∏i∈C,p i) f
  have hcoef₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₁ N‖≤G₁:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit true Ψ₁ hΨ₁ m₁ _ f _ N).trans (hg₁ _)
  have hcoef₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset):‖C₂ N‖≤G₂:=
    (originalLabelColumn_core_norm_le p hg b.support b.leftBit b.rightBit false Ψ₂ hΨ₂ m₂ _ f _ N).trans (hg₂ _)
  have hs₁ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₁ N≠0):columnLog p X₁ N≤M₁:=
    hM₁ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit true Ψ₁ m₁ _ f _ N hn)
  have hs₂ (N:Finset ι) (hN:N∈(pool\(b.support∪C)).powerset) (hn:C₂ N≠0):columnLog p X₂ N≤M₂:=
    hM₂ _ (originalLabelColumn_core_test_ne_zero p hg b.support b.leftBit b.rightBit false Ψ₂ m₂ _ f _ N hn)
  have h:=hbound p hp hinj hcop hg hc (pool\(b.support∪C)) b.support
    (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit hFB C₁ C₂ W
    G₁ G₂ X₁ X₂ Ksrc (Ksrc/K) M₁ M₂ hG₁ hG₂ hX₁ hX₂ hKsrc (div_pos hKsrc hK).le
    hcoef₁ hcoef₂ hs₁ hs₂ ((∏i∈D,p i)) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
  rw [canonicalFirstFrequencyRadius_eq_global p hp b hb C D Ksrc K ell hKsrc hK] at h
  change _ ≤ (1+diagonalControl sieveCutoff)*(X₁*Real.exp M₁)*
      ((1+diagonalControl sieveCutoff)*(X₂*Real.exp M₂))*(G₁*G₂*Ksrc)*
      ((Ctail*s.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)/
        ((min 1 (Ksrc/(primeProductNorm p D*primeProductNorm p
          (cubeActiveSupport b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit)*(X₁*Real.exp M₁)*(X₂*Real.exp M₂)) ))^2*
          (1+(Ksrc/K)/Real.exp (M₁+M₂))^A)) at h
  have heq := fun h:O=>canonical_log_kernel p hp hg pool b hb C hCB Ψ₁ Ψ₂ m₁ m₂ f
    ((∏i∈D,p i)) h g₁ g₂ W Ksrc ell hell
  simp_rw [heq]
  exact h

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels MeasureTheory
open scoped Classical SchwartzMap ContDiff
theorem padded_orientedCubeFirstBlock_input_transfer
    (W V₁ V₂ : 𝓢(ℝ,ℂ)) (M₁ M₂ : ℝ) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₁ : ∀ t,V₁ t≠0 → |t|≤M₁) (hV₂ : ∀ t,V₂ t≠0 → |t|≤M₂)
    (J : ℕ) (deltaLoss : ℝ) (hδ : 0<deltaLoss) :
    ∃ C : ℝ,0≤C ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (_hc : ∀ i,ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (_hpr : ∀ i,lambda^2 ∣ p i-1)
      (pool : Finset ι) (blocks : Finset (GlobalCubeBlock ι))
      (s : GlobalCubeBlock ι → Finset (Ideal O × O)) (a : GlobalCubeBlock ι → Ideal O × O → ℂ)
      (w : GlobalCubeBlock ι → ℝ) (T : GlobalCubeBlock ι → Finset O)
      (Ψ₁ Ψ₂ : O →* ℂ) (m₁ m₂ : O) (g₁ g₂ : 𝓢(ℝ,ℂ)) (Ksrc K ell B F Ymax : ℝ),
      0<Ksrc → 0<K → 0<ell → 0<B → 0<F →
      (∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      (∀ b∈blocks,0≤w b) → (∀ b∈blocks,∀ x∈s b,‖a b x‖≤w b) →
      (∀ b∈blocks,globalFirstPooledRow p K ell B F true (b.withCommon ∅)≤Ymax) →
      (∀ b∈blocks,∀ x∈s b,Squarefree x.1) → (∀ b∈blocks,∀ x∈s b,x.2≠0) →
      (∀ b∈blocks,∀ x∈s b,DescentWeightedCauchy.firstElementRowMap
        (dilationLabel p b.cube.support (fun i => b.cube.leftExponent i+b.cube.rightExponent i)
          b.cube.leftBit b.cube.rightBit) x∈T b) →
      (∀ b∈blocks,∀ z∈T b,z≠0) →
      (∀ b∈blocks,∀ z∈T b,(Ideal.absNorm (Ideal.span {z}) : ℝ)≤
        globalFirstPooledRow p K ell B F true (b.withCommon ∅)) →
      ‖(ell*B^2*F : ℂ)⁻¹*∑ b∈blocks,orientedCubeFirstBlock p hp hg pool b (s b) (a b)
        Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      (Ksrc/K)*C*Ymax^deltaLoss*
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F true b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)) *
        Real.sqrt (∑ b∈blocks,w b*globalCubeCoefficient p K ell B F false b*
          globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)) := by
  obtain ⟨C,hC,hfirst⟩ := first_passage_to_input_family W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ J deltaLoss hδ
  refine ⟨C,hC,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr pool blocks s a w T Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ Ksrc K ell B F Ymax hKsrc hK hell hB hF hΨ₁ hΨ₂ hw ha hYmax hsf hs0 hmap hT0 hT
  by_cases hempty : blocks=∅
  · subst blocks
    simp only [Finset.sum_empty,mul_zero,norm_zero,Real.sqrt_zero,le_refl]
  have hne : blocks.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  let E₁ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₁ m₁ g₁ V₁ ell true J (T b)
  let E₂ := fun b => globalCubeInputFamilyEnergy p hg pool b Ψ₂ m₂ g₂ V₂ ell false J (T b)
  let v := fun b => w b*globalCubeCoefficient p K ell B F true b
  have hv (b) (hb : b∈blocks) : 0≤v b := mul_nonneg (hw b hb)
    (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _)
  have hE₁ (b) : 0≤E₁ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hE₂ (b) : 0≤E₂ b := firstInputFamilyEnergy_nonneg p hg _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  have hden : 0<ell*B^2*F := by positivity
  have hYmax0 : 0≤Ymax := by
    obtain ⟨b,hb⟩ := hne
    exact (globalPooledRowScale_pos K ell B F hK hell hB hF _).le.trans (hYmax b hb)
  have hpref : 0≤(Ksrc/K)*C*Ymax^deltaLoss := mul_nonneg (mul_nonneg (div_nonneg hKsrc.le hK.le) hC) (Real.rpow_nonneg hYmax0 deltaLoss)
  have hpoint (b) (hb : b∈blocks) : (ell*B^2*F)⁻¹*
      ‖orientedCubeFirstBlock p hp hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ ≤
      ((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
    have hFB : Disjoint (globalCubePool pool b) b.cube.support := by
      apply Finset.disjoint_left.mpr
      intro i hi hiB
      exact (Finset.mem_sdiff.mp hi).2 (Finset.mem_union_left _ hiB)
    have hX₁ := globalCubeColumnScale_pos p hp ell hell true b
    have hX₂ := globalCubeColumnScale_pos p hp ell hell false b
    have hD := primeProductNorm_pos p hp b.firstDivisor
    have hY := globalPooledRowScale_pos K ell B F hK hell hB hF (globalFirstIndex p true (b.withCommon ∅))
    have hswapD := FirstPassCubeLabels.dilationLabel_swap p b.cube.support
      (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit
    have hh := hfirst p hp hinj hcop hg hc hpr (globalCubePool pool b) b.cube.support hFB
      (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit b.cube.support_pos
      Ψ₁ Ψ₂ m₁ m₂ (fun A => g₁ (columnLog p (globalCubeColumnScale p ell true b) A))
      (fun A => g₂ (columnLog p (globalCubeColumnScale p ell false b) A))
      (fun A hA => hΨ₁ _) (fun A hA => hΨ₂ _)
      _ _ hX₁ hX₂ Ksrc hKsrc ((∏i∈b.common,p i))
      ((∏i∈b.firstDivisor,p i)) (Finset.prod_ne_zero_iff.mpr (fun i _=>hp i))
      (s b) (T b) (a b) (w b) (globalFirstPooledRow p K ell B F true (b.withCommon ∅))
      (hw b hb) hY.le (hs0 b hb) (by simpa only [hswapD] using hmap b hb) (hT0 b hb) (hT b hb) (ha b hb)
    rw [firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit true,
      firstInputFamilyEnergy_swap p hg (globalCubePool pool b) b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit false,
      FirstPassCubeLabels.cubeActiveSupport_swap b.cube.support
        (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.rightBit b.cube.leftBit] at hh
    have hscl := globalCube_first_scalar_bound p hp K ell B F hK hell hB hF b
    have hscl' : (ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
        ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
          (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖) ≤
        (Ksrc/K)*globalCubeCoefficient p K ell B F true b := by
      have hKratio : Ksrc=(Ksrc/K)*K := by field_simp
      calc
        _ = (Ksrc/K)*((ell*B^2*F)⁻¹*((K/primeProductNorm p b.firstDivisor)/
          ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
            (fun i=>b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖)) := by
          conv_lhs => rw [hKratio]
          ring
        _ ≤ _ := mul_le_mul_of_nonneg_left hscl (div_nonneg hKsrc.le hK.le)
    have hpow := Real.rpow_le_rpow hY.le (hYmax b hb) hδ.le
    have hmul := mul_le_mul_of_nonneg_left hh
      (show 0≤(ell*B^2*F)⁻¹*(primeProductNorm p b.firstDivisor)⁻¹ by positivity)
    simp only [orientedCubeFirstBlock,norm_mul,norm_inv,Complex.norm_real,
      Real.norm_of_nonneg hD.le,←mul_assoc]
    apply hmul.trans
    calc
      _ = ((ell*B^2*F)⁻¹*((Ksrc/primeProductNorm p b.firstDivisor)/
          ‖ringComplex (∏ i∈cubeActiveSupport b.cube.support
            (fun i => b.cube.leftExponent i+b.cube.rightExponent i) b.cube.leftBit b.cube.rightBit,p i)‖))*
          (w b*C*(globalFirstPooledRow p K ell B F true (b.withCommon ∅))^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by dsimp [E₁,E₂,globalCubeInputFamilyEnergy];ring
      _ ≤ ((Ksrc/K)*globalCubeCoefficient p K ell B F true b)*(w b*C*Ymax^deltaLoss)*
          (Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
        apply mul_le_mul_of_nonneg_right _ (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
        apply mul_le_mul hscl'
          (mul_le_mul_of_nonneg_left hpow (mul_nonneg (hw b hb) hC))
          (mul_nonneg (mul_nonneg (hw b hb) hC) (Real.rpow_nonneg hY.le _))
          (mul_nonneg (div_nonneg hKsrc.le hK.le) (globalBinFirstCoefficient_nonneg K ell B F hK.le hell hB hF _))
      _ = _ := by dsimp [v];ring
  rw [norm_mul, norm_inv]
  have hn : ‖(ell*B^2*F : ℂ)‖=ell*B^2*F := by
    norm_cast
    exact abs_of_pos hden
  rw [hn]
  calc
    _ ≤ (ell*B^2*F)⁻¹*∑ b∈blocks,‖orientedCubeFirstBlock p hp hg pool b (s b) (a b) Ψ₁ Ψ₂ m₁ m₂ g₁ g₂ W V₁ V₂ Ksrc ell‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hden.le)
    _ ≤ ∑ b∈blocks,((Ksrc/K)*C*Ymax^deltaLoss)*v b*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hpoint
    _ = ((Ksrc/K)*C*Ymax^deltaLoss)*∑ b∈blocks,Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Real.sqrt_mul (hv b hb),Real.sqrt_mul (hv b hb)]
      have hs := Real.sq_sqrt (hv b hb)
      calc
        _ = ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (v b))^2*(Real.sqrt (E₁ b)*Real.sqrt (E₂ b)) := by rw [hs]
        _ = _ := by ring
    _ ≤ ((Ksrc/K)*C*Ymax^deltaLoss)*(Real.sqrt (∑ b∈blocks,v b*E₁ b)*Real.sqrt (∑ b∈blocks,v b*E₂ b)) :=
      mul_le_mul_of_nonneg_left (by
        have hcauchy := Real.sum_sqrt_mul_sqrt_le blocks.attach
          (fun b => mul_nonneg (hv b.val b.property) (hE₁ b.val))
          (fun b => mul_nonneg (hv b.val b.property) (hE₂ b.val))
        simpa only [Finset.sum_attach (f := fun b => Real.sqrt (v b*E₁ b)*Real.sqrt (v b*E₂ b)),
          Finset.sum_attach (f := fun b => v b*E₁ b),Finset.sum_attach (f := fun b => v b*E₂ b)] using hcauchy) hpref
    _ = _ := by simp only [v,E₁,E₂,globalCubeCoefficient_side,mul_assoc]

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
