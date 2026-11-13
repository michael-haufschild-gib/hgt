/-
Cube labels and prime pools adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.SecondPassPoisson

/-!
# Cube labels and prime pools

First-pass cube labels (`jLabel`, `b0Label`, `aLabel`) on prime products and their norm
bounds. Removing common primes leaves sixteen fixed column masks; common-prime extraction
commutes with every conductor kernel.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma subsetTraceRayFactor_eq_row (S : Finset ι) :
    subsetTraceRayFactor p hg S =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S 4 /
        rayQuadraticPhase (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i)) := by
  simp only [subsetTraceRayFactor,secondTraceRayFactor,Finset.prod_coe_sort,
    primeSubsetRow,map_ofNat,rayQuadraticPhase_mk]
  congr 1
  exact Finset.prod_coe_sort S (fun i => complexSexticChar (Ideal.span {p i}) (hg i) 4)

/-- A fixed residue sector with its multiplicative value at four. -/
def secondRayColumn (r : QuadraticRayRing) (H : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S 4 *
    (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r then H S else 0)

lemma secondRayColumn_norm_le (r : QuadraticRayRing) (H : Finset ι → ℂ) (S : Finset ι) :
    ‖secondRayColumn p hg r H S‖ ≤ ‖H S‖ := by
  unfold secondRayColumn
  split_ifs
  · rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (primeSubsetRow_norm_le_one p _ S 4)
  · simp only [mul_zero,norm_zero]
    exact norm_nonneg _

def secondRayTransition (V : Finset ι) (r s : QuadraticRayRing) : ℂ :=
  (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V 4 /
    rayQuadraticPhase r) *
    (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ V, p i)*s = r then 1 else 0)

lemma secondRayTransition_norm_le (V : Finset ι) (r s : QuadraticRayRing) :
    ‖secondRayTransition p hg V r s‖ ≤ 1 := by
  unfold secondRayTransition
  split_ifs
  · rw [mul_one,div_eq_mul_inv,norm_mul]
    exact (mul_le_mul (primeSubsetRow_norm_le_one p _ V 4)
      (fixedDualAverage_bounds
        (QuadraticPhase.Eisenstein.GaussianShiftedPartition.representative 4 r)).2
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  · simp only [mul_zero,norm_zero,zero_le_one]

/-- Removing common primes leaves sixteen fixed column masks and bounded outer factors. -/
theorem secondRayMask_union (V N : Finset ι) (hd : Disjoint V N)
    (r : QuadraticRayRing) (H : Finset ι → ℂ) :
    secondRayMask p hg r H (V ∪ N) =
      ∑ s : QuadraticRayRing, secondRayTransition p hg V r s *
        secondRayColumn p hg s (fun U => H (V ∪ U)) N := by
  have hs : secondRayMask p hg r H (V ∪ N) =
      (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) V 4 *
        primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N 4 /
        rayQuadraticPhase r) *
      (if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ V, p i) *
        Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ N, p i) = r then H (V ∪ N) else 0) := by
    unfold secondRayMask
    rw [subsetTraceRayFactor_eq_row,Finset.prod_union hd,map_mul,
      primeSubsetRow_union p _ V N hd]
    split_ifs with h
    · rw [h]
    · simp only [mul_zero]
  rw [hs]
  symm
  rw [Finset.sum_eq_single (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ N, p i))]
  · simp only [secondRayTransition,secondRayColumn,if_pos rfl]
    split_ifs <;> ring
  · intro s _ hs
    simp only [secondRayColumn,if_neg hs.symm,mul_zero]
  · intro h
    exact (h (Finset.mem_univ _)).elim

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- The arithmetic pair with an arbitrary kernel in its two conductors. -/
def secondPreKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H₁ H₂ : Finset ι → ℂ)
    (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    star (secondPreColumn p hg Ψ₁ (m * (e * r)) c d e k₁ H₁ S) *
      secondPreColumn p hg Ψ₂ (m * (e * r)) c d e k₂ H₂ T * K S T else 0

def secondChildKernelPair (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m r c d e k₁ k₂ : O) (H₁ H₂ : Finset ι → ℂ)
    (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
    star (secondChildColumn p hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₁) (fun U => H₁ (V ∪ U)) N) *
    secondChildColumn p hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
      (d * e * k₂) (fun U => H₂ (V ∪ U)) M * K (V ∪ N) (V ∪ M)

theorem secondPreKernelPair_eq_children (hp : ∀ i, p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime p))
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondPreKernelPair p hg F Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂ K =
      ∑ V ∈ F.powerset, secondCommonWeight p hg Ψ₁ Ψ₂ m r c d e k₁ k₂ V *
        secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂ H₁ H₂ K := by
  unfold secondPreKernelPair
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro V hV
  rw [secondCommonWeight, supportMobius]
  simp only [secondChildKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro M hM
  have hdN : Disjoint V N := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
  have hdM : Disjoint V M := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
  rw [secondPreColumn_union p hg hp hcop hpr Ψ₁ m r c d e k₁ H₁ V N hdN,
    secondPreColumn_union p hg hp hcop hpr Ψ₂ m r c d e k₂ H₂ V M hdM, star_mul]
  ring

def secondKernelPair (hp : ∀ i, p i ≠ 0)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T * K S T else 0

theorem secondKernelPair_eq_pre (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hg hp F Ψ₁ Ψ₂ m r c d e k H₁ H₂ K =
      ∑ z : QuadraticRayRing × QuadraticRayRing, rayQuadraticPair z.1 z.2 *
        secondPreKernelPair p hg F Ψ₁ Ψ₂ m r c d e k (-k)
          (secondRayMask p hg z.1 H₁) (secondRayMask p hg z.2 H₂) K := by
  have hterm (S T : Finset ι) :
      (if Disjoint S T then secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T * K S T else 0) =
      ∑ z : QuadraticRayRing × QuadraticRayRing, rayQuadraticPair z.1 z.2 *
        (if Disjoint S T then
          star (secondPreColumn p hg Ψ₁ (m * (e * r)) c d e k (secondRayMask p hg z.1 H₁) S) *
          secondPreColumn p hg Ψ₂ (m * (e * r)) c d e (-k) (secondRayMask p hg z.2 H₂) T * K S T
        else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd, secondGaussTerm]
      have h := congrArg (fun a : ℂ => a * K S T)
        (secondGaussTerm_residue_separation p hg hp hinj hodd hpr Ψ₁ Ψ₂
          (m * (e * r)) c d e k H₁ H₂ S T hd)
      simpa only [Finset.sum_mul, mul_assoc] using h
    · simp only [if_neg hd, mul_zero, Finset.sum_const_zero]
  unfold secondKernelPair
  simp_rw [hterm]
  calc
    _ = ∑ S ∈ F.powerset, ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ T ∈ F.powerset,
        rayQuadraticPair z.1 z.2 * (if Disjoint S T then
          star (secondPreColumn p hg Ψ₁ (m * (e * r)) c d e k (secondRayMask p hg z.1 H₁) S) *
          secondPreColumn p hg Ψ₂ (m * (e * r)) c d e (-k) (secondRayMask p hg z.2 H₂) T * K S T
        else 0) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [secondPreKernelPair, Finset.mul_sum]

/-- Common-prime extraction commutes with every conductor kernel. -/
theorem secondKernelPair_eq_children (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    secondKernelPair p hg hp F Ψ₁ Ψ₂ m r c d e k H₁ H₂ K =
      ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ V ∈ F.powerset,
        secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V) *
          secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k (-k)
            (secondRayMask p hg z.1 H₁) (secondRayMask p hg z.2 H₂) K := by
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    exact (Ideal.isCoprime_span_singleton_iff _ _).mp
      (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
  rw [secondKernelPair_eq_pre p hg hp hinj hodd hpr]
  simp only [secondPreKernelPair_eq_children p hg hp hcop hpr,
    secondTotalWeight, Finset.mul_sum, mul_assoc]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma secondChildColumn_rayMask_union (Ψ : O →* ℂ) (m f y : O)
    (V N : Finset ι) (hd : Disjoint V N) (r : QuadraticRayRing) (H : Finset ι → ℂ) :
    secondChildColumn p hg Ψ m f y (fun U => secondRayMask p hg r H (V ∪ U)) N =
      ∑ s : QuadraticRayRing, secondRayTransition p hg V r s *
        secondChildColumn p hg Ψ m f y (secondRayColumn p hg s (fun U => H (V ∪ U))) N := by
  rw [secondChildColumn, secondRayMask_union p hg V N hd]
  simp only [secondChildColumn, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  ring

def fixedChildKernelPair (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m f y₁ y₂ : O) (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) : ℂ :=
  ∑ N ∈ F.powerset, ∑ M ∈ F.powerset,
    star (secondChildColumn p hg Ψ₁ m f y₁ H₁ N) *
      secondChildColumn p hg Ψ₂ m f y₂ H₂ M * K N M

/-- Residues of common prime factors affect only bounded outer coefficients. -/
theorem secondChildKernelPair_ray_separation
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (r₁ r₂ : QuadraticRayRing) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (secondRayMask p hg r₁ (fun _ => 1)) (secondRayMask p hg r₂ (fun _ => 1)) K =
      ∑ s : QuadraticRayRing × QuadraticRayRing,
        (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
          fixedChildKernelPair p hg (F \ V) Ψ₁ Ψ₂ (m * r)
            (c * e * ∏ i ∈ V, p i) (d * e * k₁) (d * e * k₂)
            (secondRayColumn p hg s.1 (fun _ => 1))
            (secondRayColumn p hg s.2 (fun _ => 1))
            (fun N M => K (V ∪ N) (V ∪ M)) := by
  let Q := fun (N M : Finset ι) (s : QuadraticRayRing × QuadraticRayRing) =>
    (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
      (star (secondChildColumn p hg Ψ₁ (m * r) (c * e * ∏ i ∈ V, p i)
          (d * e * k₁) (secondRayColumn p hg s.1 (fun _ => 1)) N) *
        secondChildColumn p hg Ψ₂ (m * r) (c * e * ∏ i ∈ V, p i)
          (d * e * k₂) (secondRayColumn p hg s.2 (fun _ => 1)) M * K (V ∪ N) (V ∪ M))
  calc
    _ = ∑ N ∈ (F \ V).powerset, ∑ M ∈ (F \ V).powerset,
        ∑ s : QuadraticRayRing × QuadraticRayRing, Q N M s := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_congr rfl
      intro M hM
      have hdN : Disjoint V N := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hN) disjoint_sdiff_self_right
      have hdM : Disjoint V M := Finset.disjoint_of_subset_right
        (Finset.mem_powerset.mp hM) disjoint_sdiff_self_right
      rw [secondChildColumn_rayMask_union p hg Ψ₁ _ _ _ V N hdN,
        secondChildColumn_rayMask_union p hg Ψ₂ _ _ _ V M hdM]
      simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type, Q]
      conv_lhs => rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s hs
      apply Finset.sum_congr rfl
      intro t ht
      ring
    _ = ∑ N ∈ (F \ V).powerset, ∑ s : QuadraticRayRing × QuadraticRayRing,
        ∑ M ∈ (F \ V).powerset, Q N M s := by
      apply Finset.sum_congr rfl
      intro N hN
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Q, fixedChildKernelPair, Finset.mul_sum]

lemma secondRayTransition_pair_norm_le (V : Finset ι)
    (r₁ r₂ s₁ s₂ : QuadraticRayRing) :
    ‖star (secondRayTransition p hg V r₁ s₁) * secondRayTransition p hg V r₂ s₂‖ ≤ 1 := by
  rw [norm_mul, norm_star]
  exact (mul_le_mul (secondRayTransition_norm_le p hg V r₁ s₁)
    (secondRayTransition_norm_le p hg V r₂ s₂) (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hp : ∀ i, p i ≠ 0)

/-- One dual lattice mode, with the trace Gauss factor kept at its exact normalization. -/
def secondPairRadialMode (S T : Finset ι) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  let ap : ↥((T \ S) ∪ (S \ T)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ T S
  let n := ∏ i, ap i
  ((Y : ℂ) * primeRowTraceGauss ap (fun i => hp i.val) ac /
    (‖ringComplex n‖ ^ 2 : ℝ)) * primeCuspRowCharacter ap ac e *
    primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2))

theorem secondPairRadialMode_summable (S T : Finset ι) (e : O) (he : e ≠ 0)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => secondPairRadialMode p χ hp S T e k W Y) := by
  let ap : ↥((T \ S) ∪ (S \ T)) → O := fun i => p i.val
  let ac := activePrimeRowCharacter p χ T S
  let n := ∏ i, ap i
  let A := ((Y : ℂ) * primeRowTraceGauss ap (fun i => hp i.val) ac /
    (‖ringComplex n‖ ^ 2 : ℝ)) * primeCuspRowCharacter ap ac e
  have hn : n ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i hi => hp i.val)
  have hK : 0 < Y / (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2) :=
    div_pos hY (mul_pos (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero he)))
      (sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hn))))
  have hs := paperRadialFourier_lattice_summable_norm W _ hK
  have hr (k : O) : ‖primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k‖ ≤ 1 :=
    primeCuspRowCharacter_norm_le_one ap (fun i => (ac i)⁻¹) k
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun _ => norm_nonneg _) _ (hs.mul_left ‖A‖)
  intro k
  change ‖A * primeCuspRowCharacter ap (fun i => (ac i)⁻¹) k *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2))‖ ≤ _
  rw [norm_mul, norm_mul, show Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2) =
      Y / (‖ringComplex e‖ ^ 2 * ‖ringComplex n‖ ^ 2) * ‖ringComplex k‖ ^ 2 by ring]
  exact mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) (hr k)) (norm_nonneg _)

theorem maskedSecondDual_eq_modes (G S T : Finset ι) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    maskedSecondDual p χ hp G S T W Y =
      ∑ E ∈ G.powerset,
        (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, secondPairRadialMode p χ hp S T (∏ i ∈ E, p i) k W Y := by
  simp only [maskedSecondDual, secondPairRadialMode, supportMobius,
    mul_assoc, tsum_mul_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  ring

def residualSecondMode (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
    if Disjoint S T then
      star (supportMobius S * secondInputCoefficient p χ Ψ₁ m c d H₁ S) *
        (supportMobius T * secondInputCoefficient p χ Ψ₂ m c d H₂ T) *
        secondPairRadialMode p χ hp S T e k W Y else 0

theorem residualSecondMode_summable (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    Summable (fun k : O => residualSecondMode p χ hp F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) := by
  apply summable_sum
  intro S hS
  apply summable_sum
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd]
    exact (secondPairRadialMode_summable p χ hp S T e he W Y hY).mul_left _
  · simp only [if_neg hd]
    exact summable_zero

theorem residualSecondMode_tsum (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (e : O) (he : e ≠ 0) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' k : O, residualSecondMode p χ hp F G Ψ₁ Ψ₂ m c d H₁ H₂ e k W Y) =
      ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑' k : O, if Disjoint S T then
          star (supportMobius S * secondInputCoefficient p χ Ψ₁ m c d H₁ S) *
            (supportMobius T * secondInputCoefficient p χ Ψ₂ m c d H₂ T) *
            secondPairRadialMode p χ hp S T e k W Y else 0 := by
  have hs (S T : Finset ι) : Summable (fun k : O => if Disjoint S T then
      star (supportMobius S * secondInputCoefficient p χ Ψ₁ m c d H₁ S) *
        (supportMobius T * secondInputCoefficient p χ Ψ₂ m c d H₂ T) *
        secondPairRadialMode p χ hp S T e k W Y else 0) := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd]
      exact (secondPairRadialMode_summable p χ hp S T e he W Y hY).mul_left _
    · simp only [if_neg hd]
      exact summable_zero
  unfold residualSecondMode
  rw [Summable.tsum_finsetSum (fun S _ => summable_sum (fun T _ => hs S T))]
  apply Finset.sum_congr rfl
  intro S hS
  exact Summable.tsum_finsetSum (fun T _ => hs S T)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hp : ∀ i, p i ≠ 0)

def secondOverlapBlock (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset, if Disjoint S T then
    overlapPairWeight p χ Ψ m c d H G S T * maskedSecondDual p χ hp G S T W Y
  else 0

theorem secondOverlapBlock_eq_modes (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O)
    (H : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    secondOverlapBlock p χ hp F G Ψ m c d H W Y =
      (↑(‖secondInputCoefficient p χ Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ) *
        ∑ E ∈ G.powerset,
          ((supportMobius E : ℂ) /
            (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, residualSecondMode p χ hp F G Ψ Ψ m c d
            (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
            (∏ i ∈ E, p i) k W Y := by
  let a := (↑(‖secondInputCoefficient p χ Ψ m c d (fun _ => 1) G‖ ^ 2) : ℂ)
  let w := fun E : Finset ι =>
    (supportMobius E : ℂ) /
      (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)
  let f := fun (E S T : Finset ι) (k : O) => if Disjoint S T then
    star (supportMobius S *
      secondInputCoefficient p χ Ψ m c d (fun U => H (G ∪ U)) S) *
    (supportMobius T *
      secondInputCoefficient p χ Ψ m c d (fun U => H (G ∪ U)) T) *
    secondPairRadialMode p χ hp S T (∏ i ∈ E, p i) k W Y
    else 0
  have hterm (S T : Finset ι) :
      (if Disjoint S T then overlapPairWeight p χ Ψ m c d H G S T *
        maskedSecondDual p χ hp G S T W Y else 0) =
      a * ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
    by_cases hd : Disjoint S T
    · simp only [if_pos hd, maskedSecondDual_eq_modes p χ hp,
        overlapPairWeight, f, Finset.mul_sum, tsum_mul_left]
      apply Finset.sum_congr rfl
      intro E hE
      dsimp only [a, w]
      ring
    · simp [hd, f]
  calc
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ T ∈ (F \ G).powerset,
        ∑ E ∈ G.powerset, w E * ∑' k : O, f E S T k := by
      simp only [secondOverlapBlock, hterm, Finset.mul_sum]
    _ = a * ∑ S ∈ (F \ G).powerset, ∑ E ∈ G.powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      apply Finset.sum_congr rfl
      intro S hS
      rw [Finset.sum_comm]
    _ = a * ∑ E ∈ G.powerset, ∑ S ∈ (F \ G).powerset,
        ∑ T ∈ (F \ G).powerset, w E * ∑' k : O, f E S T k := by
      congr 1
      rw [Finset.sum_comm]
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro E hE
      rw [residualSecondMode_tsum p χ hp F G Ψ Ψ m c d
        (fun U => H (G ∪ U)) (fun U => H (G ∪ U))
        (∏ i ∈ E, p i)
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hp i)) W Y hY]
      simp only [Finset.mul_sum]
      rfl


end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondPairRadialMode_normalized (S T : Finset ι) (hd : Disjoint S T)
    (e k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondPairRadialMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp S T e k W Y =
      ((Y : ℂ) / (‖ringComplex (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
        paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
          (‖ringComplex e‖ ^ 2 * primeProductNorm p (S ∪ T))) *
        secondNormalizedGaussTerm p hp hg S T e k := by
  have hn : (∏ i : ↥((T \ S) ∪ (S \ T)), p i.val) = ∏ i ∈ S ∪ T, p i := by
    rw [Finset.prod_coe_sort]
    simp only [Finset.sdiff_eq_self_of_disjoint hd,
      Finset.sdiff_eq_self_of_disjoint hd.symm, Finset.union_comm T S]
  have hnorm : (‖ringComplex (∏ i ∈ S ∪ T, p i)‖ : ℂ) =
      (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) * (‖ringComplex (∏ i ∈ T, p i)‖ : ℂ) := by
    rw [Finset.prod_union hd, map_mul, norm_mul, Complex.ofReal_mul]
  simp only [secondPairRadialMode, secondNormalizedGaussTerm, hn, primeProductNorm,
    Complex.ofReal_pow, Complex.ofReal_mul, hnorm, div_eq_mul_inv, mul_inv_rev, inv_pow, pow_two]
  ring

def secondFrequencyKernel (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) : ℂ :=
  secondKernelPair p hg hp F Ψ₁ Ψ₂ m r c d e k H₁ H₂ (fun S T =>
    ((Y : ℂ) / (‖ringComplex (∏ i ∈ S ∪ T, p i)‖ : ℂ)) *
      paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
        (‖ringComplex e‖ ^ 2 * primeProductNorm p (S ∪ T))))

theorem secondGaussTerm_test_factors (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) (S T : Finset ι) :
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k H₁ H₂ S T =
      star (H₁ S) * H₂ T *
        secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k (fun _ => 1) (fun _ => 1) S T := by
  simp only [secondGaussTerm, secondInputCoefficient, star_mul, mul_one]
  ring

theorem secondFrequencyKernel_log_tests (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (W : 𝓢(ℝ, ℂ)) :
    secondFrequencyKernel p hp hg F Ψ₁ Ψ₂ m r c d e k
      (fun S => V₁ (columnLog p X₁ S)) (fun T => V₂ (columnLog p X₂ T)) W Y =
      actualSecondKernel p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y := by
  unfold secondFrequencyKernel secondKernelPair actualSecondKernel
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd]
    rw [secondGaussTerm_test_factors]
    ring
  · simp only [if_neg hd]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]

theorem commonProduct_mask
    (hinj : Function.Injective (fun i => Ideal.span {p i})) (U G : Finset ι) :
    primeCoprimeMask p U (∏ i ∈ G, p i) = if Disjoint U G then 1 else 0 := by
  by_cases hd : Disjoint U G
  · rw [primeCoprimeMask_indicator, if_pos hd]
    apply if_pos
    intro i hi hdiv
    have hc : IsCoprime (p i) (∏ j ∈ G, p j) := by
      apply IsCoprime.prod_right
      intro j hj
      have hij : i ≠ j := fun h => Finset.disjoint_left.mp hd hi (h.symm ▸ hj)
      exact (Ideal.isCoprime_span_singleton_iff _ _).mp
        (Ideal.isCoprime_of_isMaximal (hinj.ne hij))
    obtain ⟨a, b, hab⟩ := hc
    have hi0 : Ideal.Quotient.mk (Ideal.span {p i}) (p i) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr (dvd_refl _))
    have hg0 : Ideal.Quotient.mk (Ideal.span {p i}) (∏ j ∈ G, p j) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv)
    have h01 : (0 : O ⧸ Ideal.span {p i}) = 1 := by
      simpa only [map_add, map_mul, map_one, hi0, hg0, mul_zero, zero_add] using
        congrArg (Ideal.Quotient.mk (Ideal.span {p i})) hab
    exact zero_ne_one h01
  · obtain ⟨i, hiU, hiG⟩ := Finset.not_disjoint_iff.mp hd
    rw [primeCoprimeMask_indicator, if_neg hd]
    exact if_neg (fun h => h i hiU (Finset.dvd_prod_of_mem p hiG))

theorem sum_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, A U) =
      ∑ U ∈ F.powerset, primeCoprimeMask p U (∏ i ∈ G, p i) * A U := by
  have hsub : (F \ G).powerset ⊆ F.powerset := Finset.powerset_mono.mpr Finset.sdiff_subset
  calc
    _ = ∑ U ∈ (F \ G).powerset, primeCoprimeMask p U (∏ i ∈ G, p i) * A U := by
      apply Finset.sum_congr rfl
      intro U hU
      have hd : Disjoint U G := Finset.disjoint_left.mpr (fun i hi hG =>
        (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hi)).2 hG)
      rw [commonProduct_mask p hinj U G, if_pos hd, one_mul]
    _ = _ := by
      apply Finset.sum_subset hsub
      intro U hUF hUG
      have hd : ¬ Disjoint U G := by
        intro hd
        apply hUG
        apply Finset.mem_powerset.mpr
        intro i hi
        exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hUF) hi,
          fun hG => Finset.disjoint_left.mp hd hi hG⟩
      rw [commonProduct_mask p hinj U G, if_neg hd, zero_mul]

theorem sum_pair_remove_common_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (A : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset, A U V) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        primeCoprimeMask p U (∏ i ∈ G, p i) *
        primeCoprimeMask p V (∏ i ∈ G, p i) * A U V := by
  rw [sum_remove_common_pool p hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  rw [sum_remove_common_pool p hinj F G, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro V hV
  ring

lemma star_primeCoprimeMask (S : Finset ι) (a : O) :
    star (primeCoprimeMask p S a) = primeCoprimeMask p S a := by
  rw [primeCoprimeMask_indicator]
  split_ifs <;> simp only [star_one, star_zero]

variable (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

theorem secondInputCoefficient_fixed_mask (Ψ : O →* ℂ) (m g c d : O)
    (H : Finset ι → ℂ) (U : Finset ι) :
    secondInputCoefficient p χ Ψ (m * g) c d H U =
      primeCoprimeMask p U g * secondInputCoefficient p χ Ψ m c d H U := by
  rw [secondInputCoefficient, subsetMask_mul p χ U m g]
  unfold secondInputCoefficient
  ring

theorem input_pair_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O)
    (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    (∑ U ∈ (F \ G).powerset, ∑ V ∈ (F \ G).powerset,
      if Disjoint U V then
        star (supportMobius U * secondInputCoefficient p χ Ψ₁ m c d H₁ U) *
        (supportMobius V * secondInputCoefficient p χ Ψ₂ m c d H₂ V) * K U V else 0) =
      ∑ U ∈ F.powerset, ∑ V ∈ F.powerset,
        if Disjoint U V then
          star (supportMobius U * secondInputCoefficient p χ Ψ₁ (m * ∏ i ∈ G, p i) c d H₁ U) *
          (supportMobius V * secondInputCoefficient p χ Ψ₂ (m * ∏ i ∈ G, p i) c d H₂ V) * K U V
        else 0 := by
  rw [sum_pair_remove_common_pool p hinj F G]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  by_cases hd : Disjoint U V
  · rw [if_pos hd, if_pos hd, secondInputCoefficient_fixed_mask, secondInputCoefficient_fixed_mask]
    simp only [star_mul, star_primeCoprimeMask]
    ring
  · simp only [if_neg hd, mul_zero]

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

/-- Divisor modes use a fixed prime pool after absorbing the removed primes into its mask. -/
theorem residualSecondMode_eq_frequencyKernel
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G E : Finset ι) (hEG : E ⊆ G)
    (Ψ₁ Ψ₂ : O →* ℂ) (m c d : O) (H₁ H₂ : Finset ι → ℂ)
    (k : O) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    residualSecondMode p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp
      F G Ψ₁ Ψ₂ m c d H₁ H₂ (∏ i ∈ E, p i) k W Y =
      secondFrequencyKernel p hp hg F Ψ₁ Ψ₂ m (∏ i ∈ G \ E, p i) c d
        (∏ i ∈ E, p i) k H₁ H₂ W Y := by
  have hprod : (∏ i ∈ G, p i) = (∏ i ∈ E, p i) * ∏ i ∈ G \ E, p i := by
    rw [← Finset.prod_union (show Disjoint E (G \ E) from disjoint_sdiff_self_right),
      Finset.union_sdiff_of_subset hEG]
  unfold residualSecondMode
  rw [input_pair_fixed_pool p _ hinj F G Ψ₁ Ψ₂ m c d H₁ H₂]
  unfold secondFrequencyKernel secondKernelPair
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · rw [if_pos hd, if_pos hd, secondPairRadialMode_normalized p hp hg S T hd, hprod]
    unfold secondGaussTerm
    ring
  · simp only [if_neg hd]

theorem secondOverlapBlock_eq_frequencyKernel
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F G : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    secondOverlapBlock p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp
      F G Ψ m c d H W Y =
      (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
        Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
      ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
        ∑' k : O, secondFrequencyKernel p hp hg F Ψ Ψ m (∏ i ∈ G \ E, p i) c d
          (∏ i ∈ E, p i) k (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  rw [secondOverlapBlock_eq_modes p _ hp F G Ψ m c d H W Y hY]
  apply congrArg (fun x : ℂ =>
    (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
      Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) * x)
  apply Finset.sum_congr rfl
  intro E hE
  apply congrArg (fun x : ℂ => (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) * x)
  exact tsum_congr (fun k => residualSecondMode_eq_frequencyKernel p hp hg hinj F G E
    (Finset.mem_powerset.mp hE) Ψ Ψ m c d (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) k W Y)

/-- The complete second reflection is a divisor sum of fixed-pool frequency kernels. -/
theorem inputConjugateRow_second_frequency_expansion
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F : Finset ι) (Ψ : O →* ℂ) (m c d : O) (H : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F Ψ m c d H z‖ ^ 2 : ℝ)) =
      ∑ G ∈ F.powerset,
        (‖secondInputCoefficient p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          Ψ m c d (fun _ => 1) G‖ ^ 2 : ℝ) *
        ∑ E ∈ G.powerset, (supportMobius E / (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' k : O, secondFrequencyKernel p hp hg F Ψ Ψ m (∏ i ∈ G \ E, p i) c d
            (∏ i ∈ E, p i) k (fun U => H (G ∪ U)) (fun U => H (G ∪ U)) W Y := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  have hχ : ∀ i, χ i ≠ 1 := fun i => complexSexticChar_ne_one (Ideal.span {p i}) (hg i)
  calc
    _ = ∑ G ∈ F.powerset, secondOverlapBlock p χ hp F G Ψ m c d H W Y :=
      inputConjugateRow_smoothed_second_poisson p χ hp hinj hχ F Ψ m c d H W Y hY
    _ = _ := Finset.sum_congr rfl (fun G hG =>
      secondOverlapBlock_eq_frequencyKernel p hp hg hinj F G Ψ m c d H W Y hY)

end SecondPassArithmetic

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem secondChildColumn_zero_of_overlap
    (Ψ : O →* ℂ) (m c e y : O) (H : Finset ι → ℂ)
    (V N : Finset ι) (hd : ¬ Disjoint V N) :
    secondChildColumn p hg Ψ m (c * e * ∏ i ∈ V, p i) y H N = 0 := by
  obtain ⟨i, hiV, hiN⟩ := Finset.not_disjoint_iff.mp hd
  have hdiv : p i ∣ c * e * ∏ j ∈ V, p j :=
    dvd_mul_of_dvd_right (Finset.dvd_prod_of_mem p hiV) (c * e)
  have hz : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N
      (c * e * ∏ j ∈ V, p j) = 0 := by
    apply Finset.prod_eq_zero hiN
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr hdiv), MulChar.map_zero]
  simp only [secondChildColumn, hz, zero_pow (by decide : (4 : ℕ) ≠ 0), mul_zero, zero_mul]

/-- The label annihilates every column meeting its common prime support. -/
theorem fixedChildKernelPair_fixed_pool (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ)
    (m c e y₁ y₂ : O) (H₁ H₂ : Finset ι → ℂ) (K : Finset ι → Finset ι → ℂ) :
    fixedChildKernelPair p hg (F \ V) Ψ₁ Ψ₂ m (c * e * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K =
      fixedChildKernelPair p hg F Ψ₁ Ψ₂ m (c * e * ∏ i ∈ V, p i) y₁ y₂ H₁ H₂ K := by
  have hzero (N : Finset ι) (hNF : N ∈ F.powerset)
      (hNV : N ∉ (F \ V).powerset) : ¬ Disjoint V N := by
    intro hd
    apply hNV
    apply Finset.mem_powerset.mpr
    intro i hi
    exact Finset.mem_sdiff.mpr ⟨(Finset.mem_powerset.mp hNF) hi,
      fun hiv => Finset.disjoint_left.mp hd hiv hi⟩
  unfold fixedChildKernelPair
  calc
    _ = ∑ N ∈ (F \ V).powerset, ∑ M ∈ F.powerset,
        star (secondChildColumn p hg Ψ₁ m (c * e * ∏ i ∈ V, p i) y₁ H₁ N) *
          secondChildColumn p hg Ψ₂ m (c * e * ∏ i ∈ V, p i) y₂ H₂ M * K N M := by
      apply Finset.sum_congr rfl
      intro N hN
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro M hMF hMV
      rw [secondChildColumn_zero_of_overlap p hg Ψ₂ m c e y₂ H₂ V M (hzero M hMF hMV),
        mul_zero, zero_mul]
    _ = _ := by
      apply Finset.sum_subset (Finset.powerset_mono.mpr Finset.sdiff_subset)
      intro N hNF hNV
      rw [secondChildColumn_zero_of_overlap p hg Ψ₁ m c e y₁ H₁ V N (hzero N hNF hNV), star_zero]
      simp only [zero_mul, Finset.sum_const_zero]

theorem secondChildKernelPair_ray_fixed_pool
    (F V : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k₁ k₂ : O)
    (r₁ r₂ : QuadraticRayRing) (K : Finset ι → Finset ι → ℂ) :
    secondChildKernelPair p hg F V Ψ₁ Ψ₂ m r c d e k₁ k₂
      (secondRayMask p hg r₁ (fun _ => 1)) (secondRayMask p hg r₂ (fun _ => 1)) K =
      ∑ s : QuadraticRayRing × QuadraticRayRing,
        (star (secondRayTransition p hg V r₁ s.1) * secondRayTransition p hg V r₂ s.2) *
          fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * r)
            (c * e * ∏ i ∈ V, p i) (d * e * k₁) (d * e * k₂)
            (secondRayColumn p hg s.1 (fun _ => 1))
            (secondRayColumn p hg s.2 (fun _ => 1))
            (fun N M => K (V ∪ N) (V ∪ M)) := by
  rw [secondChildKernelPair_ray_separation]
  simp only [fixedChildKernelPair_fixed_pool]

end SecondPassArithmetic

open scoped Classical SchwartzMap FourierTransform ContDiff

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def radialPairKernel (e k : O) (W : 𝓢(ℝ, ℂ))
    (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) (S T : Finset ι) : ℂ :=
  star (normalizedColumn p (fun U => V₁ (columnLog p X₁ U)) S) *
    normalizedColumn p (fun U => V₂ (columnLog p X₂ U)) T *
    paperRadialFourier W (Y * ‖ringComplex k‖ ^ 2 /
      (‖ringComplex e‖ ^ 2 * primeProductNorm p S * primeProductNorm p T))

theorem actualSecondKernel_eq_coupled
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * secondKernelPair p hg hp F Ψ₁ Ψ₂ m r c d e k
        (fun _ => 1) (fun _ => 1) (radialPairKernel p e k W V₁ V₂ X₁ X₂ Y) := by
  simp only [actualSecondKernel, secondKernelPair, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  apply Finset.sum_congr rfl
  intro T hT
  by_cases hd : Disjoint S T
  · simp only [if_pos hd, radialPairKernel, normalizedColumn,
      primeProductNorm_union p S T hd, Finset.prod_union hd,
      map_mul, norm_mul, Complex.ofReal_mul, Complex.star_def,
      Complex.conj_ofReal, div_eq_mul_inv, mul_inv_rev, map_inv₀]
    ring
  · simp only [if_neg hd, mul_zero]

/-- The smooth kernel decomposes into fixed residue sectors on a single prime pool. -/
theorem actualSecondKernel_eq_fixed_children
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F : Finset ι) (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ Y : ℝ) :
    actualSecondKernel p hp hg F Ψ₁ Ψ₂ m r c d e k W V₁ V₂ X₁ X₂ Y =
      (Y : ℂ) * ∑ z : QuadraticRayRing × QuadraticRayRing, ∑ V ∈ F.powerset,
        ∑ s : QuadraticRayRing × QuadraticRayRing,
          secondTotalWeight p hg Ψ₁ Ψ₂ m r c d e k (z,V) *
            (star (secondRayTransition p hg V z.1 s.1) * secondRayTransition p hg V z.2 s.2) *
            fixedChildKernelPair p hg F Ψ₁ Ψ₂ (m * r)
              (c * e * ∏ i ∈ V, p i) (d * e * k) (d * e * (-k))
              (secondRayColumn p hg s.1 (fun _ => 1))
              (secondRayColumn p hg s.2 (fun _ => 1))
              (fun N M => radialPairKernel p e k W V₁ V₂ X₁ X₂ Y (V ∪ N) (V ∪ M)) := by
  rw [actualSecondKernel_eq_coupled, secondKernelPair_eq_children p hg hp hinj hodd hpr]
  simp only [secondChildKernelPair_ray_fixed_pool, Finset.mul_sum, mul_assoc]

end SecondPassArithmetic

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar
open scoped Classical

lemma primeRowTraceGauss_empty {ι : Type*} [Fintype ι] [DecidableEq ι] [IsEmpty ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : primeRowTraceGauss p hp χ = 1 := by
  have hinj : Function.Injective (fun i => Ideal.span {p i}) := fun i => isEmptyElim i
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [primeRowTraceGauss_eq_crt p hp hinj,
    ProductGauss.factorization_equiv (fun i => O ⧸ Ideal.span {p i}) (primeProductCRT p hinj)]
  simp only [Fintype.prod_empty]

end SchwartzPlanePoisson

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hp : ∀ i, p i ≠ 0)
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

lemma secondNormalizedGaussTerm_zero_of_ne (S T : Finset ι) (hne : S ≠ T) (e : O) :
    secondNormalizedGaussTerm p hp hg S T e 0 = 0 := by
  have hs : ((T \ S) ∪ (S \ T)).Nonempty := by
    by_contra hn
    have he := Finset.not_nonempty_iff_eq_empty.mp hn
    simp only [Finset.union_eq_empty, Finset.sdiff_eq_empty_iff_subset] at he
    exact hne (Finset.Subset.antisymm he.2 he.1)
  letI : Nonempty ↥((T \ S) ∪ (S \ T)) := hs.to_subtype
  simp only [secondNormalizedGaussTerm, primeCuspRowCharacter_zero, mul_zero]

lemma secondNormalizedGaussTerm_empty (e k : O) :
    secondNormalizedGaussTerm p hp hg ∅ ∅ e k = 1 := by
  letI : IsEmpty ↥(((∅ : Finset ι) \ ∅) ∪ (∅ \ ∅)) := ⟨fun i => by
    rcases Finset.mem_union.mp i.property with hi | hi
    · exact Finset.notMem_empty i.val (Finset.mem_sdiff.mp hi).1
    · exact Finset.notMem_empty i.val (Finset.mem_sdiff.mp hi).1⟩
  simp only [secondNormalizedGaussTerm, primeRowTraceGauss_empty, primeCuspRowCharacter,
    Fintype.prod_empty, Finset.prod_empty, map_one, norm_one, Complex.ofReal_one, one_mul, div_one]
  change (1 : ℂ) * 1 = 1
  exact mul_one 1

theorem secondGaussTerm_empty (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e k : O)
    (H₁ H₂ : Finset ι → ℂ) :
    secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e k H₁ H₂ ∅ ∅ = star (H₁ ∅) * H₂ ∅ := by
  simp only [secondGaussTerm, supportMobius, Finset.card_empty, pow_zero,
    secondInputCoefficient, primeCoprimeMask, primeSubsetRow, Finset.prod_empty,
    map_one, one_mul, one_pow, secondNormalizedGaussTerm_empty, mul_one]

/-- Only the empty conductor contributes at zero dual frequency. -/
theorem secondFrequencyKernel_zero (F : Finset ι)
    (Ψ₁ Ψ₂ : O →* ℂ) (m r c d e : O) (H₁ H₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    secondFrequencyKernel p hp hg F Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ W Y =
      (Y : ℂ) * paperRadialFourier W 0 * star (H₁ ∅) * H₂ ∅ := by
  have hz (S T : Finset ι) (hne : S ≠ T) :
      secondGaussTerm p hp hg Ψ₁ Ψ₂ m r c d e 0 H₁ H₂ S T = 0 := by
    unfold secondGaussTerm
    rw [secondNormalizedGaussTerm_zero_of_ne p hp hg S T hne e, mul_zero]
  unfold secondFrequencyKernel secondKernelPair
  rw [Finset.sum_eq_single ∅]
  · rw [Finset.sum_eq_single ∅]
    · simp [secondGaussTerm_empty, mul_comm, mul_left_comm, mul_assoc]
    · intro T hT hne
      rw [hz ∅ T (Ne.symm hne)]
      simp only [zero_mul, ite_self]
    · simp
  · intro S hS hne
    apply Finset.sum_eq_zero
    intro T hT
    by_cases hd : Disjoint S T
    · have hneq : S ≠ T := by
        intro heq
        subst T
        exact hne (by simpa using Finset.disjoint_iff_inter_eq_empty.mp hd)
      rw [if_pos hd, hz S T hneq, zero_mul]
    · simp only [if_neg hd]
  · simp

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson
open scoped Classical
variable {κ : Type*}

/- The retained fourth-power label and its complementary square factor. -/
def bit (b : Bool) : ℕ := if b then 1 else 0

def conductorExponent (parityBit ε₁ ε₂ : Bool) : ZMod 6 :=
  (bit ε₁ : ZMod 6) - (bit ε₂ : ZMod 6) + 3 * (bit parityBit : ZMod 6)

def crtExponent (side parityBit ε₁ ε₂ : Bool) : ℕ :=
  if conductorExponent parityBit ε₁ ε₂ = 0 then 0 else
    ((1 : ZMod 6) + if side then -conductorExponent parityBit ε₁ ε₂
      else conductorExponent parityBit ε₁ ε₂).val

def dilationExponent (parityBit ε₁ ε₂ : Bool) : ℕ :=
  if parityBit then bit ε₁ + bit ε₂ else 0

def retained (parityBit ε₁ ε₂ : Bool) : Bool := parityBit || (ε₁ && ε₂)

theorem exponent_table (side parityBit ε₁ ε₂ : Bool) :
    (4 * bit (if side then ε₂ else ε₁) + crtExponent side parityBit ε₁ ε₂ +
      dilationExponent parityBit ε₁ ε₂) % 6 = if retained parityBit ε₁ ε₂ then 4 else 0 := by
  cases side <;> cases parityBit <;> cases ε₁ <;> cases ε₂ <;> decide


def parity (m : ℕ) : Bool := decide (m % 2 = 1)

def evenDouble (m : ℕ) (ε₁ ε₂ : Bool) : Bool := !parity m && ε₁ && ε₂

def b0Exponent (m : ℕ) (ε₁ ε₂ : Bool) : ℕ := m / 2 - bit (evenDouble m ε₁ ε₂)

theorem multiplicity_decomposition (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m) :
    2 * b0Exponent m ε₁ ε₂ + 2 * bit (evenDouble m ε₁ ε₂) + bit (parity m) = m := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp [b0Exponent, evenDouble, parity, bit, h] <;> omega

theorem b0Exponent_pos_of_not_retained (m : ℕ) (ε₁ ε₂ : Bool) (hm : 0 < m)
    (hret : retained (parity m) ε₁ ε₂ = false) : 0 < b0Exponent m ε₁ ε₂ := by
  have hmod := Nat.mod_lt m (by decide : 0 < 2)
  have hdiv := Nat.mod_add_div m 2
  cases ε₁ <;> cases ε₂ <;> by_cases h : m % 2 = 1 <;>
    simp_all [b0Exponent, evenDouble, parity, retained, bit] <;> omega


def primeProduct (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O := ∏ j ∈ B, p j ^ v j

def cubeRadical (p : κ → O) (B : Finset κ) : O := ∏ j ∈ B, p j

def aLabel (p : κ → O) (B : Finset κ) (ε : κ → Bool) : O :=
  primeProduct p B (fun j => bit (ε j))

def crtLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (side : Bool) : O :=
  primeProduct p B (fun j => crtExponent side (parity (v j)) (ε₁ j) (ε₂ j))

def dilationLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j))

def jLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (retained (parity (v j)) (ε₁ j) (ε₂ j)))

def j2Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => bit (evenDouble (v j) (ε₁ j) (ε₂ j)))

def squarefreeLabel (p : κ → O) (B : Finset κ) (v : κ → ℕ) : O :=
  primeProduct p B (fun j => bit (parity (v j)))

def b0Label (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) : O :=
  primeProduct p B (fun j => b0Exponent (v j) (ε₁ j) (ε₂ j))


theorem cube_product_decomposition (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) :
    primeProduct p B v = b0Label p B v ε₁ ε₂ ^ 2 * j2Label p B v ε₁ ε₂ ^ 2 *
      squarefreeLabel p B v := by
  simp only [b0Label, j2Label, squarefreeLabel, primeProduct, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib, ← pow_mul, ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  have h := multiplicity_decomposition (v j) (ε₁ j) (ε₂ j) (hv j hj)
  omega

theorem jLabel_eq_squarefree_mul_j2 (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) :
    jLabel p B v ε₁ ε₂ = squarefreeLabel p B v * j2Label p B v ε₁ ε₂ := by
  simp only [jLabel, squarefreeLabel, j2Label, primeProduct, ← Finset.prod_mul_distrib,
    ← pow_add]
  apply Finset.prod_congr rfl
  intro j hj
  congr 1
  cases hp : parity (v j) <;> cases ε₁ j <;> cases ε₂ j <;>
    simp [bit, retained, evenDouble, hp]

theorem cube_pair_product_decomposition
    (p : κ → O) (B : Finset κ) (v₁ v₂ : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v₁ j + v₂ j) :
    primeProduct p B v₁ * primeProduct p B v₂ =
      b0Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      j2Label p B (fun j => v₁ j + v₂ j) ε₁ ε₂ ^ 2 *
      squarefreeLabel p B (fun j => v₁ j + v₂ j) := by
  rw [← cube_product_decomposition p B (fun j => v₁ j + v₂ j) ε₁ ε₂ hv]
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson
open scoped Classical

section Rows
variable {ι : Type*} [DecidableEq ι] (q : ι → O) [∀ i, (Ideal.span {q i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {q i}) (S : Finset ι)

theorem row_pow (a : O) (m : ℕ) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (a ^ m) = primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ m := by
  simp only [primeSubsetRow, map_pow, Finset.prod_pow]

theorem row_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (∏ j ∈ B, a j) =
      ∏ j ∈ B, primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (a j) := by
  classical
  induction B using Finset.induction_on with
  | empty => simp [primeSubsetRow]
  | @insert j B hj ih =>
    simp only [Finset.prod_insert hj, SecondPassArithmetic.subsetRow_mul, ih]

theorem row_sixth (a : O) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ 6 = primeCoprimeMask q S a := by
  rw [← primeSubsetRow_diagonal q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a,
    SecondPassArithmetic.sexticRow_star q hg S a]
  ring

include hg

theorem mask_mul (a b : O) :
    primeCoprimeMask q S (a * b) = primeCoprimeMask q S a * primeCoprimeMask q S b := by
  simp only [← row_sixth q hg S, SecondPassArithmetic.subsetRow_mul, mul_pow]

theorem mask_pow (a : O) (m : ℕ) :
    primeCoprimeMask q S (a ^ m) = primeCoprimeMask q S a ^ m := by
  rw [← row_sixth q hg S, row_pow, ← row_sixth q hg S]
  simp only [← pow_mul, Nat.mul_comm]

theorem mask_prod {κ : Type*} (B : Finset κ) (a : κ → O) :
    primeCoprimeMask q S (∏ j ∈ B, a j) = ∏ j ∈ B, primeCoprimeMask q S (a j) := by
  rw [← row_sixth q hg S, row_prod, ← Finset.prod_pow]
  simp only [row_sixth]

theorem row_zero_of_mask_zero (a : O) (h : primeCoprimeMask q S a = 0) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a = 0 := by
  have hq := row_sixth q hg S a
  rw [h] at hq
  exact (pow_eq_zero_iff (by decide : (6 : ℕ) ≠ 0)).mp hq

theorem row_power_mul_mask_power (a : O) (k m : ℕ) (hk : 0 < k) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ k * primeCoprimeMask q S a ^ m =
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ k := by
  by_cases h : ∃ i ∈ S, q i ∣ a
  · have hm : primeCoprimeMask q S a = 0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (by intro hn; obtain ⟨i, hi, hd⟩ := h; exact hn i hi hd)
    rw [row_zero_of_mask_zero q hg S a hm]
    simp [Nat.ne_of_gt hk]
  · have hm : primeCoprimeMask q S a = 1 := by
      rw [primeCoprimeMask_indicator]
      exact if_pos (fun i hi hd => h ⟨i, hi, hd⟩)
    simp only [hm, one_pow, mul_one]

def localFactor (side parityBit ε₁ ε₂ : Bool) (a : O) : ℂ :=
  primeCoprimeMask q S a *
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ (4 * bit (if side then ε₂ else ε₁)) *
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ crtExponent side parityBit ε₁ ε₂ *
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ dilationExponent parityBit ε₁ ε₂

theorem localFactor_eq (side parityBit ε₁ ε₂ : Bool) (a : O) :
    localFactor q hg S side parityBit ε₁ ε₂ a =
      if retained parityBit ε₁ ε₂ then primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ 4
      else primeCoprimeMask q S a := by
  by_cases h : ∃ i ∈ S, q i ∣ a
  · have hm : primeCoprimeMask q S a = 0 := by
      rw [primeCoprimeMask_indicator]
      exact if_neg (by intro hn; obtain ⟨i, hi, hd⟩ := h; exact hn i hi hd)
    have hz := row_zero_of_mask_zero q hg S a hm
    simp [localFactor, hm, hz]
  · have hm : primeCoprimeMask q S a = 1 := by
      rw [primeCoprimeMask_indicator]
      exact if_pos (fun i hi hd => h ⟨i, hi, hd⟩)
    have h6 : primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S a ^ 6 = 1 := (row_sixth q hg S a).trans hm
    simp only [localFactor, hm, one_mul, ← pow_add]
    rw [pow_eq_pow_mod _ h6, exponent_table]
    split <;> simp

end Rows
section
variable {ι κ : Type*} [DecidableEq ι] (q : ι → O) [∀ i, (Ideal.span {q i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {q i}) (S : Finset ι)

theorem localFactor_eq_b0 (side ε₁ ε₂ : Bool) (a : O) (m : ℕ) (hm : 0 < m) :
    localFactor q hg S side (parity m) ε₁ ε₂ a =
      (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (a ^ bit (retained (parity m) ε₁ ε₂))) ^ 4 *
        primeCoprimeMask q S (a ^ b0Exponent m ε₁ ε₂) := by
  rw [localFactor_eq, row_pow, mask_pow q hg S]
  cases hr : retained (parity m) ε₁ ε₂
  · have hpos := b0Exponent_pos_of_not_retained m ε₁ ε₂ hm hr
    simp only [Bool.false_eq_true, ↓reduceIte, bit, Bool.false_eq_true, pow_zero, one_pow,
      one_mul]
    rw [primeCoprimeMask_indicator]
    split <;> simp [Nat.ne_of_gt hpos]
  · simp only [↓reduceIte, bit, pow_one]
    exact (row_power_mul_mask_power q hg S a 4 _ (by decide)).symm

theorem first_pass_label_identity (p : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j) (side : Bool) :
    primeCoprimeMask q S (cubeRadical p B) *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side) *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (dilationLabel p B v ε₁ ε₂) =
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (jLabel p B v ε₁ ε₂) ^ 4 *
      primeCoprimeMask q S (b0Label p B v ε₁ ε₂) := by
  classical
  simp only [cubeRadical, aLabel, crtLabel, dilationLabel, jLabel, b0Label,
    primeProduct, mask_prod q hg S, row_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [row_pow, row_pow, row_pow]
  convert localFactor_eq_b0 q hg S side (ε₁ j) (ε₂ j) (p j) (v j) (hv j hj) using 1
  cases side <;> simp only [localFactor, Bool.false_eq_true, ↓reduceIte,
    ← _root_.pow_mul, _root_.Nat.mul_comm]

include hg in

theorem radical_mask_absorbs (p : κ → O) (B : Finset κ) (v : κ → ℕ) :
    primeCoprimeMask q S (cubeRadical p B) * primeCoprimeMask q S (primeProduct p B v) =
      primeCoprimeMask q S (cubeRadical p B) := by
  simp only [cubeRadical, primeProduct, mask_prod q hg S, mask_pow q hg S,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro j hj
  rw [primeCoprimeMask_indicator]
  split <;> simp

theorem masked_dual_dilation (p : κ → O) (B : Finset κ) (v : κ → ℕ) (z : O) (c : ℂ) :
    primeCoprimeMask q S (cubeRadical p B) * c * star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S z) =
      (primeCoprimeMask q S (cubeRadical p B) * c *
        primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (primeProduct p B v)) *
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (z * primeProduct p B v)) := by
  rw [SecondPassArithmetic.subsetRow_mul, star_mul]
  calc
    _ = (primeCoprimeMask q S (cubeRadical p B) *
        primeCoprimeMask q S (primeProduct p B v)) * c *
        star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S z) := by rw [radical_mask_absorbs q hg S]
    _ = _ := by rw [← primeSubsetRow_diagonal q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (primeProduct p B v)]; ring

theorem first_pass_after_dual_dilation
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (primeCoprimeMask q S (cubeRadical p B) *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side)) *
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S z) =
    (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (jLabel p B v ε₁ ε₂) ^ 4 *
      primeCoprimeMask q S (b0Label p B v ε₁ ε₂)) *
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (z * dilationLabel p B v ε₁ ε₂)) := by
  have hd := masked_dual_dilation q hg S p B
    (fun j => dilationExponent (parity (v j)) (ε₁ j) (ε₂ j)) z
    (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side))
  change _ = (_ * primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (dilationLabel p B v ε₁ ε₂)) * _ at hd
  simp only [← mul_assoc] at hd
  rw [first_pass_label_identity q hg S p B v ε₁ ε₂ hv side] at hd
  exact hd


end

theorem mobius_column_after_dual_dilation
    {ι κ : Type*} [DecidableEq ι] (q : ι → O) [∀ i, (Ideal.span {q i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {q i}) (columns : Finset ι) (C : Finset ι → ℂ)
    (p : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (z : O) :
    (∑ S ∈ columns.powerset, SecondPassArithmetic.supportMobius S * C S *
      ((primeCoprimeMask q S (cubeRadical p B) *
        primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side)) *
        star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S z))) =
    SecondPassArithmetic.supportConjugateSum q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) columns
      (fun S => C S * primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (jLabel p B v ε₁ ε₂) ^ 4 *
        primeCoprimeMask q S (b0Label p B v ε₁ ε₂))
      (z * dilationLabel p B v ε₁ ε₂) := by
  unfold SecondPassArithmetic.supportConjugateSum
  apply Finset.sum_congr rfl
  intro S hS
  rw [first_pass_after_dual_dilation q hg S p B v ε₁ ε₂ hv side z]
  ring

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

/-- Units reconcile chosen ideal generators with the products used in Poisson summation. -/
def subsetProductUnit {ι : Type*} (p : ι → O) (S : Finset ι) : Oˣ :=
  Classical.choose (exists_label_unit (∏ i ∈ S, p i) (∏ i ∈ S, Ideal.span {p i})
    (span_finset_prime_product p S))

lemma subsetProductUnit_spec {ι : Type*} (p : ι → O) (S : Finset ι) :
    (∏ i ∈ S, p i) = (subsetProductUnit p S : O) *
      cubicIdealGenerator (∏ i ∈ S, Ideal.span {p i}) :=
  Classical.choose_spec (exists_label_unit (∏ i ∈ S, p i) (∏ i ∈ S, Ideal.span {p i})
    (span_finset_prime_product p S))

lemma subsetProductUnit_row {ι : Type*} (p : ι → O) (D E : Finset ι) (k : O) :
    cubicIdealGenerator (∏ i ∈ D, Ideal.span {p i}) *
      cubicIdealGenerator (∏ i ∈ E, Ideal.span {p i}) *
      ((subsetProductUnit p D : O) * (subsetProductUnit p E : O) * k) =
      (∏ i ∈ D, p i) * (∏ i ∈ E, p i) * k := by
  rw [subsetProductUnit_spec p D, subsetProductUnit_spec p E]
  ring

lemma span_dvd_of_element_dvd {a b : O} (h : a ∣ b) :
    (Ideal.span {a} : Ideal O) ∣ Ideal.span {b} := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Ideal.span {c}, (Ideal.span_singleton_mul_span_singleton a c).symm⟩

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma primeProduct_add (B : Finset ι) (u v : ι → ℕ) :
    primeProduct p B (fun i => u i + v i) = primeProduct p B u * primeProduct p B v := by
  simp only [primeProduct, pow_add, Finset.prod_mul_distrib]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma aLabel_dvd_primeProduct (B : Finset ι) (v : ι → ℕ) (ε : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : aLabel p B ε ∣ primeProduct p B v := by
  unfold aLabel primeProduct
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  cases h : ε i <;> simp only [bit, h, Bool.false_eq_true, ite_false, ite_true]
  · exact Nat.zero_le _
  · exact hv i hi

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cubeRadical_dvd_jLabel_b0 (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v i) : cubeRadical p B ∣ jLabel p B v ε₁ ε₂ * b0Label p B v ε₁ ε₂ := by
  have hle (i : ι) (hi : i ∈ B) :
      1 ≤ bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i) := by
    cases h : retained (parity (v i)) (ε₁ i) (ε₂ i)
    · have hp := FirstPassCubeLabels.b0Exponent_pos_of_not_retained (v i) (ε₁ i) (ε₂ i) (hv i hi) h
      simp only [bit,  Bool.false_eq_true, ite_false, zero_add]
      omega
    · simp only [bit,  ite_true]
      omega
  have hd := Finset.prod_dvd_prod_of_dvd (s := B) (fun i => p i ^ 1)
    (fun i => p i ^ (bit (retained (parity (v i)) (ε₁ i) (ε₂ i)) + b0Exponent (v i) (ε₁ i) (ε₂ i)))
    (fun i hi => pow_dvd_pow (p i) (hle i hi))
  simpa only [cubeRadical, jLabel, b0Label, primeProduct, pow_one, pow_add,
    Finset.prod_mul_distrib] using hd

def actualSecondTuple (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (k : O) : SecondPassFiber.OldTuple where
  core := ![Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂},
    ∏ i ∈ C, Ideal.span {p i}, ∏ i ∈ E, Ideal.span {p i},
    Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)},
    Ideal.span {primeProduct p B v₁}, Ideal.span {aLabel p B ε₁},
    Ideal.span {aLabel p B ε₂}, ∏ i ∈ D, Ideal.span {p i}]
  v := ∏ i ∈ V, Ideal.span {p i}
  j2 := Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
  b2 := Ideal.span {primeProduct p B v₂}
  row := (subsetProductUnit p D : O) * (subsetProductUnit p E : O) * k

def actualSecondLabel (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Ideal O :=
  Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂} *
    (∏ i ∈ C, Ideal.span {p i}) * (∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i})

def actualSecondRow (D E : Finset ι) (k : O) : O :=
  (∏ i ∈ D, p i) *
    (∏ i ∈ E, p i) * k

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actualSecondTuple_valid
    (B C D E V : Finset ι) (hCB : Disjoint C B) (hD : D ⊆ C ∪ B)
    (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ i ∈ B, 0 < v₁ i + v₂ i) (k : O) :
    SecondPassFiber.Valid (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k)
      (actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂)
      (Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂})
      (actualSecondRow p D E k) := by
  have hJ := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2 p B (fun i => v₁ i + v₂ i) ε₁ ε₂)
  have hb := congrArg (fun a : O => (Ideal.span {a} : Ideal O))
    (FirstPassCubeLabels.cube_product_decomposition p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [primeProduct_add] at hb
  have hA₁ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₁ hv)
  have hA₂ := span_dvd_of_element_dvd (aLabel_dvd_primeProduct p B (fun i => v₁ i + v₂ i) ε₂ hv)
  rw [primeProduct_add, ← Ideal.span_singleton_mul_span_singleton] at hA₁ hA₂
  have hrad := span_dvd_of_element_dvd (cubeRadical_dvd_jLabel_b0 p B (fun i => v₁ i + v₂ i) ε₁ ε₂ hv)
  rw [← Ideal.span_singleton_mul_span_singleton] at hrad
  have hD' : (∏ i ∈ D, Ideal.span {p i}) ∣
      (∏ i ∈ C, Ideal.span {p i}) * Ideal.span {cubeRadical p B} := by
    have hh := Finset.prod_dvd_prod_of_subset D (C ∪ B) (fun i => (Ideal.span {p i} : Ideal O)) hD
    rw [Finset.prod_union hCB] at hh
    simpa only [cubeRadical, span_finset_prime_product] using hh
  have hD'' := hD'.trans (mul_dvd_mul_left (∏ i ∈ C, (Ideal.span {p i} : Ideal O)) hrad)
  constructor
  · rfl
  · change Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)} *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} =
          Ideal.span {jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂}
    simpa only [← Ideal.span_singleton_mul_span_singleton] using hJ.symm
  · change Ideal.span {primeProduct p B v₁} * Ideal.span {primeProduct p B v₂} =
        Ideal.span {b0Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {j2Label p B (fun i => v₁ i + v₂ i) ε₁ ε₂} ^ 2 *
        Ideal.span {squarefreeLabel p B (fun i => v₁ i + v₂ i)}
    simpa only [pow_two, ← Ideal.span_singleton_mul_span_singleton] using hb
  · exact hA₁
  · exact hA₂
  · apply hD''.trans
    refine ⟨(∏ i ∈ E, Ideal.span {p i}) * (∏ i ∈ V, Ideal.span {p i}), ?_⟩
    simp only [actualSecondLabel]
    ring
  · exact subsetProductUnit_row p D E k

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actualSecondTuple_newLabel
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newLabel (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := rfl

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actualSecondTuple_newRow
    (B C D E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) (k : O) :
    SecondPassFiber.newRow (actualSecondTuple p B C D E V v₁ v₂ ε₁ ε₂ k) =
      actualSecondRow p D E k := subsetProductUnit_row p D E k

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem actualSecondLabel_span
    (B C E V : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    Ideal.span {(∏ i ∈ C, p i) *
      jLabel p B (fun i => v₁ i + v₂ i) ε₁ ε₂ *
      (∏ i ∈ E, p i) * (∏ i ∈ V, p i)} =
      actualSecondLabel p B C E V v₁ v₂ ε₁ ε₂ := by
  simp only [actualSecondLabel, ← Ideal.span_singleton_mul_span_singleton,
    span_finset_prime_product]
  ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein
open scoped Classical

/-- Primes where the two cube columns leave a nontrivial conductor. -/
def cubeActiveSupport {ι : Type*} (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) : Finset ι :=
  B.filter (fun i => conductorExponent (parity (v i)) (ε₁ i) (ε₂ i) ≠ 0)

end FirstPassCubeLabels

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels
open scoped Classical

lemma element_norm_ge_one (a : O) (ha : a ≠ 0) : 1 ≤ ‖ringComplex a‖ ^ 2 := by
  rw [ringComplex_norm_sq_eq_absNorm_span]
  exact_mod_cast Nat.one_le_iff_ne_zero.mpr (show Ideal.absNorm (Ideal.span {a}) ≠ 0 by
    rw [ne_eq, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact ha)

theorem primeProductNorm_eq_ideal_norm {ι : Type*} (p : ι → O) (S : Finset ι) :
    primeProductNorm p S = (Ideal.absNorm (∏ i ∈ S, Ideal.span {p i}) : ℝ) := by
  rw [primeProductNorm, ringComplex_norm_sq_eq_absNorm_span, span_finset_prime_product]

theorem primeProductNorm_ge_one {ι : Type*} (p : ι → O) (hp : ∀ i, p i ≠ 0) (S : Finset ι) :
    1 ≤ primeProductNorm p S :=
  element_norm_ge_one _ (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))

theorem primeProductNorm_mono {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) {S T : Finset ι} (hST : S ⊆ T) :
    primeProductNorm p S ≤ primeProductNorm p T := by
  have hd : Disjoint S (T \ S) := Finset.disjoint_sdiff
  have hu : S ∪ (T \ S) = T := Finset.union_sdiff_of_subset hST
  rw [← hu, primeProductNorm_union p S (T \ S) hd]
  exact le_mul_of_one_le_right (primeProductNorm_pos p hp S).le (primeProductNorm_ge_one p hp _)

lemma element_norm_le_of_dvd {a b : O} (hb : b ≠ 0) (h : a ∣ b) :
    ‖ringComplex a‖^2 ≤ ‖ringComplex b‖^2 := by
  obtain ⟨c,rfl⟩ := h
  have hc : c ≠ 0 := (mul_ne_zero_iff.mp hb).2
  rw [map_mul, norm_mul, mul_pow]
  exact le_mul_of_one_le_right (sq_nonneg _) (element_norm_ge_one c hc)

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]

include hp in
omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma primeProduct_ne_zero (B : Finset ι) (v : ι → ℕ) : primeProduct p B v ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr (fun i _hi => pow_ne_zero _ (hp i))

include hp in
omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma squarefreeLabel_active_bound (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖ringComplex (squarefreeLabel p B v)‖^2 ≤ primeProductNorm p (cubeActiveSupport B v ε₁ ε₂) := by
  let S := B.filter (fun i => parity (v i))
  have he : squarefreeLabel p B v = ∏ i ∈ S, p i := by
    unfold squarefreeLabel primeProduct S
    rw [Finset.prod_filter]
    apply Finset.prod_congr rfl
    intro i hi
    cases hb : parity (v i) <;> simp [bit,hb]
  have hsub : S ⊆ cubeActiveSupport B v ε₁ ε₂ := by
    intro i hi
    obtain ⟨hi,hpi⟩ := Finset.mem_filter.mp hi
    apply Finset.mem_filter.mpr
    refine ⟨hi,?_⟩
    change parity (v i) = true at hpi
    rw [hpi]
    cases h1 : ε₁ i <;> cases h2 : ε₂ i <;> decide
  rw [he]
  exact primeProductNorm_mono p hp hsub

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma jLabel_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [← primeProduct_add]
  apply Finset.prod_dvd_prod_of_dvd
  intro i hi
  apply pow_dvd_pow
  dsimp only
  unfold bit
  split <;> have h := hv i hi <;> omega

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma b0_square_dvd_cube_product (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ ^ 2 ∣ primeProduct p B v₁ * primeProduct p B v₂ := by
  rw [FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  exact dvd_mul_of_dvd_left (dvd_mul_right _ _) _

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
lemma b0_jLabel_square (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) :
    (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂ * jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)^2 =
      primeProduct p B v₁ * primeProduct p B v₂ * squarefreeLabel p B (fun i => v₁ i+v₂ i) := by
  rw [FirstPassCubeLabels.jLabel_eq_squarefree_mul_j2,
    FirstPassCubeLabels.cube_pair_product_decomposition p B v₁ v₂ ε₁ ε₂ hv]
  ring

include hp in

omit [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem cube_label_norm_bounds (B : Finset ι) (v₁ v₂ : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (hv : ∀ i ∈ B, 0 < v₁ i+v₂ i) (B₀ : ℝ) (hB : 0 ≤ B₀)
    (hb₁ : ‖ringComplex (primeProduct p B v₁)‖^2 ≤ B₀)
    (hb₂ : ‖ringComplex (primeProduct p B v₂)‖^2 ≤ B₀) :
    let v := fun i => v₁ i+v₂ i
    ‖ringComplex (jLabel p B v ε₁ ε₂)‖^2 ≤ B₀^2 ∧
    ‖ringComplex (b0Label p B v ε₁ ε₂)‖^2 ≤ B₀ ∧
    ‖ringComplex (b0Label p B v ε₁ ε₂)‖^2 ≤
      B₀*‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂,p i)‖ /
        ‖ringComplex (jLabel p B v ε₁ ε₂)‖^2 := by
  dsimp only
  have hbb : ‖ringComplex (primeProduct p B v₁ * primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    rw [map_mul,norm_mul,mul_pow]
    simpa only [pow_two] using mul_le_mul hb₁ hb₂ (sq_nonneg _) hB
  have hbb0 := mul_ne_zero (primeProduct_ne_zero p hp B v₁) (primeProduct_ne_zero p hp B v₂)
  have hJ := (element_norm_le_of_dvd hbb0 (jLabel_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  have hb0sq := (element_norm_le_of_dvd hbb0 (b0_square_dvd_cube_product p B v₁ v₂ ε₁ ε₂ hv)).trans hbb
  simp only [map_pow,norm_pow] at hb0sq
  have hb0 : ‖ringComplex (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 ≤ B₀ := by
    nlinarith only [hb0sq, hB, sq_nonneg ‖ringComplex (b0Label p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖]
  refine ⟨hJ,hb0,?_⟩
  have heq := congrArg (fun a : O => ‖ringComplex a‖^2) (b0_jLabel_square p B v₁ v₂ ε₁ ε₂ hv)
  simp only [map_pow,map_mul,norm_pow,norm_mul,mul_pow] at heq
  have hs := squarefreeLabel_active_bound p hp B (fun i => v₁ i+v₂ i) ε₁ ε₂
  have hNprod : ‖ringComplex (primeProduct p B v₁)‖^2 * ‖ringComplex (primeProduct p B v₂)‖^2 ≤ B₀^2 := by
    simpa only [map_mul,norm_mul,mul_pow] using hbb
  have hmul := mul_le_mul hNprod hs (sq_nonneg _) (sq_nonneg B₀)
  change _ ≤ B₀^2*‖ringComplex (∏ i ∈ cubeActiveSupport B (fun i => v₁ i+v₂ i) ε₁ ε₂,p i)‖^2 at hmul
  have hjpos : 0 < ‖ringComplex (jLabel p B (fun i => v₁ i+v₂ i) ε₁ ε₂)‖^2 := by
    exact zero_lt_one.trans_le (element_norm_ge_one _ (primeProduct_ne_zero p hp B _))
  apply (le_div_iff₀ hjpos).mpr
  apply (sq_le_sq₀ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    (mul_nonneg hB (norm_nonneg _))).mp
  simp only [mul_pow]
  exact heq.trans_le hmul

end SecondPassArithmetic

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
