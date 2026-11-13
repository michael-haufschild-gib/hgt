/-
First core ray attachment adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialRayAttachment

/-!
# First core ray attachment

First core indices, twists and mass bounds (`InverseFirstRayAttachment`). The quadratic cross
phase separates into two multiplicative characters, and the exact Gauss product into a unit
phase and the normalized bracket (`NormalizedReflection`).
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

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic
open RayFourExpansion InverseInitialRayAttachment
open scoped BigOperators Classical
noncomputable section

def supportRay {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) : ℂ :=
  rayMonoid χ (∏ i ∈ S,p i)

def gCoeff : RayCharacter → ℂ := phaseCoeff (fun r => star (initialTracePhase r))

def crossCoeff (χ η : RayCharacter) : ℂ :=
  phaseCoeff (fun s => phaseCoeff (fun r => rayQuadraticPair r s) χ) η

/-- The quadratic cross phase separates into two multiplicative characters. -/
theorem cross_phase_expansion (x y : O)
    (hx : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x))
    (hy : IsUnit (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y)) :
    rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) x)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y) =
      ∑ χ : RayCharacter, ∑ η : RayCharacter,
        crossCoeff χ η * rayMonoid χ x * rayMonoid η y := by
  have h₁ := phase_expansion
    (fun r => rayQuadraticPair r (Ideal.Quotient.mk (Ideal.span {(4 : O)}) y)) x
  rw [if_pos hx,one_mul] at h₁
  rw [h₁]
  apply Finset.sum_congr rfl
  intro χ hχ
  have h₂ := phase_expansion (fun s => phaseCoeff (fun r => rayQuadraticPair r s) χ) y
  rw [if_pos hy,one_mul] at h₂
  rw [h₂,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro η hη
  unfold crossCoeff
  ring

theorem fixedRayExpansion_eq_characters {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) (F S : Finset ι) :
    fixedRayExpansion p F S = ∑ χ : RayCharacter, ∑ η : RayCharacter,
      crossCoeff χ η * supportRay p χ S * supportRay p η F :=
  cross_phase_expansion _ _ (prime_product_unit_mod_four p hc S) (prime_product_unit_mod_four p hc F)

theorem supportRay_star {ι : Type*} (p : ι → O) (χ : RayCharacter) (S : Finset ι) :
    supportRay p (star χ) S = star (supportRay p χ S) := by
  simp only [supportRay, rayMonoid_apply, MulChar.star_apply]

theorem supportRay_mul {ι : Type*} (p : ι → O) (χ η : RayCharacter) (S : Finset ι) :
    supportRay p (χ * η) S = supportRay p χ S * supportRay p η S := by
  simp only [supportRay, rayMonoid_apply, MulChar.mul_apply]

theorem columnG_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (S : Finset ι) :
    firstColumnPhase p hg S = ∑ χ : RayCharacter, gCoeff χ * supportRay p χ S := by
  rw [firstColumnPhase, subsetTraceRayFactor_eq_phase p hg hc hpr]
  simpa only [if_pos (prime_product_unit_mod_four p hc S),one_mul,gCoeff,supportRay]
    using phase_expansion (fun r => star (initialTracePhase r)) (∏ i ∈ S,p i)

def coreRayCharacter (negative : Bool) (χ ξ : RayCharacter) : RayCharacter :=
  (if negative then star χ else χ) * ξ

def coreRayCoefficient {ι : Type*} (p : ι → O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) : ℂ :=
  (if negative then star (crossCoeff χ η * supportRay p η F)
    else crossCoeff χ η * supportRay p η F) * gCoeff ξ

theorem core_phase_ray_expansion {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F S : Finset ι) (negative : Bool) :
    (if negative then star (fixedRayExpansion p F S) else fixedRayExpansion p F S) *
        firstColumnPhase p hg S =
      ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        coreRayCoefficient p F negative χ η ξ * supportRay p (coreRayCharacter negative χ ξ) S := by
  rw [columnG_ray_expansion p hg hc hpr S, fixedRayExpansion_eq_characters p hc F S]
  cases negative <;> simp only [Bool.false_eq_true,  ite_false, ite_true,
    star_sum, star_mul, Finset.sum_mul, Finset.mul_sum,
    coreRayCoefficient, coreRayCharacter, supportRay_mul, supportRay_star]
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring
  · conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro χ _
    conv_lhs => rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro η _
    apply Finset.sum_congr rfl
    intro ξ _
    ring

theorem coreRayCoefficient_norm_le {ι : Type*} (p : ι → O) (F : Finset ι) (negative : Bool)
    (χ η ξ : RayCharacter) :
    ‖coreRayCoefficient p F negative χ η ξ‖ ≤ ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
  have hη : ‖supportRay p η F‖ ≤ 1 := rayMonoid_norm_le η _
  have hmul : ‖crossCoeff χ η‖ * ‖supportRay p η F‖ ≤ ‖crossCoeff χ η‖ :=
    mul_le_of_le_one_right (norm_nonneg _) hη
  cases negative <;> simp only [coreRayCoefficient, Bool.false_eq_true,
    ite_false, ite_true, norm_mul, norm_star]
  all_goals exact mul_le_mul_of_nonneg_right hmul (norm_nonneg _)

def firstCoreMassBound : ℝ :=
  (∑ χ : RayCharacter, ∑ η : RayCharacter, ‖crossCoeff χ η‖) *
    (∑ ξ : RayCharacter, ‖gCoeff ξ‖)

theorem firstCoreMassBound_nonneg : 0 ≤ firstCoreMassBound := by
  unfold firstCoreMassBound
  positivity

theorem coreRayCoefficient_mass {ι : Type*} (p : ι → O) (F : Finset ι) (negative : Bool) :
    (∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
      ‖coreRayCoefficient p F negative χ η ξ‖) ≤ firstCoreMassBound := by
  calc
    _ ≤ ∑ χ : RayCharacter, ∑ η : RayCharacter, ∑ ξ : RayCharacter,
        ‖crossCoeff χ η‖ * ‖gCoeff ξ‖ := by
      gcongr with χ _ η _ ξ _
      exact coreRayCoefficient_norm_le p F negative χ η ξ
    _ = _ := by simp only [firstCoreMassBound, ← Finset.mul_sum, ← Finset.sum_mul]

def coreRayTwist (negative : Bool) (χ ξ : RayCharacter) : O →* ℂ where
  toFun a := rayMonoid (coreRayCharacter negative χ ξ) a
  map_one' := by simp [rayMonoid]
  map_mul' a b := map_mul (rayMonoid _) a b

@[simp] theorem coreRayTwist_prod {ι : Type*} (p : ι → O)
    (S : Finset ι) (negative : Bool) (χ ξ : RayCharacter) :
    coreRayTwist negative χ ξ (∏ i ∈ S, p i) =
      supportRay p (coreRayCharacter negative χ ξ) S := rfl

@[simp] theorem twisted_core_product {ι : Type*} (p : ι → O)
    (S : Finset ι) (Ψ : O →* ℂ) (negative : Bool) (χ ξ : RayCharacter) :
    (Ψ * coreRayTwist negative χ ξ) (∏ i ∈ S, p i) =
      Ψ (∏ i ∈ S, p i) * supportRay p (coreRayCharacter negative χ ξ) S := rfl

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open scoped BigOperators Classical
noncomputable section

/-- Removing common primes converts disjoint pairs into products of finite rows. -/
theorem coprime_pair_sum_reindexed {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
      supportPairTerm p χ C₁ C₂ h S T else 0) =
    ∑ D ∈ B.powerset, (supportMobius D * primeCoprimeMask p D h) *
      star (supportConjugateSum p χ (B \ D) (fun U => C₁ (D ∪ U)) h) *
      supportConjugateSum p χ (B \ D) (fun U => C₂ (D ∪ U)) h := by
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  apply Finset.sum_congr rfl
  intro D hD
  have he : (∑ S ∈ (B \ D).powerset, ∑ T ∈ (B \ D).powerset,
      supportPairTerm p χ C₁ C₂ h (D ∪ S) (D ∪ T)) =
      primeCoprimeMask p D h *
        (∑ S ∈ (B \ D).powerset, ∑ T ∈ (B \ D).powerset,
          supportPairTerm p χ (fun U => C₁ (D ∪ U)) (fun U => C₂ (D ∪ U)) h S T) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    exact supportPairTerm_union p χ C₁ C₂ h D S T
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right)
      (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right)
  rw [he, supportPairTerm_sum]
  simp only [supportMobius]
  ring

theorem supportRay_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (χ : RayCharacter) (S T : Finset ι) (hd : Disjoint S T) :
    supportRay p χ (S ∪ T) = supportRay p χ S * supportRay p χ T := by
  rw [supportRay, Finset.prod_union hd, map_mul]
  rfl

theorem supportConjugateSum_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
      (fun U => supportRay p χ (D ∪ U) * C (D ∪ U)) h =
    supportRay p χ D * supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
      (fun U => supportRay p χ U * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU]
  ring

theorem supportConjugateSum_star_ray_common
    {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B D : Finset ι)
    (C : Finset ι → ℂ) (χ : RayCharacter) (h : O) :
    supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
      (fun U => star (supportRay p χ (D ∪ U)) * C (D ∪ U)) h =
    star (supportRay p χ D) * supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
      (fun U => star (supportRay p χ U) * C (D ∪ U)) h := by
  rw [supportConjugateSum, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  rw [supportRay_union p χ D U hdU, star_mul]
  ring

theorem quadratic_phase_coprime_ray_reindex
    {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hchar : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
      if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius S * C₁ S * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
          (supportMobius T * C₂ T * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0) =
    ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
      ∑ D ∈ B.powerset,
        (supportMobius D * primeCoprimeMask p D h * supportRay p r.1 D * supportRay p r.2 D) *
        star (supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
          (fun U => star (supportRay p r.1 U) * C₁ (D ∪ U)) h) *
        supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (B \ D)
          (fun V => supportRay p r.2 V * C₂ (D ∪ V)) h := by
  let Z (r : RayCharacter × RayCharacter) (S T : Finset ι) : ℂ :=
    if Disjoint S T then
      star (supportMobius S * (star (supportRay p r.1 S) * C₁ S) *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
      (supportMobius T * (supportRay p r.2 T * C₂ T) *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0
  have ht (S T : Finset ι) :
      (if Disjoint S T then quadraticCrossPhase p hg S T *
        star (supportMobius S * C₁ S * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
          (supportMobius T * C₂ T * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0) =
      ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
    by_cases hd : Disjoint S T
    · rw [if_pos hd, quadraticCrossPhase_eq_ray p hp hinj hg hchar S T hd, cross_phase_expansion _ _ (prime_product_unit_mod_four p hchar S) (prime_product_unit_mod_four p hchar T)]
      simp only [Fintype.sum_prod_type, Z, if_pos hd, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro χ hχ
      apply Finset.sum_congr rfl
      intro η hη
      simp only [supportRay, star_mul, star_star]
      ring
    · simp [Z, hd]
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 * Z r S T := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => ht S T)
    _ = ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, Z r S T := by
      simp only [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ r : RayCharacter × RayCharacter,
            ∑ T ∈ B.powerset, crossCoeff r.1 r.2 * Z r S T := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro r hr
      congr 1
      change (∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
        if Disjoint S T then star (supportMobius S *
          (star (supportRay p r.1 S) * C₁ S) * star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S h)) *
          (supportMobius T * (supportRay p r.2 T * C₂ T) *
            star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T h)) else 0) = _
      change (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then
        supportPairTerm p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          (fun S => star (supportRay p r.1 S)*C₁ S) (fun S => supportRay p r.2 S*C₂ S) h S T else 0) = _
      rw [coprime_pair_sum_reindexed p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) B]
      apply Finset.sum_congr rfl
      intro D hD
      rw [supportConjugateSum_star_ray_common p hg B D C₁ r.1 h,
        supportConjugateSum_ray_common p hg B D C₂ r.2 h]
      simp only [star_mul, star_star]
      ring

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open scoped BigOperators Classical SchwartzMap
noncomputable section
def rayIdealRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U)*C (D ∪ U)) h

def idealPairReindex {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset,
      (supportMobius D * primeCoprimeMask p D h * supportRay p r.1 D * supportRay p r.2 D) *
      star (rayIdealRow p hg F C₁ true r.1 D h) * rayIdealRow p hg F C₂ false r.2 D h

theorem rayIdealRow_eq_supportRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter) (h : O) :
    rayIdealRow p hg F C negative χ D h =
    supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
      (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) h := rfl

def dilatedRayColumn {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
    (fun U => (if negative then star (supportRay p χ U) else supportRay p χ U) *
      C (D ∪ U) * afterDilationLabel p hg q B v ε₁ ε₂ c d U) y

theorem rayIdealRow_beforeDilation {ι κ : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D : Finset ι)
    (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    rayIdealRow p hg F
      (fun S => C S * beforeDilationLabel p hg q B v ε₁ ε₂ side c d f S)
      negative χ D h =
    beforeDilationLabel p hg q B v ε₁ ε₂ side c d f D *
      dilatedRayColumn p hg F D C negative χ q B v ε₁ ε₂ c d
        (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  rw [rayIdealRow_eq_supportRow p hinj]
  unfold dilatedRayColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := by
    exact Finset.disjoint_left.mpr (fun i hiD hiU =>
      (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hiU)).2 hiD)
  dsimp only
  rw [beforeDilationLabel_union p hg q B v ε₁ ε₂ side c d f D U hd]
  calc
    _ = beforeDilationLabel p hg q B v ε₁ ε₂ side c d f D *
      supportMobius U *
      ((if negative then star (supportRay p χ U) else supportRay p χ U) * C (D ∪ U)) *
      (beforeDilationLabel p hg q B v ε₁ ε₂ side c d f U *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) := by ring
    _ = _ := by
      rw [beforeDilationLabel_star_row p hg q B v ε₁ ε₂ hv side c d f h U]
      ring
theorem rayIdealRow_cube_labels {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    rayIdealRow p hg F
      (cubeLogCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) negative χ D h =
    beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
      dilatedRayColumn p hg F D (cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t)
        negative χ p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
    fun S => cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact rayIdealRow_beforeDilation p hinj hg F D _ negative χ p B v ε₁ ε₂ hv negative c d f h

def dilatedCoreRow {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) : ℂ :=
  dilatedRayColumn p hg F D (cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t)
    negative χ p B v ε₁ ε₂ c d z

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open scoped BigOperators Classical SchwartzMap
noncomputable section
abbrev FirstCoreIndex := RayCharacter × (RayCharacter × RayCharacter)

def sideRayMonoid (negative : Bool) (χ : RayCharacter) : O →* ℂ :=
  if negative then rayMonoid (star χ) else rayMonoid χ

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCoreOuter (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) : ℂ :=
  coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
    (Ψ * coreRayTwist negative r.1 r.2.2) (∏ i ∈ D, p i) *
    primeCoprimeMask p D m *
    (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D (-1)) else 1)

def firstCoreTwist (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) : O →* ℂ :=
  sideRayMonoid negative χ * (Ψ * coreRayTwist negative r.1 r.2.2)

include hp hcop in
theorem cubeCoreCoefficient_ray_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) :
    cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S =
      ∑ r : FirstCoreIndex,
        coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2 *
          supportRay p (coreRayCharacter negative r.1 r.2.2) S * C S *
          (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)) else 1) *
          (if negative then star (V (y S) * kernelLogPhase t (-(y S))) else V (y S) * kernelLogPhase t (-(y S))) := by
  have hphase := core_phase_ray_expansion p hp hcop hg hc hpr
    (cubeOddSupport B v ε₁ ε₂) S negative
  have he : cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S =
      ((if negative then star (FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S)
          else FirstPassCubeLabels.fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
        firstColumnPhase p hg S) * C S *
          (if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)) else 1) *
          (if negative then star (V (y S) * kernelLogPhase t (-(y S))) else V (y S) * kernelLogPhase t (-(y S))) := by
    cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true] <;> ring
  rw [he, hphase]
  simp only [Fintype.sum_prod_type, Finset.sum_mul]

include hp hcop in
theorem dilatedCoreRow_eq_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) :
    dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z =
    ∑ r : FirstCoreIndex, firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z) := by
  unfold dilatedCoreRow dilatedRayColumn supportConjugateSum
  simp_rw [cubeCoreCoefficient_ray_family p hp hcop hg hc hpr]
  simp only [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [inputConjugateRow, supportConjugateSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hDU : Disjoint D U := Finset.disjoint_left.mpr (fun i hi hu =>
    (Finset.mem_sdiff.mp ((Finset.mem_powerset.mp hU) hu)).2 hi)
  have hz : primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-z) =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-1) *
        primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U z := by
    simpa only [neg_one_mul] using subsetRow_mul p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (-1) z
  cases negative <;>
    simp only [multiplicativeCoreColumn, firstCoreOuter, firstCoreTwist, sideRayMonoid,
      firstCoreTest, secondInputCoefficient, afterDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      Finset.prod_union hDU, map_mul, FirstPassCubeLabels.mask_union p hg D U hDU,
      primeSubsetRow_union p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D U hDU, FirstPassCubeLabels.mask_mul p hg U,
      coreRayTwist_prod, MonoidHom.mul_apply, MulChar.mul_apply, MulChar.star_apply, rayMonoid_apply,
      supportRay, coreRayCharacter, map_mul, hz, star_mul, mul_one] <;> ring

def firstCoreInputRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (z : O) : ℂ :=
  inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open scoped BigOperators Classical
noncomputable section
theorem sum_threeGaussRowFactor_eq_ideal_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (R B : Finset ι) (hRB : Disjoint R B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      idealPairReindex p hg R
        (cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d)
        (cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d) h := by
  let A := cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d
  let C := cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d
  have hsum :
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      (∑ N ∈ R.powerset, ∑ P ∈ R.powerset, if Disjoint N P then
        quadraticCrossPhase p hg N P *
          star (supportMobius N * A N *
            star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N h)) *
          (supportMobius P * C P *
            star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) P h)) else 0) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro N hN
    apply Finset.sum_congr rfl
    intro P hP
    by_cases hd : Disjoint N P
    · rw [if_pos hd, if_pos hd,
        threeGaussRowFactor_eq_ray_columns p hp hinj hcop hg hc hpr N P B hd
          (hRB.mono_left (Finset.mem_powerset.mp hN))
          (hRB.mono_left (Finset.mem_powerset.mp hP))]
      rw [←quadraticCrossPhase_eq_ray p hp hinj hg hc N P hd]
      dsimp only [A, C, supportPairTerm]
      ring
    · simp [hd]
  rw [hsum]
  congr 1
  exact quadratic_phase_coprime_ray_reindex p hp hinj hg hc R A C h

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open scoped BigOperators Classical
noncomputable section
def rayPairWeight {ι : Type*} (p : ι → O)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) : ℂ :=
  crossCoeff r.1 r.2 * (supportMobius D *
    primeCoprimeMask p D h * supportRay p r.1 D * supportRay p r.2 D)

def rayIdealEnergy {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖rayPairWeight p r D h‖ *
      ‖rayIdealRow p hg F C negative (if negative then r.1 else r.2) D h‖ ^ 2

theorem rayIdealEnergy_nonneg {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (h : O) :
    0 ≤ rayIdealEnergy p hg F C negative h := by
  unfold rayIdealEnergy
  positivity

theorem idealPairReindex_eq_ray_rows {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    idealPairReindex p hg F C₁ C₂ h =
    ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h) := by
  simp only [idealPairReindex, rayPairWeight, rayIdealRow, Bool.false_eq_true,
    ite_false, ite_true, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  exact Finset.sum_congr rfl (fun D hD => by ring)

theorem idealPairReindex_norm_le {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    ‖idealPairReindex p hg F C₁ C₂ h‖ ≤
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) *
        Real.sqrt (rayIdealEnergy p hg F C₂ false h) := by
  rw [idealPairReindex_eq_ray_rows]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)
    (fun z => rayPairWeight p z.1 z.2 h)
    (fun z => rayIdealRow p hg F C₂ false z.1.2 z.2 h)
    (fun z => rayIdealRow p hg F C₁ true z.1.1 z.2 h)
  simp only [Finset.sum_product] at hc
  change ‖∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      rayPairWeight p r D h * rayIdealRow p hg F C₂ false r.2 D h *
        star (rayIdealRow p hg F C₁ true r.1 D h)‖ ≤
    Real.sqrt (rayIdealEnergy p hg F C₂ false h) *
      Real.sqrt (rayIdealEnergy p hg F C₁ true h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem norm_rayPairWeight {ι : Type*} [DecidableEq ι] (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : O) :
    ‖rayPairWeight p r D h‖ = ‖crossCoeff r.1 r.2‖ *
      ‖primeCoprimeMask p D h‖ := by
  have hmu : ‖supportMobius D‖ = 1 := supportMobius_norm D
  have hr (χ : RayCharacter) : ‖supportRay p χ D‖ = 1 := by
    obtain ⟨u, hu⟩ := RayFourExpansion.prime_product_unit_mod_four p hc D
    change ‖χ (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i))‖ = 1
    rw [← hu]
    exact FiniteRayExpansion.norm_char_unit χ u
  simp only [rayPairWeight, norm_mul, hmu, hr, one_mul, mul_one]

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion MeasureTheory
open scoped BigOperators Classical SchwartzMap
noncomputable section
lemma sideRayMonoid_norm_le_one (negative : Bool) (χ : RayCharacter) (a : O) :
    ‖sideRayMonoid negative χ a‖ ≤ 1 := by
  cases negative <;> simp only [sideRayMonoid, Bool.false_eq_true, ite_false, ite_true,
    MulChar.star_apply, rayMonoid_apply, norm_star]
  all_goals exact FiniteRayExpansion.norm_char_le_one _ _

lemma firstCoreTwist_norm_le (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ)
    (r : FirstCoreIndex) (a : O) :
    ‖firstCoreTwist negative χ Ψ r a‖ ≤ ‖Ψ a‖ := by
  have hc : ‖coreRayTwist negative r.1 r.2.2 a‖ ≤ 1 := by
    change ‖rayMonoid (coreRayCharacter negative r.1 r.2.2) a‖ ≤ 1
    exact rayMonoid_norm_le (coreRayCharacter negative r.1 r.2.2) a
  simp only [firstCoreTwist, MonoidHom.mul_apply, norm_mul]
  calc
    _ ≤ 1 * (‖Ψ a‖ * 1) := by gcongr; exact sideRayMonoid_norm_le_one _ _ _
    _ = _ := by ring

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

omit [DecidableEq ι] in
theorem firstCoreOuter_norm_le
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι) (r : FirstCoreIndex) :
    ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ ≤
      ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        ‖Ψ (∏ i ∈ D, p i)‖ := by
  have hm : ‖primeCoprimeMask p D m‖ ≤ 1 := primeCoprimeMask_norm_le_one p D m
  have hc : ‖coreRayTwist negative r.1 r.2.2 (∏ i ∈ D, p i)‖ ≤ 1 := by
    change ‖rayMonoid (coreRayCharacter negative r.1 r.2.2) (∏ i ∈ D, p i)‖ ≤ 1
    exact rayMonoid_norm_le (coreRayCharacter negative r.1 r.2.2) (∏ i ∈ D,p i)
  have hs : ‖(if negative then star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D (-1))
      else 1 : ℂ)‖ ≤ 1 := by
    cases negative <;> simp only [Bool.false_eq_true, ite_false, ite_true, norm_one, norm_star]
    · exact le_rfl
    · exact primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) D _
  simp only [firstCoreOuter, norm_mul, MonoidHom.mul_apply]
  calc
    _ ≤ ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ *
        (‖Ψ (∏ i ∈ D, p i)‖ * 1) * 1 * 1 := by gcongr
    _ = _ := by ring

omit [DecidableEq ι] in
theorem firstCoreOuter_mass
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (Ψ : O →* ℂ) (m : O) (D : Finset ι)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    (∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖) ≤ firstCoreMassBound := by
  calc
    _ ≤ ∑ r : FirstCoreIndex,
        ‖coreRayCoefficient p (cubeOddSupport B v ε₁ ε₂) negative r.1 r.2.1 r.2.2‖ := by
      apply Finset.sum_le_sum
      intro r hr
      exact (firstCoreOuter_norm_le p hg B v ε₁ ε₂ negative Ψ m D r).trans
        (mul_le_of_le_one_right (norm_nonneg _) hΨ)
    _ ≤ firstCoreMassBound := by
      simpa only [Fintype.sum_prod_type] using
        coreRayCoefficient_mass p (cubeOddSupport B v ε₁ ε₂) negative

include hp hcop in
theorem dilatedCoreRow_sq_le_input_family
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O)
    (hΨ : ‖Ψ (∏ i ∈ D, p i)‖ ≤ 1) :
    ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) V y c d t z‖ ^ 2 ≤
    (firstCoreMassBound) * ∑ r : FirstCoreIndex, ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      ‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) (if negative then -z else z)‖ ^ 2 := by
  rw [dilatedCoreRow_eq_input_family p hp hcop hg hc hpr]
  let w := firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D
  let Q := fun r : FirstCoreIndex => inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist negative χ Ψ r)
    (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
    (firstCoreTest H V y negative t D) (if negative then -z else z)
  have h := DescentWeightedCauchy.weighted_cauchy_sq Finset.univ w (fun _ => 1) (fun r => star (Q r))
  simp only [mul_one, star_star, norm_one, one_pow, norm_star] at h
  exact h.trans (mul_le_mul_of_nonneg_right
    (firstCoreOuter_mass p hg B v ε₁ ε₂ negative Ψ m D hΨ) (by positivity))

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion MeasureTheory
open scoped BigOperators Classical SchwartzMap
noncomputable section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
theorem firstCoreInputRow_smoothed_sign
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (↑(‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist negative χ Ψ r)
        (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
        (firstCoreTest H V y negative t D) z‖ ^ 2) : ℂ) := by
  cases negative
  · rfl
  · simpa only [firstCoreInputRow, Bool.true_eq, ite_true, Equiv.neg_apply, map_neg, norm_neg] using
      (Equiv.neg O).tsum_eq (fun z : O => W (‖ringComplex z‖ ^ 2 / Y) *
        (↑(‖inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D) (firstCoreTwist true χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y true t D) z‖ ^ 2) : ℂ))

theorem firstCoreInputRow_smoothed_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (W : 𝓢(ℝ, ℂ)) (Y : ℝ) (hY : 0 < Y) :
    (∑' z : O, W (‖ringComplex z‖ ^ 2 / Y) *
      (↑(‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) : ℂ)) =
    ∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
      if Disjoint U V' then
        overlapPairWeight p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (firstCoreTwist negative χ Ψ r)
          (m * b0Label p B v ε₁ ε₂) (c * jLabel p B v ε₁ ε₂) d
          (firstCoreTest H V y negative t D) G U V' *
          maskedSecondDual p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp G U V' W Y
      else 0 := by
  rw [firstCoreInputRow_smoothed_sign]
  exact inputConjugateRow_smoothed_second_poisson p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp hinj (fun i => complexSexticChar_ne_one _ (hg i)) (F \ D)
    (firstCoreTwist negative χ Ψ r) (m * b0Label p B v ε₁ ε₂)
    (c * jLabel p B v ε₁ ε₂) d (firstCoreTest H V y negative t D) W Y hY

end
end InverseFirstRayAttachment

namespace InverseFirstRayAttachment
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion MeasureTheory
open scoped BigOperators Classical SchwartzMap
noncomputable section
variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
theorem firstCoreInputRow_finite_le_second_poisson
    (hp : ∀ i, p i ≠ 0)
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : O →* ℂ) (m : O)
    (H : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O)
    (r : FirstCoreIndex) (t : ℝ) (T : Finset O) (Y : ℝ) (hY : 0 < Y)
    (hT : ∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) :
    (∑ z ∈ T, ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H V y c d r t z‖ ^ 2) ≤
      (∑ G ∈ (F \ D).powerset, ∑ U ∈ ((F \ D) \ G).powerset, ∑ V' ∈ ((F \ D) \ G).powerset,
        if Disjoint U V' then
          overlapPairWeight p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (firstCoreTwist negative χ Ψ r)
            (m * FirstPassCubeLabels.b0Label p B v ε₁ ε₂) (c * FirstPassCubeLabels.jLabel p B v ε₁ ε₂) d
            (firstCoreTest H V y negative t D) G U V' *
            maskedSecondDual p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp G U V' rowMajorant Y
        else 0).re := by
  have he := firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
    negative χ Ψ m H V y c d r t rowMajorant Y hY
  rw [← he]
  exact finite_row_energy_le_rowMajorant _ T Y hY hT

end
end InverseFirstRayAttachment

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein
open scoped BigOperators Classical
namespace NormalizedReflection
section
variable {F:Type*} [Field F] [Fintype F]
def tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) : ℂ :=
  (rootCard F : ℂ)⁻¹ * gaussSum (χ ^ j) ψ

def phase (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ) (ε : Fˣ) : ℂ :=
  if j = 4 then tau χ (ψ.mulShift (-1)) 4
  else if j = 0 then -tau χ ψ 2 * (χ ^ 2)⁻¹ ε
  else tau χ (ψ.mulShift (-1)) j * tau χ ψ (j + 2) * (χ ^ (j + 2))⁻¹ ε

theorem norm_tau (χ : MulChar F ℂ) (ψ : AddChar F ℂ) (j : ℕ)
    (hχ : χ^j≠1) (hψ : ψ.IsPrimitive) : ‖tau χ ψ j‖=1 := by
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  have hg : ‖gaussSum (χ^j) ψ‖^2=(Fintype.card F:ℝ) := by
    rw [←Complex.normSq_eq_norm_sq,ArithmeticEffectivityTheory.normSq_gaussSum_eq_card hχ hψ]
  rw [tau,norm_mul,mul_pow,norm_inv,Complex.norm_real,
    Real.norm_of_nonneg (rootCard_pos (F:=F)).le,inv_pow,rootCard_sq,hg]
  have hq : (Fintype.card F:ℝ)≠0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [inv_mul_cancel₀ hq,one_pow]

omit [Fintype F] in
theorem shifted_power_nontrivial (χ : MulChar F ℂ) (h6 : χ ^ 6 = 1)
    (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (j : ℕ) (hj0 : j ≠ 0) (hj6 : j < 6) (hj4 : j ≠ 4) : χ ^ (j + 2) ≠ 1 := by
  by_cases hj : j = 5
  · subst j
    have heq : χ ^ (5 + 2) = χ ^ 1 := by
      rw [show (5 + 2 : ℕ) = 6 + 1 by decide, pow_add, h6, one_mul]
    rw [heq]
    exact hn 1 (by decide) (by decide)
  · exact hn (j + 2) (by omega) (by omega)

theorem phase_norm (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ ^ 6 = 1) (hn : ∀ k : ℕ, k ≠ 0 → k < 6 → χ ^ k ≠ 1)
    (hψ : ψ.IsPrimitive) (j : ℕ) (hj6 : j < 6) (ε : Fˣ) :
    ‖phase χ ψ j ε‖ = 1 := by
  have hψminus : (ψ.mulShift (-1)).IsPrimitive :=
    AddChar.IsPrimitive.of_ne_one (hψ (a := (-1 : F)) (by simp))
  by_cases hj4 : j = 4
  · subst j
    simp only [phase, ↓reduceIte]
    exact norm_tau χ _ 4 (hn 4 (by decide) (by decide)) hψminus
  by_cases hj0 : j = 0
  · subst j
    simp only [phase, if_neg hj4, ↓reduceIte, norm_mul, norm_neg]
    rw [norm_tau χ ψ 2 (hn 2 (by decide) (by decide)) hψ,
      finiteMulChar_unit_norm]
    norm_num
  · simp only [phase, if_neg hj4, if_neg hj0, norm_mul]
    rw [norm_tau χ _ j (hn j hj0 hj6) hψminus,
      norm_tau χ ψ (j + 2) (shifted_power_nontrivial χ h6 hn j hj0 hj6 hj4) hψ,
      finiteMulChar_unit_norm]
    norm_num

/-- The exact Gauss product separates into a unit phase and the normalized bracket. -/
theorem gauss_eq_phase_bracket (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (h6 : χ^6=1) (hn : ∀k:ℕ,k≠0→k<6→χ^k≠1) (hψ : ψ.IsPrimitive)
    (j:ℕ) (hj:j<6) (ε:Fˣ) (x:F) :
    finiteReflectionGauss χ ψ j ((ε:F)*x)=phase χ ψ j ε*bracket χ j x := by
  have hr : (rootCard F:ℂ)≠0 := Complex.ofReal_ne_zero.mpr (rootCard_pos (F:=F)).ne'
  have hq : (Fintype.card F:ℂ)=(rootCard F:ℂ)^2 := by exact_mod_cast (rootCard_sq (F:=F)).symm
  by_cases h4:j=4
  · subst j
    rw [finiteReflectionGauss_fourth_indicator χ ψ h6 hψ]
    simp only [phase,bracket,if_pos rfl,tau,mul_eq_zero,ε.ne_zero,false_or]
    rw [hq]
    split_ifs <;> field_simp [hr] <;> ring
  by_cases h0:j=0
  · subst j
    have hnext : χ^(0+2)≠1 := hn 2 (by decide) (by decide)
    rw [finiteReflectionGauss_nonexceptional χ ψ 0 hnext]
    simp only [phase,bracket,if_neg h4,if_pos rfl,tau,zero_add,pow_zero,map_mul,↓reduceIte]
    rw [gaussSum_one_left (hψ (neg_ne_zero.mpr one_ne_zero)),hq]
    field_simp [hr] <;> ring
  · rw [finiteReflectionGauss_nonexceptional χ ψ j
      (shifted_power_nontrivial χ h6 hn j h0 hj h4)]
    simp only [phase,bracket,if_neg h4,if_neg h0,tau,map_mul]
    rw [hq]
    field_simp [hr] <;> ring

end

theorem canonical_phase_norm (P:Ideal Eisenstein.O) [P.IsMaximal]
    (hg:Eisenstein.lambda∉P) (hchar:ringChar (Eisenstein.O⧸P)≠2)
    (ψ:AddChar (Eisenstein.O⧸P) ℂ) (hψ:ψ.IsPrimitive)
    (j:ℕ) (hj:j<6) (ε:(Eisenstein.O⧸P)ˣ) :
    ‖phase (complexSexticChar P hg) ψ j ε‖=1 :=
  phase_norm _ _ (complexSexticChar_powers P hg).2.2
    (fun k hk0 hk => complexSexticChar_pow_ne_one P hg hchar k hk hk0) hψ j hj ε

theorem canonical_gauss_eq_phase_bracket (P:Ideal Eisenstein.O) [P.IsMaximal]
    (hg:Eisenstein.lambda∉P) (hchar:ringChar (Eisenstein.O⧸P)≠2)
    (ψ:AddChar (Eisenstein.O⧸P) ℂ) (hψ:ψ.IsPrimitive)
    (j:ℕ) (hj:j<6) (ε:(Eisenstein.O⧸P)ˣ) (x:Eisenstein.O⧸P) :
    finiteReflectionGauss (complexSexticChar P hg) ψ j ((ε:Eisenstein.O⧸P)*x)=
      phase (complexSexticChar P hg) ψ j ε*bracket (complexSexticChar P hg) j x :=
  gauss_eq_phase_bracket _ _ (complexSexticChar_powers P hg).2.2
    (fun k hk0 hk => complexSexticChar_pow_ne_one P hg hchar k hk hk0) hψ j hj ε x

end NormalizedReflection
end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CubicSieve
open scoped BigOperators Classical
noncomputable section

theorem square_eq_star_of_fourth_eq (z : ℂ) (hz : z ^ 4 = z) : z ^ 2 = star z := by
  by_cases h0 : z = 0
  · simp [h0]
  have h3 : z ^ 3 = 1 := by
    apply mul_right_cancel₀ h0
    simpa only [← pow_succ, one_mul] using hz
  have hn := Complex.norm_eq_one_of_pow_eq_one h3 (by decide : (3 : ℕ) ≠ 0)
  change z ^ 2 = (starRingEnd ℂ) z
  rw [← Complex.inv_eq_conj hn]
  apply mul_right_cancel₀ h0
  rw [inv_mul_cancel₀ h0]
  simpa only [← pow_succ] using h3

variable {R : Type*} [CommRing R] [Finite Rˣ]

omit [Finite Rˣ] in
theorem cubic_inv_eq_square (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) :
    χ⁻¹ = χ ^ 2 := by
  calc
    χ⁻¹ = χ⁻¹ * χ ^ 3 := by rw [hχ, mul_one]
    _ = χ ^ 2 := by group

theorem cubic_square_eq_star (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 2 = star (χ x) := by
  rw [MulChar.star_apply', cubic_inv_eq_square χ hχ, MulChar.pow_apply' _ (by decide)]

omit [Finite Rˣ] in
theorem cubic_fourth_eq (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ x ^ 4 = χ x := by
  have h : χ ^ 4 = χ := by
    rw [show (4 : ℕ) = 3 + 1 by decide, pow_add, hχ, one_mul, pow_one]
  rw [← MulChar.pow_apply' χ (by decide : (4 : ℕ) ≠ 0), h]

omit [Finite Rˣ] in
theorem cubic_cube_eq_mask (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    χ (x ^ 3) = if IsUnit x then 1 else 0 := by
  classical
  rw [map_pow, ← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ]
  by_cases hx : IsUnit x
  · rw [if_pos hx, MulChar.one_apply hx]
  · rw [if_neg hx, MulChar.map_nonunit _ hx]

theorem cubic_row_decomposition (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1)
    (a b c : R) :
    χ (a * b ^ 2 * c ^ 3) =
      χ a * star (χ b) * (if IsUnit c then 1 else 0) := by
  rw [map_mul, map_mul, map_pow, cubic_square_eq_star χ hχ,
    cubic_cube_eq_mask χ hχ]

omit [Finite Rˣ] in
theorem cubic_norm_le_one (χ : MulChar R ℂ) (hχ : χ ^ 3 = 1) (x : R) :
    ‖χ x‖ ≤ 1 := by
  by_cases hx : IsUnit x
  · have hc : χ x ^ 3 = 1 := by
      rw [← MulChar.pow_apply' χ (by decide : (3 : ℕ) ≠ 0), hχ, MulChar.one_apply hx]
    exact (Complex.norm_eq_one_of_pow_eq_one hc (by decide)).le
  · rw [MulChar.map_nonunit _ hx, norm_zero]
    exact zero_le_one

theorem row_decomposition_sum {ι M : Type*} [CommMonoid M]
    (S : Finset ι) (coef : ι → ℂ) (ρ : ι → M →* R)
    (χ : ι → MulChar R ℂ) (hχ : ∀ n ∈ S, χ n ^ 3 = 1)
    (a b c : M) :
    (∑ n ∈ S, coef n * χ n (ρ n (a * b ^ 2 * c ^ 3))) =
      ∑ n ∈ S,
        (coef n * star (χ n (ρ n b)) *
          (if IsUnit (ρ n c) then 1 else 0)) * χ n (ρ n a) := by
  classical
  apply Finset.sum_congr rfl
  intro n hn
  have hmap : ρ n (a * b ^ 2 * c ^ 3) =
      ρ n a * (ρ n b) ^ 2 * (ρ n c) ^ 3 := by simp only [map_mul, map_pow]
  rw [hmap, cubic_row_decomposition (χ n) (hχ n hn)]
  ring

omit [Finite Rˣ] in
theorem extracted_coefficients_energy_le {ι : Type*}
    (S : Finset ι) (coef : ι → ℂ) (χ : ι → MulChar R ℂ)
    (hχ : ∀ n ∈ S, χ n ^ 3 = 1) (b c : ι → R) :
    (∑ n ∈ S, ‖coef n * star (χ n (b n)) *
      (if IsUnit (c n) then (1 : ℂ) else 0)‖ ^ 2) ≤
      ∑ n ∈ S, ‖coef n‖ ^ 2 := by
  classical
  apply Finset.sum_le_sum
  intro n hn
  by_cases hc : IsUnit (c n)
  · simp only [if_pos hc, mul_one, norm_mul, norm_star]
    apply pow_le_pow_left₀ (by positivity)
    exact mul_le_of_le_one_right (norm_nonneg _) (cubic_norm_le_one (χ n) (hχ n hn) _)
  · simp only [if_neg hc, mul_zero, norm_zero, zero_pow (by decide : 2 ≠ 0)]
    exact sq_nonneg _

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion FiniteSieveOperator
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace FiniteSieveOperator
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def conjugateVector (x : EuclideanSpace ℂ n) : EuclideanSpace ℂ n :=
  WithLp.toLp 2 (fun j => star (x j))

omit [Fintype n] [DecidableEq n] in
@[simp] theorem conjugateVector_apply (x : EuclideanSpace ℂ n) (j : n) :
    conjugateVector x j = star (x j) := rfl

omit [DecidableEq n] in
@[simp] theorem norm_conjugateVector (x : EuclideanSpace ℂ n) :
    ‖conjugateVector x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  simp only [EuclideanSpace.norm_sq_eq, conjugateVector_apply, norm_star]

omit [DecidableEq m] in
theorem operator_conjugate_apply (A : Matrix m n ℂ) (x : EuclideanSpace ℂ n) :
    operator (fun i j => star (A i j)) x = conjugateVector (operator A (conjugateVector x)) := by
  ext i
  change (∑ j, star (A i j) * x j) = star (∑ j, A i j * star (x j))
  simp only [star_sum, star_mul, star_star]
  apply Finset.sum_congr rfl
  intro j _
  exact mul_comm _ _

omit [DecidableEq m] in
theorem operator_conjugate_norm_le (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ ≤ ‖operator A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro x
  rw [operator_conjugate_apply, norm_conjugateVector]
  simpa only [norm_conjugateVector] using (operator A).le_opNorm (conjugateVector x)

omit [DecidableEq m] in
theorem operator_conjugate_norm (A : Matrix m n ℂ) :
    ‖operator (fun i j => star (A i j))‖ = ‖operator A‖ := by
  apply le_antisymm (operator_conjugate_norm_le A)
  simpa only [star_star] using operator_conjugate_norm_le (fun i j => star (A i j))

end FiniteSieveOperator
namespace CubicSieve
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
def squaredNorm (A : Matrix m n ℂ) : ℝ := ‖FiniteSieveOperator.operator A‖ ^ 2
theorem squaredNorm_transpose (A : Matrix m n ℂ) :
    squaredNorm A.transpose = squaredNorm A := by
  unfold squaredNorm
  have h := operator_conjugate_norm A.transpose
  change ‖operator A.conjTranspose‖ = ‖operator A.transpose‖ at h
  rw [operator_conjTranspose_norm] at h
  exact congrArg (fun x : ℝ => x ^ 2) h.symm

theorem squaredNorm_reciprocity (A : Matrix m n ℂ) (B : Matrix n m ℂ)
    (hrecip : ∀ i j, A i j = B j i) : squaredNorm A = squaredNorm B := by
  have h : A = B.transpose := by ext i j; exact hrecip i j
  rw [h, squaredNorm_transpose]

omit [DecidableEq m] in
theorem energy_le_squaredNorm (A : Matrix m n ℂ) (c : n → ℂ) :
    (∑ i, ‖∑ j, A i j * c j‖ ^ 2) ≤ squaredNorm A * ∑ j, ‖c j‖ ^ 2 :=
  FiniteSieveOperator.energy_bound A c
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion FiniteSieveOperator
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CubicSieve
open scoped BigOperators
noncomputable section

variable {a b n : Type*} [Fintype a] [Fintype b] [Fintype n]
  [DecidableEq n]

theorem squaredNorm_nonneg (A : Matrix a n ℂ) : 0 ≤ squaredNorm A := sq_nonneg _

theorem masked_energy_le (A : Matrix a n ℂ) (coef phase : n → ℂ)
    (hphase : ∀ j, ‖phase j‖ ≤ 1) :
    (∑ i, ‖∑ j, A i j * (coef j * phase j)‖ ^ 2) ≤
      squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
  apply (energy_le_squaredNorm A (fun j => coef j * phase j)).trans
  apply mul_le_mul_of_nonneg_left _ (squaredNorm_nonneg A)
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mul]
  apply pow_le_pow_left₀ (by positivity)
  exact mul_le_of_le_one_right (norm_nonneg _) (hphase j)

theorem rectangular_block_energy_le
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef mask : n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ j, ‖mask j‖ ≤ 1) :
    (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
      min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  have hleft :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card b : ℝ) * squaredNorm A) * ∑ j, ‖coef j‖ ^ 2 := by
    calc
      _ ≤ ∑ k : b, squaredNorm A * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro k _
        have h := masked_energy_le A coef (fun j => star (B k j) * mask j) (by
          intro j
          rw [norm_mul, norm_star]
          exact (mul_le_mul_of_nonneg_right (hB k j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by simp [mul_assoc]
  have hright :
      (∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask j‖ ^ 2) ≤
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
    rw [Finset.sum_comm]
    calc
      _ ≤ ∑ i : a, squaredNorm (fun k j => star (B k j)) * ∑ j, ‖coef j‖ ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        have h := masked_energy_le (fun k j => star (B k j)) coef
          (fun j => A i j * mask j) (by
            intro j
            rw [norm_mul]
            exact (mul_le_mul_of_nonneg_right (hA i j) (norm_nonneg _)).trans (by simpa using hmask j))
        simpa only [mul_assoc, mul_left_comm, mul_comm] using h
      _ = _ := by
        have hn : squaredNorm (fun k j => star (B k j)) = squaredNorm B := by
          unfold squaredNorm
          rw [operator_conjugate_norm]
        rw [hn]
        simp [mul_assoc]
  rcases le_total ((Fintype.card b : ℝ) * squaredNorm A)
      ((Fintype.card a : ℝ) * squaredNorm B) with h | h
  · rw [min_eq_left h]
    exact hleft
  · rw [min_eq_right h]
    exact hright

theorem cube_family_block_energy_le {c : Type*} [Fintype c]
    (A : Matrix a n ℂ) (B : Matrix b n ℂ) (coef : n → ℂ) (mask : c → n → ℂ)
    (hA : ∀ i j, ‖A i j‖ ≤ 1) (hB : ∀ k j, ‖B k j‖ ≤ 1)
    (hmask : ∀ l j, ‖mask l j‖ ≤ 1) :
    (∑ l, ∑ k, ∑ i, ‖∑ j, A i j * star (B k j) * coef j * mask l j‖ ^ 2) ≤
      (Fintype.card c : ℝ) *
        min ((Fintype.card b : ℝ) * squaredNorm A)
          ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
  calc
    _ ≤ ∑ l : c, min ((Fintype.card b : ℝ) * squaredNorm A)
        ((Fintype.card a : ℝ) * squaredNorm B) * ∑ j, ‖coef j‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro l _
      exact rectangular_block_energy_le A B coef (mask l) hA hB (hmask l)
    _ = _ := by simp [mul_assoc]

end
end CubicSieve

end

noncomputable section
open Eisenstein CubicJacobi CompletedGauss CanonicalRowCompletion FiniteSieveOperator
open scoped BigOperators Classical
local notation "Eis" => Eisenstein.O
namespace CubicSieve
open scoped BigOperators Classical
open UniqueFactorizationMonoid
noncomputable section

variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]
  [NormalizationMonoid M] [Subsingleton Mˣ]

def firstPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 1), p

def secondPart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset.filter
    (fun p => (normalizedFactors x).count p % 3 = 2), p

def cubePart (x : M) : M :=
  ∏ p ∈ (normalizedFactors x).toFinset, p ^ ((normalizedFactors x).count p / 3)

theorem count_mod_three (k : ℕ) :
    k = (if k % 3 = 1 then 1 else 0) +
      2 * (if k % 3 = 2 then 1 else 0) + 3 * (k / 3) := by
  have h := Nat.mod_add_div k 3
  have hlt := Nat.mod_lt k (by decide : 0 < 3)
  split_ifs <;> omega

omit [Subsingleton Mˣ] in
private theorem residual_squarefree (x : M) (r : ℕ) :
    Squarefree (∏ p ∈ (normalizedFactors x).toFinset.filter
      (fun p => (normalizedFactors x).count p % 3 = r), p) := by
  apply Finset.squarefree_prod_of_pairwise_isCoprime
  · intro p hp q hq hpq
    have hp' : p ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1
    have hq' : q ∈ normalizedFactors x := Multiset.mem_toFinset.mp (Finset.mem_filter.mp hq).1
    apply (irreducible_of_normalized_factor p hp').isRelPrime_iff_not_dvd.mpr
    intro hd
    exact hpq (normalizedFactors_eq_of_dvd x p hp' q hq' hd)
  · intro p hp
    exact (irreducible_of_normalized_factor p
      (Multiset.mem_toFinset.mp (Finset.mem_filter.mp hp).1)).squarefree

omit [Subsingleton Mˣ] in
theorem firstPart_squarefree (x : M) : Squarefree (firstPart x) :=
  residual_squarefree x 1

omit [Subsingleton Mˣ] in
theorem secondPart_squarefree (x : M) : Squarefree (secondPart x) :=
  residual_squarefree x 2

omit [Subsingleton Mˣ] in
theorem residual_parts_isRelPrime (x : M) : IsRelPrime (firstPart x) (secondPart x) := by
  unfold firstPart secondPart
  apply IsRelPrime.prod_left
  intro p hp
  apply IsRelPrime.prod_right
  intro q hq
  have hp' := Finset.mem_filter.mp hp
  have hq' := Finset.mem_filter.mp hq
  apply (irreducible_of_normalized_factor p (Multiset.mem_toFinset.mp hp'.1)).isRelPrime_iff_not_dvd.mpr
  intro hd
  have heq := normalizedFactors_eq_of_dvd x p (Multiset.mem_toFinset.mp hp'.1)
    q (Multiset.mem_toFinset.mp hq'.1) hd
  subst q
  omega

theorem cubic_factorization (x : M) (hx : x ≠ 0) :
    x = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
  have hp : (∏ p ∈ (normalizedFactors x).toFinset,
      p ^ (normalizedFactors x).count p) = x := by
    rw [← Finset.prod_multiset_count]
    exact associated_iff_eq.mp (prod_normalizedFactors hx)
  have hper (p : M) : p ^ (normalizedFactors x).count p =
      (if (normalizedFactors x).count p % 3 = 1 then p else 1) *
      (if (normalizedFactors x).count p % 3 = 2 then p else 1) ^ 2 *
      (p ^ ((normalizedFactors x).count p / 3)) ^ 3 := by
    conv_lhs => rw [count_mod_three ((normalizedFactors x).count p)]
    rw [pow_add, pow_add, Nat.mul_comm 3, pow_mul]
    split_ifs <;> simp [pow_mul]
  calc
    x = ∏ p ∈ (normalizedFactors x).toFinset,
        p ^ (normalizedFactors x).count p := hp.symm
    _ = firstPart x * secondPart x ^ 2 * cubePart x ^ 3 := by
      simp_rw [hper]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow]
      simp only [firstPart, secondPart, cubePart, Finset.prod_filter]

theorem extraction_injective_on_nonzero :
    Set.InjOn (fun x : M => (firstPart x, secondPart x, cubePart x)) {x | x ≠ 0} := by
  intro x hx y hy h
  have h1 := congrArg (fun t : M × M × M => t.1) h
  have h2 := congrArg (fun t : M × M × M => t.2.1) h
  have h3 := congrArg (fun t : M × M × M => t.2.2) h
  dsimp only at h1 h2 h3
  rw [cubic_factorization x hx, cubic_factorization y hy, h1, h2, h3]

end
end CubicSieve

end

noncomputable section
open CubicJacobi CubicKubota CubicRamified RationalSource
open Eisenstein CompletedGauss CanonicalRowCompletion NormalizedReflection
open scoped BigOperators Classical ContDiff
local notation "Eis" => Eisenstein.O
namespace NormalizedReflection
section
variable {F:Type*} [Field F] [Fintype F]
def frequencyMultiplier (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (σ ε : Fˣ) (x h : F) : ℂ :=
  if h=0 then 1 else (((χ⁻¹)^2) ((σ:F)*h))*ψ (((ε:F)*x)*h⁻¹)

def frequencyRow (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (j : ℕ) (σ ε : Fˣ) (x h : F) : ℂ :=
  finiteAdditiveFourierCoeff ψ (fun t=>(χ^j) t) h*frequencyMultiplier χ ψ σ ε x h


/-- Separating the fixed unit leaves the native finite Gauss reflection. -/
theorem frequencyRow_units (χ:MulChar F ℂ) (ψ:AddChar F ℂ)
    (j:ℕ) (σ ε:Fˣ) (x:F) :
    (∑h:Fˣ,frequencyRow χ ψ j σ ε x h)=
      ((χ⁻¹)^2) σ * finiteReflectionGauss χ ψ j ((ε:F)*x) := by
  simp only [frequencyRow,frequencyMultiplier,Units.ne_zero,ite_false,
    finiteReflectionGauss,Finset.mul_sum,map_mul,Units.val_inv_eq_inv_val]
  apply Finset.sum_congr rfl
  intro h hh
  ring
end

theorem canonical_frequencyRow_units (P:Ideal Eis) [P.IsMaximal]
    (hg:lambda∉P) (hc:ringChar (Eis⧸P)≠2) (ψ:AddChar (Eis⧸P) ℂ)
    (hψ:ψ.IsPrimitive) (j:ℕ) (hj:j<6) (σ ε:(Eis⧸P)ˣ) (x:Eis⧸P) :
    (∑h:(Eis⧸P)ˣ,frequencyRow (complexSexticChar P hg) ψ j σ ε x h)=
      (((complexSexticChar P hg)⁻¹)^2) σ *
        phase (complexSexticChar P hg) ψ j ε * bracket (complexSexticChar P hg) j x := by
  rw [frequencyRow_units,canonical_gauss_eq_phase_bracket P hg hc ψ hψ j hj]
  ring
end NormalizedReflection

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
