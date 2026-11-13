/-
First blocks and family energy adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Descent.FirstCommonRows

/-!
# First blocks and family energy

Uniform first profiles `InverseMomentFirstProfileUniform`, retained cube weights and the first
family energy; fresh second Poisson passes of blocked physical rows.
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
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstCommonColumn (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool)
    (χ : RayCharacter) (omega : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℂ :=
  supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F\D)
    (fun U => (if negative then star (supportRay p χ (D∪U)) else supportRay p χ (D∪U)) *
      C (D∪U) * (if negative then star (omega (primeProductNorm p U/X)*
        kernelLogPhase t (Real.log (primeProductNorm p U/X))) else
        omega (primeProductNorm p U/X)*kernelLogPhase t (Real.log (primeProductNorm p U/X)))) h

theorem firstCommonColumn_pair (F D : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (omega₁ omega₂ : ℝ → ℂ) (X₁ X₂ t₁ t₂ : ℝ) (h : Eis) :
    (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
      firstCommonCoefficient p hg C₁ C₂ r D U V h *
        (omega₁ (primeProductNorm p U/X₁)*omega₂ (primeProductNorm p V/X₂)) *
        kernelLogPhase t₁ (Real.log (primeProductNorm p U/X₁)) *
        kernelLogPhase t₂ (Real.log (primeProductNorm p V/X₂))) =
    star (firstCommonColumn p hg F D C₁ true r.1 omega₁ X₁ t₁ h) *
      firstCommonColumn p hg F D C₂ false r.2 omega₂ X₂ t₂ h := by
  simp only [firstCommonColumn,supportConjugateSum,star_sum,Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  apply Finset.sum_congr rfl
  intro V hV
  simp only [firstCommonCoefficient,Bool.false_eq_true,ite_false,ite_true,star_mul,star_star]
  ring

def firstCommonOuterLog (A₁ A₂ C R : ℝ) (d h : Eis) (D : Finset ι) (s : Fin 9 → ℝ) : Fin 7 → ℝ :=
  ![Real.log (A₁/s 0),Real.log (A₂/s 1),Real.log (C/s 2),Real.log (‖ringComplex d‖^2/s 3),
    Real.log (R/s 4),Real.log (primeProductNorm p D/s 5),Real.log (‖ringComplex h‖^2/s 6)]

omit [DecidableEq ι] [∀ (i : ι), (Ideal.span {p i}).IsMaximal] in
theorem first_common_source_mode (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (j : FirstCommonIndex ι) (z : Frequency × (Fin 9 → ℝ)) :
    pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
      (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2 =
    firstOuterPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2)
      (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s) *
    kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7)
      (Real.log (primeProductNorm p j.2.2.1/s 7)) *
    kernelLogPhase (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8)
      (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
  have hy : firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s =
      firstCoordinates (firstCommonOuterLog p A₁ A₂ C R d h j.2.1 s)
        (Real.log (primeProductNorm p j.2.2.1/s 7))
        (Real.log (primeProductNorm p j.2.2.2/s 8)) := by
    funext i
    fin_cases i <;> rfl
  rw [hy,first_mode_split]

def firstCommonSeparatedRow (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, supportMobius D * primeCoprimeMask p D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 omega₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 omega₂ (s 8) (H 8) h

theorem first_common_modes_eq_columns (F : Finset ι) (C₁ C₂ : Finset ι → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,firstCommonWeight p hg C₁ C₂ h j *
      (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstCommonSeparatedRow p hg F C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstCommonSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (supportMobius D * primeCoprimeMask p D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (omega₁ (primeProductNorm p U/s 7)*omega₂ (primeProductNorm p V/s 8)) *
            kernelLogPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            kernelLogPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstBlockedPhysicalRows (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) : ℂ :=
  ∑ j ∈ firstCommonIndices F, selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j *
    firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K (firstCommonNorms p A₁ A₂ C R d h j)

def firstBlockedSeparatedRow (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  ∑ r : RayCharacter × RayCharacter, crossCoeff r.1 r.2 *
    ∑ D ∈ F.powerset, selector D * supportMobius D *
      primeCoprimeMask p D h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s) *
      star (firstCommonColumn p hg F D C₁ true r.1 omega₁ (s 7) (H 7) h) *
      firstCommonColumn p hg F D C₂ false r.2 omega₂ (s 8) (H 8) h

theorem first_block_modes_eq_columns (F : Finset ι) (selector : Finset ι → ℂ) (C₁ C₂ : Finset ι → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (z : Frequency × (Fin 9 → ℝ)) :
    (∑ j ∈ firstCommonIndices F,(selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
      (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8)) *
      pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
        (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) =
    firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z := by
  simp only [firstCommonIndices,Finset.sum_product,Finset.sum_sigma,
    firstCommonWeight,firstBlockedSeparatedRow,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro D hD
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  calc
    _ = crossCoeff r.1 r.2 *
        (selector D * supportMobius D * primeCoprimeMask p D h *
          firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h D s)) *
        (∑ U ∈ (F\D).powerset, ∑ V ∈ (F\D).powerset,
          firstCommonCoefficient p hg C₁ C₂ r D U V h *
            (omega₁ (primeProductNorm p U/s 7)*omega₂ (primeProductNorm p V/s 8)) *
            kernelLogPhase (H 7) (Real.log (primeProductNorm p U/s 7)) *
            kernelLogPhase (H 8) (Real.log (primeProductNorm p V/s 8))) := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro U hU
      apply Finset.sum_congr rfl
      intro V hV
      rw [first_common_source_mode]
      dsimp only [H]
      ring
    _ = _ := by
      rw [firstCommonColumn_pair]
      dsimp only [H]
      ring

theorem first_blocks_reconstruct {κ : Type*} (blocks : Finset κ)
    (F : Finset ι) (selector : κ → Finset ι → ℂ)
    (hpartition : ∀ D ∈ F.powerset, ∑ a ∈ blocks, selector a D = 1)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ blocks, firstBlockedPhysicalRows p hg F (selector a) C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  rw [firstPhysicalCommonRows_indexed]
  unfold firstBlockedPhysicalRows
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j hj
  have hDj : j.2.1 ∈ F.powerset := (Finset.mem_sigma.mp (Finset.mem_product.mp hj).2).1
  rw [← Finset.sum_mul, ← Finset.sum_mul, hpartition j.2.1 hDj, one_mul]

def firstCommonBlockSelector {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (D : Finset ι) : ℂ :=
  if label D = a then 1 else 0

theorem first_source_blocks_reconstruct {κ : Type*} [DecidableEq κ]
    (F : Finset ι) (label : Finset ι → κ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) :
    (∑ a ∈ F.powerset.image label,
      firstBlockedPhysicalRows p hg F (firstCommonBlockSelector label a)
        C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h) =
      firstPhysicalCommonRows p hg F C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h := by
  apply first_blocks_reconstruct
  intro D hD
  have hm : label D ∈ F.powerset.image label := Finset.mem_image_of_mem label hD
  simp [firstCommonBlockSelector,hm]

theorem first_block_nonzero_label {κ : Type*} [DecidableEq κ]
    (label : Finset ι → κ) (a : κ) (C₁ C₂ : Finset ι → ℂ) (h : Eis)
    (j : FirstCommonIndex ι)
    (hn : firstCommonBlockSelector label a j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0) :
    label j.2.1 = a := by
  by_contra he
  simp [firstCommonBlockSelector,he] at hn

theorem first_block_normalized_density (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (W₁ W₂ omega₁ omega₂ : ℝ → ℂ) (Φ : 𝓢(ℝ,ℂ))
    (A₁ A₂ C R K : ℝ) (d h : Eis) (s : Fin 9 → ℝ)
    (density : Frequency × (Fin 9 → ℝ) → ℂ) (hDensity : Integrable density)
    (normalization : ℂ)
    (he : ∀ j ∈ firstCommonIndices F,
      selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j ≠ 0 →
      normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
        (firstCommonNorms p A₁ A₂ C R d h j) =
      (firstRootScale s:ℂ)⁻¹ *
        (omega₁ (primeProductNorm p j.2.2.1/s 7)*omega₂ (primeProductNorm p j.2.2.2/s 8)) *
        ∫ z : Frequency × (Fin 9 → ℝ),density z *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope
            (firstRelativeLog (firstCommonNorms p A₁ A₂ C R d h j) s) z.1 z.2) :
    normalization * firstBlockedPhysicalRows p hg F selector C₁ C₂ W₁ W₂ Φ A₁ A₂ C R K d h =
    (firstRootScale s:ℂ)⁻¹ * ∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z := by
  simp_rw [← first_block_modes_eq_columns]
  rw [← density_finite_sum _ density hDensity]
  simp only [firstBlockedPhysicalRows,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases hz : selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j = 0
  · simp only [hz,zero_mul,mul_zero]
  · calc
      _ = (selector j.2.1 * firstCommonWeight p hg C₁ C₂ h j) *
          (normalization * firstNormProfile W₁ W₂ Φ (fun _ _ => 1) K
            (firstCommonNorms p A₁ A₂ C R d h j)) := by ring
      _ = _ := by rw [he j hj hz]; ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def firstBlockOuterWeight (selector : Finset ι → ℂ)
    (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) : ℂ :=
  crossCoeff r.1 r.2 * selector D * supportMobius D *
    primeCoprimeMask p D h

def firstBlockEnergy (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (omega : ℝ → ℂ) (X t : ℝ) (h : Eis) : ℝ :=
  ∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
    ‖firstBlockOuterWeight p selector r D h‖ *
      ‖firstCommonColumn p hg F D C negative (if negative then r.1 else r.2) omega X t h‖^2

theorem firstBlockEnergy_nonneg (F : Finset ι) (selector : Finset ι → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (omega : ℝ → ℂ) (X t : ℝ) (h : Eis) :
    0 ≤ firstBlockEnergy p hg F selector C negative omega X t h := by
  unfold firstBlockEnergy
  positivity

theorem first_block_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstBlockEnergy p hg F selector C₁ true omega₁ (s 7) (H 7) h) *
      Real.sqrt (firstBlockEnergy p hg F selector C₂ false omega₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let w := fun j : (RayCharacter × RayCharacter) × Finset ι =>
    firstBlockOuterWeight p selector j.1 j.2 h *
      firstOuterPhase H (firstCommonOuterLog p A₁ A₂ C R d h j.2 s)
  have hn (j : (RayCharacter × RayCharacter) × Finset ι) :
      ‖w j‖ = ‖firstBlockOuterWeight p selector j.1 j.2 h‖ := by
    simp only [w,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset) w
    (fun j => firstCommonColumn p hg F j.2 C₂ false j.1.2 omega₂ (s 8) (H 8) h)
    (fun j => firstCommonColumn p hg F j.2 C₁ true j.1.1 omega₁ (s 7) (H 7) h)
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ r : RayCharacter × RayCharacter, ∑ D ∈ F.powerset,
      w (r,D) * firstCommonColumn p hg F D C₂ false r.2 omega₂ (s 8) (H 8) h *
        star (firstCommonColumn p hg F D C₁ true r.1 omega₁ (s 7) (H 7) h)) =
      firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z := by
    simp only [firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [w,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  change ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
    Real.sqrt (firstBlockEnergy p hg F selector C₂ false omega₂ (s 8) (H 8) h) *
    Real.sqrt (firstBlockEnergy p hg F selector C₁ true omega₁ (s 7) (H 7) h) at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_block_integral_of_energy (F : Finset ι) (selector : Finset ι → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : ℝ)
    (d h : Eis) (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₁ true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstBlockEnergy p hg F selector C₂ false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstBlockedSeparatedRow p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_block_energy p hg F selector C₁ C₂ omega₁ omega₂ A₁ A₂ C R d h s z).trans
    have h := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact h.trans_eq (by rw [← sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open JointLogSeparation MeasureTheory
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι κ : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def firstFamilySeparatedRow (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) : ℂ :=
  ∑ x∈source,w x*firstBlockedSeparatedRow p hg F (selector x) (C₁ x) (C₂ x)
    omega₁ omega₂ (A₁ x) (A₂ x) (C x) (R x) (d x) (h x) s z

def firstFamilyEnergy (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (omega : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) : ℝ :=
  ∑ x∈source,‖w x‖*firstBlockEnergy p hg F (selector x) (C x) negative omega X t (h x)

theorem firstFamilyEnergy_nonneg (source : Finset κ) (F : Finset ι)
    (selector C : κ → Finset ι → ℂ) (w : κ → ℂ)
    (negative : Bool) (omega : ℝ → ℂ) (X t : ℝ) (h : κ → Eis) :
    0 ≤ firstFamilyEnergy p hg source F selector C w negative omega X t h :=
  Finset.sum_nonneg (fun x _ => mul_nonneg (norm_nonneg _)
    (firstBlockEnergy_nonneg p hg F (selector x) (C x) negative omega X t (h x)))

theorem first_family_cauchy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (z : Frequency × (Fin 9 → ℝ)) :
    let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
    ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
      Real.sqrt (firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7) (H 7) h)*
      Real.sqrt (firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8) (H 8) h) := by
  dsimp only
  let H := profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2
  let weight (j : κ × (RayCharacter × RayCharacter) × Finset ι) : ℂ :=
    w j.1*firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)*
      firstOuterPhase H (firstCommonOuterLog p (A₁ j.1) (A₂ j.1) (C j.1) (R j.1)
        (d j.1) (h j.1) j.2.2 s)
  have hn (j : κ × (RayCharacter × RayCharacter) × Finset ι) :
      ‖weight j‖ = ‖w j.1‖*‖firstBlockOuterWeight p (selector j.1) j.2.1 j.2.2 (h j.1)‖ := by
    simp only [weight,norm_mul,firstOuterPhase_norm,mul_one]
  have hc := DescentWeightedCauchy.weighted_cauchy
    (source ×ˢ ((Finset.univ : Finset (RayCharacter × RayCharacter)) ×ˢ F.powerset)) weight
    (fun j => firstCommonColumn p hg F j.2.2 (C₂ j.1) false j.2.1.2 omega₂ (s 8) (H 8) (h j.1))
    (fun j => firstCommonColumn p hg F j.2.2 (C₁ j.1) true j.2.1.1 omega₁ (s 7) (H 7) (h j.1))
  simp only [hn,Finset.sum_product] at hc
  have he : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      weight (x,r,D)*firstCommonColumn p hg F D (C₂ x) false r.2 omega₂ (s 8) (H 8) (h x)*
        star (firstCommonColumn p hg F D (C₁ x) true r.1 omega₁ (s 7) (H 7) (h x))) =
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z := by
    simp only [firstFamilySeparatedRow,firstBlockedSeparatedRow,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro D hD
    dsimp only [weight,firstBlockOuterWeight,H]
    ring
  rw [he] at hc
  have hleft : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₁ x) true r.1 omega₁ (s 7) (H 7) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7) (H 7) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,ite_true]
  have hright : (∑ x∈source,∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
      ‖w x‖*‖firstBlockOuterWeight p (selector x) r D (h x)‖*
        ‖firstCommonColumn p hg F D (C₂ x) false r.2 omega₂ (s 8) (H 8) (h x)‖^2) =
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8) (H 8) h := by
    simp only [firstFamilyEnergy,firstBlockEnergy,Finset.mul_sum,mul_assoc,Bool.false_eq_true,ite_false]
  rw [hleft,hright] at hc
  exact hc.trans_eq (mul_comm _ _)

theorem first_family_integral_of_energy (source : Finset κ) (F : Finset ι)
    (selector C₁ C₂ : κ → Finset ι → ℂ) (w : κ → ℂ)
    (omega₁ omega₂ : ℝ → ℂ) (A₁ A₂ C R : κ → ℝ) (d h : κ → Eis)
    (s : Fin 9 → ℝ) (density : Frequency × (Fin 9 → ℝ) → ℂ)
    (J : ℕ) (B : ℝ) (hB : 0 ≤ B)
    (hDensity : Integrable (fun z : Frequency × (Fin 9 → ℝ) =>
      tripleHeight J z.1*coordinateHeight J z.2*‖density z‖))
    (hleft : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₁ w true omega₁ (s 7)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 7) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2))
    (hright : ∀ z : Frequency × (Fin 9 → ℝ),
      firstFamilyEnergy p hg source F selector C₂ w false omega₂ (s 8)
        (profileHeight firstLeftSlope firstRightSlope firstKernelSlope z.1 z.2 8) h ≤
        B*(tripleHeight J z.1*coordinateHeight J z.2)) :
    ‖∫ z : Frequency × (Fin 9 → ℝ),density z *
      firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
    B*∫ z : Frequency × (Fin 9 → ℝ),tripleHeight J z.1*coordinateHeight J z.2*‖density z‖ := by
  have hb (z : Frequency × (Fin 9 → ℝ)) :
      ‖firstFamilySeparatedRow p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z‖ ≤
      B*(tripleHeight J z.1*coordinateHeight J z.2) := by
    apply (first_family_cauchy p hg source F selector C₁ C₂ w omega₁ omega₂ A₁ A₂ C R d h s z).trans
    have hh := mul_le_mul (Real.sqrt_le_sqrt (hleft z)) (Real.sqrt_le_sqrt (hright z))
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    exact hh.trans_eq (by rw [←sq,Real.sq_sqrt]; unfold tripleHeight coordinateHeight; positivity)
  calc
    _ ≤ ∫ z : Frequency × (Fin 9 → ℝ),B*(tripleHeight J z.1*coordinateHeight J z.2*‖density z‖) := by
      apply norm_integral_le_of_norm_le (hDensity.const_mul B)
      filter_upwards with z
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_left (hb z) (norm_nonneg _)).trans_eq (by ring)
    _ = _ := integral_const_mul _ _

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp in
theorem firstCommonColumn_eq_rayIdealRow
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D : Finset ι) (C : Finset ι → ℂ) (negative : Bool) (χ : RayCharacter)
    (omega : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (h : Eis) :
    firstCommonColumn p hg F D C negative χ omega X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
    rayIdealRow p hg F
      (fun S => C S * if negative then
        star (omega (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          kernelLogPhase t (columnLog p (primeProductNorm p D*X) S)) else
        omega (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
          kernelLogPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ D h := by
  rw [rayIdealRow_eq_supportRow p hinj hg F D
    (fun S => C S * if negative then
      star (omega (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        kernelLogPhase t (columnLog p (primeProductNorm p D*X) S)) else
      omega (Real.exp (columnLog p (primeProductNorm p D*X) S)) *
        kernelLogPhase t (columnLog p (primeProductNorm p D*X) S)) negative χ h]
  simp only [firstCommonColumn,supportConjugateSum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hdU : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  have hy : columnLog p (primeProductNorm p D*X) (D∪U) =
      Real.log (primeProductNorm p U/X) := by
    unfold columnLog
    rw [primeProductNorm_union p D U hdU,mul_div_mul_left _ _ (primeProductNorm_pos p hp D).ne']
  have hR : supportRay p χ (D∪U) = supportRay p χ D*supportRay p χ U := by
    rw [supportRay,Finset.prod_union hdU,map_mul]
    rfl
  rw [hy,Real.exp_log (div_pos (primeProductNorm_pos p hp U) hX),hR]
  cases negative <;> simp only [Bool.false_eq_true,ite_false,ite_true,star_mul] <;> ring

variable (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))

def firstBareCubeCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (d : Eis) : Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hg B v ε₁ ε₂ C d
  else cubePlusCoefficient p hg B v ε₁ ε₂ C d

theorem firstBareCubeCoefficient_window (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (d : Eis) :
    (fun S => firstBareCubeCoefficient p hg B v ε₁ ε₂ negative C d S *
      if negative then star (V (y S)*kernelLogPhase t (y S)) else V (y S)*kernelLogPhase t (y S)) =
    cubeLogCoefficient p hg B v ε₁ ε₂ negative C V y (-t) d := by
  funext S
  have ht : kernelLogPhase (-t) (-(y S)) = kernelLogPhase t (y S) := by
    unfold kernelLogPhase
    congr 1
    push_cast
    ring
  cases negative <;>
    simp only [firstBareCubeCoefficient,cubeLogCoefficient,cubeMinusCoefficient,cubePlusCoefficient,
      firstPassColumnMinus,firstPassColumnPlus,logTwistMinus,logTwistPlus,
      Bool.false_eq_true,ite_false,ite_true,ht] <;> ring

include hp hcop in
theorem firstCommonColumn_original_labels
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
    (omega : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) d) negative χ omega X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
        dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ C
          (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_eq_rayIdealRow p hp hg hinj F D _ negative χ omega X t hX h,
    firstBareCubeCoefficient_window p hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f)
      (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) t d,
    rayIdealRow_cube_labels p hp hinj hcop hg F D B v ε₁ ε₂ hv]
  rfl

include hp hcop in
theorem firstCommonColumn_marked_priority {σ : Type*} [DecidableEq σ]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i, ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda^2 ∣ p i-1)
    (F D B A : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B,0 < v j)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (slots : Finset σ) (lists : σ → Finset ι) (a : σ → ι → ℂ) (H : Finset ι → ℂ)
    (omega : ℝ → ℂ) (X t : ℝ) (hX : 0 < X) (c d f h : Eis) :
    firstCommonColumn p hg F D
      (firstBareCubeCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U)) c f) d)
      negative χ omega X t h =
    (if negative then star (supportRay p χ D) else supportRay p χ D) *
      (beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
        ∑ r : FirstCoreIndex,firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r *
          ∑ J ∈ slots.powerset,primeMark J lists a (A∪D) *
            firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m
              (fun U => primeMark (slots\J) (fun i => lists i\(A∪D)) a U*H U)
              (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t)
              (h*f^2*dilationLabel p B v ε₁ ε₂)) := by
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ (multiplicativeCoreColumn p Ψ m (fun U => primeMark slots lists a (A∪U)*H U))
    omega X t hX c d f h]
  rw [marked_dilatedCoreRow_eq_input_family p hp hcop hg hc hpr F D B A v ε₁ ε₂
    negative χ Ψ m slots lists a H (fun u => omega (Real.exp u))
    (columnLog p (primeProductNorm p D*X)) c d (-t)]
  simp_rw [firstCoreInputRow_marked_priority]

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

theorem first_fresh_energy_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (_hv : ∀ j ∈ B,0 < v j)
      (negative : Bool) (χ : RayCharacter) (C : Finset ι → ℂ)
      (omega : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x ∈ source,Squarefree x.1) →
      (∀ x ∈ source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z ∈ rows,z ≠ 0) → (∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x ∈ source,‖w x‖ ≤ M) →
      (∑ x ∈ source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (cubicIdealGenerator x.1)) d)
        negative χ omega X t x.2‖^2) ≤
      M*K*Y^ε * ∑ z ∈ rows,‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ C
        (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := DescentWeightedCauchy.first_element_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F D B v ε₁ ε₂ hv negative χ C omega X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply le_trans _ (hpush source rows (dilationLabel p B v ε₁ ε₂) w
    (dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ C
      (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)) M Y hM hmap hrows hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [firstCommonColumn_original_labels p hp hg hcop hinj F D B v ε₁ ε₂ hv
    negative χ C omega X t hX c d (cubicIdealGenerator x.1) x.2]
  simp only [norm_mul]
  have hr0 : ‖supportRay p χ D‖ ≤ 1 := rayMonoid_norm_le χ _
  have hr : ‖if negative then star (supportRay p χ D) else supportRay p χ D‖ ≤ 1 := by
    cases negative <;> simpa only [Bool.false_eq_true,ite_false,ite_true,norm_star]
      using hr0
  have hb := beforeDilationLabel_norm_le_one p hg p B v ε₁ ε₂
    negative c d (cubicIdealGenerator x.1) D
  calc
    _ ≤ ‖beforeDilationLabel p hg p B v ε₁ ε₂ negative c d
        (cubicIdealGenerator x.1) D‖ *
        ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ C
          (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d (-t)
          (x.2*(cubicIdealGenerator x.1)^2*dilationLabel p B v ε₁ ε₂)‖ :=
      mul_le_of_le_one_left (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hr
    _ ≤ _ := mul_le_of_le_one_left (norm_nonneg _) hb

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion
open SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) [∀ i,(Ideal.span {p i}).IsMaximal]

theorem firstBlockOuterWeight_norm_le
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (selector : Finset ι → ℂ) (r : RayCharacter × RayCharacter) (D : Finset ι) (h : Eis) :
    ‖firstBlockOuterWeight p selector r D h‖ ≤ ‖crossCoeff r.1 r.2‖*‖selector D‖ := by
  have hm : ‖supportMobius D‖ = 1 := supportMobius_norm D
  have hc : ‖primeCoprimeMask p D h‖ ≤ 1 := primeCoprimeMask_norm_le_one p D h
  simp only [firstBlockOuterWeight,norm_mul,hm,mul_one]
  exact mul_le_of_le_one_right (mul_nonneg (norm_nonneg _) (norm_nonneg _)) hc

def firstOldLabelCoefficient (hp : ∀ i,p i ≠ 0)
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i,lambda ∉ Ideal.span {p i})
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (c d : Eis) (f : Ideal Eis) : Finset ι → ℂ :=
  firstBareCubeCoefficient p hg B v ε₁ ε₂ negative
    (originalLabelColumn p hg B ε₁ ε₂ negative C c (cubicIdealGenerator f)) d

theorem first_block_old_label_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (_hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i})
      (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ j∈B,0 < v j) → ∀ (negative : Bool) (C : Finset ι → ℂ)
      (omega : ℝ → ℂ) (X t : ℝ),0 < X → ∀ (c d : Eis)
      (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis) (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),
      0 ≤ M → 0 ≤ Y → (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * firstBlockEnergy p hg F selector
        (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
        negative omega X t x.2) ≤
      M*K*Y^ε * ∑ r : RayCharacter × RayCharacter, ∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖) *
          ∑ z∈rows,‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => omega (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2 := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg F B selector v ε₁ ε₂ hv negative C omega X t hX c d
    source rows w M Y hM hY hs hmap hrows hnorm hw
  calc
    _ = ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,∑ x∈source,
        ‖w x‖*‖firstBlockOuterWeight p selector r D x.2‖*
          ‖firstCommonColumn p hg F D
            (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
            negative (if negative then r.1 else r.2) omega X t x.2‖^2 := by
      simp only [firstBlockEnergy,Finset.mul_sum,← mul_assoc]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r hr
      exact Finset.sum_comm
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          (M*K*Y^ε*∑ z∈rows,‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative
            (if negative then r.1 else r.2) C (fun u => omega (Real.exp u))
            (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      calc
        _ ≤ (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ x∈source,
            ‖w x‖*‖firstCommonColumn p hg F D
              (firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative C c d x.1)
              negative (if negative then r.1 else r.2) omega X t x.2‖^2 := by
          rw [Finset.mul_sum]
          apply Finset.sum_le_sum
          intro x hx
          have hh := mul_le_mul_of_nonneg_left
            (firstBlockOuterWeight_norm_le p hinj selector r D x.2) (norm_nonneg (w x))
          exact (mul_le_mul_of_nonneg_right hh (sq_nonneg _)).trans_eq (by ring)
        _ ≤ _ := mul_le_mul_of_nonneg_left
          (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative
            (if negative then r.1 else r.2) C omega X t hX c d source rows w M Y
              hM hY hs hmap hrows hnorm hw) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      ring_nf

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i,lambda ∉ Ideal.span {p i})

def firstFreshSecondPoisson
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (omega : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) : ℂ :=
  ∑ G ∈ (F\D).powerset, ∑ U ∈ ((F\D)\G).powerset, ∑ V ∈ ((F\D)\G).powerset,
    if Disjoint U V then overlapPairWeight p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (firstCoreTwist negative χ Ψ r)
      (m*b0Label p B v ε₁ ε₂) (c*jLabel p B v ε₁ ε₂) d
      (firstCoreTest H (fun u => omega (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
      maskedSecondDual p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp G U V rowMajorant Y else 0

theorem firstFreshSecondPoisson_fixed_pool
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (omega : ℝ → ℂ) (X : ℝ) (c d : Eis)
    (r : FirstCoreIndex) (t Y : ℝ) (hY : 0 < Y) :
    firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H omega X c d r t Y =
    ∑ G∈F.powerset,∑ U∈(F\G).powerset,∑ V∈(F\G).powerset,
      if Disjoint U V then overlapPairWeight p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (firstCoreTwist negative χ Ψ r)
        ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i) (c*jLabel p B v ε₁ ε₂) d
        (firstCoreTest H (fun u => omega (Real.exp u))
          (columnLog p (primeProductNorm p D*X)) negative (-t) D) G U V *
        maskedSecondDual p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp G U V rowMajorant Y else 0 := by
  unfold firstFreshSecondPoisson
  rw [← firstCoreInputRow_smoothed_second_poisson p hg hp hinj hc F D B v ε₁ ε₂ negative χ Ψ m
    H (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y hY]
  rw [firstCoreInputRow_smoothed_sign p hg F D B v ε₁ ε₂ negative χ Ψ m H
    (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) rowMajorant Y]
  simp_rw [inputConjugateRow_fixed_pool p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hinj F D]
  exact inputConjugateRow_smoothed_second_poisson p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) hp hinj (fun i => complexSexticChar_ne_one _ (hg i)) F
    (firstCoreTwist negative χ Ψ r) ((m*b0Label p B v ε₁ ε₂)*∏ i∈D,p i)
    (c*jLabel p B v ε₁ ε₂) d
    (firstCoreTest H (fun u => omega (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) negative (-t) D) rowMajorant Y hY

include hcop in
theorem first_fresh_core_energy_to_second
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hc : ∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i,lambda^2 ∣ p i-1)
    (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis)
    (H : Finset ι → ℂ) (omega : ℝ → ℂ) (X : ℝ) (c d : Eis) (t : ℝ)
    (rows : Finset Eis) (Y : ℝ) (hY : 0 < Y)
    (hrows : ∀ z ∈ rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y)
    (hΨ : ‖Ψ (∏ i∈D,p i)‖ ≤ 1) :
    (∑ z∈rows,‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative χ
      (multiplicativeCoreColumn p Ψ m H) (fun u => omega (Real.exp u))
      (columnLog p (primeProductNorm p D*X)) c d (-t) z‖^2) ≤
    (firstCoreMassBound) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
      (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H omega X c d r t Y).re := by
  calc
    _ ≤ ∑ z∈rows,(firstCoreMassBound) * ∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          ‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
            (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      apply Finset.sum_le_sum
      intro z hz
      exact dilatedCoreRow_sq_le_input_family p hp hcop hg hc hpr F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => omega (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d (-t) z hΨ
    _ = (firstCoreMassBound) * ∑ r : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
        ∑ z∈rows,‖firstCoreInputRow p hg F D B v ε₁ ε₂ negative χ Ψ m H
          (fun u => omega (Real.exp u)) (columnLog p (primeProductNorm p D*X)) c d r (-t) z‖^2 := by
      rw [← Finset.mul_sum,Finset.sum_comm]
      simp only [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ firstCoreMassBound_nonneg
      apply Finset.sum_le_sum
      intro r hr
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact firstCoreInputRow_finite_le_second_poisson p hg hp hinj hc F D B v ε₁ ε₂
        negative χ Ψ m H (fun u => omega (Real.exp u))
        (columnLog p (primeProductNorm p D*X)) c d r (-t) rows Y hY hrows

theorem first_fresh_old_labels_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,lambda^2 ∣ p i-1) →
      ∀ (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), (∀ j∈B,0 < v j) →
      ∀ (negative : Bool) (χ : RayCharacter) (Ψ : Eis →* ℂ) (m : Eis),
      ‖Ψ (∏ i∈D,p i)‖ ≤ 1 → ∀ (H : Finset ι → ℂ) (omega : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      (∑ x∈source,‖w x‖ * ‖firstCommonColumn p hg F D
        (firstBareCubeCoefficient p hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative (multiplicativeCoreColumn p Ψ m H)
            c (cubicIdealGenerator x.1)) d)
        negative χ omega X t x.2‖^2) ≤
      M*K*Y^ε * ((firstCoreMassBound)*∑ r : FirstCoreIndex,
        ‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D r‖ *
          (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative χ Ψ m H omega X c d r t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_fresh_energy_small_power ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F D B v ε₁ ε₂ hv negative χ Ψ m hΨ H omega X t hX
    c d source rows w M Y hM hY hs hmap hrows hnorm hw
  apply (hpush p hp hinj hcop hg F D B v ε₁ ε₂ hv negative χ
    (multiplicativeCoreColumn p Ψ m H) omega X t hX c d source rows w M Y hM hY.le
      hs hmap hrows hnorm hw).trans
  exact mul_le_mul_of_nonneg_left
    (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative χ
      Ψ m H omega X c d t rows Y hY hnorm hΨ) (by positivity)

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels RayFourExpansion SecondPassArithmetic
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "Eis" => Eisenstein.O

theorem first_family_original_to_second (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℝ,0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → Eis) (hp : ∀ i,p i ≠ 0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i,lambda ∉ Ideal.span {p i}),
      (∀ i,ringChar (Eis ⧸ Ideal.span {p i}) ≠ 2) →
      (∀ i,lambda^2 ∣ p i-1) →
      ∀ (F B : Finset ι) (selector : Finset ι → ℂ) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool),
      (∀ i∈B,0 < v i) → ∀ (negative : Bool) (Ψ : Eis →* ℂ) (m : Eis),
      (∀ a,‖Ψ a‖ ≤ 1) → ∀ (H : Finset ι → ℂ) (omega : ℝ → ℂ) (X t : ℝ),0 < X →
      ∀ (c d : Eis) (source : Finset (Ideal Eis × Eis)) (rows : Finset Eis)
        (w : Ideal Eis × Eis → ℂ) (M Y : ℝ),0 ≤ M → 0 < Y →
      (∀ x∈source,Squarefree x.1) →
      (∀ x∈source,DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x∈rows) →
      (∀ z∈rows,z ≠ 0) → (∀ z∈rows,(Ideal.absNorm (Ideal.span {z}):ℝ) ≤ Y) →
      (∀ x∈source,‖w x‖ ≤ M) →
      firstFamilyEnergy p hg source F (fun _ => selector)
        (fun x => firstOldLabelCoefficient p hp hcop hg B v ε₁ ε₂ negative
          (multiplicativeCoreColumn p Ψ m H) c d x.1) w negative omega X t Prod.snd ≤
      M*K*Y^ε * ((firstCoreMassBound)*
        ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
          (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H omega X c d core t Y).re) := by
  obtain ⟨K,hK,hpush⟩ := first_block_old_label_energy ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B selector v ε₁ ε₂ hv negative Ψ m hΨ
    H omega X t hX c d source rows w M Y hM hY hs hmap hrows hnorm hw
  have h := hpush p hp hinj hcop hg F B selector v ε₁ ε₂ hv negative
    (multiplicativeCoreColumn p Ψ m H) omega X t hX c d source rows w M Y hM hY.le
    hs hmap hrows hnorm hw
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  calc
    _ ≤ ∑ r : RayCharacter × RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*
          ((firstCoreMassBound)*∑ core : FirstCoreIndex,‖firstCoreOuter p hg B v ε₁ ε₂ negative Ψ m D core‖ *
            (firstFreshSecondPoisson p hp hg hinj F D B v ε₁ ε₂ negative
              (if negative then r.1 else r.2) Ψ m H omega X c d core t Y).re) := by
      apply Finset.sum_le_sum
      intro r hr
      apply Finset.sum_le_sum
      intro D hD
      exact mul_le_mul_of_nonneg_left
        (first_fresh_core_energy_to_second p hp hcop hg hinj hc hpr F D B v ε₁ ε₂ negative
          (if negative then r.1 else r.2) Ψ m H omega X c d t rows Y hY hnorm (hΨ _)) (by positivity)
    _ = _ := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      apply Finset.sum_congr rfl
      intro D hD
      apply Finset.sum_congr rfl
      intro core hcore
      ring

end
end InverseMoment

namespace InverseMoment
open scoped BigOperators Classical SchwartzMap
open InverseInitialRayAttachment Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic RayFourExpansion
open Eisenstein (ringComplex)
noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open InverseFirstRayAttachment
local notation "O" => Eisenstein.O
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀ i,lambda∉Ideal.span {p i})

def retainedCubeWeight (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) : ℂ :=
  a x * canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1) *
    cubeBaseFactor p hp hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit d x.2

include hcop in
theorem retainedCubeWeight_norm
    (hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
    (b : CubeCoordinates ι) (C : Finset ι) (Ψ₁ Ψ₂ : O→*ℂ)
    (hΨ₁ : ∀ u,‖Ψ₁ u‖≤1) (hΨ₂ : ∀ u,‖Ψ₂ u‖≤1)
    (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (x : Ideal O×O) :
    ‖retainedCubeWeight p hp hg b C Ψ₁ Ψ₂ m₁ m₂ d a x‖≤‖a x‖ := by
  have hinj : Function.Injective (fun i => (Ideal.span {p i} : Ideal O)) := by
    intro i j hij
    by_contra hne
    have ht := (hcop hne).sup_eq
    rw [hij, sup_idem] at ht
    exact (inferInstance : (Ideal.span {p j}).IsMaximal).ne_top ht
  have hsource (Ψ : O →* ℂ) (hΨ : ∀ u, ‖Ψ u‖ ≤ 1) (m f : O) (S : Finset ι) :
      ‖canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) S‖ ≤ 1 := by
    have hm := primeCoprimeMask_norm_le_one p S m
    have hr := primeSubsetRow_norm_le_one p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f
    simp only [canonicalSourceCoefficient,norm_mul,norm_pow,norm_one,mul_one,
      secondColumnCoefficient_norm_one_of_good p hp hinj hg hc S,one_mul]
    calc
      ‖Ψ (∏ i ∈ S, p i)‖ * ‖primeCoprimeMask p S m‖ *
          ‖primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f‖^4
        ≤ 1 * 1 * 1^4 := by gcongr; exact hΨ _
      _ = 1 := by norm_num
  have hout : ‖canonicalCubeOuter p hg b C Ψ₁ Ψ₂ m₁ m₂ (cubicIdealGenerator x.1)‖ ≤ 1 := by
    simp only [canonicalCubeOuter,norm_mul,norm_star]
    exact (mul_le_mul (hsource Ψ₁ hΨ₁ _ _ _) (hsource Ψ₂ hΨ₂ _ _ _)
      (norm_nonneg _) zero_le_one).trans_eq (one_mul 1)
  simp only [retainedCubeWeight,norm_mul]
  calc
    _ ≤ ‖a x‖*1*1 := mul_le_mul
      (mul_le_mul_of_nonneg_left hout (norm_nonneg _))
      (cubeBaseFactor_norm_le_one p hp hinj hg hc _ _ _ _ _ _)
      (norm_nonneg _) (by positivity)
    _ = _ := by ring

include hp in
theorem retained_physical_row_support (b : CubeCoordinates ι) (x : Ideal O×O) (hx : x.1≠0)
    (Y : ℝ) (hcut : x.2∈nonzeroChildFrequencyBall
      (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) :
    DescentWeightedCauchy.firstElementRowMap
      (dilationLabel p b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit) x ∈
        nonzeroChildFrequencyBall 1 Y := by
  have hh := (mem_nonzeroChildFrequencyBall _
    (firstPhysicalMultiplier_ne_zero p hp _ _ _ _ _ x.1 hx) _ _).mp hcut
  apply (mem_nonzeroChildFrequencyBall 1 one_ne_zero _ _).mpr
  simpa only [one_mul,firstPhysicalMultiplier_row] using hh

theorem retained_cube_energy_to_second (ε : ℝ) (hε : 0<ε) :
    ∃ K : ℝ,0<K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι→O) (hp : ∀ i,p i≠0) [∀ i,(Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i=>Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
      (hg : ∀ i,lambda∉Ideal.span {p i})
      (_hc : ∀ i,ringChar (O⧸Ideal.span {p i})≠2)
      (_hpr : ∀ i,lambda^2∣p i-1)
      (F : Finset ι) (b : CubeCoordinates ι) (C : Finset ι)
      (Ψ₁ Ψ₂ : O→*ℂ),(∀ u,‖Ψ₁ u‖≤1) → (∀ u,‖Ψ₂ u‖≤1) →
      ∀ (m₁ m₂ d : O) (a : Ideal O×O→ℂ) (source : Finset (Ideal O×O)) (Γ Y : ℝ),0≤Γ → 0<Y →
      (∀ x∈source,Squarefree x.1) → (∀ x∈source,x.1≠0) → (∀ x∈source,‖a x‖≤Γ) →
      (∀ x∈source,x.2∈nonzeroChildFrequencyBall
        (firstPhysicalMultiplier p b.support b.leftExponent b.rightExponent b.leftBit b.rightBit x.1) Y) →
      ∀ (negative : Bool) (H : Finset ι→ℂ) (selector : Finset ι→ℂ)
        (omega : ℝ→ℂ) (X t : ℝ),0<X →
      let Ψ := if negative then Ψ₁ else Ψ₂
      let m := if negative then m₁ else m₂
      let Hshift := fun U=>H (((if negative then b.rightDivisor else b.leftDivisor)∪C)∪U)
      let w := retainedCubeWeight p hp hg b C Ψ₁ Ψ₂ m₁ m₂ d a
      firstFamilyEnergy p hg source F (fun _=>selector)
        (fun x=>firstOldLabelCoefficient p hp hcop hg b.support (fun i=>b.leftExponent i+b.rightExponent i)
          b.leftBit b.rightBit negative (multiplicativeCoreColumn p Ψ m Hshift)
          (∏i∈C,p i) d x.1) w negative omega X t Prod.snd ≤
      Γ*K*Y^ε*((firstCoreMassBound)*∑ r : RayCharacter×RayCharacter,∑ D∈F.powerset,
        (‖crossCoeff r.1 r.2‖*‖selector D‖)*∑ core : FirstCoreIndex,
          ‖firstCoreOuter p hg b.support (fun i=>b.leftExponent i+b.rightExponent i) b.leftBit b.rightBit negative Ψ m D core‖ *
          (firstFreshSecondPoisson p hp hg hinj F D b.support (fun i=>b.leftExponent i+b.rightExponent i)
            b.leftBit b.rightBit negative (if negative then r.1 else r.2) Ψ m Hshift omega X (∏i∈C,p i) d core t Y).re) := by
  obtain ⟨K,hK,hstep⟩ := first_family_original_to_second ε hε
  refine ⟨K,hK,?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a source Γ Y hΓ hY
    hs hn ha hcut negative H selector omega X t hX Ψ m Hshift w
  apply hstep p hp hinj hcop hg hc hpr F b.support selector _ _ _ b.support_pos negative Ψ m
    (by intro u; cases negative
        · exact hΨ₂ u
        · exact hΨ₁ u) Hshift omega X t hX (∏i∈C,p i) d source
    (nonzeroChildFrequencyBall 1 Y) w Γ Y hΓ hY hs
  · intro x hx
    exact retained_physical_row_support p hp b x (hn x hx) Y (hcut x hx)
  · intro z hz
    exact (Finset.mem_erase.mp hz).1
  · intro z hz
    have hb := ((mem_nonzeroChildFrequencyBall 1 one_ne_zero Y z).mp hz).2
    simpa only [one_mul,ringComplex_norm_sq_eq_absNorm_span] using hb
  · intro x hx
    exact (retainedCubeWeight_norm p hp hcop hg hc b C Ψ₁ Ψ₂ hΨ₁ hΨ₂ m₁ m₂ d a x).trans (ha x hx)

end
end InverseMoment

noncomputable section
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open InverseFirstRayAttachment
open scoped BigOperators Classical SchwartzMap FourierTransform ContDiff
open MeasureTheory JointLogSeparation SchwartzPlanePoisson
open InverseMoment
open InverseInitialProfile
open InverseAmbientProfileTower
namespace InverseMomentFirstProfileUniform

def rooted (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) : 𝓢(ℝ, ℂ) :=
  InverseClippingProfiles.rootSchwartz g M 0 1 0 a 0 zero_lt_one (by simp) hg

@[simp] theorem rooted_apply (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (y : ℝ) :
    rooted g M a hg y = (Real.exp (a*y) : ℂ)*g y := by
  simp [rooted, InverseClippingProfiles.rootedWindow, InverseClippingProfiles.logWindow]

theorem rooted_support (g : 𝓢(ℝ, ℂ)) (M a : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) :
    Function.support (rooted g M a hg) ⊆ Set.Icc (-M) M := by
  intro y hy
  exact hg (by simpa using hy)

def translated (g : 𝓢(ℝ, ℂ)) (ρ : ℝ) : 𝓢(ℝ, ℂ) :=
  SchwartzMap.compSubConstCLM ℂ (-ρ) g

@[simp] theorem translated_apply (g : 𝓢(ℝ, ℂ)) (ρ y : ℝ) :
    translated g ρ y = g (y+ρ) := by simp [translated]

theorem fourier_translated (g : 𝓢(ℝ, ℂ)) (ρ t : ℝ) :
    (𝓕 (translated g ρ)) t = kernelLogPhase t ρ * (𝓕 g) t := by
  rw [SchwartzMap.fourier_coe]
  have he : (translated g ρ : ℝ → ℂ) = fun y => g (y+ρ) := by ext y; simp
  rw [he, InverseClippingProfiles.fourier_translate, ← SchwartzMap.fourier_coe]

def normalization (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) : ℝ :=
  Real.exp (-(9/2:ℝ)*L - ∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i +
    (Real.log c₁+Real.log c₂)/2)

def density (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    fullProfileDensity (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃ p

theorem density_formula (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p =
      (normalization ρ c₁ c₂ L : ℂ) *
        (sourceDensity g₁ c₁ θ₁ p.1.1 * (sourceDensity g₂ c₂ θ₂ p.1.2.1 * b₃ p.1.2.2)) *
        (∏ i, kernelLogPhase (p.2 i) (ρ i) * (𝓕 (g i)) (p.2 i)) := by
  simp only [density, fullProfileDensity, tripleCoefficient, coordinateDensity,
    fourier_translated, fourier_clippedTwist]
  ring

private theorem fourier_twist (g : 𝓢(ℝ, ℂ)) (θ t : ℝ) :
    (𝓕 (frequencyTwist g θ)) t = (𝓕 g) (t-θ) := by
  rw [SchwartzMap.fourier_coe]
  have he : (frequencyTwist g θ : ℝ → ℂ) = fun y => kernelLogPhase θ y * g y := by
    ext y
    exact frequencyTwist_apply g θ y
  rw [he, InverseClippingProfiles.fourier_phase_shift, ← SchwartzMap.fourier_coe]

theorem density_norm (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (p : Ambient (Fin 9)) :
    ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖ = normalization ρ c₁ c₂ L *
      ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖ := by
  rw [density_formula]
  simp only [norm_mul, norm_prod, sourceDensity_norm, kernelLogPhase_norm, one_mul,
    Complex.norm_real, Real.norm_eq_abs, normalization,
    abs_of_pos (Real.exp_pos _), twistedFullDensity, fullProfileDensity,
    tripleCoefficient, coordinateDensity, fourier_twist]
  ring

theorem density_joint_measurable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ)) :
    StronglyMeasurable (fun z : ((Fin 9 → ℝ) × (ℝ × ℝ) × (ℝ × ℝ) × ℝ) × Ambient (Fin 9) =>
      density g g₁ g₂ b₃ z.1.1 z.1.2.1.1 z.1.2.1.2 z.1.2.2.1.1 z.1.2.2.1.2 z.1.2.2.2 z.2) := by
  simp_rw [density_formula]
  apply Measurable.stronglyMeasurable
  unfold normalization sourceDensity kernelLogPhase
  have h1 := (𝓕 g₁ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h2 := (𝓕 g₂ : 𝓢(ℝ, ℂ)).continuous.measurable
  have h3 := b₃.continuous.measurable
  have hu (i : Fin 9) := (𝓕 (g i) : 𝓢(ℝ, ℂ)).continuous.measurable
  have he := Complex.continuous_exp.measurable
  fun_prop

theorem normalization_bound (B : Fin 9 → ℝ) (b : ℝ)
    (ρ : Fin 9 → ℝ) (c₁ c₂ L : ℝ) (hρ : ∀ i, |ρ i| ≤ B i)
    (hc₁ : 0 < c₁) (hc₂ : 0 < c₂) (hc₁b : c₁ ≤ b) (hc₂b : c₂ ≤ b) (hL : 0 ≤ L) :
    normalization ρ c₁ c₂ L ≤
      Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i)+Real.log b) := by
  unfold normalization
  apply Real.exp_le_exp.mpr
  have hs : -(∑ i, InverseClippingProfiles.firstBalancedSlope i*ρ i) ≤
      ∑ i, |InverseClippingProfiles.firstBalancedSlope i| *B i := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_le_sum
    intro i _
    calc
      _ ≤ |InverseClippingProfiles.firstBalancedSlope i*ρ i| := neg_le_abs _
      _ = |InverseClippingProfiles.firstBalancedSlope i| *|ρ i| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (hρ i) (abs_nonneg _)
  have h1 := Real.log_le_log hc₁ hc₁b
  have h2 := Real.log_le_log hc₂ hc₂b
  linarith

theorem density_weighted_integrable (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) := by
  simp_rw [density_norm]
  convert (InverseAmbientProfileTower.fullProfileDensity_weighted_integrable g
    (𝓕 (frequencyTwist g₁ θ₁)) (𝓕 (frequencyTwist g₂ θ₂)) b₃ J).const_mul
      (normalization ρ c₁ c₂ L) using 1 <;> first | rfl | (funext p; unfold twistedFullDensity; ring)

private theorem radial_common_box (Φ : 𝓢(ℝ, ℂ)) (M : Fin 9 → ℝ)
    (hM : ∀ i, 0 ≤ M i) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      (∀ (V : Fin 9 → ℝ → ℂ), (∀ i y, V i y ≠ 0 → |y| ≤ M i) →
        ∀ y : Fin 9 → ℝ,
        (∏ i, V i (y i))*paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) =
          ∫ t : ℝ, (∏ i, V i (y i)*kernelLogPhase t (firstKernelSlope i*y i))*b₃ t) ∧
      (1+R)^A * (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) ≤ C := by
  let box : Fin 9 → ℝ → ℂ := fun i y => if |y| ≤ M i then 1 else 0
  have hb : ∀ i y, box i y ≠ 0 → |y| ≤ M i := by
    intro i y h
    simpa [box] using h
  obtain ⟨C,hC,hs⟩ := InverseMoment.radial_profile_envelope Φ box
    firstKernelSlope M hM hb A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,he,_,hm,_⟩ := hs R hR
  refine ⟨b₃,?_,hm⟩
  intro V hV y
  simp only [Finset.prod_mul_distrib]
  by_cases hz : (∏ i, V i (y i)) = 0
  · simp [hz]
  · have hall (i : Fin 9) : V i (y i) ≠ 0 :=
      (Finset.prod_ne_zero_iff.mp hz) i (Finset.mem_univ i)
    have hbox (i : Fin 9) : box i (y i) = 1 := by simp [box, hV i _ (hall i)]
    have h := he y
    simp only [hbox, one_mul, Finset.prod_const_one] at h
    rw [h, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring

theorem translated_box (g : 𝓢(ℝ, ℂ)) (M B ρ : ℝ)
    (hg : Function.support g ⊆ Set.Icc (-M) M) (hρ : |ρ| ≤ B)
    {y : ℝ} (hy : translated g ρ y ≠ 0) : |y| ≤ M+B := by
  have h := hg (show g (y+ρ) ≠ 0 from by simpa only [translated_apply] using hy)
  have hr := abs_le.mp hρ
  apply abs_le.mpr
  constructor <;> linarith [h.1,h.2,hr.1,hr.2]

theorem density_weighted_integral (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ b₃ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ) (J : ℕ) :
    (∫ p : Ambient (Fin 9), ambientWeight J p *
      ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) = normalization ρ c₁ c₂ L *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₁ θ₁)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (frequencyTwist g₂ θ₂)) t‖) *
        (∫ t : ℝ, (1+‖t‖)^J * ‖b₃ t‖) *
        (∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖) := by
  simp_rw [density_norm]
  have he (p : Ambient (Fin 9)) :
      ambientWeight J p * (normalization ρ c₁ c₂ L *
        ‖twistedFullDensity g g₁ g₂ b₃ (θ₁,θ₂) p‖) =
      normalization ρ c₁ c₂ L * (tripleHeight J p.1 * coordinateHeight J p.2 *
        ‖fullProfileDensity g (𝓕 (frequencyTwist g₁ θ₁))
          (𝓕 (frequencyTwist g₂ θ₂)) b₃ p‖) := by
    unfold ambientWeight tripleHeight coordinateHeight twistedFullDensity
    ring
  simp_rw [he]
  rw [integral_const_mul, InverseMoment.fullProfileDensity_weighted_integral]
  simp only [tripleHeight]
  rw [tripleCoefficient_weighted_integral]
  ring

def profile (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) : ℂ :=
  (normalization ρ c₁ c₂ L : ℂ) *
    ((∏ i, translated (g i) (ρ i) (y i)) *
      clippedTwist g₁ c₁ θ₁ (∑ i, firstLeftSlope i*y i) *
      clippedTwist g₂ c₂ θ₂ (∑ i, firstRightSlope i*y i) *
      paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)))

def requiredOuterOrder (J : ℕ) : ℕ := J+2*InverseClippingProfiles.momentOrder J

theorem common_measure (g : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hg : ∀ i, Function.support (g i) ⊆ Set.Icc (-M i) (M i)) (A J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 0 < c₁ → 0 < c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ, profile g g₁ g₂ Φ ρ c₁ c₂ θ₁ θ₂ R L y =
        ∫ p : Ambient (Fin 9), density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density g g₁ g₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  obtain ⟨C₃,hC₃,hsep⟩ := radial_common_box Φ (fun i => M i+B i)
    (fun i => add_nonneg (hM i) (hB i)) A J
  obtain ⟨C₁,hC₁,h₁⟩ := frequencyTwist_fourier_moment J g₁
  obtain ⟨C₂,hC₂,h₂⟩ := frequencyTwist_fourier_moment J g₂
  let D := ∏ i, ∫ t : ℝ, (1+‖t‖)^J * ‖(𝓕 (g i)) t‖
  let E := Real.exp ((∑ i, |InverseClippingProfiles.firstBalancedSlope i| * B i)+Real.log b)
  have hD : 0 ≤ D := Finset.prod_nonneg (fun i _ => integral_nonneg (fun _ => by positivity))
  have hE : 0 ≤ E := (Real.exp_pos _).le
  refine ⟨E*C₁*C₂*C₃*D, by positivity, ?_⟩
  intro R hR
  obtain ⟨b₃,he,hm⟩ := hsep R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  refine ⟨?_, density_weighted_integrable _ _ _ _ _ _ _ _ _ _ _, ?_⟩
  · intro y
    have hb : ∀ i z, translated (g i) (ρ i) z ≠ 0 → |z| ≤ M i+B i :=
      fun i z hz => translated_box (g i) (M i) (B i) (ρ i) (hg i) (hρ i) hz
    have hid := descent_profile_identity (clippedTwist g₁ c₁ θ₁) (clippedTwist g₂ c₂ θ₂)
      Φ (fun i => translated (g i) (ρ i)) firstLeftSlope firstRightSlope firstKernelSlope
      R b₃ (he _ hb) y
    have habs := profile_integral_coordinate_absorption (fun i => translated (g i) (ρ i))
      (𝓕 (clippedTwist g₁ c₁ θ₁)) (𝓕 (clippedTwist g₂ c₂ θ₂)) b₃
      firstLeftSlope firstRightSlope firstKernelSlope y
    simp only [profileMode] at habs
    unfold profile
    rw [hid, habs, ← full_density_mode_fubini, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with p
    unfold density
    ring
  · rw [density_weighted_integral]
    have h12 := mul_le_mul (h₁ θ₁) (h₂ θ₂)
      (integral_nonneg (fun _ => by positivity)) (by positivity)
    have h123 := mul_le_mul h12 hm (by positivity) (by positivity)
    have hd := mul_le_mul_of_nonneg_right h123 hD
    have hn := normalization_bound B b ρ c₁ c₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
    have hh := mul_le_mul hn hd (by positivity) hE
    convert hh using 1 <;> first | rfl | (dsimp only [InverseClippingProfiles.momentOrder, E, D]; ring)

theorem balanced_exponential_identity (ρ y : Fin 9 → ℝ) (c₁ c₂ L : ℝ) :
    normalization ρ c₁ c₂ L *
      (∏ i, Real.exp (InverseClippingProfiles.firstBalancedSlope i*(y i+ρ i))) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstLeftSlope i*y i)+Real.log c₁)) *
      Real.exp (-(1/2:ℝ)*((∑ i, firstRightSlope i*y i)+Real.log c₂)) =
      Real.exp (-(9/2:ℝ)*L)*Real.exp (InverseClippingProfiles.firstRootExponent y) := by
  rw [normalization, ← Real.exp_sum, ← Real.exp_add, ← Real.exp_add,
    ← Real.exp_add, ← Real.exp_add]
  congr 1
  norm_num [InverseClippingProfiles.firstBalancedSlope,
    InverseClippingProfiles.firstRootExponent, firstLeftSlope, firstRightSlope,
    Fin.sum_univ_succ, Fin.succ, Fin.val_mk]
  ring_nf <;> rfl

def positiveSource (g : 𝓢(ℝ, ℂ)) (c θ x : ℝ) : ℂ :=
  kernelLogPhase θ (Real.log x)*g (Real.log x+Real.log c)

theorem positiveSource_logSchwartz (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    {c x : ℝ} (hc : 0 < c) (hx : 0 < x) (θ : ℝ) :
    positiveSource (CanonicalCubeSeparation.sourceLogProfile W a b ha hs hW) c θ x =
      clippedSource W c θ x := by
  simp only [positiveSource, CanonicalCubeSeparation.sourceLogProfile_apply,
    Real.exp_add, Real.exp_log hc, Real.exp_log hx, clippedSource]
  rw [mul_comm x c]

theorem balanced_profile_identity
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M : Fin 9 → ℝ) (m₁ m₂ : ℝ)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂)
    (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ R L : ℝ) (y : Fin 9 → ℝ) :
    profile (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
      (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂)
      Φ ρ c₁ c₂ θ₁ θ₂ R L y =
      (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
        (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
        Φ (fun i y => U i (y+ρ i)) R y := by
  have he := congrArg (fun x : ℝ => (x : ℂ)) (balanced_exponential_identity ρ y c₁ c₂ L)
  simp only [Complex.ofReal_mul, Complex.ofReal_prod] at he
  unfold profile firstPoissonProfile
  rw [InverseClippingProfiles.firstRootWindows_prod]
  simp only [translated_apply, clippedTwist_apply, rooted_apply, positiveSource, Real.log_exp,
    Finset.prod_mul_distrib]
  linear_combination
    (∏ i, U i (y i+ρ i)) * kernelLogPhase θ₁ (∑ i, firstLeftSlope i*y i) *
    g₁ ((∑ i, firstLeftSlope i*y i)+Real.log c₁) *
    kernelLogPhase θ₂ (∑ i, firstRightSlope i*y i) *
    g₂ ((∑ i, firstRightSlope i*y i)+Real.log c₂) *
    paperRadialFourier Φ (R*Real.exp (∑ i, firstKernelSlope i*y i)) * he

theorem first_profile_common_measure
    (U : Fin 9 → 𝓢(ℝ, ℂ)) (g₁ g₂ Φ : 𝓢(ℝ, ℂ))
    (M B : Fin 9 → ℝ) (m₁ m₂ b : ℝ)
    (hM : ∀ i, 0 ≤ M i) (hB : ∀ i, 0 ≤ B i)
    (hU : ∀ i, Function.support (U i) ⊆ Set.Icc (-M i) (M i))
    (h₁ : Function.support g₁ ⊆ Set.Icc (-m₁) m₁)
    (h₂ : Function.support g₂ ⊆ Set.Icc (-m₂) m₂) (A J : ℕ) :
    let G := fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i)
    let f₁ := rooted g₁ m₁ (-(1/2:ℝ)) h₁
    let f₂ := rooted g₂ m₂ (-(1/2:ℝ)) h₂
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 < R → ∃ b₃ : 𝓢(ℝ, ℂ),
      ∀ (ρ : Fin 9 → ℝ) (c₁ c₂ θ₁ θ₂ L : ℝ),
      (∀ i, |ρ i| ≤ B i) → 1 ≤ c₁ → 1 ≤ c₂ → c₁ ≤ b → c₂ ≤ b → 0 ≤ L →
      (∀ y : Fin 9 → ℝ,
        (Real.exp (-(9/2:ℝ)*L) : ℂ) * firstPoissonProfile
          (positiveSource g₁ c₁ θ₁) (positiveSource g₂ c₂ θ₂)
          Φ (fun i y => U i (y+ρ i)) R y =
        ∫ p : Ambient (Fin 9), density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p *
          pureProfileMode firstLeftSlope firstRightSlope firstKernelSlope y p.1 p.2) ∧
      Integrable (fun p : Ambient (Fin 9) => ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ∧
      (1+R)^A * (∫ p : Ambient (Fin 9), ambientWeight J p *
        ‖density G f₁ f₂ b₃ ρ c₁ c₂ θ₁ θ₂ L p‖) ≤
        C*((1+‖θ₁‖)^(InverseClippingProfiles.momentOrder J) *
          (1+‖θ₂‖)^(InverseClippingProfiles.momentOrder J)) := by
  dsimp only
  obtain ⟨C,hC,hs⟩ := common_measure
    (fun i => rooted (U i) (M i) (InverseClippingProfiles.firstBalancedSlope i) (hU i))
    (rooted g₁ m₁ (-(1/2:ℝ)) h₁) (rooted g₂ m₂ (-(1/2:ℝ)) h₂) Φ M B b hM hB
    (fun i => rooted_support _ _ _ _) A J
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨b₃,hb₃⟩ := hs R hR
  refine ⟨b₃,?_⟩
  intro ρ c₁ c₂ θ₁ θ₂ L hρ hc₁ hc₂ hc₁b hc₂b hL
  have h := hb₃ ρ c₁ c₂ θ₁ θ₂ L hρ (zero_lt_one.trans_le hc₁)
    (zero_lt_one.trans_le hc₂) hc₁b hc₂b hL
  refine ⟨?_,h.2⟩
  intro y
  rw [← balanced_profile_identity U g₁ g₂ Φ M m₁ m₂ hU h₁ h₂]
  exact h.1 y

end InverseMomentFirstProfileUniform

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
