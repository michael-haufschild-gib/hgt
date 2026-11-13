/-
Retained energies and zero modes adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.Inversion.InitialDyadicAssembly
import GaloisForLFunctions.MetaplecticMobiusDescent.Moments.DivisorAllocations

/-!
# Retained energies and zero modes

Supported columns and source generators of source rows; eligible and Gauss energies; active
divisor shells; aggregated row polynomials and the normalized zero-mode bound.
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
open scoped BigOperators Classical
namespace CenteredMomentRetainedEnergy
open CenteredMomentHeckeSlots CenteredMomentHeckeHeight CenteredMomentRetainedProfile
open CenteredMomentDivisorRawEnergy HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def positiveSlotRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  (Real.sqrt (X₁*X₂*∏ i,P i):ℂ)⁻¹ *
    ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
      ∏ i,rowSlot η m A z (S i) (β i) t)

def retainedPositiveRow (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (t X₁ X₂ : ℝ) : ℂ :=
  positiveSlotRow η m A z (dilated W₁ (clipDilation X₁)) (dilated W₂ (clipDilation X₂))
    S β P t (clippedScale X₁) (clippedScale X₂)

omit [DecidableEq ι] in
theorem retained_rectangle_raw_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ T : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hT : 0 < T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
      ((rowTwistedSum η m A z W₁ t X₁*rowTwistedSum η m A z W₂ t X₂)*
        ∏ i,rowSlot η m A z (S i) (β i) t)‖^2 =
      (clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hp : 0 < ∏ i,P i := Finset.prod_pos (fun i _ => hP i)
  have hc₁ : 0 < clippedScale X₁ := zero_lt_one.trans_le (clippedScale_ge_one _)
  have hc₂ : 0 < clippedScale X₂ := zero_lt_one.trans_le (clippedScale_ge_one _)
  unfold retainedPositiveRow positiveSlotRow
  rw [normalized_norm_sq _ (mul_pos hT hp),normalized_norm_sq _ (mul_pos (mul_pos hc₁ hc₂) hp),
    clipped_rowTwistedSum η m A z W₁ t X₁ hX₁,clipped_rowTwistedSum η m A z W₂ t X₂ hX₂]
  field_simp [hp.ne',hT.ne',hc₁.ne',hc₂.ne']

omit [DecidableEq ι] in
theorem centered_to_retained_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(clippedScale X₁*clippedScale X₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
      2*(clippedScale Y₁*clippedScale Y₂/T)*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2 := by
  let F (U V : ℝ) : ℂ := (Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
    ((rowTwistedSum η m A z W₁ t U*rowTwistedSum η m A z W₂ t V)*
      ∏ i,rowSlot η m A z (S i) (β i) t)
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T=F X₁ X₂-F Y₁ Y₂ := by
    unfold centeredSlotRow F
    ring
  rw [he]
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (F X₁ X₂) (F Y₁ Y₂)) 2
  have hn : ‖F X₁ X₂-F Y₁ Y₂‖^2 ≤ 2*‖F X₁ X₂‖^2+2*‖F Y₁ Y₂‖^2 := by
    nlinarith [sq_nonneg (‖F X₁ X₂‖-‖F Y₁ Y₂‖)]
  have hx := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ T hX₁ hX₂ hT
  have hy := retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t Y₁ Y₂ T hY₁ hY₂ hT
  change ‖F X₁ X₂‖^2=_ at hx
  change ‖F Y₁ Y₂‖^2=_ at hy
  rw [hx,hy] at hn
  convert hn using 1 ; ring

omit [DecidableEq ι] in
theorem centered_to_retained_weighted_energy (η : Character) (m A : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂) (hT : 0 < T)
    (rows : Finset O) («ω» : O → ℝ) (hω : ∀ z∈rows,0 ≤ «ω» z) :
    (∑ z∈rows,«ω» z*‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2) ≤
      2*(clippedScale X₁*clippedScale X₂/T)*
        (∑ z∈rows,«ω» z*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2)+
      2*(clippedScale Y₁*clippedScale Y₂/T)*
        (∑ z∈rows,«ω» z*‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro z hz
  have hh := mul_le_mul_of_nonneg_left
    (centered_to_retained_energy η m A z W₁ W₂ S β P hP t X₁ X₂ Y₁ Y₂ T
      hX₁ hX₂ hY₁ hY₂ hT) (hω z hz)
  convert hh using 1 ; ring

omit [DecidableEq ι] in
theorem retained_rectangle_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 ≤
      (max 1 b₁*max 1 b₂)*‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2 := by
  have hB : 0 ≤ max 1 b₁*max 1 b₂ := mul_nonneg
    (zero_le_one.trans (le_max_left _ _)) (zero_le_one.trans (le_max_left _ _))
  by_cases h₁ : X₁*b₁ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₁ b₁ t X₁ hX₁ hs₁ h₁,zero_mul,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  by_cases h₂ : X₂*b₂ < 1
  · unfold positiveSlotRow
    rw [strict_subunit_rowTwistedSum_zero η m A z W₂ b₂ t X₂ hX₂ hs₂ h₂,mul_zero,zero_mul,mul_zero,norm_zero,zero_pow (by decide)]
    exact mul_nonneg hB (sq_nonneg _)
  have hr : clippedScale X₁*clippedScale X₂/(X₁*X₂) ≤ max 1 b₁*max 1 b₂ := by
    have h := mul_le_mul (clipDilation_le b₁ X₁ hX₁ (le_of_not_gt h₁))
      (clipDilation_le b₂ X₂ hX₂ (le_of_not_gt h₂))
      (zero_le_one.trans (clipDilation_ge_one _ hX₂)) (zero_le_one.trans (le_max_left _ _))
    simpa only [clipDilation,div_mul_div_comm] using h
  unfold positiveSlotRow
  rw [retained_rectangle_raw_energy η m A z W₁ W₂ S β P hP t X₁ X₂ (X₁*X₂) hX₁ hX₂ (mul_pos hX₁ hX₂)]
  exact mul_le_mul_of_nonneg_right hr (sq_nonneg _)

omit [DecidableEq ι] in
theorem centered_to_retained_uniform_energy (η : Character) (m A z : O) (W₁ W₂ : ℝ → ℂ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (hP : ∀ i,0 < P i) (b₁ b₂ t X₁ X₂ Y₁ Y₂ T : ℝ)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T)
    (hs₁ : Function.support W₁ ⊆ Set.Iic b₁) (hs₂ : Function.support W₂ ⊆ Set.Iic b₂) :
    ‖centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T‖^2 ≤
      2*(max 1 b₁*max 1 b₂)*
        (‖retainedPositiveRow η m A z W₁ W₂ S β P t X₁ X₂‖^2+
         ‖retainedPositiveRow η m A z W₁ W₂ S β P t Y₁ Y₂‖^2) := by
  have he : centeredSlotRow η m A z W₁ W₂ S β P t X₁ X₂ Y₁ Y₂ T =
      positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂-
      positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂ := by
    unfold centeredSlotRow positiveSlotRow
    rw [hX,hY]
    ring
  rw [he]
  have hx := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t X₁ X₂ hX₁ hX₂ hs₁ hs₂
  have hy := retained_rectangle_uniform_energy η m A z W₁ W₂ S β P hP b₁ b₂ t Y₁ Y₂ hY₁ hY₂ hs₁ hs₂
  have hh := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le
    (positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂)
    (positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂)) 2
  nlinarith [sq_nonneg (‖positiveSlotRow η m A z W₁ W₂ S β P t X₁ X₂‖-
    ‖positiveSlotRow η m A z W₁ W₂ S β P t Y₁ Y₂‖)]

end CenteredMomentRetainedEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical

namespace CenteredMomentDivisorRetained
open CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction CenteredMomentDivisorRectangle
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy HeckeFamily
local notation "O" => Eisenstein.O
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def allocatedPositiveRow (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ) (P : ι → ℝ)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ : ℝ) : ℂ :=
  retainedPositiveRow η m A z W₁ W₂ (fun i : liveIndices D a => S i)
    (fun i : liveIndices D a => β i) (fun i : liveIndices D a => P i) t
    (X₁/Ideal.absNorm (selectedPlain D a 0)) (X₂/Ideal.absNorm (selectedPlain D a 1))

theorem allocated_to_retained_energy (η : Character) (m A z : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (β : ι → Ideal O → ℂ) (M P : ι → ℝ) (hM : ∀ i,0 ≤ M i) (hP : ∀ i,0 < P i)
    (hβ : ∀ i,∀ I∈S i,‖β i I‖ ≤ M i)
    (D : Ideal O) (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ)
    (hW₁ : Function.support W₁ ⊆ Set.Iic b₁) (hW₂ : Function.support W₂ ⊆ Set.Iic b₂)
    (hX₁ : 0 < X₁) (hX₂ : 0 < X₂) (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (hX : X₁*X₂=T) (hY : Y₁*Y₂=T) :
    ‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 ≤
      (2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P *
        (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
         ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have hN (j : Fin 2) : (0:ℝ) < Ideal.absNorm (selectedPlain D a j) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (selectedDivisor_ne_zero D Finset.univ a (Sum.inr j)))
  have hx : (X₁/Ideal.absNorm (selectedPlain D a 0))*(X₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hX]; rfl
  have hy : (Y₁/Ideal.absNorm (selectedPlain D a 0))*(Y₂/Ideal.absNorm (selectedPlain D a 1))=
      T/selectedNorm D a := by rw [div_mul_div_comm,hY]; rfl
  have hr := allocated_raw_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
    b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hT
  have hc := centered_to_retained_uniform_energy η m A z W₁ W₂
    (fun i : liveIndices D a => S i) (fun i : liveIndices D a => β i)
    (fun i : liveIndices D a => P i) (fun i => hP i) b₁ b₂ t _ _ _ _ _
    (div_pos hX₁ (hN 0)) (div_pos hX₂ (hN 1)) (div_pos hY₁ (hN 0)) (div_pos hY₂ (hN 1))
    hx hy hW₁ hW₂
  have hF : 0 < formalReductionFactor D a P := mul_pos (selectedNorm_pos D a)
    (Finset.prod_pos (fun i _ => hP i))
  have hh := mul_le_mul_of_nonneg_left hc (div_nonneg (sq_nonneg (∏ i∈frozenIndices D a,M i)) hF.le)
  apply hr.trans
  convert hh using 1 <;> simp only [residualCenteredRow,allocatedPositiveRow] ; ring

theorem masked_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) («ω» : O → ℝ),(∀ z∈rows,0 ≤ «ω» z) →
      (∑ z∈rows,«ω» z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)),
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,«ω» z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := actual_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows «ω» hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => «ω» z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : («ω» z/(T*∏ i,P i))*‖x‖^2 =
      «ω» z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

end CenteredMomentDivisorRetained

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentActiveAllocation
open HeckeFamily CenteredMomentDivisorAllocation CenteredMomentDivisorExtraction
open CenteredMomentDivisorRows CenteredMomentDivisorRaw CenteredMomentDivisorRawEnergy
open CenteredMomentRetainedEnergy CenteredMomentDivisorRowEnergy CenteredMomentDivisorRetained
open CenteredMomentSlotRatios CenteredMomentDivisorActualBoundary CenteredMomentDivisorRectangle
local notation "O" => Eisenstein.O
variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def activeAllocations (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ) :
    Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  Finset.univ.filter (fun a=>∃z:O,allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂≠0)

theorem inactive_zero (η:Character) (m A:O) (t:ℝ) (S:ι→Finset (Ideal O))
    (β:ι→Ideal O→ℂ) (D:Ideal O) (W₁ W₂:ℝ→ℂ) (X₁ X₂ Y₁ Y₂:ℝ)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (ha:a∉activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂) (z:O) :
    allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂=0 := by
  by_contra hn
  exact ha (Finset.mem_filter.mpr ⟨Finset.mem_univ _,z,hn⟩)

theorem masked_eq_active_allocations (η:Character) (m A z:O) (t:ℝ)
    (S:ι→Finset (Ideal O)) (β:ι→Ideal O→ℂ) (D:Ideal O) (hD:Squarefree D)
    (W₁ W₂:ℝ→ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂:ℝ)
    (hs₁:Function.support W₁⊆Set.Iic b₁) (hs₂:Function.support W₂⊆Set.Iic b₂)
    (hX₁:0< X₁) (hX₂:0< X₂) (hY₁:0< Y₁) (hY₂:0< Y₂) :
    maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂=
      ∑a∈activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
        allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂ := by
  unfold maskedRectangle
  rw [CenteredMomentDivisorFullMask.full_mask_eq_allocated_rectangles η m A z t S β D hD
    W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂]
  symm
  exact Finset.sum_subset (Finset.subset_univ _) (fun a _ ha=> inactive_zero η m A t S β D
    W₁ W₂ X₁ X₂ Y₁ Y₂ a ha z)

theorem active_allocated_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)) (β : ι → Ideal O → ℂ)
      (D : Ideal O),Squarefree D → ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ →
      ∀ (rows : Finset O) («ω» : O → ℝ),(∀ z ∈ rows,0 ≤ «ω» z) →
      (∑ z ∈ rows,«ω» z*‖maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
        C*(Ideal.absNorm D:ℝ)^ε*
          ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
            ∑ z ∈ rows,«ω» z*‖allocatedRectangle η m A z t S β D a W₁ W₂ X₁ X₂ Y₁ Y₂‖^2 := by
  obtain ⟨C,hC,hbase⟩:=actual_allocated_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows «ω» hω
  apply (hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ hs₁ hs₂ hX₁ hX₂ hY₁ hY₂ rows «ω» hω).trans_eq
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro a ha hn
  simp only [inactive_zero η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂ a hn,norm_zero,zero_pow (by norm_num:2≠0),mul_zero,Finset.sum_const_zero]

theorem active_raw_to_retained_energy (N : ℕ) (hslots : Fintype.card ι ≤ N)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ,0 < C ∧ ∀ (η : Character) (m A : O) (t : ℝ)
      (S : ι → Finset (Ideal O)),(∀ i,∀ I∈S i,Prime I) →
      ∀ (β : ι → Ideal O → ℂ) (M P : ι → ℝ),(∀ i,0 ≤ M i) → (∀ i,0 < P i) →
      (∀ i,∀ I∈S i,‖β i I‖ ≤ M i) → ∀ (D : Ideal O),Squarefree D →
      ∀ (W₁ W₂ : ℝ → ℂ) (b₁ b₂ X₁ X₂ Y₁ Y₂ T : ℝ),
      Function.support W₁ ⊆ Set.Iic b₁ → Function.support W₂ ⊆ Set.Iic b₂ →
      0 < X₁ → 0 < X₂ → 0 < Y₁ → 0 < Y₂ → X₁*X₂=T → Y₁*Y₂=T →
      ∀ (rows : Finset O) («ω» : O → ℝ),(∀ z∈rows,0 ≤ «ω» z) →
      (∑ z∈rows,«ω» z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*
        maskedRectangle η m A z t S β D W₁ W₂ X₁ X₂ Y₁ Y₂‖^2) ≤
      C*(Ideal.absNorm D:ℝ)^ε*
        ∑ a ∈ activeAllocations η m A t S β D W₁ W₂ X₁ X₂ Y₁ Y₂,
          ((2*(max 1 b₁*max 1 b₂))*(∏ i∈frozenIndices D a,M i)^2/formalReductionFactor D a P)*
          ∑ z∈rows,«ω» z*
            (‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ X₁ X₂‖^2+
             ‖allocatedPositiveRow η m A z t S β P D a W₁ W₂ Y₁ Y₂‖^2) := by
  obtain ⟨C,hC,hbase⟩ := active_allocated_energy (ι := ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro η m A t S hS β M P hM hP hβ D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂ T
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY rows «ω» hω
  have hT : 0 < T := hX ▸ mul_pos hX₁ hX₂
  have htotal : 0 < T*∏ i,P i := mul_pos hT (Finset.prod_pos (fun i _ => hP i))
  have hh := hbase η m A t S β D hD W₁ W₂ b₁ b₂ X₁ X₂ Y₁ Y₂
    hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ rows (fun z => «ω» z/(T*∏ i,P i))
    (fun z hz => div_nonneg (hω z hz) htotal.le)
  have he (z : O) (x : ℂ) : («ω» z/(T*∏ i,P i))*‖x‖^2 =
      «ω» z*‖(Real.sqrt (T*∏ i,P i):ℂ)⁻¹*x‖^2 := by
    rw [normalized_norm_sq _ htotal]
    ring
  simp_rw [he] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  apply Finset.sum_le_sum
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hb := mul_le_mul_of_nonneg_left
    (allocated_to_retained_energy η m A z t S hS β M P hM hP hβ D a W₁ W₂
      b₁ b₂ X₁ X₂ Y₁ Y₂ T hW₁ hW₂ hX₁ hX₂ hY₁ hY₂ hX hY) (hω z hz)
  convert hb using 1 ; ring

theorem active_formal_boundary (η : Character) (m A : O) (t : ℝ)
    (S : ι → Finset (Ideal O)) (hS : ∀ i,∀ I∈S i,Prime I)
    (ν : ι → Ideal O → ℂ) (W : ι → ℝ → ℂ) (lo hi P : ι → ℝ)
    (hlo : ∀ i,0 < lo i) (hP : ∀ i,0 < P i)
    (hW : ∀ i,Function.support (W i) ⊆ Set.Icc (lo i) (hi i))
    (D : Ideal O) (hD : Squarefree D)
    (a : Allocation D (Finset.univ : Finset (ι ⊕ Fin 2)))
    (W₁ W₂ : ℝ → ℂ) (X₁ X₂ Y₁ Y₂ Z : ℝ) (hZ : 1 < Z)
    (hactive : a∈activeAllocations η m A t S
      (fun i I => ν i I*W i ((Ideal.absNorm I:ℝ)/P i)) D W₁ W₂ X₁ X₂ Y₁ Y₂) :
    Real.logb Z (Ideal.absNorm D:ℝ) ≤ Real.logb Z (formalReductionFactor D a P)+
      (∑ i,logWindow (lo i) (hi i))/Real.log Z := by
  obtain ⟨z,hz⟩:=(Finset.mem_filter.mp hactive).2
  exact original_nonzero_row_formal_boundary η m A z t S hS ν W lo hi P hlo hP hW
    D hD a W₁ W₂ X₁ X₂ Y₁ Y₂ Z hZ hz

end CenteredMomentActiveAllocation

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentActiveDivisorShell
open HeckeFamily CenteredMomentActiveAllocation CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentDivisorBoundary CenteredMomentSlotRatios
local notation "O" => Eisenstein.O

structure Source (ι:Type*) [Fintype ι] where
  η : Character
  m : O
  A : O
  t : ℝ
  slots : ι→Finset (Ideal O)
  prime : ∀i,∀I∈slots i,Prime I
  ν : ι→Ideal O→ℂ
  W : ι→ℝ→ℂ
  lo : ι→ℝ
  hi : ι→ℝ
  P : ι→ℝ
  lo_pos : ∀i,0< lo i
  P_pos : ∀i,0< P i
  support : ∀i,Function.support (W i)⊆Set.Icc (lo i) (hi i)
  W₁ : ℝ→ℂ
  W₂ : ℝ→ℂ
  X₁ : ℝ
  X₂ : ℝ
  Y₁ : ℝ
  Y₂ : ℝ

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Source.active (s:Source ι) (D:Ideal O) : Finset (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) :=
  activeAllocations s.η s.m s.A s.t s.slots
    (fun i I=> s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)) D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂

def Source.allowance (s:Source ι) (Z:ℝ) : ℝ :=
  (∑i,logWindow (s.lo i) (s.hi i))/Real.log Z

theorem Source.active_boundary (s:Source ι) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) (ha:a∈s.active D) (Z:ℝ) (hZ:1< Z) :
    Real.logb Z (Ideal.absNorm D:ℝ)≤ Real.logb Z (formalReductionFactor D a s.P)+s.allowance Z :=
  active_formal_boundary s.η s.m s.A s.t s.slots s.prime s.ν s.W s.lo s.hi s.P s.lo_pos s.P_pos
    s.support D hD a s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂ Z hZ ha

theorem reciprocal_sqrt_log (Z x y:ℝ) (hZ:1< Z) (hx:0< x) (hy:0< y) :
    1/Real.sqrt (x*y)=Z^(-(Real.logb Z x+Real.logb Z y)/2) := by
  have hz:0< Z:=zero_lt_one.trans hZ
  calc
    _=(x*y)^(-(1/2:ℝ)):=by rw [Real.sqrt_eq_rpow,one_div,Real.rpow_neg (mul_nonneg hx.le hy.le)]
    _=(Z^(Real.logb Z x+Real.logb Z y))^(-(1/2:ℝ)):=by
      rw [Real.rpow_add hz,Real.rpow_logb hz hZ.ne' hx,Real.rpow_logb hz hZ.ne' hy]
    _=_:=by rw [←Real.rpow_mul hz.le]; congr 1; ring

theorem Source.active_pair_weight {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) (hD:Squarefree D)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (ha:a∈s.active D) (hb:b∈v.active D) (Z:ℝ) (hZ:1< Z) :
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)≤
      Z^((s.allowance Z+v.allowance Z)/2)/(Ideal.absNorm D:ℝ) := by
  have hs:0< formalReductionFactor D a s.P:=
    mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> s.P_pos i))
  have hv:0< formalReductionFactor D b v.P:=
    mul_pos (selectedNorm_pos D b) (Finset.prod_pos (fun i _=> v.P_pos i))
  have hn:0<(Ideal.absNorm D:ℝ):=by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr hD.ne_zero)
  rw [reciprocal_sqrt_log Z _ _ hZ hs hv]
  have hl:=s.active_boundary D hD a ha Z hZ
  have hr:=v.active_boundary D hD b hb Z hZ
  have he:-(Real.logb Z (formalReductionFactor D a s.P)+Real.logb Z (formalReductionFactor D b v.P))/2≤
      (s.allowance Z+v.allowance Z)/2-Real.logb Z (Ideal.absNorm D:ℝ):=by linarith
  have hp:=Real.rpow_le_rpow_of_exponent_le hZ.le he
  rwa [Real.rpow_sub (zero_lt_one.trans hZ),
    Real.rpow_logb (zero_lt_one.trans hZ) hZ.ne' hn] at hp

theorem paired_active_divisor_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (Ds:Finset (Ideal O))
    (a:∀D:Ideal O,Allocation D (Finset.univ:Finset (ι⊕Fin 2)))
    (b:∀D:Ideal O,Allocation D (Finset.univ:Finset (κ⊕Fin 2)))
    (hD:∀D∈Ds,Squarefree D) (ha:∀D∈Ds,a D∈s.active D) (hb:∀D∈Ds,b D∈v.active D)
    (T Z:ℝ) (hT:1≤ T) (hZ:1< Z)
    (hlo:∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) (hhi:∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) :
    (∑D∈Ds,1/Real.sqrt (formalReductionFactor D (a D) s.P*formalReductionFactor D (b D) v.P))≤
      256*Z^((s.allowance Z+v.allowance Z)/2) := by
  have hs (D:Ideal O):0< formalReductionFactor D (a D) s.P:=
    mul_pos (selectedNorm_pos D (a D)) (Finset.prod_pos (fun i _=> s.P_pos i))
  have hv (D:Ideal O):0< formalReductionFactor D (b D) v.P:=
    mul_pos (selectedNorm_pos D (b D)) (Finset.prod_pos (fun i _=> v.P_pos i))
  simp_rw [reciprocal_sqrt_log Z _ _ hZ (hs _) (hv _)]
  apply paired_raw_divisor_bound Ds T Z ((s.allowance Z+v.allowance Z)/2) hT hZ
    (fun D=> Real.logb Z (formalReductionFactor D (a D) s.P))
    (fun D=> Real.logb Z (formalReductionFactor D (b D) v.P))
    (fun _=> s.allowance Z) (fun _=> v.allowance Z)
    (fun D hd=>(hD D hd).ne_zero) hlo hhi
    (fun D hd=> s.active_boundary D (hD D hd) (a D) (ha D hd) Z hZ)
    (fun D hd=> v.active_boundary D (hD D hd) (b D) (hb D hd) Z hZ)
  intro D hd
  linarith

theorem paired_all_active_shell {κ:Type*} [Fintype κ] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤ N) (hκ:Fintype.card κ≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2) := by
  obtain ⟨C₁,hC₁,hcard₁⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=ι⊕Fin 2) (N+2) (by omega) ε hε
  obtain ⟨C₂,hC₂,hcard₂⟩:=CenteredMomentDivisorEnergy.allocation_card_small_power
    (ι:=κ⊕Fin 2) (N+2) (by omega) ε hε
  refine ⟨256*C₁*C₂,by positivity,?_⟩
  intro s v Ds hD T Z hT hZ hlo hhi
  have ht:0< T:=zero_lt_one.trans_le hT
  have hz:0< Z:=zero_lt_one.trans hZ
  let θ:ℝ:=(s.allowance Z+v.allowance Z)/2
  have hc₁ (D:Ideal O) (hd:D∈Ds):( (s.active D).card:ℝ)≤ C₁*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((s.active D).card:ℝ)≤ Fintype.card (Allocation D (Finset.univ:Finset (ι⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₁ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hc₂ (D:Ideal O) (hd:D∈Ds):( (v.active D).card:ℝ)≤ C₂*(Ideal.absNorm D:ℝ)^ε:=by
    apply (show ((v.active D).card:ℝ)≤ Fintype.card (Allocation D (Finset.univ:Finset (κ⊕Fin 2))) by
      exact_mod_cast Finset.card_le_univ _).trans
    apply hcard₂ D (hD D hd).ne_zero Finset.univ
    simp only [Finset.card_univ,Fintype.card_sum,Fintype.card_fin]
    omega
  have hp (D:Ideal O) (hd:D∈Ds):
      (∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
      (C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have he:((Ideal.absNorm D:ℝ)^ε)*((Ideal.absNorm D:ℝ)^ε)=(Ideal.absNorm D:ℝ)^(2*ε):=by
      rw [←Real.rpow_add hn]; congr 1; ring
    have hpow:(Ideal.absNorm D:ℝ)^(2*ε)≤(2*T)^(2*ε):=
      Real.rpow_le_rpow hn.le (hhi D hd).le (by positivity)
    calc
      _≤∑_a∈s.active D,∑_b∈v.active D,Z^θ/(Ideal.absNorm D:ℝ):=
        Finset.sum_le_sum (fun a ha=> Finset.sum_le_sum (fun b hb=> s.active_pair_weight v D (hD D hd) a b ha hb Z hZ))
      _=((s.active D).card:ℝ)*((v.active D).card:ℝ)*(Z^θ/(Ideal.absNorm D:ℝ)):=by simp;ring
      _≤(C₁*(Ideal.absNorm D:ℝ)^ε)*(C₂*(Ideal.absNorm D:ℝ)^ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=
        mul_le_mul_of_nonneg_right (mul_le_mul (hc₁ D hd) (hc₂ D hd) (by positivity) (by positivity)) (by positivity)
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^(2*ε)*(Z^θ/(Ideal.absNorm D:ℝ)):=by rw [←he];ring
      _≤(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=
        mul_le_mul (mul_le_mul_of_nonneg_left hpow (by positivity))
          (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) ht (hlo D hd)) (by positivity) (by positivity)
  calc
    _≤∑_D∈Ds,(C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T):=Finset.sum_le_sum hp
    _=(Ds.card:ℝ)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=by simp
    _≤(256*T)*((C₁*C₂)*(2*T)^(2*ε)*(Z^θ/T)):=
      mul_le_mul_of_nonneg_right (divisor_dyad_card Ds T hT (fun D hd=>(hD D hd).ne_zero) hhi) (by positivity)
    _=(256*C₁*C₂)*(2*T)^(2*ε)*Z^θ:=by field_simp

end CenteredMomentActiveDivisorShell

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentUniformDivisorShell
open CenteredMomentActiveDivisorShell CenteredMomentDivisorAllocation
open CenteredMomentDivisorRaw CenteredMomentSlotRatios
local notation "O" => Eisenstein.O

def ShellBound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (C ε:ℝ) : Prop := ∀(s:Source ι) (v:Source κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((s.allowance Z+v.allowance Z)/2)

theorem uniform_subset_shell {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0< C ∧ ∀J L:Finset ι,ShellBound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0< C ∧ ShellBound p.1 p.2 C ε:=
    paired_all_active_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0< B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD T Z hT hZ hlo hhi
  have hc:C (J,L)≤ B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD T Z hT hZ hlo hhi).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg (by linarith) _))

theorem subset_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (J:Finset ι) (s:Source J) (lo hi:ι→ℝ) (hlo:∀i:J,s.lo i=lo i) (hhi:∀i:J,s.hi i=hi i)
    (Z:ℝ) (hZ:1< Z) : s.allowance Z≤(∑i,logWindow (lo i) (hi i))/Real.log Z := by
  unfold Source.allowance
  simp_rw [hlo,hhi]
  rw [Finset.sum_coe_sort J (fun i:ι=> logWindow (lo i) (hi i))]
  apply div_le_div_of_nonneg_right _ (Real.log_pos hZ).le
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun i _ _=> logWindow_nonneg _ _)

theorem paired_entrance_allowance {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0< C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L)
      (lo hi:ι→ℝ), (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤
        C*(2*T)^(2*ε)*Z^((∑i,logWindow (lo i) (hi i))/Real.log Z) := by
  obtain ⟨C,hC,hbound⟩:=uniform_subset_shell (ι:=ι) ε hε
  refine ⟨C,hC,?_⟩
  intro J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  apply (hbound J L s v Ds hD T Z hT hZ hlo hhi).trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (by linarith) _))
  apply Real.rpow_le_rpow_of_exponent_le hZ.le
  have hs:=subset_allowance J s lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v lo hi hvlo hvhi Z hZ
  linarith

theorem numerical_allowance (Z H:ℝ) (hZ:1< Z) : Z^(H/Real.log Z)=Real.exp H := by
  rw [Real.rpow_def_of_pos (zero_lt_one.trans hZ)]
  congr 1
  field_simp [(Real.log_pos hZ).ne']

theorem paired_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀(J L:Finset ι) (s:Source J) (v:Source L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀T Z:ℝ,1≤ T → 1< Z → T≤ Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∑D∈Ds,∑a∈s.active D,∑b∈v.active D,
        1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P))≤ C*Z^δ := by
  let ε:ℝ:=δ/(2*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:2*B*ε≤δ:=by
    have hh:ε*(2*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=paired_entrance_allowance (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(2*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD T Z hT hZ hTZ hlo hhi
  have ht:0< T:=zero_lt_one.trans_le hT
  have hz:0< Z:=zero_lt_one.trans hZ
  have hh:=hbound J L s v lo hi hslo hshi hvlo hvhi Ds hD T Z hT hZ hlo hhi
  rw [numerical_allowance Z _ hZ,Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le] at hh
  have hpow:T^(2*ε)≤ Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  apply hh.trans
  calc
    C*(2^(2*ε)*T^(2*ε))*E=(C*2^(2*ε)*E)*T^(2*ε):=by ring
    _≤(C*2^(2*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hpow (by dsimp [E];positivity)

end CenteredMomentUniformDivisorShell

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentEligibleEnergy
open HeckeFamily CenteredMomentActiveDivisorShell CenteredMomentActiveAllocation
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw CenteredMomentDivisorRetained
open CenteredMomentDivisorRowEnergy
local notation "O" => Eisenstein.O

structure Data (ι:Type*) [Fintype ι] extends Source ι where
  M : ι→ℝ
  M_ge_one : ∀i,1≤ M i
  coefficient_bound : ∀i,∀I∈slots i,‖ν i I*W i ((Ideal.absNorm I:ℝ)/P i)‖≤ M i
  b₁ : ℝ
  b₂ : ℝ
  support₁ : Function.support W₁⊆Set.Iic b₁
  support₂ : Function.support W₂⊆Set.Iic b₂
  X₁_pos : 0< X₁
  X₂_pos : 0< X₂
  Y₁_pos : 0< Y₁
  Y₂_pos : 0< Y₂
  same_product : Y₁*Y₂=X₁*X₂
  rows : Finset O
  weight : O→ℝ
  weight_nonneg : ∀z∈rows,0≤ weight z

variable {ι:Type*} [Fintype ι] [DecidableEq ι]

def Data.coefficient (s:Data ι) (i:ι) (I:Ideal O) : ℂ :=
  s.ν i I*s.W i ((Ideal.absNorm I:ℝ)/s.P i)

def Data.energy (s:Data ι) (D:Ideal O) : ℝ :=
  ∑z∈s.rows,s.weight z*‖(Real.sqrt (s.X₁*s.X₂*∏i,s.P i):ℂ)⁻¹*
    maskedRectangle s.η s.m s.A z s.t s.slots s.coefficient D s.W₁ s.W₂ s.X₁ s.X₂ s.Y₁ s.Y₂‖^2

def Data.childEnergy (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : ℝ :=
  ∑z∈s.rows,s.weight z*
    (‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.X₁ s.X₂‖^2+
     ‖allocatedPositiveRow s.η s.m s.A z s.t s.slots s.coefficient s.P D a s.W₁ s.W₂ s.Y₁ s.Y₂‖^2)

def Data.profileFactor (s:Data ι) : ℝ :=
  (2*(max 1 s.b₁*max 1 s.b₂))*(∏i,s.M i)^2

lemma Data.energy_nonneg (s:Data ι) (D:Ideal O) : 0≤ s.energy D :=
  Finset.sum_nonneg (fun z hz=> mul_nonneg (s.weight_nonneg z hz) (sq_nonneg _))

lemma Data.child_nonneg (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0≤ s.childEnergy D a :=
  Finset.sum_nonneg (fun z hz=> mul_nonneg (s.weight_nonneg z hz) (add_nonneg (sq_nonneg _) (sq_nonneg _)))

omit [DecidableEq ι] in
lemma Data.profile_nonneg (s:Data ι) : 0≤ s.profileFactor :=by
  unfold Data.profileFactor
  exact mul_nonneg (by positivity) (sq_nonneg _)

lemma Data.reduction_pos (s:Data ι) (D:Ideal O)
    (a:Allocation D (Finset.univ:Finset (ι⊕Fin 2))) : 0< formalReductionFactor D a s.P :=
  mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> s.P_pos i))

theorem actual_source_from_children (N:ℕ) (hslots:Fintype.card ι≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤ E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤ E) →
      s.energy D≤ C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
        ∑a∈s.toSource.active D,1/formalReductionFactor D a s.P := by
  obtain ⟨C,hC,hbound⟩:=active_raw_to_retained_energy (ι:=ι) N hslots ε hε
  refine ⟨C,hC,?_⟩
  intro s D hD E hE hchild
  have hh:=hbound s.η s.m s.A s.t s.slots s.prime s.coefficient s.M s.P
    (fun i=> zero_le_one.trans (s.M_ge_one i)) s.P_pos s.coefficient_bound D hD s.W₁ s.W₂
    s.b₁ s.b₂ s.X₁ s.X₂ s.Y₁ s.Y₂ (s.X₁*s.X₂) s.support₁ s.support₂
    s.X₁_pos s.X₂_pos s.Y₁_pos s.Y₂_pos rfl s.same_product s.rows s.weight s.weight_nonneg
  change s.energy D≤ _ at hh
  apply hh.trans
  calc
    _≤ C*(Ideal.absNorm D:ℝ)^ε*∑a∈s.toSource.active D,
        (s.profileFactor/formalReductionFactor D a s.P)*E:=by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg hC.le (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      apply Finset.sum_le_sum
      intro a ha
      have hp:(∏i∈frozenIndices D a,s.M i)≤∏i,s.M i:=
        Finset.prod_le_prod_of_subset_of_one_le (Finset.subset_univ _)
          (fun i _=> zero_le_one.trans (s.M_ge_one i)) (fun i _ _=> s.M_ge_one i)
      apply mul_le_mul _ (hchild a ha) (s.child_nonneg D a) _
      · apply div_le_div_of_nonneg_right _ (s.reduction_pos D a).le
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact pow_le_pow_left₀ (Finset.prod_nonneg (fun i _=> zero_le_one.trans (s.M_ge_one i))) hp 2
      · exact div_nonneg s.profile_nonneg (s.reduction_pos D a).le
    _=_:=by
      simp only [div_eq_mul_inv,one_mul,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a ha
      ring

lemma sqrt_sum_le {α:Type*} (S:Finset α) (f:α→ℝ) (hf:∀a∈S,0≤ f a) :
    Real.sqrt (∑a∈S,f a)≤∑a∈S,Real.sqrt (f a) := by
  apply Real.sqrt_le_iff.mpr
  refine ⟨Finset.sum_nonneg (fun a _=> Real.sqrt_nonneg _),?_⟩
  have hh:=Finset.sum_sq_le_sq_sum_of_nonneg (s:=S) (f:=fun a=> Real.sqrt (f a))
    (fun a _=> Real.sqrt_nonneg _)
  have he:(∑a∈S,Real.sqrt (f a)^2)=∑a∈S,f a:=Finset.sum_congr rfl (fun a ha=> Real.sq_sqrt (hf a ha))
  rwa [he] at hh

lemma sqrt_reciprocal (x:ℝ) (_hx:0< x) : Real.sqrt (1/x)=1/Real.sqrt x := by
  rw [Real.sqrt_div (by norm_num:0≤(1:ℝ)),Real.sqrt_one]

theorem actual_source_root_from_children (N:ℕ) (hslots:Fintype.card ι≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀s:Data ι,∀D:Ideal O,Squarefree D → ∀E:ℝ,0≤ E →
      (∀a∈s.toSource.active D,s.childEnergy D a≤ E) →
      Real.sqrt (s.energy D)≤ C*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)*Real.sqrt (s.profileFactor*E)*
        ∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P) := by
  obtain ⟨C,hC,hbase⟩:=actual_source_from_children (ι:=ι) N hslots ε hε
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,?_⟩
  intro s D hD E hE hc
  have hp:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he:0≤ s.profileFactor*E:=mul_nonneg s.profile_nonneg hE
  have hs:=sqrt_sum_le (s.toSource.active D) (fun a=>1/formalReductionFactor D a s.P)
    (fun a _=> div_nonneg zero_le_one (s.reduction_pos D a).le)
  simp_rw [sqrt_reciprocal _ (s.reduction_pos D _)] at hs
  have hh:=Real.sqrt_le_sqrt (hbase s D hD E hE hc)
  have hrew:C*(Ideal.absNorm D:ℝ)^ε*s.profileFactor*E*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P)=
      (C*(Ideal.absNorm D:ℝ)^ε*(s.profileFactor*E))*
      (∑a∈s.toSource.active D,1/formalReductionFactor D a s.P):=by ring
  rw [hrew,Real.sqrt_mul (mul_nonneg (mul_nonneg hC.le hp) he),
    Real.sqrt_mul (mul_nonneg hC.le hp),Real.sqrt_mul hC.le] at hh
  exact hh.trans (mul_le_mul_of_nonneg_left hs (by positivity))

end CenteredMomentEligibleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentPairedEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentActiveDivisorShell
open CenteredMomentDivisorAllocation CenteredMomentDivisorRaw
local notation "O" => Eisenstein.O

lemma reciprocal_sums {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (s:Source ι) (v:Source κ) (D:Ideal O) :
    (∑a∈s.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
      (∑b∈v.active D,1/Real.sqrt (formalReductionFactor D b v.P))=
    ∑a∈s.active D,∑b∈v.active D,
      1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P) := by
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b hb
  have hf:0≤ formalReductionFactor D a s.P:=
    (mul_pos (selectedNorm_pos D a) (Finset.prod_pos (fun i _=> s.P_pos i))).le
  rw [Real.sqrt_mul hf]
  ring

theorem actual_paired_source_shell {ι κ:Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (N:ℕ) (hι:Fintype.card ι≤ N) (hκ:Fintype.card κ≤ N) (ε:ℝ) (hε:0<ε) :
    ∃C:ℝ,0< C ∧ ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤ E₁ → 0≤ E₂ → 1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤ E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤ E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  obtain ⟨C₁,hC₁,hl⟩:=actual_source_root_from_children (ι:=ι) N hι ε hε
  obtain ⟨C₂,hC₂,hr⟩:=actual_source_root_from_children (ι:=κ) N hκ ε hε
  obtain ⟨C₃,hC₃,hshell⟩:=paired_all_active_shell (ι:=ι) (κ:=κ) N hι hκ ε hε
  refine ⟨C₁*C₂*C₃,by positivity,?_⟩
  intro s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  let W:ℝ:=Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)
  let θ:ℝ:=(s.toSource.allowance Z+v.toSource.allowance Z)/2
  let F:Ideal O→ℝ:=fun D=>∑a∈s.toSource.active D,∑b∈v.toSource.active D,
    1/Real.sqrt (formalReductionFactor D a s.P*formalReductionFactor D b v.P)
  have hW:0≤ W:=mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hF (D:Ideal O):0≤ F D:=Finset.sum_nonneg (fun a _=> Finset.sum_nonneg
    (fun b _=> div_nonneg zero_le_one (Real.sqrt_nonneg _)))
  have ht:0< T:=zero_lt_one.trans_le hT
  have hp (D:Ideal O) (hd:D∈Ds):Real.sqrt (s.energy D)*Real.sqrt (v.energy D)≤
      (C₁*C₂)*(2*T)^ε*W*F D:=by
    have hn:0<(Ideal.absNorm D:ℝ):=ht.trans_le (hlo D hd)
    have hpow:0≤(Ideal.absNorm D:ℝ)^ε:=Real.rpow_nonneg hn.le _
    have hmul:=mul_le_mul (hl s D (hD D hd) E₁ hE₁ (hleft D hd))
      (hr v D (hD D hd) E₂ hE₂ (hright D hd)) (Real.sqrt_nonneg _) (by positivity)
    apply hmul.trans
    calc
      _=(C₁*C₂)*Real.sqrt ((Ideal.absNorm D:ℝ)^ε)^2*W*
          ((∑a∈s.toSource.active D,1/Real.sqrt (formalReductionFactor D a s.P))*
           (∑b∈v.toSource.active D,1/Real.sqrt (formalReductionFactor D b v.P))):=by dsimp [W];ring
      _=(C₁*C₂)*(Ideal.absNorm D:ℝ)^ε*W*F D:=by
        rw [Real.sq_sqrt hpow,reciprocal_sums]
      _≤ _:=mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn.le (hhi D hd).le hε.le) (by positivity)) hW) (hF D)
  calc
    _≤∑D∈Ds,(C₁*C₂)*(2*T)^ε*W*F D:=Finset.sum_le_sum hp
    _=((C₁*C₂)*(2*T)^ε*W)*(∑D∈Ds,F D):=(Finset.mul_sum ..).symm
    _≤((C₁*C₂)*(2*T)^ε*W)*(C₃*(2*T)^(2*ε)*Z^θ):=
      mul_le_mul_of_nonneg_left (hshell s.toSource v.toSource Ds hD T Z hT hZ hlo hhi) (by positivity)
    _=(C₁*C₂*C₃)*(2*T)^(3*ε)*Z^θ*W:=by
      have hpow:(2*T)^ε*(2*T)^(2*ε)=(2*T)^(3*ε):=by
        rw [←Real.rpow_add (by positivity:0<2*T)];congr 1;ring
      calc
        _=(C₁*C₂*C₃)*((2*T)^ε*(2*T)^(2*ε))*Z^θ*W:=by ring
        _=_:=by rw [hpow]

end CenteredMomentPairedEligibleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped Classical BigOperators

namespace CenteredMomentUniformEligibleEnergy
open CenteredMomentEligibleEnergy CenteredMomentPairedEligibleEnergy
open CenteredMomentUniformDivisorShell CenteredMomentSlotRatios
local notation "O" => Eisenstein.O

def Bound (ι κ:Type*) [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] (C ε:ℝ) : Prop :=
  ∀(s:Data ι) (v:Data κ) (Ds:Finset (Ideal O)),
      (∀D∈Ds,Squarefree D) → ∀(E₁ E₂ T Z:ℝ),0≤ E₁ → 0≤ E₂ → 1≤ T → 1< Z →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤ E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤ E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*(2*T)^(3*ε)*Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)*
          (Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂))

theorem uniform_subset_energy {ι:Type*} [Fintype ι] [DecidableEq ι]
    (ε:ℝ) (hε:0<ε) : ∃C:ℝ,0< C ∧ ∀J L:Finset ι,Bound J L C ε := by
  have he (p:Finset ι×Finset ι):∃C:ℝ,0< C ∧ Bound p.1 p.2 C ε:=
    actual_paired_source_shell (ι:=p.1) (κ:=p.2) (Fintype.card ι)
      (by simpa using Finset.card_le_univ p.1) (by simpa using Finset.card_le_univ p.2) ε hε
  choose C hC hbound using he
  let B:ℝ:=1+∑p:Finset ι×Finset ι,C p
  have hs:0≤∑p:Finset ι×Finset ι,C p:=Finset.sum_nonneg (fun p _=>(hC p).le)
  have hB:0< B:=by dsimp [B];linarith
  refine ⟨B,hB,?_⟩
  intro J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  have hc:C (J,L)≤ B:=by
    have hp:=Finset.single_le_sum (fun p _=>(hC p).le) (Finset.mem_univ (J,L))
    dsimp [B]
    linarith
  exact (hbound (J,L) s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hc (Real.rpow_nonneg (by linarith) _))
      (Real.rpow_nonneg (by linarith) _)) (by positivity))

theorem actual_source_shell_subpower {ι:Type*} [Fintype ι] [DecidableEq ι]
    (lo hi:ι→ℝ) (B δ:ℝ) (hB:0≤ B) (hδ:0<δ) :
    ∃C:ℝ,0< C ∧ ∀(J L:Finset ι) (s:Data J) (v:Data L),
      (∀i:J,s.lo i=lo i) → (∀i:J,s.hi i=hi i) →
      (∀i:L,v.lo i=lo i) → (∀i:L,v.hi i=hi i) →
      ∀Ds:Finset (Ideal O),(∀D∈Ds,Squarefree D) → ∀E₁ E₂ T Z:ℝ,
      0≤ E₁ → 0≤ E₂ → 1≤ T → 1< Z → T≤ Z^B →
      (∀D∈Ds,T≤(Ideal.absNorm D:ℝ)) → (∀D∈Ds,(Ideal.absNorm D:ℝ)<2*T) →
      (∀D∈Ds,∀a∈s.toSource.active D,s.childEnergy D a≤ E₁) →
      (∀D∈Ds,∀a∈v.toSource.active D,v.childEnergy D a≤ E₂) →
      (∑D∈Ds,Real.sqrt (s.energy D)*Real.sqrt (v.energy D))≤
        C*Z^δ*(Real.sqrt (s.profileFactor*E₁)*Real.sqrt (v.profileFactor*E₂)) := by
  let ε:ℝ:=δ/(3*(B+1))
  have hε:0<ε:=div_pos hδ (by positivity)
  have he:3*B*ε≤δ:=by
    have hh:ε*(3*(B+1))=δ:=div_mul_cancel₀ δ (by positivity)
    nlinarith
  obtain ⟨C,hC,hbound⟩:=uniform_subset_energy (ι:=ι) ε hε
  let E:ℝ:=Real.exp (∑i,logWindow (lo i) (hi i))
  refine ⟨C*2^(3*ε)*E,by dsimp [E];positivity,?_⟩
  intro J L s v hslo hshi hvlo hvhi Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hTZ hlo hhi hleft hright
  have ht:0< T:=zero_lt_one.trans_le hT
  have hz:0< Z:=zero_lt_one.trans hZ
  have hs:=subset_allowance J s.toSource lo hi hslo hshi Z hZ
  have hv:=subset_allowance L v.toSource lo hi hvlo hvhi Z hZ
  have hnum:Z^((s.toSource.allowance Z+v.toSource.allowance Z)/2)≤ E:=by
    dsimp [E]
    rw [←numerical_allowance Z _ hZ]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    linarith
  have hh:=hbound J L s v Ds hD E₁ E₂ T Z hE₁ hE₂ hT hZ hlo hhi hleft hright
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply (mul_le_mul_of_nonneg_left hnum (mul_nonneg hC.le (Real.rpow_nonneg (by positivity) _))).trans
  rw [Real.mul_rpow (by norm_num:0≤(2:ℝ)) ht.le]
  have hp:T^(3*ε)≤ Z^δ:=by
    apply (Real.rpow_le_rpow ht.le hTZ (by positivity)).trans
    rw [←Real.rpow_mul hz.le]
    apply Real.rpow_le_rpow_of_exponent_le hZ.le
    nlinarith [he]
  calc
    C*(2^(3*ε)*T^(3*ε))*E=(C*2^(3*ε)*E)*T^(3*ε):=by ring
    _≤(C*2^(3*ε)*E)*Z^δ:=mul_le_mul_of_nonneg_left hp (by dsimp [E];positivity)

end CenteredMomentUniformEligibleEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentRowNorm
open Eisenstein  CubicEisenstein SchwartzPlanePoisson
open CanonicalRowCompletion CanonicalQuadraticSieve
open CenteredMomentCorrelation CenteredMomentFourier CenteredMomentSupportedCorrelation
open CenteredMomentCommonSupport
local notation "O" => Eisenstein.O

def pairResidue (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x : Residue (a * b)) : ℂ :=
  supportedModulusCharacter a ha (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (supportedModulusCharacter b hb
      (frequencyReduction b (a * b) (dvd_mul_left b a) x))

@[simp] theorem pairResidue_mk (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (z : O) :
    pairResidue a b ha hb (Ideal.Quotient.mk _ z) =
      idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b})) := by
  simp only [pairResidue, frequencyReduction_mk, supportedModulusCharacter_mk]

def pairFourier (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (h : O) : ℂ :=
  ∑' x : Residue (a * b), pairResidue a b ha hb x *
    residueTraceQuotientChar 1 (a * b) (mul_ne_zero (supported_element_ne_zero a ha)
      (supported_element_ne_zero b hb)) (Ideal.Quotient.mk _ h * x)

theorem row_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O =>
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖ringComplex z‖ ^ 2 / K)) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) (pairResidue a b ha hb)
  simpa only [pairResidue_mk, scaledRadialTest_apply] using h

theorem row_pair_poisson (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (idealRowHom z (Ideal.span {a}) * star (idealRowHom z (Ideal.span {b}))) *
        W (‖ringComplex z‖ ^ 2 / K)) =
    ((K / ‖ringComplex (a * b)‖ ^ 2 : ℝ) : ℂ) *
      ∑' h : O, pairFourier a b ha hb h *
        paperRadialFourier W (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex (a * b)‖ ^ 2) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  have h := actual_radial_poisson_trace W K hK (a * b)
    (mul_ne_zero (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))
    (pairResidue a b ha hb)
  simpa only [pairResidue_mk, pairFourier, tsum_fintype, Complex.real_smul, div_mul_eq_mul_div] using h

def rowPolynomial {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * idealRowHom z (Ideal.span {a i})

def rowEnergy {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖ringComplex z‖ ^ 2 / K)

theorem rowPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (c : α → ℂ) (z : O) :
    ((‖rowPolynomial S a c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (idealRowHom z (Ideal.span {a i}) * star (idealRowHom z (Ideal.span {a j}))) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [rowPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rowEnergy_expand {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (idealRowHom z (Ideal.span {a i}) *
          star (idealRowHom z (Ideal.span {a j}))) * W (‖ringComplex z‖ ^ 2 / K) := by
  have hs (i j : α) := (row_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [rowEnergy, rowPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem rowEnergy_poisson {α : Type*} (S : Finset α) (a : α → O) (c : α → ℂ)
    (ha : ∀ i, Supported (Ideal.span {a i}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    rowEnergy S a c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K / ‖ringComplex (a i * a j)‖ ^ 2 : ℝ) : ℂ) *
          ∑' h : O, pairFourier (a i) (a j) (ha i) (ha j) h *
            paperRadialFourier W
              (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex (a i * a j)‖ ^ 2)) := by
  rw [rowEnergy_expand S a c ha W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  rw [row_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end CenteredMomentRowNorm

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap

namespace CenteredMomentSourceRow
open CenteredMomentHeckeExpansion CenteredMomentRowNorm HeckeFamily CanonicalRowCompletion
open CanonicalQuadraticSieve  CompletedGauss
local notation "O" => Eisenstein.O

theorem rowWeight_split (η : Character) (m A z : O) (t : ℝ) (I : Ideal O) :
    rowWeight η m A z t I = rowWeight η m A 1 t I*idealRowHom z I := by
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t) =
    ((idealCoeff η I*idealRowHom (m^6*(A*1)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t))*idealRowHom z I
  rw [mul_one,← mul_assoc,idealRowHom_argument_mul]
  ring

theorem rowWeight_zero_of_not_supported (η : Character) (m A z : O) (t : ℝ)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m) (I : Ideal O) (hI : ¬Supported I) :
    rowWeight η m A z t I=0 := by
  by_cases h0 : I=0
  · rw [h0,map_zero]
  let n := cubicIdealGenerator I
  have hn : n ≠ 0 := cubicIdealGenerator_ne_zero I h0
  have hs : Ideal.span {n}=I := span_cubicIdealGenerator I
  have hz := rowTwist_zero_of_not_supported (HeckeRowClosure.elementHom η) m 1 (A*z) n
    hmLam hm2 ((supported_iff_native _).not.mp (hs ▸ hI))
  have he : rowTwist (HeckeRowClosure.elementHom η) m 1 (A*z) n =
      idealCoeff η I*idealRowHom (m^6*(A*z)) I := by
    change elementCoeff η n*idealRowHom (m^6*1^4*(A*z)) (Ideal.span {n})=_
    rw [one_pow,mul_one,hs,← idealCoeff_span η hn,hs]
  rw [he] at hz
  change (idealCoeff η I*idealRowHom (m^6*(A*z)) I)*(Ideal.absNorm I:ℂ)^(Complex.I*t)=0
  rw [hz,zero_mul]

def supportedColumns (S : Finset (Ideal O)) : Finset (Ideal O) := S.filter Supported

theorem primary_span_supported (I : Ideal O) (hI : Supported I) : Ideal.span {primaryIdealGenerator I}=I :=
  (primaryIdealGenerator_spec I (supported_primaryIdealGenerator_ne_zero I hI)).1

def sourceGenerator (S : Finset (Ideal O)) (I : supportedColumns S) : O := primaryIdealGenerator I

theorem sourceGenerator_supported (S : Finset (Ideal O)) (I : supportedColumns S) :
    Supported (Ideal.span {sourceGenerator S I}) := by
  have hI := (Finset.mem_filter.mp I.property).2
  rw [sourceGenerator,primary_span_supported I hI]
  exact hI

theorem finite_hecke_sum_eq_rowPolynomial (η : Character) (m A z : O) (t : ℝ)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) :
    (∑ I∈S,c I*rowWeight η m A z t I) =
      rowPolynomial Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) z := by
  have he : (∑ I∈S,c I*rowWeight η m A z t I) =
      ∑ I∈supportedColumns S,c I*rowWeight η m A z t I := by
    symm
    apply Finset.sum_filter_of_ne
    intro I hI hn
    by_contra hs
    exact hn (by rw [rowWeight_zero_of_not_supported η m A z t hmLam hm2 I hs,mul_zero])
  rw [he,← Finset.sum_coe_sort (supportedColumns S) (fun I => c I*rowWeight η m A z t I)]
  unfold rowPolynomial
  apply Finset.sum_congr rfl
  intro I hI
  rw [sourceGenerator,primary_span_supported I (Finset.mem_filter.mp I.property).2,rowWeight_split]
  ring

def finiteHeckeEnergy (η : Character) (m A : O) (t : ℝ)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O,((‖∑ I∈S,c I*rowWeight η m A z t I‖^2:ℝ):ℂ)*
    W (‖ringComplex z‖^2/K)

theorem finiteHeckeEnergy_eq (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) :
    finiteHeckeEnergy η m A t S c W K =
      CenteredMomentRowNorm.rowEnergy Finset.univ (sourceGenerator S)
        (fun I : supportedColumns S => c I*rowWeight η m A 1 t I) W K := by
  unfold finiteHeckeEnergy CenteredMomentRowNorm.rowEnergy
  simp_rw [finite_hecke_sum_eq_rowPolynomial η m A _ t hmLam hm2 S c]

theorem finiteHeckeEnergy_poisson (η : Character) (m A : O) (t : ℝ)
    (hmLam : lambda ∣ m) (hm2 : (2:O) ∣ m)
    (S : Finset (Ideal O)) (c : Ideal O → ℂ) (W : 𝓢(ℝ,ℂ)) (K : ℝ) (hK : 0 < K) :
    finiteHeckeEnergy η m A t S c W K =
      ∑ I : supportedColumns S,∑ J : supportedColumns S,
        ((c I*rowWeight η m A 1 t I)*star (c J*rowWeight η m A 1 t J))*
          (((K/‖ringComplex (sourceGenerator S I*sourceGenerator S J)‖^2:ℝ):ℂ)*
            ∑' h : O,pairFourier (sourceGenerator S I) (sourceGenerator S J)
              (sourceGenerator_supported S I) (sourceGenerator_supported S J) h*
              SchwartzPlanePoisson.paperRadialFourier W
                (K*‖ringComplex h‖^2/
                  ‖ringComplex (sourceGenerator S I*sourceGenerator S J)‖^2)) := by
  rw [finiteHeckeEnergy_eq η m A t hmLam hm2 S c W K]
  exact rowEnergy_poisson Finset.univ (sourceGenerator S)
    (fun I : supportedColumns S => c I*rowWeight η m A 1 t I)
    (sourceGenerator_supported S) W K hK

end CenteredMomentSourceRow

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
local notation "O" => Eisenstein.O
namespace CenteredMomentPoisson
open Eisenstein  SchwartzPlanePoisson CubicEisenstein
open CenteredMomentCorrelation CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
open CenteredMomentFourier

theorem full_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finiteEisensteinQuotientOfNonzero hu
    letI := finiteEisensteinQuotientOfNonzero hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, residueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖ringComplex z‖ ^ 2 / K)) =
      (K : ℂ) * ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (u * v)‖ ^ 2) := by
  let := finiteEisensteinQuotientOfNonzero hu
  let := finiteEisensteinQuotientOfNonzero hv
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero hu hv)
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let : Fintype (Residue (u * v)) := Fintype.ofFinite _
  let P := fun h : Residue (u * v) =>
    residueGauss u hu χu (frequencyReduction u (u * v) (dvd_mul_right u v) h) *
      star (residueGauss v hv χv (frequencyReduction v (u * v) (dvd_mul_left v u) h))
  have hcoeff (j : O) :
      (∑ r : Residue (u * v), P r * residueTraceQuotientChar 1 (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) =
      (Fintype.card (Residue (u * v)) : ℂ) * fullModulusCorrelation u v χu χv (-j) := by
    have ht := actual_gauss_correlation u v hu hv χu χv (-j)
    have heq (r : Residue (u * v)) : -(r * Ideal.Quotient.mk _ (-j)) =
        Ideal.Quotient.mk _ j * r := by
      simp only [map_neg, mul_neg, neg_neg]
      exact mul_comm _ _
    simp_rw [heq] at ht
    exact ht
  have hcard : (Fintype.card (Residue (u * v)) : ℂ) = (‖ringComplex (u * v)‖ ^ 2 : ℝ) := by
    rw [ringComplex_norm_sq_eq_absNorm_span, Ideal.absNorm_apply,
      Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
    norm_cast
  have hpoisson := actual_radial_poisson_trace W K hK (u * v) (mul_ne_zero hu hv) P
  change (∑' z : O, P (Ideal.Quotient.mk _ z) * W (‖ringComplex z‖ ^ 2 / K)) =
    (K / ‖ringComplex (u * v)‖ ^ 2 : ℝ) •
      ∑' j : O, (∑ r : Residue (u * v), P r * residueTraceQuotientChar 1 (u * v) (mul_ne_zero hu hv)
        (Ideal.Quotient.mk _ j * r)) *
          paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (u * v)‖ ^ 2) at hpoisson
  simp only [P, frequencyReduction_mk] at hpoisson ⊢
  rw [hpoisson]
  change (K / ‖ringComplex (u * v)‖ ^ 2 : ℝ) •
    (∑' j : O, (∑ r : Residue (u * v), P r * residueTraceQuotientChar 1 (u * v) (mul_ne_zero hu hv)
      (Ideal.Quotient.mk _ j * r)) *
      paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (u * v)‖ ^ 2)) = _
  simp_rw [hcoeff, hcard, mul_assoc]
  rw [tsum_mul_left, Complex.real_smul, Complex.ofReal_div, ← mul_assoc]
  have hn : (‖ringComplex (u * v)‖ ^ 2 : ℂ) ≠ 0 := by
    exact pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr
      (ringComplex_ne_zero (mul_ne_zero hu hv))))
  rw [Complex.ofReal_pow, div_mul_cancel₀ _ hn]

theorem normalized_gauss_pair_poisson (u v : O) (hu : u ≠ 0) (hv : v ≠ 0)
    (χu : MulChar (Residue u) ℂ) (χv : MulChar (Residue v) ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    letI := finiteEisensteinQuotientOfNonzero hu
    letI := finiteEisensteinQuotientOfNonzero hv
    letI : Fintype (Residue u) := Fintype.ofFinite _
    letI : Fintype (Residue v) := Fintype.ofFinite _
    (∑' z : O, normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
      star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖ringComplex z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, fullModulusCorrelation u v χu χv (-j) *
        paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (u * v)‖ ^ 2) := by
  let := finiteEisensteinQuotientOfNonzero hu
  let := finiteEisensteinQuotientOfNonzero hv
  let : Fintype (Residue u) := Fintype.ofFinite _
  let : Fintype (Residue v) := Fintype.ofFinite _
  let ru : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ)
  let rv : ℂ := Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ)
  have hterm (z : O) :
      normalizedResidueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (normalizedResidueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖ringComplex z‖ ^ 2 / K) =
      (ru * rv)⁻¹ * (residueGauss u hu χu (Ideal.Quotient.mk _ z) *
        star (residueGauss v hv χv (Ideal.Quotient.mk _ z)) * W (‖ringComplex z‖ ^ 2 / K)) := by
    simp only [normalizedResidueGauss, star_div₀, Complex.star_def, Complex.conj_ofReal]
    dsimp only [ru, rv]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, full_gauss_pair_poisson u v hu hv χu χv W K hK]
  dsimp only [ru, rv]
  ring

theorem sextic_gauss_pair_poisson (u v : O)
    (hu : CanonicalQuadraticSieve.Supported (Ideal.span {u}))
    (hv : CanonicalQuadraticSieve.Supported (Ideal.span {v}))
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    (∑' z : O,
      (ProbePhysical.sexticGauss u (supported_element_ne_zero u hu) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ)) *
      star (ProbePhysical.sexticGauss v (supported_element_ne_zero v hv) z /
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ)) * W (‖ringComplex z‖ ^ 2 / K)) =
      ((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {u}) : ℝ) : ℂ) *
        (Real.sqrt (Ideal.absNorm (Ideal.span {v}) : ℝ) : ℂ))) *
      ∑' j : O, actualCorrelation u v hu hv (-j) *
        paperRadialFourier W (K * ‖ringComplex j‖ ^ 2 / ‖ringComplex (u * v)‖ ^ 2) := by
  have h := normalized_gauss_pair_poisson u v
    (supported_element_ne_zero u hu) (supported_element_ne_zero v hv)
    (supportedModulusCharacter u hu) (supportedModulusCharacter v hv) W K hK
  simpa only [normalizedResidueGauss, residueGauss_supported_mk, actualCorrelation,
    supportedCorrelation] using h

end CenteredMomentPoisson
end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical SchwartzMap
namespace CenteredMomentGaussEnergy
open Eisenstein  SchwartzPlanePoisson
open CanonicalQuadraticSieve CenteredMomentFourier CenteredMomentPoisson
open CenteredMomentCommonSupport CenteredMomentSupportedCorrelation
local notation "O" => Eisenstein.O

def gaussRow (a : O) (ha : Supported (Ideal.span {a})) (z : O) : ℂ :=
  ProbePhysical.sexticGauss a (supported_element_ne_zero a ha) z /
    (Real.sqrt (Ideal.absNorm (Ideal.span {a}) : ℝ) : ℂ)

theorem gaussRow_pair_summable (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => gaussRow a ha z * star (gaussRow b hb z) *
      W (‖ringComplex z‖ ^ 2 / K)) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  let P : Residue (a * b) → ℂ := fun x =>
    normalizedResidueGauss a (supported_element_ne_zero a ha)
      (supportedModulusCharacter a ha) (frequencyReduction a (a * b) (dvd_mul_right a b) x) *
    star (normalizedResidueGauss b (supported_element_ne_zero b hb)
      (supportedModulusCharacter b hb) (frequencyReduction b (a * b) (dvd_mul_left b a) x))
  have hs := actual_eisenstein_periodic_summable (scaledRadialTest W K hK)
    (Ideal.Quotient.mk (Ideal.span {a * b})) P
  simpa only [P, frequencyReduction_mk, normalizedResidueGauss,
    residueGauss_supported_mk, scaledRadialTest_apply, gaussRow] using hs

def gaussPolynomial {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) : ℂ :=
  ∑ i ∈ S, c i * gaussRow (a i) (ha i) z

def gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) : ℂ :=
  ∑' z : O, ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
    W (‖ringComplex z‖ ^ 2 / K)

theorem gaussPolynomial_norm_sq {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ) (z : O) :
    ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) := by
  rw [Complex.ofReal_pow, ← Complex.mul_conj']
  simp only [gaussPolynomial, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum,
    Complex.star_def]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem gaussEnergy_expand {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        ∑' z : O, (gaussRow (a i) (ha i) z * star (gaussRow (a j) (ha j) z)) *
          W (‖ringComplex z‖ ^ 2 / K) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussEnergy, gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  rw [Summable.tsum_finsetSum (fun i _ => (hasSum_sum (fun j _ => (hs i j).hasSum)).summable)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Summable.tsum_finsetSum (fun j _ => hs i j)]
  simp only [tsum_mul_left]

theorem gaussEnergy_summable {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    Summable (fun z : O => ((‖gaussPolynomial S a ha c z‖ ^ 2 : ℝ) : ℂ) *
      W (‖ringComplex z‖ ^ 2 / K)) := by
  have hs (i j : α) := (gaussRow_pair_summable (a i) (a j) (ha i) (ha j) W K hK).mul_left
    (c i * star (c j))
  simp only [mul_assoc] at hs
  simp only [gaussPolynomial_norm_sq, Finset.sum_mul, mul_assoc]
  exact (hasSum_sum (fun i _ =>
    (hasSum_sum (fun j _ => (hs i j).hasSum)))).summable

theorem finite_energy_le_gaussEnergy {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) (rows : Finset O)
    (hW : ∀ z : O, 0 ≤ (W (‖ringComplex z‖ ^ 2 / K)).re)
    (hmajor : ∀ z ∈ rows, 1 ≤ (W (‖ringComplex z‖ ^ 2 / K)).re) :
    (∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2) ≤
      (gaussEnergy S a ha c W K).re := by
  have hs := Complex.hasSum_re (gaussEnergy_summable S a ha c W K hK).hasSum
  change HasSum _ (gaussEnergy S a ha c W K).re at hs
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hs
  calc
    _ ≤ ∑ z ∈ rows, ‖gaussPolynomial S a ha c z‖ ^ 2 *
        (W (‖ringComplex z‖ ^ 2 / K)).re := by
      apply Finset.sum_le_sum
      intro z hz
      exact le_mul_of_one_le_right (sq_nonneg _) (hmajor z hz)
    _ ≤ _ := sum_le_hasSum rows (fun z _ => mul_nonneg (sq_nonneg _) (hW z)) hs

theorem gaussEnergy_poisson {α : Type*} (S : Finset α) (a : α → O)
    (ha : ∀ i, Supported (Ideal.span {a i})) (c : α → ℂ)
    (W : 𝓢(ℝ, ℂ)) (K : ℝ) (hK : 0 < K) :
    gaussEnergy S a ha c W K =
      ∑ i ∈ S, ∑ j ∈ S, (c i * star (c j)) *
        (((K : ℂ) / ((Real.sqrt (Ideal.absNorm (Ideal.span {a i}) : ℝ) : ℂ) *
          (Real.sqrt (Ideal.absNorm (Ideal.span {a j}) : ℝ) : ℂ))) *
          ∑' h : O, actualCorrelation (a i) (a j) (ha i) (ha j) (-h) *
            paperRadialFourier W
              (K * ‖ringComplex h‖ ^ 2 / ‖ringComplex (a i * a j)‖ ^ 2)) := by
  rw [gaussEnergy_expand S a ha c W K hK]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  simp only [gaussRow]
  rw [sextic_gauss_pair_poisson (a i) (a j) (ha i) (ha j) W K hK]

end CenteredMomentGaussEnergy

end

end

noncomputable section
open Eisenstein CubicJacobi CubicRamified CompletedGauss CanonicalRowCompletion SchwartzPlanePoisson


noncomputable section
open scoped BigOperators Classical
namespace CenteredMomentZeroMode
open Eisenstein CanonicalRowCompletion CanonicalQuadraticSieve
open  CubicEisenstein
open CenteredMomentRowNorm CenteredMomentCorrelation CenteredMomentCommonSupport
open CenteredMomentSupportedCorrelation CenteredMomentFourier
open UniqueFactorizationMonoid CenteredExceptionalCount CenteredExceptionalProfile
local notation "O" => Eisenstein.O

@[simp] theorem pairResidue_mul (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (x y : Residue (a * b)) :
    pairResidue a b ha hb (x * y) =
      pairResidue a b ha hb x * pairResidue a b ha hb y := by
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_mul, pairResidue_mk, pairResidue_mk, pairResidue_mk,
    idealRowHom_argument_mul, idealRowHom_argument_mul, star_mul]
  ring

@[simp] theorem pairFourier_zero (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    pairFourier a b ha hb 0 = ∑' x : Residue (a * b), pairResidue a b ha hb x := by
  simp only [pairFourier, map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one]

theorem pairResidue_unit_eq_one_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (u : (Residue (a * b))ˣ) :
    pairResidue a b ha hb u = 1 := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype] at hm
  have he : pairResidue a b ha hb u * (∑ x : Residue (a * b), pairResidue a b ha hb x) =
      ∑ x : Residue (a * b), pairResidue a b ha hb x := by
    simpa only [Finset.mul_sum, pairResidue_mul] using
      u.mulLeft_bijective.sum_comp (pairResidue a b ha hb)
  exact (mul_right_cancel₀ hm (he.trans (one_mul _).symm))

theorem rows_agree_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (n : O)
    (hn : IsCoprime (Ideal.span {n}) (Ideal.span {a} * Ideal.span {b})) :
    idealRowHom n (Ideal.span {a}) = idealRowHom n (Ideal.span {b}) := by
  have hunit : IsUnit (Ideal.Quotient.mk (Ideal.span {a * b}) n) := by
    apply (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr
    simpa only [Ideal.span_singleton_mul_span_singleton] using hn
  have he := pairResidue_unit_eq_one_of_mean_ne_zero a b ha hb hm hunit.unit
  rw [hunit.unit_spec, pairResidue_mk] at he
  let := finiteEisensteinQuotientOfNonzero (supported_element_ne_zero b hb)
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {b}) n) :=
    (IdealCharacter.isUnit_mk_iff_isCoprime _ _).mpr hn.of_mul_right_right
  have hj : idealRowHom n (Ideal.span {b}) * star (idealRowHom n (Ideal.span {b})) = 1 := by
    change supportedModulusCharacter b hb (Ideal.Quotient.mk _ n) *
      star (supportedModulusCharacter b hb (Ideal.Quotient.mk _ n)) = 1
    rw [MulChar.star_apply', ← MulChar.mul_apply, mul_inv_cancel]
    exact MulChar.one_apply hu
  exact mul_right_cancel₀ (by intro hz; simp [hz] at hj) (he.trans hj.symm)

theorem valuation_profile_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) (P : Ideal O) [P.IsMaximal]
    (hg : lambda ∉ P)
    (hodd : ringChar (O ⧸ P) ≠ 2) :
    valuation (Ideal.span {a}) P % 6 = valuation (Ideal.span {b}) P % 6 := by
  apply valuation_mod_six_of_unit_agreement 1
    (Ideal.span {a} * Ideal.span {b}) _ _ P (mul_ne_zero ha.1 hb.1) ha hb
    hg hodd isCoprime_one_left
  intro n _ hn
  exact rows_agree_of_mean_ne_zero a b ha hb hm n hn

theorem powerful_product_of_mean_ne_zero (a b : O)
    (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b}))
    (hm : pairFourier a b ha hb 0 ≠ 0) :
    CompletedGauss.PowerfulIdeal (Ideal.span {a} * Ideal.span {b}) := by
  have hs := (supported_mul_iff _ _).mpr ⟨ha, hb⟩
  refine ⟨hs.1, ?_⟩
  intro P hP
  obtain ⟨hmax, hg, hodd⟩ := CanonicalQuadraticSieve.supported_factors_good _ hs P hP
  let := hmax
  have he := valuation_profile_of_mean_ne_zero a b ha hb hm P hg hodd
  have hp := Multiset.count_pos.mpr hP
  rw [normalizedFactors_mul ha.1 hb.1, Multiset.count_add] at hp ⊢
  unfold valuation at he
  omega

theorem powerful_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O × Ideal O)) (Y : ℝ), 1 ≤ Y →
      (∀ p ∈ S, CompletedGauss.PowerfulIdeal (p.1 * p.2) ∧
        (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ Y) →
      (S.card : ℝ) ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hp⟩ := CompletedGauss.powerful_ideal_count (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) (by positivity)
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro S Y hY hS
  let T := S.image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hT (I : Ideal O) (hI : I ∈ T) :
      CompletedGauss.PowerfulIdeal I ∧ (Ideal.absNorm I : ℝ) ≤ Y := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    exact hS p hp
  have hcard : (S.card : ℝ) = ∑ I ∈ T,
      ((S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card : ℝ) := by
    calc
      _ = ∑ _p ∈ S, (1 : ℝ) := by simp
      _ = ∑ I ∈ T, ∑ _p ∈ S.filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), (1 : ℝ) :=
        (Finset.sum_fiberwise_of_maps_to (fun p hp =>
          Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp) _).symm
      _ = _ := by simp
  rw [hcard]
  calc
    _ ≤ ∑ I ∈ T, D * Y ^ (ε / 2) := by
      apply Finset.sum_le_sum
      intro I hI
      calc
        _ ≤ ((idealDivisors I).card : ℝ) := by
          exact_mod_cast CompletedGauss.product_fiber_card S I (hT I hI).1.1
        _ ≤ D * (Ideal.absNorm I : ℝ) ^ (ε / 2) := hd I (hT I hI).1.1
        _ ≤ D * Y ^ (ε / 2) := mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow (Nat.cast_nonneg _) (hT I hI).2 (by positivity)) hD.le
    _ = (T.card : ℝ) * (D * Y ^ (ε / 2)) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε / 2)) * (D * Y ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_right (hp T Y hY hT) (by positivity)
    _ = (C * D) * (Y ^ (1 / 2 + ε / 2) * Y ^ (ε / 2)) := by ring
    _ = (C * D) * Y ^ (1 / 2 + ε) := by
      rw [← Real.rpow_add (by linarith : 0 < Y)]
      congr 2
      ring

theorem pairFourier_zero_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) :
    ‖pairFourier a b ha hb 0‖ ≤ (Ideal.absNorm (Ideal.span {a * b}) : ℝ) := by
  let := finiteEisensteinQuotientOfNonzero (mul_ne_zero (supported_element_ne_zero a ha)
    (supported_element_ne_zero b hb))
  let : Fintype (Residue (a * b)) := Fintype.ofFinite _
  rw [pairFourier_zero, tsum_fintype]
  calc
    _ ≤ ∑ x : Residue (a * b), ‖pairResidue a b ha hb x‖ := norm_sum_le _ _
    _ ≤ ∑ _x : Residue (a * b), (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro x _
      obtain ⟨n, rfl⟩ := Ideal.Quotient.mk_surjective x
      rw [pairResidue_mk, norm_mul, norm_star]
      exact (mul_le_of_le_one_left (norm_nonneg _) (idealRowHom_norm _ _)).trans
        (idealRowHom_norm _ _)
    _ = _ := by simp [Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

theorem scaled_zero_mean_norm_le (a b : O) (ha : Supported (Ideal.span {a}))
    (hb : Supported (Ideal.span {b})) (K : ℝ) (hK : 0 ≤ K) :
    ‖((K / ‖ringComplex (a * b)‖ ^ 2 : ℝ) : ℂ) * pairFourier a b ha hb 0‖ ≤ K := by
  have hn : (0 : ℝ) < Ideal.absNorm (Ideal.span {a * b}) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr (mul_ne_zero
        (supported_element_ne_zero a ha) (supported_element_ne_zero b hb))))
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    ringComplex_norm_sq_eq_absNorm_span, abs_of_nonneg (div_nonneg hK hn.le)]
  calc
    _ ≤ (K / (Ideal.absNorm (Ideal.span {a * b}) : ℝ)) *
        (Ideal.absNorm (Ideal.span {a * b}) : ℝ) :=
      mul_le_mul_of_nonneg_left (pairFourier_zero_norm_le a b ha hb) (div_nonneg hK hn.le)
    _ = K := div_mul_cancel₀ _ hn.ne'

theorem nonzero_mean_pair_count (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (Y : ℝ), 1 ≤ Y →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      ((S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)).card : ℝ)
        ≤ C * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := powerful_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb Y hY hinj hN
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  let f := fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})
  have hf : Set.InjOn f (T : Set (α × β)) := by
    intro p hp q hq he
    exact hinj (Finset.mem_filter.mp hp).1 (Finset.mem_filter.mp hq).1 he
  have ht : (T.image f).card = T.card := Finset.card_image_of_injOn hf
  have hbound := hc (T.image f) Y hY (by
    intro I hI
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hI
    have hp' := Finset.mem_filter.mp hp
    exact ⟨powerful_product_of_mean_ne_zero (a p.1) (b p.2) (ha p.1) (hb p.2) hp'.2,
      hN p hp'.1⟩)
  simpa only [ht] using hbound

theorem first_zero_sum_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ {α β : Type*} (S : Finset (α × β))
      (a : α → O) (b : β → O)
      (ha : ∀ i, Supported (Ideal.span {a i}))
      (hb : ∀ j, Supported (Ideal.span {b j})) (d : α × β → ℂ)
      (Y K B : ℝ), 1 ≤ Y → 0 ≤ K → 0 ≤ B →
      Set.InjOn (fun p : α × β => (Ideal.span {a p.1}, Ideal.span {b p.2})) S →
      (∀ p ∈ S, (Ideal.absNorm (Ideal.span {a p.1} * Ideal.span {b p.2}) : ℝ) ≤ Y) →
      (∀ p ∈ S, ‖d p‖ ≤ B) →
      ‖∑ p ∈ S, d p * (((K / ‖ringComplex (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ ≤
        C * K * B * Y ^ (1 / 2 + ε) := by
  obtain ⟨C, hC, hc⟩ := nonzero_mean_pair_count ε hε
  refine ⟨C, hC, ?_⟩
  intro α β S a b ha hb d Y K B hY hK hB hinj hN hd
  let T := S.filter (fun p : α × β => pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 ≠ 0)
  have hsum : (∑ p ∈ S, d p * (((K / ‖ringComplex (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)) =
      ∑ p ∈ T, d p * (((K / ‖ringComplex (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0) := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro p hp hpt
    have hz : pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0 = 0 := by
      simpa only [T, Finset.mem_filter, hp, true_and, not_not] using hpt
    rw [hz, mul_zero, mul_zero]
  rw [hsum]
  calc
    _ ≤ ∑ p ∈ T, ‖d p * (((K / ‖ringComplex (a p.1 * b p.2)‖ ^ 2 : ℝ) : ℂ) *
        pairFourier (a p.1) (b p.2) (ha p.1) (hb p.2) 0)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ T, B * K := by
      apply Finset.sum_le_sum
      intro p hp
      rw [norm_mul]
      exact mul_le_mul (hd p (Finset.mem_filter.mp hp).1)
        (scaled_zero_mean_norm_le _ _ _ _ K hK) (norm_nonneg _) hB
    _ = (T.card : ℝ) * (B * K) := by simp
    _ ≤ (C * Y ^ (1 / 2 + ε)) * (B * K) :=
      mul_le_mul_of_nonneg_right (hc S a b ha hb Y hY hinj hN) (mul_nonneg hB hK)
    _ = C * K * B * Y ^ (1 / 2 + ε) := by ring

theorem productColumnCoefficient_sextic_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    (∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)) =
      ∑ K ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2),
        CompletedGauss.productColumnCoefficient S T β K * idealRowHom z K := by
  rw [← Finset.sum_product (f := fun p : Ideal O × Ideal O =>
    β p.1 p.2 * idealRowHom z (p.1 * p.2))]
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p ∈ S ×ˢ T) => Finset.mem_image_of_mem (fun p : Ideal O × Ideal O => p.1 * p.2) hp)]
  apply Finset.sum_congr rfl
  intro K hK
  rw [CompletedGauss.productColumnCoefficient, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem productColumnCoefficient_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ),
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ 1) →
      ∀ (I : Ideal O) (X : ℝ), I ≠ 0 → (Ideal.absNorm I : ℝ) ≤ X →
        ‖CompletedGauss.productColumnCoefficient S T β I‖ ≤ D * X ^ ε := by
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨D, hD, ?_⟩
  intro S T β hβ I X hI hX
  exact (CompletedGauss.productColumnCoefficient_norm S T β hβ I hI).trans
    ((hd I hI).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) hX hε.le) hD.le))

def idealColumn (S : Finset (Ideal O)) (I : S) : O :=
  cubicIdealGenerator I.val

@[simp] theorem idealColumn_span (S : Finset (Ideal O)) (I : S) :
    Ideal.span {idealColumn S I} = I.val :=
  span_cubicIdealGenerator _

theorem idealColumn_supported (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (I : S) :
    Supported (Ideal.span {idealColumn S I}) := by
  rw [idealColumn_span]
  exact hS I.val I.property

def idealZeroEnergy (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
    (c : Ideal O → ℂ) (K : ℝ) : ℂ :=
  ∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
    (((K / ‖ringComplex (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
      pairFourier (idealColumn S I) (idealColumn S J)
        (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0)

theorem ideal_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Finset (Ideal O)) (hS : ∀ I ∈ S, Supported I)
      (c : Ideal O → ℂ) (X K B : ℝ), 1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, (Ideal.absNorm I : ℝ) ≤ X) →
      (∀ I ∈ S, ‖c I‖ ≤ B) →
      ‖idealZeroEnergy S hS c K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := first_zero_sum_bound (ε / 2) (by positivity)
  refine ⟨C, hC, ?_⟩
  intro S hS c X K B hX hK hB hN hd
  have hinj : Set.InjOn (fun p : S × S =>
      (Ideal.span {idealColumn S p.1}, Ideal.span {idealColumn S p.2}))
        (↑(Finset.univ : Finset (S × S)) : Set (S × S)) := by
    intro p _ q _ he
    apply Prod.ext
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.fst he)
    · exact Subtype.ext (by simpa only [idealColumn_span] using congrArg Prod.snd he)
  have hNpair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      (Ideal.absNorm (Ideal.span {idealColumn S p.1} * Ideal.span {idealColumn S p.2}) : ℝ) ≤ X ^ 2 := by
    rw [idealColumn_span, idealColumn_span, map_mul, Nat.cast_mul, pow_two]
    exact mul_le_mul (hN _ p.1.property) (hN _ p.2.property) (Nat.cast_nonneg _) (by linarith)
  have hdPair (p : S × S) (_hp : p ∈ (Finset.univ : Finset (S × S))) :
      ‖c p.1.val * star (c p.2.val)‖ ≤ B ^ 2 := by
    rw [norm_mul, norm_star, pow_two]
    exact mul_le_mul (hd _ p.1.property) (hd _ p.2.property) (norm_nonneg _) hB
  have hh := hc Finset.univ (idealColumn S) (idealColumn S)
    (idealColumn_supported S hS) (idealColumn_supported S hS)
    (fun p : S × S => c p.1.val * star (c p.2.val)) (X ^ 2) K (B ^ 2)
    (by nlinarith) hK (sq_nonneg _) hinj hNpair hdPair
  have hp : (X ^ 2) ^ (1 / 2 + ε / 2 : ℝ) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ X)]
    congr 1
    ring
  simpa only [idealZeroEnergy, Fintype.sum_prod_type, hp] using hh

theorem productColumnCoefficient_norm_le (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (B : ℝ) (hB : 0 ≤ B)
    (hβ : ∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) (I : Ideal O) (hI : I ≠ 0) :
    ‖CompletedGauss.productColumnCoefficient S T β I‖ ≤ B * (idealDivisors I).card := by
  unfold CompletedGauss.productColumnCoefficient
  calc
    _ ≤ ∑ p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), ‖β p.1 p.2‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ (S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I), B := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = B * ((S ×ˢ T).filter (fun p : Ideal O × Ideal O => p.1 * p.2 = I)).card := by simp [mul_comm]
    _ ≤ _ := mul_le_mul_of_nonneg_left (by exact_mod_cast CompletedGauss.product_fiber_card (S ×ˢ T) I hI) hB

theorem productColumns_supported (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J) :
    ∀ I ∈ (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2), Supported I := by
  intro I hI
  obtain ⟨⟨J, K⟩, hp, rfl⟩ := Finset.mem_image.mp hI
  have hh := Finset.mem_product.mp hp
  exact (supported_mul_iff J K).mpr ⟨hS J hh.1, hT K hh.2⟩

def productZeroEnergy (S T : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
    (β : Ideal O → Ideal O → ℂ) (K : ℝ) : ℂ :=
  idealZeroEnergy ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (productColumns_supported S T hS hT) (CompletedGauss.productColumnCoefficient S T β) K

theorem product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖productZeroEnergy S T hS hT β K‖ ≤ C * K * B ^ 2 * X ^ (1 + ε) := by
  obtain ⟨C, hC, hc⟩ := ideal_zero_energy_bound (ε / 2) (by positivity)
  obtain ⟨D, hD, hd⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 4) (by positivity)
  refine ⟨C * D ^ 2, by positivity, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
  have hs := productColumns_supported S T hS hT
  have hn (I : Ideal O) (hI : I ∈ P) : (Ideal.absNorm I : ℝ) ≤ X := by
    obtain ⟨⟨J, L⟩, hp, rfl⟩ := Finset.mem_image.mp hI
    have hh := Finset.mem_product.mp hp
    exact hN J hh.1 L hh.2
  have hb (I : Ideal O) (hI : I ∈ P) :
      ‖CompletedGauss.productColumnCoefficient S T β I‖ ≤ B * (D * X ^ (ε / 4)) := by
    apply (productColumnCoefficient_norm_le S T β B hB hβ I (hs I hI).1).trans
    apply mul_le_mul_of_nonneg_left _ hB
    exact (hd I (hs I hI).1).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hn I hI) (by positivity)) hD.le)
  have hh := hc P hs (CompletedGauss.productColumnCoefficient S T β) X K (B * (D * X ^ (ε / 4)))
    hX hK (by positivity) hn hb
  change ‖productZeroEnergy S T hS hT β K‖ ≤ _ at hh
  apply hh.trans_eq
  have hx0 : 0 < X := by linarith
  have hp : (X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2) = X ^ (1 + ε) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
    congr 1
    ring
  calc
    C * K * (B * (D * X ^ (ε / 4))) ^ 2 * X ^ (1 + ε / 2) =
        (C * D ^ 2) * K * B ^ 2 * ((X ^ (ε / 4)) ^ 2 * X ^ (1 + ε / 2)) := by ring
    _ = _ := by rw [hp]

theorem normalized_product_zero_energy_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) * productZeroEnergy S T hS hT β K‖ ≤
        C * K * B ^ 2 * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β X K B hX hK hB hN hβ
  have hx0 : 0 < X := by linarith
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hx0)]
  calc
    _ ≤ X⁻¹ * (C * K * B ^ 2 * X ^ (1 + ε)) :=
      mul_le_mul_of_nonneg_left (hc S T hS hT β X K B hX hK hB hN hβ) (by positivity)
    _ = C * K * B ^ 2 * X ^ ε := by
      rw [Real.rpow_add hx0, Real.rpow_one]
      field_simp

theorem aggregated_rowPolynomial (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (z : O) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    rowPolynomial Finset.univ (idealColumn P)
      (fun I : P => CompletedGauss.productColumnCoefficient S T β I.val) z =
      ∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J) := by
  dsimp only
  rw [rowPolynomial]
  simp only [idealColumn_span]
  rw [Finset.sum_coe_sort ((S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2))
    (fun I : Ideal O => CompletedGauss.productColumnCoefficient S T β I * idealRowHom z I)]
  exact (productColumnCoefficient_sextic_row_sum S T β z).symm

theorem aggregated_rowEnergy (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    let P := (S ×ˢ T).image (fun p : Ideal O × Ideal O => p.1 * p.2)
    CenteredMomentRowNorm.rowEnergy Finset.univ (idealColumn P)
      (fun I : P => CompletedGauss.productColumnCoefficient S T β I.val) W K =
      ∑' z : O, ((‖∑ I ∈ S, ∑ J ∈ T, β I J * idealRowHom z (I * J)‖ ^ 2 : ℝ) : ℂ) *
        W (‖ringComplex z‖ ^ 2 / K) := by
  simp only [CenteredMomentRowNorm.rowEnergy, aggregated_rowPolynomial]

theorem idealZeroEnergy_first_frequency (S : Finset (Ideal O))
    (hS : ∀ I ∈ S, Supported I) (c : Ideal O → ℂ)
    (W : SchwartzMap ℝ ℂ) (K : ℝ) :
    (∑ I : S, ∑ J : S, (c I.val * star (c J.val)) *
      (((K / ‖ringComplex (idealColumn S I * idealColumn S J)‖ ^ 2 : ℝ) : ℂ) *
        (pairFourier (idealColumn S I) (idealColumn S J)
          (idealColumn_supported S hS I) (idealColumn_supported S hS J) 0 *
          SchwartzPlanePoisson.paperRadialFourier W
            (K * ‖ringComplex (0 : O)‖ ^ 2 /
              ‖ringComplex (idealColumn S I * idealColumn S J)‖ ^ 2)))) =
      idealZeroEnergy S hS c K * SchwartzPlanePoisson.paperRadialFourier W 0 := by
  simp [idealZeroEnergy, Finset.sum_mul, mul_assoc]

theorem normalized_product_zero_mode_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S T : Finset (Ideal O))
      (hS : ∀ I ∈ S, Supported I) (hT : ∀ J ∈ T, Supported J)
      (β : Ideal O → Ideal O → ℂ) (W : SchwartzMap ℝ ℂ) (X K B : ℝ),
      1 ≤ X → 0 ≤ K → 0 ≤ B →
      (∀ I ∈ S, ∀ J ∈ T, (Ideal.absNorm (I * J) : ℝ) ≤ X) →
      (∀ I ∈ S, ∀ J ∈ T, ‖β I J‖ ≤ B) →
      ‖((X⁻¹ : ℝ) : ℂ) *
        (productZeroEnergy S T hS hT β K * SchwartzPlanePoisson.paperRadialFourier W 0)‖ ≤
        C * K * B ^ 2 * ‖SchwartzPlanePoisson.paperRadialFourier W 0‖ * X ^ ε := by
  obtain ⟨C, hC, hc⟩ := normalized_product_zero_energy_bound ε hε
  refine ⟨C, hC, ?_⟩
  intro S T hS hT β W X K B hX hK hB hN hβ
  rw [← mul_assoc, norm_mul]
  calc
    _ ≤ (C * K * B ^ 2 * X ^ ε) * ‖SchwartzPlanePoisson.paperRadialFourier W 0‖ :=
      mul_le_mul_of_nonneg_right (hc S T hS hT β X K B hX hK hB hN hβ) (norm_nonneg _)
    _ = _ := by ring

end CenteredMomentZeroMode

end

end

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
