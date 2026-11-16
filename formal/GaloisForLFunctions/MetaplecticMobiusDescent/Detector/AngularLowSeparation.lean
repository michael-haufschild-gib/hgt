import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.AngularPhysicalInverseSource

/-!
# Separating the low physical angular source

The finite physical-ray decomposition leaves the angular source intact. Mellin
separation acts on the original radial weights; exact slot splitting includes the
conjugate angular compensation factors in the selected inverse polynomial.
-/

noncomputable section
open MeasureTheory Set
open scoped Classical BigOperators ContDiff SchwartzMap
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified CompletedGauss CanonicalRowCompletion
open SchwartzPlanePoisson
namespace ProbePhysical
open ProbeRow ProbeCompleted HeckeIdealSeries CanonicalQuadraticSieve RayFourExpansion
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def angularCompensationRowTest (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character) (C : CalibrationData)
    (W0 W1 : ℝ→ℂ) (p : Fin K→ O) (J : Finset (Fin K)) (X Y T t : ℝ) : ℂ :=
  ∑'r : PhysicalRowIndex,
    physicalRowWeight C W0 W1 (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J)) r*
      correctedCompletedT C.excluded (Ideal.span {slotProduct p (Finset.univ\J)})
        (angularSourceTwist ℓ (physicalRowMonoid η C r)) (CompletedHeight.normTwistedSource gaussianFixedWindow t) T

theorem angularCompensationRowTest_low_separated (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→ O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0< X) (hY : 0< Y) (hT : 0< T) :
    angularCompensationRowTest ℓ η (calibrationForSet S hS) W0 W1 p J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
          (angularLowMarkedInverseRow ℓ η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t) v := by
  unfold angularCompensationRowTest
  simp_rw [physicalRowMonoid_eq_ray]
  have hC : (calibrationForSet S hS).excluded=S := calibrationForSet_excluded S hS
  rw [hC]
  simp_rw [angularLowMarkedInverseRow_eq ℓ η S hS hbad _ T t hT]
  exact physicalRowWeight_low_separated (calibrationForSet S hS) W0 W1 a0 b0 a1 b1 ha0 ha1
    hW0 hW1 hWs _ _ (div_pos hX (slotProduct_norm_pos p hp J))
      (div_pos hY (slotProduct_norm_pos p hp J))
      (angularLowMarkedInverseRow ℓ η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)

lemma angularCompensationRowTest_low_integrable (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (p : Fin K→ O) (hp : ∀i,p i≠0) (J : Finset (Fin K))
    (X Y T t : ℝ) (hX : 0< X) (hY : 0< Y) :
    Integrable (lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
      (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (angularLowMarkedInverseRow ℓ η S hS (Ideal.span {slotProduct p (Finset.univ\J)}) T t)) := by
  exact lowSeparatedIntegrand_integrable (calibrationForSet S hS) W0 W1 _ a0 b0 ha0 hW0 hWs
    (HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1)
    (lowOuterCutoff_compact _ _ (mul_pos ha0 ha1) (lt_of_lt_of_le (by norm_num) (le_max_left _ _)))
    (lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)) _ _
    (div_pos hX (slotProduct_norm_pos p hp J)) (div_pos hY (slotProduct_norm_pos p hp J)) _

lemma angularCompensationRowTest_join_low (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→ Finset O) (hslots : ∀i x,x∈slots i→ x≠0)
    (J : Finset (Fin K)) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J)
    (X Y T t : ℝ) (hX : 0< X) (hY : 0< Y) (hT : 0< T) :
    angularCompensationRowTest ℓ η (calibrationForSet S hS) W0 W1 (lowSlotJoin slots J a b) J X Y T t=
      (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ)*
        ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (angularLowMarkedInverseRow ℓ η S hS (lowSelectedIdeal slots J b) T t) v := by
  simpa only [lowSlotJoin_unselectedProduct,lowSlotJoin_selectedProduct,lowSelectedIdeal] using
    angularCompensationRowTest_low_separated ℓ η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
      (lowSlotJoin slots J a b) (lowSlotJoin_nonzero slots hslots J a b) J X Y T t hX hY hT

theorem angular_compensation_tuple_low_polynomial (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (W0 W1 : ℝ→ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0< a0) (ha1 : 0< a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (hWs : ContDiff ℝ ∞ W0) (slots : Fin K→ Finset O) (hslots : ∀i x,x∈slots i→ x≠0)
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ)
    (X Y T t : ℝ) (hX : 0< X) (hY : 0< Y) (hT : 0< T) :
    (∑p : (∀i,↥(slots i)),angularCompensationSubsetWeight ℓ η W P (fun i=>(p i).val) J*
      angularCompensationRowTest ℓ η (calibrationForSet S hS) W0 W1 (fun i=>(p i).val) J X Y T t*
        selectedSlotFactor W P (fun i=>(p i).val) J t)=
      ∑a : LowUnselectedTuple slots J,lowUnselectedWeight slots J W P a*
        ((Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*(1/(2*Real.pi):ℂ))*
          ∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
            (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
            (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
            (angularLowSelectedInverseRow ℓ Finset.univ (angularLowSelectedWeight ℓ η slots J W P t)
              η S hS (lowSelectedIdeal slots J) T t) v := by
  rw [sum_lowSlotJoin slots J (fun p=> angularCompensationSubsetWeight ℓ η W P p J*
    angularCompensationRowTest ℓ η (calibrationForSet S hS) W0 W1 p J X Y T t*selectedSlotFactor W P p J t)]
  apply Finset.sum_congr rfl
  intro a ha
  let L := elementNorm (∏i : J,(a i).val)
  have hL : 0< L := lowUnselectedProduct_norm_pos slots hslots J a
  let C := calibrationForSet S hS
  let Ω := lowOuterCutoff (a0*a1) (max 1 (b0*b1))
  let N : ℂ := (Real.sqrt (lowPhysicalScale C (X/L) (Y/L)):ℂ)⁻¹*(1/(2*Real.pi):ℂ)
  have hW1c : HasCompactSupport W1 := HasCompactSupport.of_support_subset_isCompact isCompact_Icc hW1
  have hΩc : HasCompactSupport Ω := lowOuterCutoff_compact _ _ (mul_pos ha0 ha1)
    (lt_of_lt_of_le (by norm_num) (le_max_left _ _))
  have hΩ0 : Ω 0=0 := lowOuterCutoff_small _ _ (mul_pos ha0 ha1) 0 (by positivity)
  calc
    _ = lowUnselectedWeight slots J W P a*N*
        ∑b : LowSelectedTuple slots J,angularLowSelectedWeight ℓ η slots J W P t b*
          ∫v : ℝ,lowSeparatedIntegrand C W0 W1 Ω (X/L) (Y/L)
            (angularLowMarkedInverseRow ℓ η S hS (lowSelectedIdeal slots J b) T t) v := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro b hb
      rw [angularCompensationRowTest_join_low ℓ η S hS hbad W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1 hWs
        slots hslots J a b X Y T t hX hY hT]
      have hw := angularLowSlotJoin_weight ℓ η slots J W P t a b
      dsimp only [C,Ω,L,N]
      linear_combination (Real.sqrt (lowPhysicalScale (calibrationForSet S hS)
        (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))):ℂ)⁻¹*
        (1/(2*Real.pi):ℂ)*(∫v : ℝ,lowSeparatedIntegrand (calibrationForSet S hS) W0 W1
          (lowOuterCutoff (a0*a1) (max 1 (b0*b1)))
          (X/elementNorm (∏i : J,(a i).val)) (Y/elementNorm (∏i : J,(a i).val))
          (angularLowMarkedInverseRow ℓ η S hS (lowSelectedIdeal slots J b) T t) v)*hw
    _ = _ := by
      rw [lowSeparatedIntegral_finite_sum Finset.univ (angularLowSelectedWeight ℓ η slots J W P t)
        C W0 W1 Ω a0 b0 ha0 hW0 hWs hW1c hΩc hΩ0 (X/L) (Y/L)
        (div_pos hX hL) (div_pos hY hL)]
      rfl

end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
