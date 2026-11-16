import GaloisForLFunctions.MetaplecticMobiusDescent.Reflection.AngularMarkedSources
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.EulerCoordinates
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.AngularSelectedWeights

/-!
# Direct angular physical inverse rows

Finite ray correction and period puncturing commute with the angular source character.
Selected prime slots therefore reduce to the same ideal polynomials and finite correction
energy, with the angular twist applied to the completed source.
-/

open scoped BigOperators Classical ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource CompletedGauss
open CanonicalRowCompletion SchwartzPlanePoisson NormalizedReflection
namespace ProbePhysical
open ProbeRow ProbeCompleted CanonicalQuadraticSieve RayFourExpansion
noncomputable section
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O
local instance : Fintype Oˣ := @Fintype.ofFinite _ cubic_units_finite

/-- Finite ray correction acts on the finite coefficient of an angular completed source. -/
theorem angular_correctedPhysicalRow_eq_periodic_inverse (ℓ : ℕ) (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (s : O) (hs : Supported (Ideal.span {s})) (z : O) (D : Id)
    (W : ℝ→ℂ) (hW : HasCompactSupport W) (X : ℝ) (hX : 0<X)
    (E : GoodMaskRowData (calibrationForSet S hS).generator 1 (calibrationForSet S hS).generator) :
    correctedCompletedT S D
      (angularSourceTwist ℓ (rowCoefficient η (calibrationForSet S hS).Xi s hs z)) W X=
      ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
        (angularSourceTwist ℓ
          (rowTwist (lowPeriodicBase η (calibrationForSet S hS)
            (calibrationForSet S hS).generator E s hs χ) (calibrationForSet S hS).generator 1 z))
        W X (fun A=>if D∣A then (1:ℂ) else 0) := by
  rw [correctedCompletedT_ray_expansion S D _ W hW X hX]
  apply Finset.sum_congr rfl
  intro χ hχ
  rw [markedCompletedT_eq_punctured S hS D _ W hW X hX]
  congr 1
  apply inverseMarkedCompletedT_congr_primary
  intro n hn
  simp only [angularSourceTwist_mul_left,angularSourceTwist_apply]
  rw [lowPeriodicRow_eq_primary η (calibrationForSet S hS) (calibrationForSet S hS).generator E
    (calibration_generator_bad S hS hbad).1 (calibration_generator_bad S hS hbad).2 s hs χ z n hn]

def angularLowMarkedInverseRow (ℓ : ℕ) (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (D : Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑χ : RayCharacter,correctionCoeff χ*InverseMoment.markedCompletedT
    (angularSourceTwist ℓ (rowTwist (physicalRayPeriodicBase η S hS σ χ)
      (calibrationForSet S hS).generator 1 m))
    (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
    (fun A=>if D∣A then (1:ℂ) else 0)

lemma angularLowMarkedInverseRow_eq (ℓ : ℕ) (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (D : Id) (T t : ℝ) (hT : 0<T) (σ : RayRing) (m : O) :
    correctedCompletedT S D
      (angularSourceTwist ℓ (physicalRayRowMonoid η (calibrationForSet S hS) σ m))
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) T=
        angularLowMarkedInverseRow ℓ η S hS D T t σ m :=
  angular_correctedPhysicalRow_eq_periodic_inverse ℓ η S hS hbad
    (physicalRayRepresentative σ).val (physicalRayRepresentative σ).property m D _
    (gaussianFixedWindow_twist_compact t) T hT (calibrationLowData S hS)

lemma angular_physical_markedCompletedT_absorb_true_period (ℓ : ℕ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (σ : RayRing) (χ : RayCharacter)
    (f z : O) (W : ℝ→ℂ) (X : ℝ) (mark : Id→ℂ) :
    InverseMoment.markedCompletedT
      (angularSourceTwist ℓ
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) f z)) W X mark=
    InverseMoment.markedCompletedT
      (angularSourceTwist ℓ
        (rowTwist (physicalRayPeriodicBase η S hS σ χ) (calibrationForSet S hS).generator f z)) W X mark := by
  rw [lowReflectionMask,physical_row_absorb_true_period η S hS hbad σ χ]

def angularLowSelectedInverseRow (ℓ : ℕ) {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→ Id) (T t : ℝ) (σ : RayRing) (m : O) : ℂ :=
  ∑k∈F,c k*angularLowMarkedInverseRow ℓ η S hS (D k) T t σ m

lemma angularLowSelectedInverseRow_correction (ℓ : ℕ) {α : Type*} (F : Finset α) (c : α→ℂ)
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (D : α→ Id) (T t : ℝ) (σ : RayRing) (m : O) :
    angularLowSelectedInverseRow ℓ F c η S hS D T t σ m=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        ∑k∈F,c k*InverseMoment.markedCompletedT
          (angularSourceTwist ℓ (CanonicalRowCompletion.rowTwist (physicalRayPeriodicBase η S hS σ χ)
            (calibrationForSet S hS).generator 1 m))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) T
          (fun A=> if D k∣A then (1:ℂ) else 0) := by
  unfold angularLowSelectedInverseRow angularLowMarkedInverseRow
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro χ hχ
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem angularLowSelectedInverseRow_actual_ideal (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=> Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (z : O) :
    angularLowSelectedInverseRow ℓ Finset.univ
      (angularLowSelectedWeight ℓ η (fun i=> canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z=
      ∑χ : RayCharacter,ProbeCompleted.correctionCoeff χ*
        lowActualIdealPolynomial
          (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
          (fun i I=> angularLowSingleSlotWeight ℓ η (W i.val) (Y i.val) t (primaryIdealGenerator I))
          (angularSourceTwist ℓ (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z))
          (CompletedHeight.normTwistedSource gaussianFixedWindow t) X := by
  rw [angularLowSelectedInverseRow_correction]
  apply Finset.sum_congr rfl
  intro χ hχ
  congr 1
  simp_rw [angularLowSelectedWeight_eq_product]
  have hm (b : LowSelectedTuple (fun i=> canonicalSlotSupport (T i)) J) :
      (fun A : Id=> if lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J b∣A then (1:ℂ) else 0)=
        (fun A=>∏i : SelectedSlot J,if Ideal.span {(b i).val}∣A then (1:ℂ) else 0) := by
    funext A
    exact lowSelectedIdeal_mark _ J b (lowCanonicalSelected_coprime T hT hdis J b) A
  simp_rw [hm,←angular_physical_markedCompletedT_absorb_true_period ℓ η S hS hbad σ χ]
  convert angular_low_actual_ideal_polynomial ℓ η S hS hbad (fun i : SelectedSlot J=> T i.val)
    (fun i=> hT i.val) (fun i=> hout i.val) (fun i=> W i.val) (fun i=> Y i.val) t
    (fun p=> InverseMoment.markedCompletedT
      (angularSourceTwist ℓ (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS) 1 z))
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X
      (fun A=>∏i : SelectedSlot J,if p i∣A then (1:ℂ) else 0)) using 1
  · congr 1
    ext p
    simp
  · rfl

theorem angularLowSelectedInverseRow_actual_reflected_energy (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (S : Finset Id) (hS : ∀P∈S,P.IsMaximal) (hbad : fixedBadPrimes⊆S)
    (T : Fin K→Finset HeckeIdealSeries.PrimeIdeal) (hT : ∀i P,P∈T i→Supported P.val)
    (hout : ∀i P,P∈T i→P.val∉S)
    (hdis : Pairwise (fun i j=> Disjoint (T i) (T j)))
    (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ) (Y : Fin K→ℝ)
    (X t : ℝ) (σ : RayRing) (R : Finset O) (hR : ∀z∈R,z≠0) :
    (∑z∈R,‖angularLowSelectedInverseRow ℓ Finset.univ
      (angularLowSelectedWeight ℓ η (fun i=> canonicalSlotSupport (T i)) J W Y t)
      η S hS (lowSelectedIdeal (fun i=> canonicalSlotSupport (T i)) J) X t σ z‖^2)≤
    lowCorrectionEnergy*∑χ : RayCharacter,∑u : Oˣ,∑I∈lowIdealRows R,
      ‖lowActualIdealPolynomial
        (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
        (fun i I=> angularLowSingleSlotWeight ℓ η (W i.val) (Y i.val) t (primaryIdealGenerator I))
        (angularSourceTwist ℓ (rowTwist (physicalRayPeriodicBase η S hS σ χ) (lowReflectionMask η S hS)
          (cubicIdealGenerator (1:Id)) (u.val*cubicIdealGenerator I)))
        (CompletedHeight.normTwistedSource gaussianFixedWindow t) X‖^2 := by
  simp_rw [angularLowSelectedInverseRow_actual_ideal ℓ η S hS hbad T hT hout hdis J W Y X t σ]
  apply (fixed_correction_energy R ProbeCompleted.correctionCoeff _).trans
  apply mul_le_mul_of_nonneg_left _ lowCorrectionEnergy_nonneg
  apply Finset.sum_le_sum
  intro χ hχ
  exact low_element_rowTwist_energy R hR (physicalRayPeriodicBase η S hS σ χ)
    (lowReflectionMask η S hS) (fun Ψ=> lowActualIdealPolynomial
      (fun i : SelectedSlot J=> lowPrimeIdealList (lowPeriodPrimeList η S hS (T i.val)))
      (fun i I=> angularLowSingleSlotWeight ℓ η (W i.val) (Y i.val) t (primaryIdealGenerator I)) (angularSourceTwist ℓ Ψ)
      (CompletedHeight.normTwistedSource gaussianFixedWindow t) X)

end
end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
