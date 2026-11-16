import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.AngularPhysicalProbe
import GaloisForLFunctions.MetaplecticMobiusDescent.Detector.LowGramProfiles

/-!
# Angular weights on compensated prime slots

Selected primes carry the conjugate angular target. The character separates over
slots, preserves their norm bounds and commutes with the exact ideal reindexing.
-/

noncomputable section
open scoped Classical BigOperators ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CanonicalRowCompletion CompletedGauss SchwartzPlanePoisson
open GaloisForLFunctions.FamilyContinuationTheory
namespace ProbePhysical
open ProbeRow HeckeIdealSeries CanonicalQuadraticSieve
local notation "O" => Eisenstein.O
local notation "Id" => Ideal O

def angularCompensationSubsetCoefficient (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  (-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
    star (angularSourceTwist ℓ (targetMonoid η) (slotProduct p (Finset.univ\J)))

lemma angularCompensationSubsetCoefficient_eq (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (p : Fin K→O) (J : Finset (Fin K)) :
    angularCompensationSubsetCoefficient ℓ η p J=
      star (elemPsiSix (slotProduct p (Finset.univ\J)))^ℓ*
        compensationSubsetCoefficient η p J := by
  rw [angularCompensationSubsetCoefficient,angularSourceTwist_apply,star_mul,star_pow]
  change _=star (elemPsiSix (slotProduct p (Finset.univ\J)))^ℓ*
    ((-1:ℂ)^J.card*((elementNorm (slotProduct p J)^(-(3/2:ℝ)):ℝ):ℂ)*
      star (targetMonoid η (slotProduct p (Finset.univ\J))))
  ring

def angularCompensationSubsetProbe (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W₀ W₁ : ℝ→ℂ) (p : Fin K→O) (J : Finset (Fin K))
    (X Y Z : ℝ) : ℂ :=
  angularCompensationSubsetCoefficient ℓ η p J*
    angularMarkedPhysicalProbe ℓ η C (Ideal.span {slotProduct p (Finset.univ\J)}) W₀ W₁
      (X/elementNorm (slotProduct p J)) (Y/elementNorm (slotProduct p J))
      (Z*elementNorm (slotProduct p (Finset.univ\J)))

lemma angularCompensatedTuple_eq_subsets (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (C : CalibrationData) (W₀ W₁ : ℝ→ℂ) (p : Fin K→O) (X Y Z : ℝ) :
    angularCompensatedTuple ℓ η C W₀ W₁ p X Y Z=
      ∑J∈(Finset.univ:Finset (Fin K)).powerset,
        angularCompensationSubsetProbe ℓ η C W₀ W₁ p J X Y Z := rfl

def angularCompensationSubsetWeight (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (W : Fin K→ℝ→ℂ) (P : Fin K→ℝ) (p : Fin K→O) (J : Finset (Fin K)) : ℂ :=
  angularCompensationSubsetCoefficient ℓ η p J*(∏i∈J,W i (elementNorm (p i)/P i))

def angularLowSingleSlotWeight (ℓ : ℕ) (η : HeckeFamily.Character)
    (W : ℝ→ℂ) (P t : ℝ) (a : O) : ℂ :=
  star (elemPsiSix a)^ℓ*lowSingleSlotWeight η W P t a

def angularLowSelectedWeight (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (slots : Fin K→Finset O) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (P : Fin K→ℝ) (t : ℝ) (b : LowSelectedTuple slots J) : ℂ :=
  star (elemPsiSix (∏i : SelectedSlot J,(b i).val))^ℓ*lowSelectedWeight η slots J W P t b

/-- Splitting compensation slots places precisely the conjugate angular weight on selected slots. -/
lemma angularLowSlotJoin_weight (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (slots : Fin K→Finset O) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (P : Fin K→ℝ) (t : ℝ) (a : LowUnselectedTuple slots J) (b : LowSelectedTuple slots J) :
    angularCompensationSubsetWeight ℓ η W P (lowSlotJoin slots J a b) J*
      selectedSlotFactor W P (lowSlotJoin slots J a b) J t=
      lowUnselectedWeight slots J W P a*angularLowSelectedWeight ℓ η slots J W P t b := by
  rw [angularCompensationSubsetWeight,angularCompensationSubsetCoefficient_eq,
    lowSlotJoin_selectedProduct,angularLowSelectedWeight]
  calc
    _=star (elemPsiSix (∏i : SelectedSlot J,(b i).val))^ℓ*
        (compensationSubsetWeight η W P (lowSlotJoin slots J a b) J*
          selectedSlotFactor W P (lowSlotJoin slots J a b) J t) := by
      unfold compensationSubsetWeight
      ring
    _=_ := by rw [lowSlotJoin_weight];ring

lemma angularLowSelectedWeight_eq_product (ℓ : ℕ) {K : ℕ} (η : HeckeFamily.Character)
    (slots : Fin K→Finset O) (J : Finset (Fin K)) (W : Fin K→ℝ→ℂ)
    (P : Fin K→ℝ) (t : ℝ) (b : LowSelectedTuple slots J) :
    angularLowSelectedWeight ℓ η slots J W P t b=
      ∏i : SelectedSlot J,angularLowSingleSlotWeight ℓ η (W i.val) (P i.val) t (b i).val := by
  simp only [angularLowSelectedWeight,lowSelectedWeight_eq_product,map_prod,star_prod,
    Finset.prod_pow,angularLowSingleSlotWeight,Finset.prod_mul_distrib]

lemma angularLowSingleSlotWeight_norm (ℓ : ℕ) (η : HeckeFamily.Character)
    (W : ℝ→ℂ) (P t : ℝ) (a : O) :
    ‖angularLowSingleSlotWeight ℓ η W P t a‖≤‖W (elementNorm a/P)‖ := by
  rw [angularLowSingleSlotWeight,norm_mul,norm_pow,norm_star]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one a))).trans
    (lowSingleSlotWeight_norm η W P t a)

lemma angular_low_actual_ideal_weight_bound (ℓ : ℕ) (η : HeckeFamily.Character)
    (W : ℝ→ℂ) (hW : ∀x,‖W x‖≤1) (Y t : ℝ) (I : Id) :
    ‖angularLowSingleSlotWeight ℓ η W Y t (primaryIdealGenerator I)‖≤1 :=
  (angularLowSingleSlotWeight_norm ℓ η W Y t _).trans (hW _)

/-- The actual conjugate angular weights pass through the canonical prime-ideal bijection. -/
theorem angular_low_actual_ideal_polynomial (ℓ : ℕ) {ι : Type*} [Fintype ι]
    (η : HeckeFamily.Character) (S : Finset Id) (hS : ∀P∈S,P.IsMaximal)
    (hbad : fixedBadPrimes⊆S) (T : ι→Finset PrimeIdeal)
    (hT : ∀i P,P∈T i→Supported P.val) (hout : ∀i P,P∈T i→P.val∉S)
    (W : ι→ℝ→ℂ) (Y : ι→ℝ) (t : ℝ) (F : (ι→Id)→ℂ) :
    (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,angularLowSingleSlotWeight ℓ η (W i) (Y i) t (p i).val)*
        F (fun i=>Ideal.span {(p i).val}))=
    ∑p : ∀i,lowPrimeIdealList (lowPeriodPrimeList η S hS (T i)),
      (∏i,angularLowSingleSlotWeight ℓ η (W i) (Y i) t (primaryIdealGenerator (p i).val))*
        F (fun i=>(p i).val) := by
  have h := low_actual_ideal_polynomial η S hS hbad T hT hout W Y t
    (fun p=>(∏i,star (idealPsiSix (p i))^ℓ)*F p)
  have hleft : (∑p : ∀i,canonicalSlotSupport (T i),
      (∏i,lowSingleSlotWeight η (W i) (Y i) t (p i).val)*
        ((∏i,star (idealPsiSix (Ideal.span {(p i).val}))^ℓ)*
          F (fun i=>Ideal.span {(p i).val})))=
      ∑p : ∀i,canonicalSlotSupport (T i),
        (∏i,angularLowSingleSlotWeight ℓ η (W i) (Y i) t (p i).val)*
          F (fun i=>Ideal.span {(p i).val}) := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [idealPsiSix_span_singleton,angularLowSingleSlotWeight,
      Finset.prod_mul_distrib,Finset.prod_pow]
    ring
  rw [hleft] at h
  refine h.trans ?_
  apply Finset.sum_congr rfl
  intro p hp
  have he (i : ι) : elemPsiSix (primaryIdealGenerator (p i).val)=idealPsiSix (p i).val := by
    rw [←idealPsiSix_span_singleton,
      CenteredMomentSourceRow.primary_span_supported _
        (lowPrimeIdealList_supported _
          (fun P hP=>hT i P (Finset.mem_filter.mp hP).1) _ (p i).property)]
  simp only [angularLowSingleSlotWeight,Finset.prod_mul_distrib,he,Finset.prod_pow]
  ring

end ProbePhysical
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
