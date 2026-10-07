import GaloisForLFunctions.HTGeometry.MultiquadraticAdjoinDegree
import GaloisForLFunctions.RHTower.XiLegendreHalvingFields
import GaloisForLFunctions.RHTower.XiSignedFactorSquareClasses
import Mathlib.Algebra.BigOperators.Option

/-!
# Exact minimal joint halving fields for finitely many source labels

The common Xi class and every positive labelled class are independent in the
actual infinite marked field. Adjoining their roots gives degree 2^(|T|+1).
For a nonempty finite label set T, this is precisely the least intermediate field
admitting a half of each translated source section. At T empty the definition
retains the common quadratic field; the minimality theorem requires nonemptiness.
-/

noncomputable section
open GaloisForLFunctions.HTGeometry
open scoped IntermediateField
namespace RHTower.XiGlobalKummer
local instance : CharZero K := charZero_of_injective_algebraMap constPlane_injective
local instance (priority := high) (F : Type*) : DecidableEq F := Classical.decEq F

/-- The common class has index `none`; positive labelled classes have indices `some n`. -/
def halvingRadicand : Option ℕ → Marked
  | none => xiMarked
  | some n => 1 + sourceParameter n

def halvingRoot : Option ℕ → HalvingClosure
  | none => commonHalfRoot
  | some n => labelledHalfRoot n

theorem halvingRoot_sq (i : Option ℕ) :
    halvingRoot i * halvingRoot i = algebraMap Marked HalvingClosure (halvingRadicand i) := by
  cases i with
  | none => exact commonHalfRoot_sq
  | some n => exact labelledHalfRoot_sq n

theorem halvingRadicands_independent (S : Finset (Option ℕ)) (hne : S.Nonempty) :
    ¬ IsSquare (∏ i ∈ S, halvingRadicand i) := by
  intro hs
  by_cases hn : none ∈ S
  · have heq : Finset.insertNone S.eraseNone = S := by
      rw [Finset.insertNone_eraseNone, Finset.insert_eq_of_mem hn]
    rw [← heq, Finset.prod_insertNone] at hs
    change IsSquare (xiMarked * ∏ n ∈ S.eraseNone, (1 + sourceParameter n)) at hs
    have h := ((sourceLambda_packet_isSquare_iff S.eraseNone 1).mp (by simpa using hs)).1
    norm_num at h
  · have heq : S = S.eraseNone.map Function.Embedding.some := by
      rw [Finset.map_some_eraseNone, Finset.erase_eq_of_notMem hn]
    rw [heq, Finset.prod_map] at hs
    change IsSquare (∏ n ∈ S.eraseNone, (1 + sourceParameter n)) at hs
    have ht := ((sourceLambda_packet_isSquare_iff S.eraseNone 0).mp (by simpa using hs)).2
    obtain ⟨i, hi⟩ := hne
    cases i with
    | none => exact hn hi
    | some n =>
      have hm : n ∈ S.eraseNone := Finset.mem_eraseNone.mpr hi
      rw [ht] at hm
      exact Finset.notMem_empty n hm

/-- The field of the common radical and the finite collection of positive labelled radicals. -/
def jointHalvingField (T : Finset ℕ) : IntermediateField Marked HalvingClosure :=
  IntermediateField.adjoin Marked (halvingRoot '' ((Finset.insertNone T : Finset (Option ℕ)) : Set (Option ℕ)))

theorem jointHalvingField_finrank (T : Finset ℕ) :
    Module.finrank Marked (jointHalvingField T) = 2 ^ (T.card + 1) := by
  have h := (multiquadratic_degree_and_twists halvingRadicand halvingRoot (by norm_num)
    halvingRoot_sq halvingRadicands_independent (Finset.insertNone T)).1
  rw [Finset.card_insertNone] at h
  exact h

/-- Exact minimality in the lattice of intermediate fields. -/
theorem jointHalvingField_le_iff_classes (T : Finset ℕ)
    (E : IntermediateField Marked HalvingClosure) :
    jointHalvingField T ≤ E ↔ IsSquare (algebraMap Marked E xiMarked) ∧
      ∀ n ∈ T, IsSquare (algebraMap Marked E (1 + sourceParameter n)) := by
  unfold jointHalvingField
  rw [IntermediateField.adjoin_le_iff]
  constructor
  · intro h
    refine ⟨(root_mem_iff_isSquare commonHalfRoot_sq E).mp ?_, ?_⟩
    · exact h ⟨none, Finset.none_mem_insertNone, rfl⟩
    · intro n hn
      apply (root_mem_iff_isSquare (labelledHalfRoot_sq n) E).mp
      exact h ⟨some n, Finset.some_mem_insertNone.mpr hn, rfl⟩
  · rintro ⟨hc, ht⟩ z ⟨i, hi, rfl⟩
    cases i with
    | none => exact (root_mem_iff_isSquare commonHalfRoot_sq E).mpr hc
    | some n =>
      exact (root_mem_iff_isSquare (labelledHalfRoot_sq n) E).mpr
        (ht n (Finset.some_mem_insertNone.mp hi))

/-- For a nonempty collection this is precisely the least field admitting all requested halves. -/
theorem jointHalvingField_le_iff_has_halves (T : Finset ℕ) (hne : T.Nonempty)
    (E : IntermediateField Marked HalvingClosure) :
    jointHalvingField T ≤ E ↔
      ∀ n ∈ T, ∃ R : (sourceCurveOver E n).Point, R + R = translatedSectionOver E n := by
  refine (jointHalvingField_le_iff_classes T E).trans ?_
  constructor
  · rintro ⟨hxi, ht⟩ n hn
    exact (translatedSectionOver_has_half_iff E n).mpr ⟨hxi, ht n hn⟩
  · intro h
    obtain ⟨n, hn⟩ := hne
    refine ⟨((translatedSectionOver_has_half_iff E n).mp (h n hn)).1, ?_⟩
    intro m hm
    exact ((translatedSectionOver_has_half_iff E m).mp (h m hm)).2

theorem translatedSection_has_half_jointHalvingField (T : Finset ℕ) {n : ℕ} (hn : n ∈ T) :
    ∃ R : (sourceCurveOver (jointHalvingField T) n).Point,
      R + R = translatedSectionOver (jointHalvingField T) n :=
  (jointHalvingField_le_iff_has_halves T ⟨n, hn⟩ (jointHalvingField T)).mp le_rfl n hn

end RHTower.XiGlobalKummer
