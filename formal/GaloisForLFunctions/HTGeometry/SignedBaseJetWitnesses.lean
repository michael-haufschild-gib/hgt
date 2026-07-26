import GaloisForLFunctions.HTGeometry.DifferentialAdjoinPairClassification

/-!
# Reflexivity realizes the signed jet-equivalence interfaces

Every element is signed jet-equivalent to itself, and likewise every family: all jets of the zero
difference are embedded constants.  The generated-differential-field equality theorems therefore have
a realized hypothesis.
-/

namespace GaloisForLFunctions

open scoped Differential

theorem differentialJet_zero_source {K : Type*} [Field K] [Differential K] (n : ℕ) :
    differentialJet n (0 : K) = 0 := by
  induction n with
  | zero => rw [differentialJet_zero]
  | succ n ih =>
      rw [differentialJet_succ, ih]
      simp

theorem signedBaseJetEquivalent_self (F : Type*) {K : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (x : K) :
    SignedBaseJetEquivalent F x x :=
  Or.inl fun n => ⟨0, by rw [sub_self, differentialJet_zero_source, map_zero]⟩

theorem signedBaseJetEquivalentFamilies_self (F : Type*) {K ι : Type*} [Field F] [Field K]
    [Algebra F K] [Differential K] (x : ι → K) :
    SignedBaseJetEquivalentFamilies F x x :=
  Or.inl fun i n => ⟨0, by rw [sub_self, differentialJet_zero_source, map_zero]⟩

end GaloisForLFunctions
