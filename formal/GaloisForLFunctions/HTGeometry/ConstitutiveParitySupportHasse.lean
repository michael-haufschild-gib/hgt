import GaloisForLFunctions.HTGeometry.ABHN.ZModTwoReciprocitySupportParity
import GaloisForLFunctions.HTGeometry.ConstitutiveParityContextuality

/-!
# Hasse support criterion for connected parity contexts

A parity charge on the vertices of a finite connected graph is globally realized by an edge
assignment exactly when its charged-vertex support has even cardinality.  Thus support parity is a
complete local--global obstruction, while an odd profile remains realizable on every proper face.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset SimpleGraph
open GaloisForLFunctions.HTGeometry.ABHN

variable {V : Type*} [Fintype V]

/-- A vertex charge, packaged as a finite-support reciprocity profile. -/
noncomputable def constitutiveParityChargeProfile (b : V → ZMod 2) : V →₀ ZMod 2 :=
  Finsupp.equivFunOnFinite.symm b

@[simp]
theorem constitutiveParityChargeProfile_apply (b : V → ZMod 2) (v : V) :
    constitutiveParityChargeProfile b v = b v := rfl

/-- Summing the finite profile is the total contextual charge. -/
theorem constitutiveParityChargeProfile_sum (b : V → ZMod 2) :
    (constitutiveParityChargeProfile b).sum (fun _ z => z) = ∑ v, b v := by
  rw [Finsupp.sum_fintype _ _ (by intro; rfl)]
  rfl

variable [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- **Exact graph Hasse criterion.**  A charge glues to a global edge law exactly when the number
of charged contexts is even. -/
theorem exists_parityBoundary_eq_iff_even_support_card
    (hG : G.Connected) (b : V → ZMod 2) :
    (∃ x, parityBoundary G x = b) ↔ Even (constitutiveParityChargeProfile b).support.card := by
  rw [exists_parityBoundary_eq_iff G hG b,
    ← constitutiveParityChargeProfile_sum b,
    finsuppZModTwo_sum_eq_zero_iff_even_support_card]

/-- Global non-realizability is exactly odd charged support. -/
theorem not_exists_parityBoundary_eq_iff_odd_support_card
    (hG : G.Connected) (b : V → ZMod 2) :
    (¬ ∃ x, parityBoundary G x = b) ↔ Odd (constitutiveParityChargeProfile b).support.card := by
  rw [exists_parityBoundary_eq_iff_even_support_card G hG b, Nat.not_even_iff_odd]

/-- Every parity boundary has an even number of charged vertices. -/
theorem parityBoundaryProfile_even_support (x : G.edgeSet → ZMod 2) :
    Even (constitutiveParityChargeProfile (parityBoundary G x)).support.card := by
  rw [← finsuppZModTwo_sum_eq_zero_iff_even_support_card]
  rw [constitutiveParityChargeProfile_sum]
  exact sum_parityBoundary_eq_zero G x

/-- A nonzero boundary charge at one vertex forces a distinct charged vertex. -/
theorem parityBoundaryProfile_exists_other_nonzero_vertex
    (x : G.edgeSet → ZMod 2) {v : V}
    (hv : parityBoundary G x v ≠ 0) :
    ∃ w : V, w ≠ v ∧ parityBoundary G x w ≠ 0 := by
  apply finsupp_exists_other_nonzero_place_of_sum_eq_zero
    (constitutiveParityChargeProfile (parityBoundary G x))
  · rw [constitutiveParityChargeProfile_sum]
    exact sum_parityBoundary_eq_zero G x
  · simpa using hv

/-- Odd charged support is invisible on every proper observer face but obstructs a global law. -/
theorem properFace_blindness_of_odd_support
    (hG : G.Connected) {b : V → ZMod 2}
    (hodd : Odd (constitutiveParityChargeProfile b).support.card) :
    (¬ ∃ x, parityBoundary G x = b) ∧
      ∀ W : Finset V, W ≠ Finset.univ → ∃ x, ∀ v ∈ W, parityBoundary G x v = b v := by
  have hprofileSumNe :
      (constitutiveParityChargeProfile b).sum (fun _ z => z) ≠ 0 := by
    intro hzero
    have heven :=
      (finsuppZModTwo_sum_eq_zero_iff_even_support_card
        (constitutiveParityChargeProfile b)).mp hzero
    exact (Nat.not_even_iff_odd.mpr hodd) heven
  have hsumNe : (∑ v, b v) ≠ 0 := by
    rw [← constitutiveParityChargeProfile_sum b]
    exact hprofileSumNe
  exact properFace_blindness G hG (zmodTwo_eq_one_of_ne_zero hsumNe)

end GaloisForLFunctions.HTGeometry
