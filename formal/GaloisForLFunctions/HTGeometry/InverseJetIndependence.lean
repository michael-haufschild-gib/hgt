import GaloisForLFunctions.HTGeometry.InverseJetTriangular
import GaloisForLFunctions.HTGeometry.AlgebraAdjoinAlgebraic
import Mathlib.RingTheory.AlgebraicIndependent.Transcendental

/-!
# Differential transcendence is invariant under inversion

If the jets of a nonzero `u` are algebraically independent over the coefficient field, so are the jets
of `u⁻¹`.

The substitution is triangular (`differentialJet_succ_inv`), the jet fields of `u` and `u⁻¹` agree at
every order (`jetFieldLe_inv`), and the top jets are algebraic over the field of the lower ones only
together (`isAlgebraic_differentialJet_succ_inv_iff`).  Feeding those into the successive
characterisation of algebraic independence — each new member transcendental over what the previous
ones generate — transfers independence from `u` to `u⁻¹`, one jet at a time.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {F K : Type*} [Field F] [Field K] [Differential F] [Differential K]
  [Algebra F K] [DifferentialAlgebra F K]

/-- The jets of `u⁻¹` up to order `n` are algebraically independent whenever those of `u` are. -/
theorem algebraicIndepOn_jets_inv_Iic {u : K} (hu : u ≠ 0)
    (h : AlgebraicIndependent F (fun i : ℕ => differentialJet i u)) (n : ℕ) :
    AlgebraicIndepOn F (fun i : ℕ => differentialJet i u⁻¹) (Set.Iic n) := by
  classical
  induction n with
  | zero =>
      have hset : (Set.Iic 0 : Set ℕ) = {0} := by
        ext m
        simp
      rw [hset]
      have htrans : Transcendental F (differentialJet 0 u⁻¹) := by
        rw [differentialJet_zero]
        intro halg
        have hu0 : IsAlgebraic F u := IsAlgebraic.inv_iff.mp halg
        have := h.transcendental 0
        rw [differentialJet_zero] at this
        exact this hu0
      exact (algebraicIndependent_unique_type_iff
        (x := fun i : ↥({0} : Set ℕ) => differentialJet (i : ℕ) u⁻¹)).mpr htrans
  | succ n ih =>
      have hset : (Set.Iic (n + 1) : Set ℕ) = insert (n + 1) (Set.Iic n) := by
        ext m
        simp [Nat.le_succ_iff_eq_or_le, or_comm]
      have hnot : (n + 1) ∉ (Set.Iic n : Set ℕ) := by simp
      rw [hset, AlgebraicIndepOn.insert_iff hnot]
      refine ⟨ih, ?_⟩
      -- the `u`-side transcendence of the top jet
      have huIic : AlgebraicIndepOn F (fun i : ℕ => differentialJet i u) (insert (n + 1)
          (Set.Iic n)) := h.comp _ Subtype.val_injective
      have hu_trans : Transcendental
          (Algebra.adjoin F ((fun i : ℕ => differentialJet i u) '' Set.Iic n))
          (differentialJet (n + 1) u) := ((AlgebraicIndepOn.insert_iff hnot).mp huIic).2
      -- transport to the field of jets, then across the inversion, then back
      rw [transcendental_algebraAdjoin_iff]
      rw [transcendental_algebraAdjoin_iff] at hu_trans
      have hfield : IntermediateField.adjoin F
          ((fun i : ℕ => differentialJet i u⁻¹) '' Set.Iic n) = jetFieldLe F u n := by
        show jetFieldLe F u⁻¹ n = jetFieldLe F u n
        exact jetFieldLe_inv F hu n
      rw [hfield]
      intro halg
      exact hu_trans ((isAlgebraic_differentialJet_succ_inv_iff hu n).mp halg)

/-- **Differential transcendence is invariant under inversion.** -/
theorem algebraicIndependent_jets_inv {u : K} (hu : u ≠ 0)
    (h : AlgebraicIndependent F (fun i : ℕ => differentialJet i u)) :
    AlgebraicIndependent F (fun i : ℕ => differentialJet i u⁻¹) := by
  classical
  refine algebraicIndependent_of_finite_type ?_
  intro t ht
  obtain ⟨n, hn⟩ := ht.bddAbove
  have hsub : t ⊆ Set.Iic n := fun m hm => hn hm
  exact (algebraicIndepOn_jets_inv_Iic hu h n).mono hsub

end GaloisForLFunctions.HTGeometry
