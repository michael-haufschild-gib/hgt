import GaloisForLFunctions.HTGeometry.DeckDegreeUpperBound
import GaloisForLFunctions.HTGeometry.NonautonomousErasedDeckBridge

/-!
# The phase tail from a one-sided degree estimate

The deck-descent form of the phase-tail identity asks that every prefix image have degree exactly the
order of the prefix kernel.  Half of that equality is automatic: a subfield of a fixed field never has
smaller degree than the group has order.  So only the upper bound is a genuine input, and for a
radical or isogeny prefix it is a direct degree estimate.

This is the form in which a concrete protocol discharges the deck hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K F : Type*} [Field K] [Field F] [Algebra K F]
variable {G : ℕ → Type*} [∀ i, CommGroup (G i)]
variable [∀ i, TopologicalSpace (G i)] [∀ i, IsTopologicalGroup (G i)]

/-- **The phase tail from an upper degree bound.**  With the prefix kernels finite and acting inside
the prefix images' fixed fields, a degree estimate in the easy direction suffices: Artin's theorem
supplies the reverse inequality. -/
theorem nonautonomousTail_eq_fixedField_erasedClosure_of_finrank_le
    (φ : ℕ → F →ₐ[K] F) (i : ℕ) (a : ∀ j, G j →* G (j + 1)) (ρ : G i →* (F ≃ₐ[K] F))
    (hfin : ∀ n, Finite ((prefixKernel a i n).map ρ))
    (hfd : ∀ n, FiniteDimensional (IntermediateField.map (forwardPrefix φ i n) ⊤) F)
    (hfix : ∀ n, IntermediateField.map (forwardPrefix φ i n) ⊤ ≤
      IntermediateField.fixedField ((prefixKernel a i n).map ρ))
    (hle : ∀ n, Module.finrank (IntermediateField.map (forwardPrefix φ i n) ⊤) F
      ≤ Nat.card ((prefixKernel a i n).map ρ))
    (hclosed : ∀ x : F, IsClosed {g : G i | ρ g x = x}) :
    nonautonomousTail φ i = IntermediateField.fixedField ((erasedClosure a i).map ρ) := by
  classical
  refine nonautonomousTail_eq_fixedField_erasedClosure_of_finrank φ i a ρ hfin hfd hfix
    (fun n => ?_) hclosed
  haveI := hfin n
  haveI : Fintype ((prefixKernel a i n).map ρ) := Fintype.ofFinite _
  haveI := hfd n
  exact finrank_eq_card_of_le_fixedField_of_finrank_le ((prefixKernel a i n).map ρ)
    (IntermediateField.map (forwardPrefix φ i n) ⊤) (hfix n) (hle n)

end

end GaloisForLFunctions.HTGeometry
