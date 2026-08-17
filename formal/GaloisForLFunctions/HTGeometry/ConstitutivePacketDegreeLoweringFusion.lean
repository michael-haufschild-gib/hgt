import GaloisForLFunctions.HTGeometry.ConstitutiveCohomologicalPacketFormation
import GaloisForLFunctions.HTGeometry.ConstitutiveCanonicalCoinducedReporter

/-!
# Packet formation fused with canonical cohomological degree lowering

The outer-product carry defining the two-step packet group is a normalized two-cocycle.  Its
antisymmetry against the marked unit vector is the complete pair-difference packet.  A nonconstant
packet makes the carry nontrivial in degree two and its canonically lowered cocycle nontrivial in
degree one.  This is the exact end-to-end fusion of formation, degree shift, and recovery.
-/

namespace GaloisForLFunctions.HTGeometry

variable {n : ℕ}

/-- Outer-product central carry of packet formation. -/
def cohomologicalPacketCarry (x y : Fin n → ℝ) : Fin n → Fin n → ℝ :=
  fun i j => x i * y j

/-- The packet carry is a degree-two formation cocycle. -/
theorem cohomologicalPacketCarry_isTwoCocycle :
    IsCohomologicalFormationTwoCocycle (cohomologicalPacketCarry (n := n)) := by
  intro x g h
  funext i j
  simp only [cohomologicalPacketCarry, Pi.add_apply]
  ring

theorem cohomologicalPacketCarry_left_normalized :
    IsCohomologicalLeftNormalized (cohomologicalPacketCarry (n := n)) := by
  intro g
  funext i j
  simp [cohomologicalPacketCarry]

/-- Antisymmetrizing the carry against the marked unit vector gives the complete pair packet. -/
theorem cohomologicalPacketCarry_antisymmetry (a : Fin n → ℝ) (i j : Fin n) :
    cohomologicalPacketCarry a 1 i j - cohomologicalPacketCarry 1 a i j =
      CohomologicalPacketGroup.packetDifference a i j := by
  simp [cohomologicalPacketCarry, CohomologicalPacketGroup.packetDifference]

/-- If the packet carry were a two-coboundary, every source packet would be constant. -/
theorem cohomologicalPacketCarry_coboundary_forces_constant
    (a : Fin n → ℝ)
    (h : ∃ φ : (Fin n → ℝ) → (Fin n → Fin n → ℝ),
      cohomologicalPacketCarry = cohomologicalFormationTwoCoboundary φ) :
    ∀ i j, a i = a j := by
  obtain ⟨φ, hφ⟩ := h
  intro i j
  have hsym := cohomologicalFormationTwoCoboundary_comm φ a (1 : Fin n → ℝ)
  rw [← hφ] at hsym
  have hij := congrFun (congrFun hsym i) j
  simpa [cohomologicalPacketCarry] using hij

/-- Every nonconstant packet witnesses a nontrivial degree-two carry class. -/
theorem cohomologicalPacketCarry_not_coboundary_of_nonconstant
    (a : Fin n → ℝ) (i j : Fin n) (hij : a i ≠ a j) :
    ¬ ∃ φ : (Fin n → ℝ) → (Fin n → Fin n → ℝ),
      cohomologicalPacketCarry = cohomologicalFormationTwoCoboundary φ := by
  intro h
  exact hij (cohomologicalPacketCarry_coboundary_forces_constant a h i j)

/-- Formation-selection obstruction: no exact reporter can turn a nonconstant packet carry into a
fixed-point coboundary.  This isolates the global gate independently of any topology or chosen
Hilbert completion. -/
theorem cohomologicalPacketCarry_no_exactReporter_fixedPoint
    {H : Type*} [AddCommGroup H]
    (R : CohomologicalExactReporter
      (G := Fin n → ℝ) (A := Fin n → Fin n → ℝ) (H := H))
    (a : Fin n → ℝ) (i j : Fin n) (hij : a i ≠ a j) :
    ¬ ∃ ξ : H, ∀ g,
      cohomologicalLoweredCocycle R cohomologicalPacketCarry g =
        R.action g ξ - ξ := by
  rintro ⟨ξ, hξ⟩
  have hsplit := cohomologicalTwoCocycle_coboundary_of_loweredCocycle_coboundary
    R cohomologicalPacketCarry_left_normalized ξ hξ
  exact cohomologicalPacketCarry_not_coboundary_of_nonconstant a i j hij hsplit

/-- Exact recovery prevents degree lowering from trivializing a nonconstant packet: the canonical
quotient-valued one-cocycle is not a coboundary. -/
theorem cohomologicalPacketCarry_lowered_not_coboundary_of_nonconstant
    (a : Fin n → ℝ) (i j : Fin n) (hij : a i ≠ a j) :
    ¬ ∃ ξ : CohomologicalCoinducedQuotient
        (G := Fin n → ℝ) (A := Fin n → Fin n → ℝ),
      ∀ g,
        cohomologicalLoweredCocycle canonicalCohomologicalExactReporter
            cohomologicalPacketCarry g =
          (canonicalCohomologicalExactReporter.action g) ξ - ξ := by
  exact cohomologicalPacketCarry_no_exactReporter_fixedPoint
    canonicalCohomologicalExactReporter a i j hij

end GaloisForLFunctions.HTGeometry
