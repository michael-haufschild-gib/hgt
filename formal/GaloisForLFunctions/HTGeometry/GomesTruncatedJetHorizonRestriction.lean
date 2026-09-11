import GaloisForLFunctions.HTGeometry.GomesFiniteFockHorizonRestriction
import GaloisForLFunctions.HTGeometry.GomesTruncatedJetGaugeArcTransport

/-!
# Horizon restriction of the actual joint geometric symmetry algebra

The full clock restriction preserves every fixed phase constraint. Its action
is a concrete matrix block, and its augmentation and arc representation agree
with the pre-existing geometric quotient restriction.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Restrict an actual joint symmetry as an ambient matrix through the geometric arc quotient. -/
def gomesTruncatedJetHorizonMatrix (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra (n + r) z →ₐ[ℂ] Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ :=
  (gomesFiniteFockCommutant (n + 1)).val.comp
    ((gomesFiniteFockHorizonRestriction n r).comp
      (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z)))

/-- Every actual restricted matrix still preserves both the derivative clock and the geometric phase clock. -/
theorem gomesTruncatedJetHorizonMatrix_mem (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra (n + r) z) :
    gomesTruncatedJetHorizonMatrix n r z E ∈ gomesTruncatedJetJointAlgebra n z := by
  obtain ⟨hD, hz⟩ := (gomesTruncatedJetJointAlgebra_mem_iff (n + r) z E.val).mp E.property
  obtain ⟨p, hp⟩ := (gomesFiniteFock_commute_iff_polynomial (n + r + 1) E.val).mp hD
  have he : Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z) E =
      gomesFiniteFockSymbolHom (n + r + 1) p := by
    apply Subtype.ext
    exact hp.symm
  change (gomesFiniteFockHorizonRestriction n r
    (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z) E)).val ∈ _
  rw [he, gomesFiniteFockHorizonRestriction_symbol]
  apply (gomesTruncatedJetJointAlgebra_mem_iff n z _).mpr
  constructor
  · exact (gomesFiniteFock_commute_iff_polynomial (n + 1) _).mpr ⟨p, rfl⟩
  · apply (gomesTruncatedJetClock_polynomial_commute_iff n z p).mpr
    intro k
    have hpz : Commute (gomesFiniteFockPolynomialHom (n + r + 1) p)
        (RHTower.truncatedJetClock (n + r) z) := by rw [hp]; exact hz
    exact (gomesTruncatedJetClock_polynomial_commute_iff (n + r) z p).mp hpz
      (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) k)

/-- The actual two-clock symmetry algebras admit a geometric horizon restriction homomorphism. -/
def gomesTruncatedJetHorizonRestriction (n r : ℕ) (z : ℂ) :
    gomesTruncatedJetJointAlgebra (n + r) z →ₐ[ℂ] gomesTruncatedJetJointAlgebra n z :=
  (gomesTruncatedJetHorizonMatrix n r z).codRestrict _ (gomesTruncatedJetHorizonMatrix_mem n r z)

/-- The joint restriction is the literal upper-left matrix block. -/
theorem gomesTruncatedJetHorizonRestriction_apply (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra (n + r) z) (i j : Fin (n + 1)) :
    (gomesTruncatedJetHorizonRestriction n r z E).val i j =
      E.val (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) i)
        (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) j) :=
  gomesFiniteFockHorizonRestriction_apply n r
    (Subalgebra.inclusion (gomesTruncatedJetJointAlgebra_le_clock (n + r) z) E) i j

/-- Restricting the actual geometry retains its scalar observation exactly. -/
theorem gomesTruncatedJetHorizonRestriction_augmentation (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra (n + r) z) :
    gomesTruncatedJetAugmentation n z (gomesTruncatedJetHorizonRestriction n r z E) =
      gomesTruncatedJetAugmentation (n + r) z E :=
  gomesTruncatedJetHorizonRestriction_apply n r z E 0 0

/-- Actual matrix restriction and the existing geometric arc quotient form a commuting square. -/
theorem gomesTruncatedJetHorizonRestriction_arc (n r : ℕ) (z : ℂ)
    (E : gomesTruncatedJetJointAlgebra (n + r) z) :
    gomesTruncatedJetArcEmbedding n z (gomesTruncatedJetHorizonRestriction n r z E) =
      truncateArcAlgHom ℂ (Nat.le_add_right n r) (gomesTruncatedJetArcEmbedding (n + r) z E) := by
  apply (gomesFiniteFockArcEquiv n).injective
  apply Subtype.ext
  rw [gomesTruncatedJetArcEmbedding_matrix]
  rfl

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
