import GaloisForLFunctions.HTGeometry.GomesFiniteFockTruncatedArcEquiv
import GaloisForLFunctions.HTGeometry.GomesFiniteFockFormalSeries

/-!
# Actual finite clock symmetries under horizon restriction

The existing arc quotient map induces a surjective algebra homomorphism
between the complete matrix clock commutants. Its matrix action is the
literal upper-left block, and every polynomial symbol is retained.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GammaFactorialFock

/-- Restrict the complete clock algebra from horizon `n + r` to horizon `n`. -/
def gomesFiniteFockHorizonRestriction (n r : ℕ) :
    gomesFiniteFockCommutant (n + r + 1) →ₐ[ℂ] gomesFiniteFockCommutant (n + 1) :=
  (gomesFiniteFockArcEquiv n).toAlgHom.comp
    ((truncateArcAlgHom ℂ (Nat.le_add_right n r)).comp
      (gomesFiniteFockArcEquiv (n + r)).symm.toAlgHom)

/-- Restriction preserves every actual polynomial symbol, interpreted at the smaller horizon. -/
theorem gomesFiniteFockHorizonRestriction_symbol (n r : ℕ) (p : Polynomial ℂ) :
    gomesFiniteFockHorizonRestriction n r (gomesFiniteFockSymbolHom (n + r + 1) p) =
      gomesFiniteFockSymbolHom (n + 1) p := by
  have hp : gomesFiniteFockSymbolHom (n + r + 1) p =
      gomesFiniteFockArcEquiv (n + r) (Ideal.Quotient.mk (truncatedArcIdeal ℂ (n + r)) p) := rfl
  change gomesFiniteFockArcEquiv n
    (truncateArcAlgHom ℂ (Nat.le_add_right n r)
      ((gomesFiniteFockArcEquiv (n + r)).symm (gomesFiniteFockSymbolHom (n + r + 1) p))) = _
  rw [hp, AlgEquiv.symm_apply_apply, truncateArcAlgHom_mk]
  rfl

/-- Restriction acts by the literal upper-left block on every actual clock symmetry. -/
theorem gomesFiniteFockHorizonRestriction_apply (n r : ℕ)
    (E : gomesFiniteFockCommutant (n + r + 1)) (i j : Fin (n + 1)) :
    (gomesFiniteFockHorizonRestriction n r E).val i j =
      E.val (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) i)
        (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) j) := by
  obtain ⟨p, rfl⟩ := gomesFiniteFockSymbolHom_surjective (n + r + 1) E
  rw [gomesFiniteFockHorizonRestriction_symbol]
  rfl

/-- Every formal clock symbol is compatible with actual geometric horizon restriction. -/
theorem gomesFiniteFockHorizonRestriction_formal (n r : ℕ) (F : PowerSeries ℂ) :
    gomesFiniteFockHorizonRestriction n r (gomesFiniteFockFormalSymbolHom (n + r + 1) F) =
      gomesFiniteFockFormalSymbolHom (n + 1) F := by
  apply Subtype.ext
  apply Matrix.ext
  intro i j
  rw [gomesFiniteFockHorizonRestriction_apply]
  change gomesFiniteFockFormalHom (n + r + 1) F
    (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) i)
    (Fin.castLE (Nat.add_le_add_right (Nat.le_add_right n r) 1) j) =
      gomesFiniteFockFormalHom (n + 1) F i j
  rw [gomesFiniteFockFormalHom_apply, gomesFiniteFockFormalHom_apply]
  rfl

/-- Every lower-horizon clock symmetry lifts to an actual higher-horizon clock symmetry. -/
theorem gomesFiniteFockHorizonRestriction_surjective (n r : ℕ) :
    Function.Surjective (gomesFiniteFockHorizonRestriction n r) := by
  intro E
  obtain ⟨p, rfl⟩ := gomesFiniteFockSymbolHom_surjective (n + 1) E
  exact ⟨gomesFiniteFockSymbolHom (n + r + 1) p, gomesFiniteFockHorizonRestriction_symbol n r p⟩

/-- Restricting by no extra jet coefficients is the identity algebra homomorphism. -/
theorem gomesFiniteFockHorizonRestriction_zero (n : ℕ) :
    gomesFiniteFockHorizonRestriction n 0 = AlgHom.id ℂ (gomesFiniteFockCommutant (n + 1)) := by
  apply AlgHom.ext
  intro E
  obtain ⟨p, rfl⟩ := gomesFiniteFockSymbolHom_surjective (n + 1) E
  exact gomesFiniteFockHorizonRestriction_symbol n 0 p

end GaloisForLFunctions.HTGeometry.GammaFactorialFock
