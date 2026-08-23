import GaloisForLFunctions.HTGeometry.HasseExactSequence
import GaloisForLFunctions.HTGeometry.MilnorPolynomialGlobalReciprocityQuotient

/-!
# Hasse classification for projective-line Milnor residues

Compatible finite-and-infinite residue profiles have global Milnor representatives unique modulo
constant-field classes.  Equality of profiles is exactly congruence modulo constants.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable section

variable {F : Type*} [Field F]

local instance milnorPolynomialGlobalResidueHasseDecidableEqMonicIrred :
    DecidableEq (MonicIrred F) := Classical.decEq _

/-- Global Milnor classes have the same all-place residue profile exactly when they differ by a
constant-field class. -/
theorem milnorPolynomialGlobalResidue_congr_hasse_iff
    (n : ℕ) (x y : MilnorKDeg (RatFunc F) n.succ) :
    x - y ∈ AddMonoidHom.range (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) ↔
      milnorPolynomialAllResidueToGlobalSumKer (F := F) n x =
        milnorPolynomialAllResidueToGlobalSumKer (F := F) n y :=
  addHasse_congr_iff
    (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
    (milnorPolynomialAllResidueToGlobalSumKer (F := F) n)
    (AddMonoidHom.exact_iff.mpr
      (milnorPolynomialAllResidueToGlobalSumKer_ker_eq_constRange (F := F) n)) x y

/-- Every compatible all-place residue profile has a global Milnor representative, unique modulo
constant-field classes. -/
theorem milnorPolynomialGlobalResidue_exists_unique_mod_constants
    (n : ℕ) (z : (milnorPolynomialGlobalSum (F := F) n).ker) :
    ∃ x : MilnorKDeg (RatFunc F) n.succ,
      milnorPolynomialAllResidueToGlobalSumKer (F := F) n x = z ∧
      ∀ y : MilnorKDeg (RatFunc F) n.succ,
        milnorPolynomialAllResidueToGlobalSumKer (F := F) n y = z ↔
          y - x ∈ AddMonoidHom.range
            (milnorKDegMap (ratFuncConstHom (F := F)) n.succ) :=
  addHasse_exists_unique_mod_global
    (milnorKDegMap (ratFuncConstHom (F := F)) n.succ)
    (milnorPolynomialAllResidueToGlobalSumKer (F := F) n)
    (AddMonoidHom.exact_iff.mpr
      (milnorPolynomialAllResidueToGlobalSumKer_ker_eq_constRange (F := F) n))
    (milnorPolynomialAllResidueToGlobalSumKer_surjective (F := F) n) z

end
end GaloisForLFunctions.HTGeometry
