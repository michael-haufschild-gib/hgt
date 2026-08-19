import GaloisForLFunctions.HTGeometry.SigmaJetCoordinateEquiv
import GaloisForLFunctions.HTGeometry.FractionRingDerivation

/-!
# Extending a derivation to an arbitrary localization

The parameterized coordinate ring is the differential polynomial ring localized at the determinant,
not its fraction field, so the fraction-field extension of a derivation is not enough.  The same
dual-numbers argument works for any localization: the graph `a ↦ (a, D a)` lands in the square-zero
extension, every element of the multiplicative set maps to a unit there because its first coordinate
is a unit in the localization, and the universal property extends the graph.  The second coordinate
of the extension is the quotient-rule derivation.

This is a mathlib gap: mathlib has no derivation on a general localization.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K A S : Type*} [CommRing K] [CommRing A] [CommRing S]
  [Algebra K A] [Algebra A S] [Algebra K S] [IsScalarTower K A S]

/-- The square-zero graph algebra homomorphism attached to a derivation into a localization. -/
def localizationGraphAlgHom (D : Derivation K A S) : A →ₐ[K] TrivSqZeroExt S S where
  toFun a := (algebraMap A S a, D a)
  map_one' := by apply TrivSqZeroExt.ext <;> simp
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · simp
    · simp [Derivation.leibniz, Algebra.smul_def, mul_comm]
  map_zero' := by apply TrivSqZeroExt.ext <;> simp
  map_add' a b := by apply TrivSqZeroExt.ext <;> simp
  commutes' k := by
    apply TrivSqZeroExt.ext
    · show algebraMap A S (algebraMap K A k) = _
      rw [← IsScalarTower.algebraMap_apply K A S]
      rfl
    · show D (algebraMap K A k) = _
      rw [Derivation.map_algebraMap]
      rfl

variable (M : Submonoid A) [IsLocalization M S]

theorem localizationGraphAlgHom_isUnit (D : Derivation K A S) (s : M) :
    IsUnit (localizationGraphAlgHom D s.1) := by
  rw [TrivSqZeroExt.isUnit_iff_isUnit_fst]
  show IsUnit (algebraMap A S s.1)
  exact IsLocalization.map_units S s

/-- The graph homomorphism extended through the localization. -/
def localizationDerivationGraphLift (D : Derivation K A S) : S →+* TrivSqZeroExt S S :=
  IsLocalization.lift (localizationGraphAlgHom_isUnit M D)

theorem localizationDerivationGraphLift_algebraMap (D : Derivation K A S) (a : A) :
    localizationDerivationGraphLift M D (algebraMap A S a) = localizationGraphAlgHom D a :=
  RingHom.congr_fun (IsLocalization.lift_comp (localizationGraphAlgHom_isUnit M D)) a

theorem localizationDerivationGraphLift_fst (D : Derivation K A S) (z : S) :
    (localizationDerivationGraphLift M D z).fst = z := by
  let f : S →+* S :=
    (TrivSqZeroExt.fstHom K S S).toRingHom.comp (localizationDerivationGraphLift M D)
  have hf : f.comp (algebraMap A S) = (RingHom.id S).comp (algebraMap A S) := by
    ext a
    simp only [RingHom.coe_comp, Function.comp_apply, RingHom.id_apply, f,
      localizationDerivationGraphLift_algebraMap]
    rfl
  have heq : f = RingHom.id S := IsLocalization.ringHom_ext M hf
  exact RingHom.congr_fun heq z

/-- **A derivation extends to any localization.** -/
def localizationDerivation (D : Derivation K A S) : Derivation K S S :=
  Derivation.mk'
    { toFun := fun z => (localizationDerivationGraphLift M D z).snd
      map_add' := by
        intro x y
        exact congrArg TrivSqZeroExt.snd (map_add (localizationDerivationGraphLift M D) x y)
      map_smul' := by
        intro k z
        simp only [Algebra.smul_def]
        rw [map_mul (localizationDerivationGraphLift M D), TrivSqZeroExt.snd_mul,
          localizationDerivationGraphLift_fst]
        have hbase : localizationDerivationGraphLift M D (algebraMap K S k)
            = localizationGraphAlgHom D (algebraMap K A k) := by
          rw [IsScalarTower.algebraMap_apply K A S]
          exact localizationDerivationGraphLift_algebraMap M D _
        rw [hbase]
        have hzero : ((localizationGraphAlgHom D) ((algebraMap K A) k)).snd = 0 := by
          show D (algebraMap K A k) = 0
          exact Derivation.map_algebraMap D k
        rw [hzero, smul_zero, add_zero]
        simp }
    (by
      intro x y
      change (localizationDerivationGraphLift M D (x * y)).snd =
        x • (localizationDerivationGraphLift M D y).snd +
          y • (localizationDerivationGraphLift M D x).snd
      rw [map_mul (localizationDerivationGraphLift M D), TrivSqZeroExt.snd_mul,
        localizationDerivationGraphLift_fst, localizationDerivationGraphLift_fst]
      simp [smul_eq_mul, mul_comm])

@[simp] theorem localizationDerivation_apply (D : Derivation K A S) (z : S) :
    localizationDerivation M D z = (localizationDerivationGraphLift M D z).snd := rfl

/-- The extension restricts to the original derivation. -/
theorem localizationDerivation_algebraMap (D : Derivation K A S) (a : A) :
    localizationDerivation M D (algebraMap A S a) = D a := by
  rw [localizationDerivation_apply, localizationDerivationGraphLift_algebraMap]
  rfl

end

end GaloisForLFunctions.HTGeometry
