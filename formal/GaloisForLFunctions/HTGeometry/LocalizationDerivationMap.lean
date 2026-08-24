import GaloisForLFunctions.HTGeometry.LocalizationDerivation

/-!
# Derivation-preserving maps out of localizations

A ring homomorphism out of a localization commutes with two derivations once
it commutes on the base ring.  Equality follows by packaging each side as a
homomorphism to the square-zero extension and invoking localization
extensionality.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {A S T : Type*} [CommRing A] [CommRing S] [CommRing T]
  [Algebra A S]

/-- A ring hom out of a localization commutes with derivations if it does so
on the base ring. -/
theorem localization_ringHom_derivation_commutes_of_base
    (M : Submonoid A) [IsLocalization M S]
    (Dₛ : Derivation ℤ S S) (Dₜ : Derivation ℤ T T) (phi : S →+* T)
    (hbase : ∀ a : A,
      phi (Dₛ (algebraMap A S a)) = Dₜ (phi (algebraMap A S a)))
    (x : S) : phi (Dₛ x) = Dₜ (phi x) := by
  let lhs : S →+* TrivSqZeroExt T T :=
    { toFun := fun z => (phi z, phi (Dₛ z))
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]
          ring }
  let rhs : S →+* TrivSqZeroExt T T :=
    { toFun := fun z => (phi z, Dₜ (phi z))
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]
          ring }
  have heq : lhs = rhs := by
    apply IsLocalization.ringHom_ext M
    ext a <;> simp [lhs, rhs, hbase]
  have hx := RingHom.congr_fun heq x
  exact congrArg TrivSqZeroExt.snd hx

/-- The graph-lift extension of a base derivation is transported by every
ring hom whose target derivation agrees on the base. -/
theorem localizationDerivationGraphLift_ringHom_commutes_of_base
    (M : Submonoid A) [IsLocalization M S]
    (D : Derivation ℤ A S) (Dₜ : Derivation ℤ T T) (phi : S →+* T)
    (hbase : ∀ a : A, phi (D a) = Dₜ (phi (algebraMap A S a)))
    (x : S) :
    phi ((localizationDerivationGraphLift M D x).snd) = Dₜ (phi x) := by
  let lhs : S →+* TrivSqZeroExt T T :=
    { toFun := fun z =>
        (phi z, phi ((localizationDerivationGraphLift M D z).snd))
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · simp [localizationDerivationGraphLift_fst] }
  let rhs : S →+* TrivSqZeroExt T T :=
    { toFun := fun z => (phi z, Dₜ (phi z))
      map_zero' := by ext <;> simp
      map_one' := by ext <;> simp
      map_add' := by intro a b; ext <;> simp
      map_mul' := by
        intro a b
        apply TrivSqZeroExt.ext
        · simp
        · simp [Derivation.leibniz, smul_eq_mul]
          ring }
  have heq : lhs = rhs := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro a
    change (phi (algebraMap A S a),
        phi ((localizationDerivationGraphLift M D
          (algebraMap A S a)).snd)) =
      (phi (algebraMap A S a), Dₜ (phi (algebraMap A S a)))
    apply TrivSqZeroExt.ext
    · rfl
    · rw [localizationDerivationGraphLift_algebraMap]
      exact hbase a
  have hx := RingHom.congr_fun heq x
  exact congrArg TrivSqZeroExt.snd hx

end

end GaloisForLFunctions.HTGeometry
