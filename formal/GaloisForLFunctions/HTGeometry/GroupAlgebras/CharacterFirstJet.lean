import GaloisForLFunctions.HTGeometry.GroupAlgebras.FirstJet

/-!
# First jets at multiplicative characters

Multiplying each group basis vector by a character gives an algebra automorphism;
the inverse character gives its inverse. Transporting the universal first jet
through this automorphism detects the square of the character's augmentation
kernel. This distinguishes first-order neighborhoods of different characters.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet
variable {R G : Type*} [CommRing R] [CommGroup G]

/-- Character-weighted group labels. -/
def twistLabel (χ : G →* R) : G →* MonoidAlgebra R G where
  toFun g := χ g • MonoidAlgebra.of R G g
  map_one' := by rw [map_one, map_one, one_smul]
  map_mul' a b := by simp

/-- The algebra map multiplying each coefficient by its group character. -/
def twist (χ : G →* R) : MonoidAlgebra R G →ₐ[R] MonoidAlgebra R G :=
  MonoidAlgebra.lift R _ G (twistLabel χ)

@[simp] theorem twist_of (χ : G →* R) (g : G) :
    twist χ (MonoidAlgebra.of R G g) = χ g • MonoidAlgebra.of R G g := by
  simp [twist, twistLabel]

/-- The reciprocal character, obtained by inverting group labels. -/
def inverseCharacter (χ : G →* R) : G →* R := χ.comp (invMonoidHom : G →* G)

theorem inverseCharacter_mul (χ : G →* R) (g : G) : inverseCharacter χ g * χ g = 1 := by
  change χ g⁻¹ * χ g = 1
  rw [← map_mul, inv_mul_cancel, map_one]

theorem twist_inverse (χ : G →* R) (v : MonoidAlgebra R G) :
    twist (inverseCharacter χ) (twist χ v) = v := by
  have h : (twist (inverseCharacter χ)).toLinearMap.comp (twist χ).toLinearMap =
      LinearMap.id := by
    apply (MonoidAlgebra.basis G R).ext
    intro g
    change twist (inverseCharacter χ) (twist χ (MonoidAlgebra.of R G g)) = _
    rw [twist_of, map_smul, twist_of, smul_smul, mul_comm,
      inverseCharacter_mul, one_smul]
    rfl
  exact LinearMap.congr_fun h v

/-- Character twisting is an algebra automorphism. -/
def twistEquiv (χ : G →* R) : MonoidAlgebra R G ≃ₐ[R] MonoidAlgebra R G :=
  { twist χ with
    invFun := twist (inverseCharacter χ)
    left_inv := twist_inverse χ
    right_inv := by
      intro v
      change twist χ (twist (inverseCharacter χ) v) = v
      have h := twist_inverse (inverseCharacter χ) v
      have he : inverseCharacter (inverseCharacter χ) = χ := by ext g; simp [inverseCharacter]
      simpa only [he] using h }

/-- Coefficient summation weighted by a multiplicative character. -/
def characterAugmentation (χ : G →* R) : MonoidAlgebra R G →ₐ[R] R :=
  MonoidAlgebra.lift R R G χ

theorem augmentation_twist (χ : G →* R) (v : MonoidAlgebra R G) :
    augmentation R G (twist χ v) = characterAugmentation χ v := by
  have h : (augmentation R G).toLinearMap.comp (twist χ).toLinearMap =
      (characterAugmentation χ).toLinearMap := by
    apply (MonoidAlgebra.basis G R).ext
    intro g
    change augmentation R G (twist χ (MonoidAlgebra.of R G g)) = _
    rw [twist_of, map_smul, augmentation_of]
    simp [characterAugmentation]
  exact LinearMap.congr_fun h v

theorem comap_square_equiv {A B : Type*} [CommRing A] [CommRing B]
    (e : A ≃+* B) (I : Ideal B) :
    (I^2).comap e.toRingHom = (I.comap e.toRingHom)^2 := by
  calc
    (I^2).comap e.toRingHom = (I^2).map e.symm.toRingHom := (Ideal.map_symm e).symm
    _ = (I.map e.symm.toRingHom)^2 := Ideal.map_pow _ _ _
    _ = (I.comap e.toRingHom)^2 := congrArg (fun J : Ideal A => J^2) (Ideal.map_symm e)

/-- The first jet at a character detects exactly the square of its augmentation kernel. -/
theorem character_jet_ker (χ : G →* R) :
    RingHom.ker ((jet R G).comp (twist χ)).toRingHom =
      (RingHom.ker (characterAugmentation χ).toRingHom)^2 := by
  have he : (augmentationIdeal R G).comap (twistEquiv χ).toRingHom =
      RingHom.ker (characterAugmentation χ).toRingHom := by
    ext v
    change augmentation R G (twist χ v) = 0 ↔ characterAugmentation χ v = 0
    rw [augmentation_twist]
  calc
    _ = (RingHom.ker (jet R G).toRingHom).comap (twistEquiv χ).toRingHom := rfl
    _ = ((augmentationIdeal R G)^2).comap (twistEquiv χ).toRingHom := by rw [jet_ker_eq_square]
    _ = ((augmentationIdeal R G).comap (twistEquiv χ).toRingHom)^2 :=
      comap_square_equiv (twistEquiv χ).toRingEquiv _
    _ = _ := by rw [he]

#print axioms character_jet_ker
end GaloisForLFunctions.HTGeometry.GroupAlgebraFirstJet
