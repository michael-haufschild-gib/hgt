import GaloisForLFunctions.HTGeometry.PaperDiscriminantClockRigidity

/-!
# Root generators and units on the ordered discriminant complement

Every root difference is invertible on this native localization. The
source factorial-closure theorem therefore forces every locally
nilpotent derivation to have the same value on all root generators.
Derivations of the localization are determined by those generators.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial StableCoordinate

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

instance paperRootDiscriminantOpen_isDomain (n : ℕ) :
    IsDomain (PaperRootDiscriminantOpen K n) := by
  have hV : paperUniversalVandermonde K n ≠ 0 := vandermondeProd_ne_zero X_injective
  exact IsLocalization.isDomain_of_le_nonZeroDivisors _
    (powers_le_nonZeroDivisors_of_noZeroDivisors (pow_ne_zero 2 hV))

instance paperRootDiscriminantOpen_charZero [CharZero K] (n : ℕ) :
    CharZero (PaperRootDiscriminantOpen K n) :=
  Algebra.charZero_of_charZero K _

/-- A root coordinate in the actual native discriminant-open ring. -/
def paperDiscriminantRoot (i : Fin n) : PaperRootDiscriminantOpen K n :=
  algebraMap (MvPolynomial (Fin n) K) (PaperRootDiscriminantOpen K n) (X i)

/-- The already proved common unit-translation derivation on the root localization. -/
def paperDiscriminantTranslation (K : Type*) [Field K] (n : ℕ) :
    Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n) :=
  paperRootDiscriminantVectorField (fun _ : Fin n => (1 : K))

/-- Every ordered root difference is invertible after discriminant inversion. -/
theorem paperDiscriminantRoot_sub_isUnit {i j : Fin n} (hij : i < j) :
    IsUnit (paperDiscriminantRoot (K := K) j - paperDiscriminantRoot i) := by
  have hv : paperUniversalVandermonde K n ∣ paperUniversalVandermonde K n ^ 2 :=
    ⟨paperUniversalVandermonde K n, pow_two _⟩
  have h := IsLocalization.Away.isUnit_of_dvd
    (S := PaperRootDiscriminantOpen K n) (paperUniversalVandermonde K n ^ 2)
    ((paperVariableDifference_dvd_vandermonde hij).trans hv)
  simpa only [map_sub, paperDiscriminantRoot] using h

private theorem localization_ext
    {A S : Type*} [CommRing A] [CommRing S] [Algebra K A] [Algebra K S]
    [Algebra A S] [IsScalarTower K A S]
    (M : Submonoid A) [IsLocalization M S]
    (D E : Derivation K S S)
    (h : ∀ a : A, D (algebraMap A S a) = E (algebraMap A S a)) : D = E := by
  ext z
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj M z
  have hunit := IsLocalization.map_units S s
  have he : D (z * algebraMap A S (s : A)) = E (z * algebraMap A S (s : A)) := by
    rw [hs]
    exact h a
  rw [Derivation.leibniz, Derivation.leibniz] at he
  simp only [smul_eq_mul, h (s : A)] at he
  have hc : algebraMap A S (s : A) * D z = algebraMap A S (s : A) * E z :=
    add_left_cancel he
  obtain ⟨u, hu⟩ := hunit
  rw [← hu] at hc
  exact (Units.mul_right_inj u).mp hc

/-- Root values determine every derivation on the discriminant-open ring. -/
theorem paperDiscriminantRoot_derivation_ext
    {D E : Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n)}
    (h : ∀ i, D (paperDiscriminantRoot i) = E (paperDiscriminantRoot i)) : D = E := by
  have hb : D.compAlgebraMap (MvPolynomial (Fin n) K) =
      E.compAlgebraMap (MvPolynomial (Fin n) K) := derivation_ext h
  apply localization_ext (Submonoid.powers (paperUniversalVandermonde K n ^ 2))
  intro a
  exact congrArg
    (fun d : Derivation K (MvPolynomial (Fin n) K) (PaperRootDiscriminantOpen K n) => d a) hb

/-- Common translation has unit derivative on every root coordinate. -/
@[simp] theorem paperDiscriminantTranslation_root (i : Fin n) :
    paperDiscriminantTranslation K n (paperDiscriminantRoot i) = 1 := by
  simp only [paperDiscriminantTranslation, paperDiscriminantRoot,
    paperRootDiscriminantVectorField, paperNativeLocalization_algebraMap,
    constVectorField_X, map_one]

variable [CharZero K]

/-- The common translation is locally nilpotent on the full localization. -/
theorem paperDiscriminantTranslation_locallyNilpotent (n : ℕ) :
    IsLocallyNilpotent (paperDiscriminantTranslation K n) :=
  paperRootDiscriminantTranslation_locallyNilpotent n 1

/-- Every locally nilpotent derivation moves all root coordinates by the same amount. -/
theorem paperDiscriminantRoot_lnd_values_eq
    (D : Derivation K (PaperRootDiscriminantOpen K n) (PaperRootDiscriminantOpen K n))
    (hD : IsLocallyNilpotent D) (i j : Fin n) :
    D (paperDiscriminantRoot i) = D (paperDiscriminantRoot j) := by
  have hlt : ∀ i j : Fin n, i < j →
      D (paperDiscriminantRoot i) = D (paperDiscriminantRoot j) := by
    intro i j hij
    obtain ⟨u, hu⟩ := paperDiscriminantRoot_sub_isUnit (K := K) hij
    have hz := paperLocallyNilpotent_kills_unit D hD u
    rw [hu, map_sub] at hz
    exact (sub_eq_zero.mp hz).symm
  rcases lt_trichotomy i j with hij | hij | hij
  · exact hlt i j hij
  · exact congrArg (fun i => D (paperDiscriminantRoot i)) hij
  · exact (hlt j i hij).symm

end

end GaloisForLFunctions.HTGeometry
