import GaloisForLFunctions.HTGeometry.ProjectiveHorizonSchwarzianCoordinates
import GaloisForLFunctions.HTGeometry.FreeCoordinateSupportKernel

/-!
# The leading jet derivatives of the Schwarzian jets

The jet shift lowers a coordinate derivation by one: the bracket of the derivation along the
`(m+1)`-st coordinate with the shift is the derivation along the `m`-th.  Iterating this against the
Schwarzian, whose only third-order term is `x'''/x'`, shows that the `k`-th Schwarzian jet involves
no coordinate beyond order `k+3` and has leading derivative exactly `1/x'` there.

So the Schwarzian jets are triangular against the coordinate derivations, which is what makes the
Schwarzian coordinate system algebraically independent.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential

variable {C : Type*} [Field C] [CharZero C]

/-! ## The shift lowers a coordinate derivation -/

theorem freeJetShiftPolynomialDerivation_lie (C : Type*) [Field C] (m : ℕ) :
    ⁅MvPolynomial.pderiv (R := C) (m + 1), freeJetShiftPolynomialDerivation C⁆ =
      MvPolynomial.pderiv m := by
  apply MvPolynomial.derivation_ext
  intro l
  rw [Derivation.commutator_apply, freeJetShiftPolynomialDerivation_X]
  rcases eq_or_ne l m with rfl | hlm
  · rw [MvPolynomial.pderiv_X_self, MvPolynomial.pderiv_X_of_ne (by omega),
      map_zero, sub_zero, MvPolynomial.pderiv_X_self]
  · rcases eq_or_ne l (m + 1) with rfl | hlm1
    · rw [MvPolynomial.pderiv_X_of_ne (by omega), MvPolynomial.pderiv_X_self,
        Derivation.map_one_eq_zero, sub_zero, MvPolynomial.pderiv_X_of_ne hlm]
    · rw [MvPolynomial.pderiv_X_of_ne (by omega), MvPolynomial.pderiv_X_of_ne hlm1,
        map_zero, sub_zero, MvPolynomial.pderiv_X_of_ne hlm]

/-- **The jet shift lowers a coordinate derivation.** -/
theorem freeCoordinateDerivation_lie_shift (C : Type*) [Field C] (m : ℕ) :
    ⁅freeCoordinateDerivation C ℕ (m + 1), freeJetShift C⁆ =
      freeCoordinateDerivation C ℕ m := by
  rw [freeCoordinateDerivation, freeJetShift, extendFreeCoordinatePolynomialDerivation_lie,
    freeJetShiftPolynomialDerivation_lie]
  rfl

theorem freeCoordinateDerivation_shift_apply (C : Type*) [Field C] (m : ℕ)
    (f : FreeScalarJetField C) :
    freeCoordinateDerivation C ℕ (m + 1) (freeJetShift C f) =
      freeJetShift C (freeCoordinateDerivation C ℕ (m + 1) f) +
        freeCoordinateDerivation C ℕ m f := by
  have h := congrArg (fun D : Derivation C (FreeScalarJetField C) (FreeScalarJetField C) => D f)
    (freeCoordinateDerivation_lie_shift C m)
  simp only [Derivation.commutator_apply] at h
  rw [← h]
  ring

/-! ## The Schwarzian sits in the first three positive jets -/

omit [CharZero C] in
theorem freeJetSchwarzian_mem :
    freeJetSchwarzian C ∈ freeCoordinateField C ℕ ({1, 2, 3} : Set ℕ) := by
  have h1 : freeCoordinate C ℕ 1 ∈ freeCoordinateField C ℕ ({1, 2, 3} : Set ℕ) :=
    IntermediateField.subset_adjoin _ _ ⟨1, by simp, rfl⟩
  have h2 : freeCoordinate C ℕ 2 ∈ freeCoordinateField C ℕ ({1, 2, 3} : Set ℕ) :=
    IntermediateField.subset_adjoin _ _ ⟨2, by simp, rfl⟩
  have h3 : freeCoordinate C ℕ 3 ∈ freeCoordinateField C ℕ ({1, 2, 3} : Set ℕ) :=
    IntermediateField.subset_adjoin _ _ ⟨3, by simp, rfl⟩
  rw [freeJetSchwarzian, schwarzian, freeJetBase_deriv3, freeJetBase_deriv2, freeJetBase_deriv]
  exact sub_mem (div_mem h3 h1)
    (mul_mem (div_mem (by simp) (by simp)) (pow_mem (div_mem h2 h1) 2))

omit [CharZero C] in
theorem freeCoordinateDerivation_freeJetSchwarzian_of_gt {m : ℕ} (hm : 3 < m) :
    freeCoordinateDerivation C ℕ m (freeJetSchwarzian C) = 0 :=
  freeCoordinateField_le_commonKernel ({1, 2, 3} : Set ℕ) freeJetSchwarzian_mem m
    (by simp; omega)

theorem freeCoordinateDerivation_freeJetSchwarzian_three :
    freeCoordinateDerivation C ℕ 3 (freeJetSchwarzian C) = (freeCoordinate C ℕ 1)⁻¹ := by
  have h1 : freeCoordinateDerivation C ℕ 3 (freeCoordinate C ℕ 1) = 0 :=
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  have h2 : freeCoordinateDerivation C ℕ 3 (freeCoordinate C ℕ 2) = 0 :=
    freeCoordinateDerivation_freeCoordinate_of_ne (by omega)
  have h3 : freeCoordinateDerivation C ℕ 3 (freeCoordinate C ℕ 3) = 1 :=
    freeCoordinateDerivation_freeCoordinate_self 3
  have hne : freeCoordinate C ℕ 1 ≠ 0 := freeScalarJetCoordinate_ne_zero 1
  have hc : freeCoordinateDerivation C ℕ 3 (3 / 2 : FreeScalarJetField C) = 0 := by
    have hnum : (3 / 2 : FreeScalarJetField C) =
        algebraMap C (FreeScalarJetField C) ((3 : C) / 2) := by
      rw [map_div₀]
      norm_num [map_ofNat]
    rw [hnum]
    exact Derivation.map_algebraMap _ _
  rw [freeJetSchwarzian, schwarzian, freeJetBase_deriv3, freeJetBase_deriv2, freeJetBase_deriv,
    map_sub, Derivation.leibniz_div, h1, h3, Derivation.leibniz, Derivation.leibniz_pow,
    Derivation.leibniz_div, h1, h2, hc]
  simp only [smul_eq_mul, smul_zero, mul_zero, sub_zero, mul_one]
  field_simp
  ring

/-! ## The Schwarzian jets are triangular -/

omit [CharZero C] in
/-- The `k`-th Schwarzian jet involves no coordinate beyond order `k+3`. -/
theorem freeCoordinateDerivation_schwarzianJet_of_gt :
    ∀ (k m : ℕ), k + 3 < m →
      freeCoordinateDerivation C ℕ m (differentialJet k (freeJetSchwarzian C)) = 0 := by
  intro k
  induction k with
  | zero =>
      intro m hm
      rw [differentialJet_zero]
      exact freeCoordinateDerivation_freeJetSchwarzian_of_gt (by omega)
  | succ k ih =>
      intro m hm
      obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      rw [differentialJet_succ, freeScalarJetField_deriv_apply,
        freeCoordinateDerivation_shift_apply, ih m' (by omega), ih (m' + 1) (by omega),
        map_zero, add_zero]

/-- **The leading jet derivative of a Schwarzian jet.** -/
theorem freeCoordinateDerivation_schwarzianJet_top :
    ∀ k : ℕ, freeCoordinateDerivation C ℕ (k + 3) (differentialJet k (freeJetSchwarzian C)) =
      (freeCoordinate C ℕ 1)⁻¹ := by
  intro k
  induction k with
  | zero =>
      rw [differentialJet_zero]
      exact freeCoordinateDerivation_freeJetSchwarzian_three
  | succ k ih =>
      rw [show k + 1 + 3 = (k + 3) + 1 from by omega, differentialJet_succ,
        freeScalarJetField_deriv_apply, freeCoordinateDerivation_shift_apply,
        freeCoordinateDerivation_schwarzianJet_of_gt k (k + 3 + 1) (by omega), map_zero,
        zero_add, ih]

end

end GaloisForLFunctions.HTGeometry
