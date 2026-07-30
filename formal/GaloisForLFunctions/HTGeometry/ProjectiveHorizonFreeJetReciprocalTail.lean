import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFreeJetCurrentCollapse
import GaloisForLFunctions.HTGeometry.ProjectiveHorizonFiniteJetRank

/-!
# Reciprocal tails in the raw free projective jet field

This file identifies the universal reciprocal-jet polynomials with the differential jets of the
inverse of the zeroth free raw coordinate.  The rational jet shift is the quotient-rule extension
of `x_n \mapsto x_(n+1)`.  Besides the opposite velocity current `F_1` constructed in
`ProjectiveHorizonFreeJetCurrentCollapse`, the constant opposite current is

`F_0(x_n) = -D^n(x^2)`.

They satisfy `[D,F_0]=0` and `[D,F_1]=-F_0`.  Since `F_0(x⁻¹)=1` and `F_1(x⁻¹)=0`, every reciprocal
jet of order at least two lies in the kernel of `F_1`.  Every raw jet of order at least one lies in
the kernel of `E_0`.  The established two-current fixed-field collapse therefore makes the raw
depth-`m` and reciprocal depth-`n` tails meet only in the coefficient field for `m \ge 1` and
`n \ge 2`.
-/

open scoped Differential

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-! ## The rational free-jet shift -/

/-- The total derivative on the rational free scalar jet field. -/
def freeJetShift
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  extendFreeCoordinatePolynomialDerivation (freeJetShiftPolynomialDerivation C)

@[simp]
theorem freeJetShift_algebraMap
    {C : Type*} [Field C] (P : FreeScalarJetPolynomial C) :
    freeJetShift C
        (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) P) =
      algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
        (freeJetShiftPolynomialDerivation C P) := by
  exact extendFreeCoordinatePolynomialDerivation_algebraMap
    (freeJetShiftPolynomialDerivation C) P

@[simp]
theorem freeJetShift_freeCoordinate
    {C : Type*} [Field C] (n : ℕ) :
    freeJetShift C (freeCoordinate C ℕ n) =
      freeCoordinate C ℕ (n + 1) := by
  rw [freeCoordinate, freeJetShift_algebraMap,
    freeJetShiftPolynomialDerivation_X]
  rfl

/-- The rational free-jet shift, regarded as the integer-linear derivation of a differential
field. -/
noncomputable instance freeScalarJetFieldDifferential
    (C : Type*) [Field C] : Differential (FreeScalarJetField C) := by
  letI : Algebra ℤ (FreeScalarJetField C) := Ring.toIntAlgebra _
  exact ⟨(freeJetShift C).restrictScalars ℤ⟩

@[simp]
theorem freeScalarJetField_deriv_apply
    {C : Type*} [Field C] (f : FreeScalarJetField C) :
    f′ = freeJetShift C f := rfl

/-- The differential jets of the zeroth free raw coordinate are exactly the free coordinates. -/
@[simp]
theorem differentialJet_freeCoordinate_zero
    {C : Type*} [Field C] (n : ℕ) :
    differentialJet n (freeCoordinate C ℕ 0) =
      freeCoordinate C ℕ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [differentialJet_succ, ih,
        freeScalarJetField_deriv_apply, freeJetShift_freeCoordinate]

/-- Every raw free coordinate is nonzero in the rational free-jet field. -/
theorem freeScalarJetCoordinate_ne_zero
    {C : Type*} [Field C] (n : ℕ) :
    freeCoordinate C ℕ n ≠ 0 := by
  intro hzero
  have h := congrArg (freeCoordinateDerivation C ℕ n) hzero
  simp at h

/-! ## The constant opposite current and its shift brackets -/

/-- The constant reciprocal-translation current on the polynomial raw free jet:
`F_0(x_n)=-D^n(x^2)`. -/
def freeJetFZeroPolynomialDerivation
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C) :=
  MvPolynomial.mkDerivation C fun n => -freeJetSquareCoefficient C n

@[simp]
theorem freeJetFZeroPolynomialDerivation_X
    {C : Type*} [Field C] (n : ℕ) :
    freeJetFZeroPolynomialDerivation C (MvPolynomial.X n) =
      -freeJetSquareCoefficient C n := by
  simp [freeJetFZeroPolynomialDerivation]

/-- The total derivative advances the universal square coefficient by one order. -/
@[simp]
theorem freeJetShiftPolynomialDerivation_squareCoefficient
    {C : Type*} [Field C] (n : ℕ) :
    freeJetShiftPolynomialDerivation C (freeJetSquareCoefficient C n) =
      freeJetSquareCoefficient C (n + 1) := by
  unfold freeJetSquareCoefficient
  rw [Function.iterate_succ_apply']

/-- The polynomial shift commutes with the constant opposite current. -/
theorem freeJetPolynomial_lie_shift_F_zero
    {C : Type*} [Field C] :
    ⁅freeJetShiftPolynomialDerivation C, freeJetFZeroPolynomialDerivation C⁆ = 0 := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply]
  simp [freeJetFZeroPolynomialDerivation]

/-- The first shifted opposite current satisfies `[D,F_1]=-F_0` on the polynomial raw jet. -/
theorem freeJetPolynomial_lie_shift_F_one
    {C : Type*} [Field C] :
    ⁅freeJetShiftPolynomialDerivation C, freeJetFOnePolynomialDerivation C⁆ =
      -freeJetFZeroPolynomialDerivation C := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply]
  cases n with
  | zero =>
      simp [freeJetFOnePolynomialDerivation,
        freeJetFZeroPolynomialDerivation, Algebra.smul_def]
  | succ n =>
      simp [freeJetFOnePolynomialDerivation,
        freeJetFZeroPolynomialDerivation, Algebra.smul_def]
      ring

/-- The constant opposite current on the rational raw free-jet field. -/
def freeJetFZero
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  extendFreeCoordinatePolynomialDerivation (freeJetFZeroPolynomialDerivation C)

@[simp]
theorem freeJetFZero_freeCoordinate
    {C : Type*} [Field C] (n : ℕ) :
    freeJetFZero C (freeCoordinate C ℕ n) =
      -algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
        (freeJetSquareCoefficient C n) := by
  rw [freeJetFZero, freeCoordinate,
    extendFreeCoordinatePolynomialDerivation_algebraMap,
    freeJetFZeroPolynomialDerivation_X, map_neg]

@[simp]
theorem freeJetFOne_freeCoordinate_zero
    {C : Type*} [Field C] :
    freeJetFOne C (freeCoordinate C ℕ 0) = 0 := by
  rw [freeJetFOne, freeCoordinate,
    extendFreeCoordinatePolynomialDerivation_algebraMap]
  simp [freeJetFOnePolynomialDerivation]

/-- Rational-field form of `[D,F_0]=0`. -/
theorem freeJet_lie_shift_F_zero
    {C : Type*} [Field C] :
    ⁅freeJetShift C, freeJetFZero C⁆ = 0 := by
  rw [freeJetShift, freeJetFZero, extendFreeCoordinatePolynomialDerivation_lie,
    freeJetPolynomial_lie_shift_F_zero,
    extendFreeCoordinatePolynomialDerivation_zero]

/-- Rational-field form of `[D,F_1]=-F_0`. -/
theorem freeJet_lie_shift_F_one
    {C : Type*} [Field C] :
    ⁅freeJetShift C, freeJetFOne C⁆ = -freeJetFZero C := by
  rw [freeJetShift, freeJetFOne, freeJetFZero,
    extendFreeCoordinatePolynomialDerivation_lie,
    freeJetPolynomial_lie_shift_F_one,
    extendFreeCoordinatePolynomialDerivation_neg]

/-- Pointwise commutation of the total derivative and `F_0`. -/
theorem freeJetFZero_freeJetShift
    {C : Type*} [Field C] (f : FreeScalarJetField C) :
    freeJetFZero C (freeJetShift C f) =
      freeJetShift C (freeJetFZero C f) := by
  have h := Derivation.congr_fun (freeJet_lie_shift_F_zero (C := C)) f
  rw [Derivation.commutator_apply] at h
  exact (sub_eq_zero.mp (by simpa using h)).symm

/-- Pointwise form of `[D,F_1]=-F_0`, solved for `F_1(Df)`. -/
theorem freeJetFOne_freeJetShift
    {C : Type*} [Field C] (f : FreeScalarJetField C) :
    freeJetFOne C (freeJetShift C f) =
      freeJetShift C (freeJetFOne C f) + freeJetFZero C f := by
  have h := Derivation.congr_fun (freeJet_lie_shift_F_one (C := C)) f
  rw [Derivation.commutator_apply, Derivation.neg_apply] at h
  linear_combination -h

/-! ## Universal reciprocal jets -/

/-- The universal reciprocal jet in the rational raw free-jet field. -/
noncomputable def freeJetReciprocalJet
    (C : Type*) [Field C] [CharZero C] (n : ℕ) : FreeScalarJetField C :=
  finiteReciprocalJetValue (F := C) (E := FreeScalarJetField C)
    (fun k => freeCoordinate C ℕ k) n

/-- The universal reciprocal polynomial is exactly the corresponding shift jet of `x_0⁻¹`. -/
theorem freeJetReciprocalJet_eq_differentialJet
    {C : Type*} [Field C] [CharZero C] (n : ℕ) :
    freeJetReciprocalJet C n =
      differentialJet n (freeCoordinate C ℕ 0)⁻¹ := by
  have h := finiteReciprocalJetValue_differentialJet_eq
    (F := C) (E := FreeScalarJetField C)
    (freeCoordinate C ℕ 0) (freeScalarJetCoordinate_ne_zero 0) n
  simpa [freeJetReciprocalJet] using h

@[simp]
theorem freeJetReciprocalJet_zero
    {C : Type*} [Field C] [CharZero C] :
    freeJetReciprocalJet C 0 = (freeCoordinate C ℕ 0)⁻¹ := by
  rw [freeJetReciprocalJet_eq_differentialJet, differentialJet_zero]

/-- The constant opposite current translates the reciprocal zeroth coordinate by one. -/
theorem freeJetFZero_freeCoordinate_zero_inv
    {C : Type*} [Field C] :
    freeJetFZero C (freeCoordinate C ℕ 0)⁻¹ = 1 := by
  let x := freeCoordinate C ℕ 0
  have hx : x ≠ 0 := freeScalarJetCoordinate_ne_zero 0
  have hsq :
      algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)
          (freeJetSquareCoefficient C 0) = x * x := by
    simp [freeJetSquareCoefficient, x, freeCoordinate]
  rw [(freeJetFZero C).leibniz_inv,
    freeJetFZero_freeCoordinate, hsq]
  simp only [smul_eq_mul]
  change -(x⁻¹) ^ 2 * -(x * x) = 1
  rw [neg_mul_neg]
  field_simp [hx]

/-- The first shifted opposite current fixes the reciprocal zeroth coordinate. -/
theorem freeJetFOne_freeCoordinate_zero_inv
    {C : Type*} [Field C] :
    freeJetFOne C (freeCoordinate C ℕ 0)⁻¹ = 0 := by
  rw [(freeJetFOne C).leibniz_inv, freeJetFOne_freeCoordinate_zero]
  simp

/-- `F_0` kills every positive differential jet of the reciprocal zeroth coordinate. -/
theorem freeJetFZero_differentialJet_inv_succ
    {C : Type*} [Field C] (n : ℕ) :
    freeJetFZero C
        (differentialJet (n + 1) (freeCoordinate C ℕ 0)⁻¹) = 0 := by
  induction n with
  | zero =>
      rw [differentialJet_succ, differentialJet_zero,
        freeScalarJetField_deriv_apply, freeJetFZero_freeJetShift,
        freeJetFZero_freeCoordinate_zero_inv]
      simp
  | succ n ih =>
      rw [show n.succ + 1 = (n + 1) + 1 by omega,
        differentialJet_succ, freeScalarJetField_deriv_apply,
        freeJetFZero_freeJetShift, ih]
      simp

/-- `F_1` takes the first reciprocal jet to one. -/
theorem freeJetFOne_differentialJet_inv_one
    {C : Type*} [Field C] :
    freeJetFOne C
        (differentialJet 1 (freeCoordinate C ℕ 0)⁻¹) = 1 := by
  rw [show 1 = 0 + 1 by omega, differentialJet_succ, differentialJet_zero,
    freeScalarJetField_deriv_apply, freeJetFOne_freeJetShift,
    freeJetFOne_freeCoordinate_zero_inv,
    freeJetFZero_freeCoordinate_zero_inv]
  simp

/-- `F_1` kills every reciprocal differential jet of order `n+2`. -/
theorem freeJetFOne_differentialJet_inv_add_two
    {C : Type*} [Field C] (n : ℕ) :
    freeJetFOne C
        (differentialJet (n + 2) (freeCoordinate C ℕ 0)⁻¹) = 0 := by
  induction n with
  | zero =>
      rw [show 0 + 2 = 1 + 1 by omega, differentialJet_succ,
        freeScalarJetField_deriv_apply, freeJetFOne_freeJetShift,
        freeJetFOne_differentialJet_inv_one,
        freeJetFZero_differentialJet_inv_succ 0]
      simp
  | succ n ih =>
      rw [show n.succ + 2 = (n + 2) + 1 by omega,
        differentialJet_succ, freeScalarJetField_deriv_apply,
        freeJetFOne_freeJetShift, ih,
        show freeJetFZero C
            (differentialJet (n + 2) (freeCoordinate C ℕ 0)⁻¹) = 0 by
          simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
            freeJetFZero_differentialJet_inv_succ (C := C) (n + 1)]
      simp

/-- The first shifted opposite current kills every universal reciprocal jet of order at least
two. -/
theorem freeJetFOne_freeJetReciprocalJet_eq_zero_of_two_le
    {C : Type*} [Field C] [CharZero C]
    {n : ℕ} (hn : 2 ≤ n) :
    freeJetFOne C (freeJetReciprocalJet C n) = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [freeJetReciprocalJet_eq_differentialJet]
  simpa [Nat.add_comm] using
    freeJetFOne_differentialJet_inv_add_two (C := C) k

/-! ## Raw and reciprocal tails -/

/-- The raw depth-`n` tail generated by the free coordinates `x_k` for `k \ge n`. -/
def freeJetRawTailField
    (C : Type*) [Field C] (n : ℕ) :
    IntermediateField C (FreeScalarJetField C) :=
  IntermediateField.adjoin C
    ((fun k => freeCoordinate C ℕ k) '' Set.Ici n)

/-- The reciprocal depth-`n` tail generated by the universal reciprocal jets of order at least
`n`. -/
noncomputable def freeJetReciprocalTailField
    (C : Type*) [Field C] [CharZero C] (n : ℕ) :
    IntermediateField C (FreeScalarJetField C) :=
  IntermediateField.adjoin C
    ((fun k => freeJetReciprocalJet C k) '' Set.Ici n)

theorem freeCoordinate_mem_freeJetRawTailField
    {C : Type*} [Field C] {n k : ℕ} (hnk : n ≤ k) :
    freeCoordinate C ℕ k ∈ freeJetRawTailField C n := by
  exact IntermediateField.subset_adjoin C _ ⟨k, hnk, rfl⟩

theorem freeJetReciprocalJet_mem_freeJetReciprocalTailField
    {C : Type*} [Field C] [CharZero C]
    {n k : ℕ} (hnk : n ≤ k) :
    freeJetReciprocalJet C k ∈ freeJetReciprocalTailField C n := by
  exact IntermediateField.subset_adjoin C _ ⟨k, hnk, rfl⟩

/-- The raw free tail is the literal differential tail of the zeroth free coordinate. -/
theorem freeJetRawTailField_eq_jetTailField
    {C : Type*} [Field C] (n : ℕ) :
    freeJetRawTailField C n =
      jetTailField C (freeCoordinate C ℕ 0) n := by
  apply le_antisymm
  · rw [freeJetRawTailField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, hk, rfl⟩
    simpa only [differentialJet_freeCoordinate_zero] using!
      differentialJet_mem_jetTailField C
        (freeCoordinate C ℕ 0) (n := n) (m := k) hk
  · rw [jetTailField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, hk, rfl⟩
    change differentialJet k (freeCoordinate C ℕ 0) ∈ freeJetRawTailField C n
    rw [differentialJet_freeCoordinate_zero]
    exact freeCoordinate_mem_freeJetRawTailField hk

/-- The universal reciprocal tail is the literal differential tail of `x_0⁻¹`. -/
theorem freeJetReciprocalTailField_eq_jetTailField_inv
    {C : Type*} [Field C] [CharZero C] (n : ℕ) :
    freeJetReciprocalTailField C n =
      jetTailField C (freeCoordinate C ℕ 0)⁻¹ n := by
  apply le_antisymm
  · rw [freeJetReciprocalTailField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, hk, rfl⟩
    change freeJetReciprocalJet C k ∈
      jetTailField C (freeCoordinate C ℕ 0)⁻¹ n
    rw [freeJetReciprocalJet_eq_differentialJet]
    exact differentialJet_mem_jetTailField C
      (freeCoordinate C ℕ 0)⁻¹ (n := n) (m := k) hk
  · rw [jetTailField, IntermediateField.adjoin_le_iff]
    rintro _ ⟨k, hk, rfl⟩
    change differentialJet k (freeCoordinate C ℕ 0)⁻¹ ∈
      freeJetReciprocalTailField C n
    rw [← freeJetReciprocalJet_eq_differentialJet]
    exact freeJetReciprocalJet_mem_freeJetReciprocalTailField hk

/-- Every element of a positive raw tail is killed by the direct position current `E_0`. -/
theorem freeJetE_zero_eq_zero_of_mem_rawTail
    {C : Type*} [Field C] [CharZero C]
    {m : ℕ} (hm : 1 ≤ m) {f : FreeScalarJetField C}
    (hf : f ∈ freeJetRawTailField C m) :
    freeJetE C 0 f = 0 := by
  have hmem : f ∈ freeCoordinateField C ℕ (Set.Ici m) := by
    simpa [freeJetRawTailField, freeCoordinateField] using hf
  have hpartial : freeCoordinateDerivation C ℕ 0 f = 0 := by
    exact ((mem_freeCoordinateField_iff (Set.Ici m) f).1 hmem) 0 (by
      simp only [Set.mem_Ici]
      omega)
  rw [freeJetE_apply]
  simpa using hpartial

/-- Every element of a reciprocal tail of depth at least two is killed by `F_1`. -/
theorem freeJetFOne_eq_zero_of_mem_reciprocalTail
    {C : Type*} [Field C] [CharZero C]
    {n : ℕ} (hn : 2 ≤ n) {f : FreeScalarJetField C}
    (hf : f ∈ freeJetReciprocalTailField C n) :
    freeJetFOne C f = 0 := by
  rw [freeJetReciprocalTailField] at hf
  apply IntermediateField.adjoin_induction C
    (s := (fun k => freeJetReciprocalJet C k) '' Set.Ici n)
    (p := fun z _ => freeJetFOne C z = 0)
  · rintro _ ⟨k, hk, rfl⟩
    apply freeJetFOne_freeJetReciprocalJet_eq_zero_of_two_le
    exact hn.trans hk
  · intro c
    exact (freeJetFOne C).map_algebraMap c
  · intro x y hx hy hdx hdy
    simp [hdx, hdy]
  · intro x hx hdx
    simp [(freeJetFOne C).leibniz_inv, hdx]
  · intro x y hx hy hdx hdy
    simp [Derivation.leibniz, hdx, hdy]
  · exact hf

/-- **Raw/reciprocal free-tail collapse.**  If the raw tail starts at positive depth and the
reciprocal tail reaches depth two, their intersection is exactly the coefficient field. -/
theorem freeJetRawTail_inf_reciprocalTail_eq_bot_of_right_depth_two
    {C : Type*} [Field C] [CharZero C]
    {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    freeJetRawTailField C m ⊓ freeJetReciprocalTailField C n = ⊥ := by
  apply le_antisymm
  · intro f hf
    rw [IntermediateField.mem_inf] at hf
    have hE : freeJetE C 0 f = 0 :=
      freeJetE_zero_eq_zero_of_mem_rawTail hm hf.1
    have hF : freeJetFOne C f = 0 :=
      freeJetFOne_eq_zero_of_mem_reciprocalTail hn hf.2
    obtain ⟨c, rfl⟩ :=
      exists_eq_algebraMap_of_freeJet_E_zero_F_one hE hF
    exact (⊥ : IntermediateField C (FreeScalarJetField C)).algebraMap_mem c
  · exact bot_le

end

end GaloisForLFunctions.HTGeometry
