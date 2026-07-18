import GaloisForLFunctions.HTGeometry.FreeJetTranslationFixedField
import GaloisForLFunctions.HTGeometry.FractionRingDerivation
import Mathlib.RingTheory.Derivation.Lie
import Mathlib.Tactic

/-!
# The free-jet fixed field of one direct and one opposite current

This file supplies the rational fixed-field engine missing from the projective-horizon current
algebra cards.  On the free scalar jet field, let `E_k` be the divided-power-normalized
translation current in the `k`-th raw jet.  Let `F_1` be the first reciprocal-translation
current, obtained by differentiating the formal identity `y = x⁻¹` in the direction
`delta y(t) = t`.  Its commutator with `E_0` is the linear diagonal current `H_1`, and
`[H_1,E_k] = 2 E_{k+1}`.

Consequently a rational free-jet observable killed by the direct position current `E_0` and the
single opposite velocity current `F_1` is killed by every coordinate current.  The exact
free-coordinate partial-kernel theorem then forces it to be a scalar.  This is the infinitesimal
fixed-field collapse underlying both the symmetric depth-two and the one-sided `(2,1)`
projective-horizon transitions.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial

/-- The polynomial algebra on one complete scalar jet. -/
abbrev FreeScalarJetPolynomial (C : Type*) [Field C] := MvPolynomial ℕ C

/-- Its rational function field. -/
abbrev FreeScalarJetField (C : Type*) [Field C] :=
  FreeCoordinateRationalField C ℕ

/-- The total-derivative shift on the polynomial free jet: `x_n` is sent to `x_(n+1)`. -/
def freeJetShiftPolynomialDerivation
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C) :=
  MvPolynomial.mkDerivation C fun n => MvPolynomial.X (n + 1)

@[simp]
theorem freeJetShiftPolynomialDerivation_X
    {C : Type*} [Field C] (n : ℕ) :
    freeJetShiftPolynomialDerivation C (MvPolynomial.X n) =
      MvPolynomial.X (n + 1) := by
  simp [freeJetShiftPolynomialDerivation]

/-- The `n`-th exponential-jet coefficient of the square of the universal scalar jet. -/
def freeJetSquareCoefficient
    (C : Type*) [Field C] (n : ℕ) : FreeScalarJetPolynomial C :=
  ((freeJetShiftPolynomialDerivation C :
      FreeScalarJetPolynomial C → FreeScalarJetPolynomial C)^[n])
    (MvPolynomial.X 0 * MvPolynomial.X 0)

/-- Iterating the total derivative sends the zeroth coordinate to the corresponding jet. -/
@[simp]
theorem freeJetShift_iterate_X_zero
    {C : Type*} [Field C] (n : ℕ) :
    ((freeJetShiftPolynomialDerivation C :
        FreeScalarJetPolynomial C → FreeScalarJetPolynomial C)^[n])
      (MvPolynomial.X 0) = MvPolynomial.X n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih, freeJetShiftPolynomialDerivation_X]

/-- The zeroth coordinate derivative commutes with the total-derivative shift. -/
theorem pderiv_zero_freeJetShift
    {C : Type*} [Field C] (P : FreeScalarJetPolynomial C) :
    MvPolynomial.pderiv 0 (freeJetShiftPolynomialDerivation C P) =
      freeJetShiftPolynomialDerivation C (MvPolynomial.pderiv 0 P) := by
  have hcomm :
      ⁅(MvPolynomial.pderiv 0 :
          Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C)),
        freeJetShiftPolynomialDerivation C⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro n
    cases n <;>
      simp [Derivation.commutator_apply, freeJetShiftPolynomialDerivation]
  have h := Derivation.congr_fun hcomm P
  rw [Derivation.commutator_apply] at h
  simpa using sub_eq_zero.mp h

/-- Differentiating the universal square coefficient with respect to `x_0` gives `2 x_n`. -/
theorem pderiv_zero_freeJetSquareCoefficient
    {C : Type*} [Field C] (n : ℕ) :
    MvPolynomial.pderiv 0 (freeJetSquareCoefficient C n) =
      2 * MvPolynomial.X n := by
  induction n with
  | zero =>
      simp [freeJetSquareCoefficient, two_mul]
  | succ n ih =>
      rw [freeJetSquareCoefficient, Function.iterate_succ_apply']
      rw [pderiv_zero_freeJetShift]
      change freeJetShiftPolynomialDerivation C
        (MvPolynomial.pderiv 0 (freeJetSquareCoefficient C n)) = _
      rw [ih]
      rw [Derivation.leibniz]
      change (2 : FreeScalarJetPolynomial C) *
          freeJetShiftPolynomialDerivation C (MvPolynomial.X n) +
        MvPolynomial.X n * freeJetShiftPolynomialDerivation C
          (2 : FreeScalarJetPolynomial C) = _
      rw [freeJetShiftPolynomialDerivation_X]
      have htwo : freeJetShiftPolynomialDerivation C
          (2 : FreeScalarJetPolynomial C) = 0 :=
        (freeJetShiftPolynomialDerivation C).map_natCast 2
      rw [htwo]
      simp

/-- The normalized raw translation mode `t^k partial_x`.  Its value on `x_k` is `k!`. -/
def freeJetEPolynomialDerivation
    (C : Type*) [Field C] (k : ℕ) :
    Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C) :=
  (Nat.factorial k : C) • MvPolynomial.pderiv k

@[simp]
theorem freeJetEPolynomialDerivation_X
    {C : Type*} [Field C] (k n : ℕ) :
    freeJetEPolynomialDerivation C k (MvPolynomial.X n) =
      if k = n then
        (Nat.factorial k : C) • (1 : FreeScalarJetPolynomial C)
      else 0 := by
  classical
  by_cases hkn : k = n <;>
    simp [freeJetEPolynomialDerivation, MvPolynomial.pderiv_X,
      hkn]

/-- The first reciprocal-translation current.  On the formal arc it is
`F_1(x_n) = -n D^(n-1)(x^2)`, i.e. the infinitesimal law `delta x(t) = -t x(t)^2`. -/
def freeJetFOnePolynomialDerivation
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C) :=
  MvPolynomial.mkDerivation C fun n =>
    if 0 < n then -(n : C) • freeJetSquareCoefficient C (n - 1) else 0

@[simp]
theorem freeJetFOnePolynomialDerivation_X
    {C : Type*} [Field C] (n : ℕ) :
    freeJetFOnePolynomialDerivation C (MvPolynomial.X n) =
      if 0 < n then -(n : C) • freeJetSquareCoefficient C (n - 1) else 0 := by
  simp [freeJetFOnePolynomialDerivation]

/-- The linear diagonal current `-2 t x partial_x`. -/
def freeJetHOnePolynomialDerivation
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C) :=
  MvPolynomial.mkDerivation C fun n =>
    if 0 < n then (-2 * (n : C)) • MvPolynomial.X (n - 1) else 0

@[simp]
theorem freeJetHOnePolynomialDerivation_X
    {C : Type*} [Field C] (n : ℕ) :
    freeJetHOnePolynomialDerivation C (MvPolynomial.X n) =
      if 0 < n then (-2 * (n : C)) • MvPolynomial.X (n - 1) else 0 := by
  simp [freeJetHOnePolynomialDerivation]

/-- The raw position current and opposite velocity current generate the first diagonal mode. -/
theorem freeJetPolynomial_lie_E_zero_F_one
    {C : Type*} [Field C] :
    ⁅freeJetEPolynomialDerivation C 0, freeJetFOnePolynomialDerivation C⁆ =
      freeJetHOnePolynomialDerivation C := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply]
  cases n with
  | zero => simp
  | succ n =>
      simp [freeJetEPolynomialDerivation,
        pderiv_zero_freeJetSquareCoefficient, Algebra.smul_def]
      rw [show MvPolynomial.C (2 : C) =
          (2 : FreeScalarJetPolynomial C) by
        exact map_ofNat (MvPolynomial.C : C →+* FreeScalarJetPolynomial C) 2]
      ring

/-- The first diagonal mode propagates every raw translation mode to the next order. -/
theorem freeJetPolynomial_lie_H_one_E
    {C : Type*} [Field C] (k : ℕ) :
    ⁅freeJetHOnePolynomialDerivation C, freeJetEPolynomialDerivation C k⁆ =
      (2 : C) • freeJetEPolynomialDerivation C (k + 1) := by
  apply MvPolynomial.derivation_ext
  intro n
  rw [Derivation.commutator_apply, Derivation.smul_apply]
  have hfirst : freeJetHOnePolynomialDerivation C
      (freeJetEPolynomialDerivation C k (MvPolynomial.X n)) = 0 := by
    rw [freeJetEPolynomialDerivation_X]
    split_ifs <;> simp
  rw [hfirst, freeJetHOnePolynomialDerivation_X]
  cases n with
  | zero => simp
  | succ n =>
      by_cases hnk : n = k
      · subst n
        simp [freeJetEPolynomialDerivation_X,
          Nat.factorial_succ, Algebra.smul_def]
        ring
      · have hkn : k ≠ n := Ne.symm hnk
        simp [freeJetEPolynomialDerivation_X, hkn,
          Algebra.smul_def]

/-- Extend a polynomial free-jet derivation to the rational free-jet field by the quotient rule. -/
def extendFreeJetPolynomialDerivation
    {C : Type*} [Field C]
    (D : Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C)) :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  GaloisForLFunctions.fractionRingDerivation
    ((Algebra.linearMap (FreeScalarJetPolynomial C) (FreeScalarJetField C)).compDer D)

@[simp]
theorem extendFreeJetPolynomialDerivation_algebraMap
    {C : Type*} [Field C]
    (D : Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C))
    (P : FreeScalarJetPolynomial C) :
    extendFreeJetPolynomialDerivation D
        (algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) P) =
      algebraMap (FreeScalarJetPolynomial C) (FreeScalarJetField C) (D P) := by
  rw [extendFreeJetPolynomialDerivation,
    GaloisForLFunctions.fractionRingDerivation_algebraMap]
  rfl

/-- Fraction-field extension preserves the Lie bracket of polynomial endoderivations. -/
theorem extendFreeJetPolynomialDerivation_lie
    {C : Type*} [Field C]
    (D E : Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C)) :
    ⁅extendFreeJetPolynomialDerivation D, extendFreeJetPolynomialDerivation E⁆ =
      extendFreeJetPolynomialDerivation ⁅D, E⁆ := by
  apply GaloisForLFunctions.fractionRing_derivation_ext
    (A := FreeScalarJetPolynomial C)
  intro P
  simp [Derivation.commutator_apply]

/-- Fraction-field extension preserves scalar multiplication of polynomial derivations. -/
theorem extendFreeJetPolynomialDerivation_smul
    {C : Type*} [Field C] (c : C)
    (D : Derivation C (FreeScalarJetPolynomial C) (FreeScalarJetPolynomial C)) :
    extendFreeJetPolynomialDerivation (c • D) =
      c • extendFreeJetPolynomialDerivation D := by
  apply GaloisForLFunctions.fractionRing_derivation_ext
    (A := FreeScalarJetPolynomial C)
  intro P
  simp only [extendFreeJetPolynomialDerivation_algebraMap,
    Derivation.smul_apply]
  simp [Algebra.smul_def,
    IsScalarTower.algebraMap_apply C (FreeScalarJetPolynomial C)]

/-- Raw translation current on the rational free-jet field. -/
def freeJetE
    (C : Type*) [Field C] (k : ℕ) :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  extendFreeJetPolynomialDerivation (freeJetEPolynomialDerivation C k)

/-- Opposite velocity current on the rational free-jet field. -/
def freeJetFOne
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  extendFreeJetPolynomialDerivation (freeJetFOnePolynomialDerivation C)

/-- First diagonal current on the rational free-jet field. -/
def freeJetHOne
    (C : Type*) [Field C] :
    Derivation C (FreeScalarJetField C) (FreeScalarJetField C) :=
  extendFreeJetPolynomialDerivation (freeJetHOnePolynomialDerivation C)

/-- Rational-field form of `[E_0,F_1]=H_1`. -/
theorem freeJet_lie_E_zero_F_one
    {C : Type*} [Field C] :
    ⁅freeJetE C 0, freeJetFOne C⁆ = freeJetHOne C := by
  rw [freeJetE, freeJetFOne, freeJetHOne,
    extendFreeJetPolynomialDerivation_lie,
    freeJetPolynomial_lie_E_zero_F_one]

/-- Rational-field form of `[H_1,E_k]=2E_(k+1)`. -/
theorem freeJet_lie_H_one_E
    {C : Type*} [Field C] (k : ℕ) :
    ⁅freeJetHOne C, freeJetE C k⁆ = (2 : C) • freeJetE C (k + 1) := by
  rw [freeJetHOne, freeJetE, extendFreeJetPolynomialDerivation_lie,
    freeJetPolynomial_lie_H_one_E,
    extendFreeJetPolynomialDerivation_smul]
  rfl

/-- The normalized `E_k` current is the nonzero factorial multiple of the coordinate partial. -/
theorem freeJetE_apply
    {C : Type*} [Field C] (k : ℕ) (f : FreeScalarJetField C) :
    freeJetE C k f =
      (Nat.factorial k : C) • freeCoordinateDerivation C ℕ k f := by
  change
    extendFreeJetPolynomialDerivation
        ((Nat.factorial k : C) • MvPolynomial.pderiv k) f = _
  rw [extendFreeJetPolynomialDerivation_smul, Derivation.smul_apply]
  rfl

/-- The intermediate field killed simultaneously by the direct position current and the opposite
velocity current. -/
def freeJetDirectZeroOppositeOneCurrentKernelField
    (C : Type*) [Field C] : IntermediateField C (FreeScalarJetField C) where
  carrier := {f | freeJetE C 0 f = 0 ∧ freeJetFOne C f = 0}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    simp [hx.1, hx.2, hy.1, hy.2]
  mul_mem' := by
    intro x y hx hy
    simp [Derivation.leibniz, hx.1, hx.2, hy.1, hy.2]
  algebraMap_mem' := by
    intro c
    exact ⟨(freeJetE C 0).map_algebraMap c,
      (freeJetFOne C).map_algebraMap c⟩
  inv_mem' := by
    intro x hx
    exact ⟨by simp [(freeJetE C 0).leibniz_inv, hx.1],
      by simp [(freeJetFOne C).leibniz_inv, hx.2]⟩

@[simp]
theorem mem_freeJetDirectZeroOppositeOneCurrentKernelField_iff
    {C : Type*} [Field C] (f : FreeScalarJetField C) :
    f ∈ freeJetDirectZeroOppositeOneCurrentKernelField C ↔
      freeJetE C 0 f = 0 ∧ freeJetFOne C f = 0 :=
  Iff.rfl

/-- **Minimal current fixed-field collapse.**  In characteristic zero, invariance under the raw
position current and the single opposite velocity current already forces a rational free-jet
observable to be a scalar. -/
theorem exists_eq_algebraMap_of_freeJet_E_zero_F_one
    {C : Type*} [Field C] [CharZero C]
    {f : FreeScalarJetField C}
    (hE : freeJetE C 0 f = 0) (hF : freeJetFOne C f = 0) :
    ∃ c : C, f = algebraMap C (FreeScalarJetField C) c := by
  have hH : freeJetHOne C f = 0 := by
    rw [← freeJet_lie_E_zero_F_one]
    simp [Derivation.commutator_apply, hE, hF]
  have hEk : ∀ k : ℕ, freeJetE C k f = 0 := by
    intro k
    induction k with
    | zero => exact hE
    | succ k ih =>
        have hbracket : ⁅freeJetHOne C, freeJetE C k⁆ f = 0 := by
          simp [Derivation.commutator_apply, hH, ih]
        rw [freeJet_lie_H_one_E, Derivation.smul_apply] at hbracket
        have htwo : (2 : C) ≠ 0 := by norm_num
        exact (smul_eq_zero.mp hbracket).resolve_left htwo
  apply (all_freeCoordinateDerivations_eq_zero_iff f).1
  intro k
  have hk := hEk k
  rw [freeJetE_apply] at hk
  have hfac : (Nat.factorial k : C) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
  exact (smul_eq_zero.mp hk).resolve_left hfac

/-- The common kernel field of `E_0` and `F_1` is exactly the scalar coefficient field. -/
@[simp]
theorem freeJetDirectZeroOppositeOneCurrentKernelField_eq_bot
    {C : Type*} [Field C] [CharZero C] :
    freeJetDirectZeroOppositeOneCurrentKernelField C = ⊥ := by
  apply le_antisymm
  · intro f hf
    obtain ⟨c, rfl⟩ :=
      exists_eq_algebraMap_of_freeJet_E_zero_F_one hf.1 hf.2
    exact (⊥ : IntermediateField C (FreeScalarJetField C)).algebraMap_mem c
  · exact bot_le

end

end GaloisForLFunctions.HTGeometry
