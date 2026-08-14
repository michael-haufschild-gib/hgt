import GaloisForLFunctions.RHTower.FieldOnePadicSoninL2FourierSupport

/-!
# Two-shell classification of band-limited radial p-adic Bruhat vectors

A radial Bruhat function which vanishes on `pℤ_p` and outside `p⁻¹ℤ_p`
is exactly a linear combination of `ε₀` and `ε₁`.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

theorem fieldOnePadicSoninBallSet_unit_mul_iff
    (m : ℤ) (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    (((u : ℤ_[p]) : ℚ_[p])) * x ∈ fieldOnePadicSoninBallSet p m ↔
      x ∈ fieldOnePadicSoninBallSet p m := by
  rcases eq_or_ne x 0 with rfl | hx0
  · constructor <;> intro h
    · simpa using h
    · simpa using h
  · rw [fieldOnePadicSoninBallSet_mem_iff_valuation p m
      (mul_ne_zero (PadicInt.coe_ne_zero.mpr (Units.ne_zero u)) hx0),
    fieldOnePadicSoninBallSet_mem_iff_valuation p m hx0,
    Padic.valuation_mul]
    · rw [fieldOnePadic_valuation_coe_unit]
      simp
    · exact PadicInt.coe_ne_zero.mpr (Units.ne_zero u)
    · exact hx0

theorem fieldOnePadicBruhatRestrict_soninBall_unitInvariant
    (m : ℤ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hf : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x) :
    ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      (fieldOnePadicBruhatRestrict p (fieldOnePadicSoninBallSet p m)
        (fieldOnePadicSoninBallSet_isClopen p m) f).1
          ((((u : ℤ_[p]) : ℚ_[p])) * x) =
        (fieldOnePadicBruhatRestrict p (fieldOnePadicSoninBallSet p m)
          (fieldOnePadicSoninBallSet_isClopen p m) f).1 x := by
  intro u x
  rw [fieldOnePadicBruhatRestrict_apply,
    fieldOnePadicBruhatRestrict_apply]
  by_cases hx : x ∈ fieldOnePadicSoninBallSet p m
  · rw [Set.indicator_of_mem hx,
      Set.indicator_of_mem
        ((fieldOnePadicSoninBallSet_unit_mul_iff p m u x).mpr hx), hf]
  · rw [Set.indicator_of_notMem hx,
      Set.indicator_of_notMem
        (by simpa [fieldOnePadicSoninBallSet_unit_mul_iff p m u x] using hx)]

theorem fieldOnePadicRadialOuterBruhat_apply_forward_eq_twoShells
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0)
    (houter : ∀ x, x ∉ fieldOnePadicSoninOuterFourierBall p → f.1 x = 0)
    (k : ℤ) (u : ℤ_[p]ˣ) :
    f.1 (((fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) =
      fieldOnePadicRadialShellCoefficient p f 0 *
        (fieldOnePadicSoninShell p 0).1
          (((fieldOnePadicValuationUnitForward p
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) +
      fieldOnePadicRadialShellCoefficient p f 1 *
        (fieldOnePadicSoninShell p 1).1
          (((fieldOnePadicValuationUnitForward p
            (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])) := by
  let x : ℚ_[p] :=
    ((fieldOnePadicValuationUnitForward p
      (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p])
  let xone : ℚ_[p] :=
    ((fieldOnePadicValuationUnitForward p
      (Multiplicative.ofAdd k, 1) : ℚ_[p]ˣ) : ℚ_[p])
  have hrad : f.1 x = f.1 xone := by
    have hmul' : (((u : ℤ_[p]) : ℚ_[p])) * xone = x := by
      dsimp [x, xone, fieldOnePadicValuationUnitForward]
      simp only [mul_one]
      ring
    rw [← hmul']
    exact hunit u xone
  rw [hrad, fieldOnePadicSoninShell_apply_forward,
    fieldOnePadicSoninShell_apply_forward]
  by_cases hk0 : k = 0
  · rw [neg_zero, if_pos hk0, if_neg (by omega)]
    simp only [mul_one, mul_zero, add_zero]
    unfold fieldOnePadicRadialShellCoefficient
    dsimp [xone]
    rw [hk0]
    simp
  · by_cases hk1 : k = -1
    · rw [neg_zero, if_neg hk0, if_pos hk1]
      simp only [mul_zero, zero_add, mul_one]
      unfold fieldOnePadicRadialShellCoefficient
      dsimp [xone]
      rw [hk1]
      simp
    · rw [neg_zero, if_neg hk0, if_neg hk1]
      simp only [mul_zero, add_zero]
      by_cases hkpos : 1 ≤ k
      · apply hgap xone
        change xone ∈ fieldOnePadicSoninBallSet p (-1)
        rw [fieldOnePadicSoninBallSet_mem_forward_iff]
        omega
      · apply houter xone
        change xone ∉ fieldOnePadicSoninBallSet p 1
        rw [fieldOnePadicSoninBallSet_mem_forward_iff]
        omega

theorem fieldOnePadicRadialOuterBruhat_eq_twoShells
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (hunit : ∀ u : ℤ_[p]ˣ, ∀ x : ℚ_[p],
      f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x) = f.1 x)
    (hgap : ∀ x ∈ fieldOnePadicSoninInnerBall p, f.1 x = 0)
    (houter : ∀ x, x ∉ fieldOnePadicSoninOuterFourierBall p → f.1 x = 0) :
    f = (fieldOnePadicRadialShellCoefficient p f 0) •
        fieldOnePadicSoninShell p 0 +
      (fieldOnePadicRadialShellCoefficient p f 1) •
        fieldOnePadicSoninShell p 1 := by
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  rcases eq_or_ne x 0 with rfl | hx
  · rw [hgap 0]
    · simp
    · change 0 ∈ fieldOnePadicSoninBallSet p (-1)
      refine ⟨(0 : ℤ_[p]), ?_⟩
      simp
  · let a : ℚ_[p]ˣ := Units.mk0 x hx
    let z := (fieldOnePadicValuationUnitContinuousMulEquiv p).symm a
    let k : ℤ := z.1.toAdd
    let u : ℤ_[p]ˣ := z.2
    have hz : z = (Multiplicative.ofAdd k, u) := by
      apply Prod.ext
      · exact Multiplicative.toAdd.injective (by rfl)
      · rfl
    have ha : fieldOnePadicValuationUnitForward p
        (Multiplicative.ofAdd k, u) = a := by
      change (fieldOnePadicValuationUnitContinuousMulEquiv p)
        (Multiplicative.ofAdd k, u) = a
      rw [← hz]
      exact (fieldOnePadicValuationUnitContinuousMulEquiv p).apply_symm_apply a
    have hxcoord :
        ((fieldOnePadicValuationUnitForward p
          (Multiplicative.ofAdd k, u) : ℚ_[p]ˣ) : ℚ_[p]) = x :=
      congrArg Units.val ha
    rw [← hxcoord]
    change _ = fieldOnePadicRadialShellCoefficient p f 0 *
        (fieldOnePadicSoninShell p 0).1 _ +
      fieldOnePadicRadialShellCoefficient p f 1 *
        (fieldOnePadicSoninShell p 1).1 _
    exact fieldOnePadicRadialOuterBruhat_apply_forward_eq_twoShells
      p f hunit hgap houter k u

end

end GaloisForLFunctions.RHTower
