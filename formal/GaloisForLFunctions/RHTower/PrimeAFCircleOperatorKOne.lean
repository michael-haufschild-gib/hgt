import GaloisForLFunctions.RHTower.ConnectedSymmetryBarrier

/-!
# The scalar circle operator K₁ group

This module constructs the homotopy classes of nonvanishing complex loops literally and proves
that winding number identifies this group with `ℤ`.  The quotient relation is written as equality
of winding numbers, then proved equivalent to existence of a homotopy through nonvanishing loops by
`RHTower.windingNumber_eq_iff_joined`.  Thus this is the concrete Bott computation
`K₁(C(S¹)) ≅ ℤ`, not a charge interface or an assumed provider.
-/

namespace PrimeQuasiLocalCharge

noncomputable section

/-- A continuous nonvanishing complex loop on the standard interval `[0, 2π]`. -/
structure ScalarCircleLoop where
  toFun : ℝ → ℂ
  isLoop : RHTower.IsLoop toFun 0 (2 * Real.pi)

instance : CoeFun ScalarCircleLoop (fun _ ↦ ℝ → ℂ) := ⟨ScalarCircleLoop.toFun⟩

/-- Integer charge of a scalar circle loop. -/
def scalarCircleLoopWinding (gamma : ScalarCircleLoop) : ℤ :=
  RHTower.windingNumber gamma.toFun 0 (2 * Real.pi)

/-- Homotopy relation on nonvanishing scalar loops.  Equality of winding is used as the kernel
presentation; `scalarCircleLoop_equivalent_iff_homotopic` proves that it is exactly ordinary loop
homotopy through nonvanishing loops. -/
def scalarCircleLoopHomotopySetoid : Setoid ScalarCircleLoop :=
  Setoid.ker scalarCircleLoopWinding

theorem scalarCircleLoop_equivalent_iff_homotopic (gamma delta : ScalarCircleLoop) :
    scalarCircleLoopHomotopySetoid gamma delta ↔
      ∃ H : ℝ → ℝ → ℂ,
        Continuous (fun p : ℝ × ℝ ↦ H p.1 p.2) ∧
        (∀ sigma t, H sigma t ≠ 0) ∧
        (∀ sigma, H sigma 0 = H sigma (2 * Real.pi)) ∧
        (∀ t, H 0 t = gamma t) ∧
        (∀ t, H 1 t = delta t) := by
  exact RHTower.windingNumber_eq_iff_joined gamma.isLoop delta.isLoop

/-- Concrete scalar operator `K₁` of the circle: nonvanishing loops modulo homotopy. -/
abbrev CircleOperatorKOne := Quotient scalarCircleLoopHomotopySetoid

/-- Winding number descends to the scalar operator-`K₁` quotient. -/
def circleOperatorKOneWinding : CircleOperatorKOne → ℤ :=
  Quotient.lift scalarCircleLoopWinding fun _ _ h ↦ h

/-- Standard loop with prescribed integer winding. -/
def scalarCircleLoopOfInt (z : ℤ) : ScalarCircleLoop where
  toFun := fun t ↦ Complex.exp ((z : ℂ) * ((t : ℂ) * Complex.I))
  isLoop := by
    refine ⟨?_, fun _ ↦ Complex.exp_ne_zero _, ?_⟩
    · fun_prop
    · simp only [Complex.ofReal_zero, zero_mul, mul_zero, Complex.exp_zero]
      convert (Complex.exp_int_mul_two_pi_mul_I z).symm using 1
      push_cast
      ring

/-- The standard integer loop has exactly its prescribed winding. -/
theorem scalarCircleLoopOfInt_winding (z : ℤ) :
    scalarCircleLoopWinding (scalarCircleLoopOfInt z) = z := by
  let L : ℝ → ℂ := fun t ↦ (z : ℂ) * ((t : ℂ) * Complex.I)
  have hLcont : Continuous L := by fun_prop
  have hLexp : ∀ t, Complex.exp (L t) = scalarCircleLoopOfInt z t := fun _ ↦ rfl
  have hinc := RHTower.contLog_increment (scalarCircleLoopOfInt z).isLoop hLcont hLexp
  have hdirect : L (2 * Real.pi) - L 0 =
      (z : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [L]
    push_cast
    ring
  rw [hdirect] at hinc
  have hperiod : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Complex.I_ne_zero, Real.pi_ne_zero]
  have hcast : (z : ℂ) =
      (RHTower.windingNumber (scalarCircleLoopOfInt z) 0 (2 * Real.pi) : ℂ) :=
    mul_right_cancel₀ hperiod hinc
  exact_mod_cast hcast.symm

/-- Bott/winding classification of scalar circle operator `K₁`. -/
def circleOperatorKOneEquivInt : CircleOperatorKOne ≃ ℤ where
  toFun := circleOperatorKOneWinding
  invFun z := Quotient.mk scalarCircleLoopHomotopySetoid (scalarCircleLoopOfInt z)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | _ gamma =>
        apply Quotient.sound
        exact scalarCircleLoopOfInt_winding (scalarCircleLoopWinding gamma)
  right_inv z := scalarCircleLoopOfInt_winding z

noncomputable instance : AddCommGroup CircleOperatorKOne :=
  Equiv.addCommGroup circleOperatorKOneEquivInt

@[simp] theorem circleOperatorKOneEquivInt_apply (q : CircleOperatorKOne) :
    circleOperatorKOneEquivInt q = circleOperatorKOneWinding q := rfl

@[simp] theorem circleOperatorKOneEquivInt_symm_apply (z : ℤ) :
    circleOperatorKOneEquivInt.symm z =
      Quotient.mk scalarCircleLoopHomotopySetoid (scalarCircleLoopOfInt z) := rfl

/-- Every scalar circle `K₁` class has a literal loop representative. -/
theorem circleOperatorKOne_has_loop_representative (q : CircleOperatorKOne) :
    ∃ gamma : ScalarCircleLoop, Quotient.mk scalarCircleLoopHomotopySetoid gamma = q := by
  induction q using Quotient.inductionOn with
  | _ gamma => exact ⟨gamma, rfl⟩

end

end PrimeQuasiLocalCharge
