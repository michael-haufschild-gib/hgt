import GaloisForLFunctions.HTGeometry.PaperNativeInvariantLocalization
import GaloisForLFunctions.HTGeometry.PaperStableCoordinate.CoactionLND
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField

/-!
# Additive-action rigidity of the full Dirichlet-convolution algebra

Every complex arithmetic function is a unit or becomes a unit after adding
one. Source factorial closure therefore kills every locally nilpotent
derivation, not just the native logarithmic clock. The logarithmic clock's
terminating inputs are exactly scalar multiples of the convolution unit.
-/

namespace GaloisForLFunctions.HTGeometry

open StableCoordinate ArithmeticFunction

noncomputable section

local instance : CharZero (ArithmeticFunction ℂ) := Algebra.charZero_of_charZero ℂ _

/-- Source factorial closure and the native unit criterion classify every terminating derivation. -/
theorem paperArithmeticFunction_LND_iff_eq_zero
    (D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ)) :
    IsLocallyNilpotent D ↔ D = 0 := by
  constructor
  · intro h
    have hu (a : ArithmeticFunction ℂ) (ha : IsUnit a) : D a = 0 := by
      obtain ⟨u, rfl⟩ := ha
      exact paperLocallyNilpotent_kills_unit D h u
    apply Derivation.ext
    intro f
    by_cases hf : f 1 = 0
    · have hunit : IsUnit (1 + f) := by
        apply ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr
        simp [hf]
      simpa using hu (1 + f) hunit
    · exact hu f (ArithmeticFunction.isUnit_iff_isUnit_apply_one.mpr
        (isUnit_iff_ne_zero.mpr hf))
  · rintro rfl
    intro f
    exact ⟨1, rfl⟩

/-- Consequently every polynomial additive action on the full convolution algebra is trivial. -/
theorem paperArithmeticFunction_additiveAction_trivial
    (ρ : CoactionLND.PolynomialAdditiveAction ℂ (ArithmeticFunction ℂ))
    (f : ArithmeticFunction ℂ) : ρ.toAlgHom f = Polynomial.C f := by
  apply ρ.action_eq_C_of_derivation_eq_zero
  exact (paperArithmeticFunction_LND_iff_eq_zero ρ.derivation).mp ρ.locallyNilpotent

/-- The existing rotated logarithmic derivation is diagonal on arithmetic coefficients. -/
theorem paperArithmeticLog_apply (f : ArithmeticFunction ℂ) (n : ℕ) :
    rotatedLogArithmeticDerivationComplex f n =
      (Complex.I * (Real.log n : ℂ)) * f n := by
  change Complex.I * ((Real.log n : ℂ) * f n) = _
  ring

/-- Every logarithmic jet has the corresponding power of the coefficient frequency. -/
theorem paperArithmeticLog_iterate_apply (f : ArithmeticFunction ℂ) (n m : ℕ) :
    ((rotatedLogArithmeticDerivationComplex : ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m]
      f) n = (Complex.I * (Real.log n : ℂ)) ^ m * f n := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply', paperArithmeticLog_apply, ih, pow_succ]
    ring

private theorem log_frequency_ne_zero {n : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) :
    Complex.I * (Real.log n : ℂ) ≠ 0 := by
  apply mul_ne_zero Complex.I_ne_zero
  apply Complex.ofReal_ne_zero.mpr
  apply Real.log_ne_zero_of_pos_of_ne_one
  · exact_mod_cast Nat.pos_of_ne_zero hn0
  · exact_mod_cast hn1

/-- The native logarithmic clock fixes exactly the scalar convolution units. -/
theorem paperArithmeticLog_kernel_iff (f : ArithmeticFunction ℂ) :
    rotatedLogArithmeticDerivationComplex f = 0 ↔ f = f 1 • (1 : ArithmeticFunction ℂ) := by
  constructor
  · intro h
    ext n
    by_cases hn0 : n = 0
    · subst n
      simp
    by_cases hn1 : n = 1
    · subst n
      simp
    have he := congrArg (fun g : ArithmeticFunction ℂ => g n) h
    rw [paperArithmeticLog_apply, ArithmeticFunction.zero_apply] at he
    rw [(mul_eq_zero.mp he).resolve_left (log_frequency_ne_zero hn0 hn1)]
    simp [ArithmeticFunction.smul_map, hn1]
  · intro h
    rw [h]
    simp

/-- A logarithmic jet terminates precisely when the input is already a scalar convolution unit. -/
theorem paperArithmeticLog_terminates_iff (f : ArithmeticFunction ℂ) :
    (∃ m, (rotatedLogArithmeticDerivationComplex :
      ArithmeticFunction ℂ → ArithmeticFunction ℂ)^[m] f = 0) ↔
      f = f 1 • (1 : ArithmeticFunction ℂ) := by
  constructor
  · rintro ⟨m, hm⟩
    apply (paperArithmeticLog_kernel_iff f).mp
    ext n
    rw [paperArithmeticLog_apply, ArithmeticFunction.zero_apply]
    by_cases hn0 : n = 0
    · simp [hn0]
    by_cases hn1 : n = 1
    · simp [hn1]
    have he := congrArg (fun g : ArithmeticFunction ℂ => g n) hm
    rw [paperArithmeticLog_iterate_apply, ArithmeticFunction.zero_apply] at he
    rw [(mul_eq_zero.mp he).resolve_left (pow_ne_zero m (log_frequency_ne_zero hn0 hn1)), mul_zero]
  · intro h
    exact ⟨1, (paperArithmeticLog_kernel_iff f).mpr h⟩

/-- The logarithmic clock is nonzero, already on the native zeta coefficient sequence. -/
theorem paperArithmeticLog_ne_zero : rotatedLogArithmeticDerivationComplex ≠ 0 := by
  intro h
  have he := congrArg
    (fun D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) =>
      D (ArithmeticFunction.zeta : ArithmeticFunction ℂ) 2) h
  have hf := log_frequency_ne_zero (n := 2) (by simp) (by simp)
  apply hf
  simpa [paperArithmeticLog_apply, ArithmeticFunction.natCoe_apply,
    ArithmeticFunction.zeta_apply] using he

/-- No nonzero convolution multiplier turns the native logarithmic clock into a terminating one. -/
theorem paperArithmeticLog_multiplier_iff (q : ArithmeticFunction ℂ) :
    IsLocallyNilpotent (q • rotatedLogArithmeticDerivationComplex) ↔ q = 0 := by
  rw [paperArithmeticFunction_LND_iff_eq_zero]
  constructor
  · intro h
    by_contra hq
    apply paperArithmeticLog_ne_zero
    apply Derivation.ext
    intro f
    have he := congrArg (fun D : Derivation ℂ (ArithmeticFunction ℂ) (ArithmeticFunction ℂ) => D f) h
    exact (mul_eq_zero.mp he).resolve_left hq
  · rintro rfl
    apply Derivation.ext
    intro f
    change (0 : ArithmeticFunction ℂ) * rotatedLogArithmeticDerivationComplex f = 0
    exact zero_mul _

/-- Every nonzero convolution speed has exactly the original scalar kernel. -/
theorem paperArithmeticLog_multiplier_kernel_iff (q f : ArithmeticFunction ℂ) :
    (q • rotatedLogArithmeticDerivationComplex) f = 0 ↔
      q = 0 ∨ f = f 1 • (1 : ArithmeticFunction ℂ) := by
  change q * rotatedLogArithmeticDerivationComplex f = 0 ↔ _
  rw [mul_eq_zero, paperArithmeticLog_kernel_iff]

end

end GaloisForLFunctions.HTGeometry
