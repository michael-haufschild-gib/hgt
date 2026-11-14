import GaloisForLFunctions.KodairaParshinAbc.Periods.EulerPolynomial
import Mathlib.Tactic

/-!
# Euler primitives and the local Picard--Fuchs factor

A regular series has an Euler primitive exactly when its constant term
vanishes. Allowing one formal logarithm removes this obstruction. This
realizes the right Euler factor of the local Picard--Fuchs operator and
separates it from the left factor, whose kernel gives an inhomogeneous
equation with a constant right side.
-/

noncomputable section

namespace GaloisForLFunctions.KodairaParshinAbc.Periods

open PowerSeries HTGeometry

/-- The regular part of the logarithmic primitive; its constant term is zero. -/
def eulerPrimitive (f : PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.mk fun n => PowerSeries.coeff n f / (n : ℂ)

theorem formalEulerOp_eulerPrimitive (f : PowerSeries ℂ) :
    formalEulerOp (eulerPrimitive f) = f - PowerSeries.C (PowerSeries.constantCoeff f) := by
  ext n
  cases n with
  | zero => simp [coeff_formalEulerOp, eulerPrimitive]
  | succ n =>
      have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
      simp only [coeff_formalEulerOp, eulerPrimitive, coeff_mk, map_sub,
        coeff_C, Nat.succ_ne_zero, if_false, sub_zero]
      exact mul_div_cancel₀ _ hn

/-- The only regular Euler-flat series are constants. -/
theorem formalEulerOp_eq_zero_iff (f : PowerSeries ℂ) :
    formalEulerOp f = 0 ↔ f = PowerSeries.C (PowerSeries.constantCoeff f) := by
  constructor
  · intro h
    ext n
    cases n with
    | zero => simp
    | succ n =>
        have hn : ((n + 1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        have hc := congrArg (PowerSeries.coeff (n + 1)) h
        simp only [coeff_formalEulerOp, map_zero] at hc
        simp only [coeff_C, Nat.succ_ne_zero, if_false]
        exact (mul_eq_zero.mp hc).resolve_left hn
  · intro h
    conv_lhs => rw [h]
    ext n
    cases n <;> simp [coeff_formalEulerOp]

/-- The constant coefficient is the sole obstruction to a regular Euler primitive. -/
theorem exists_eulerPrimitive_iff (f : PowerSeries ℂ) :
    (∃ g : PowerSeries ℂ, formalEulerOp g = f) ↔ PowerSeries.constantCoeff f = 0 := by
  constructor
  · rintro ⟨g, hg⟩
    have hc := congrArg (PowerSeries.coeff 0) hg
    simpa [coeff_formalEulerOp] using hc.symm
  · intro h
    refine ⟨eulerPrimitive f, ?_⟩
    rw [formalEulerOp_eulerPrimitive, h, map_zero, sub_zero]

/-- Euler differentiation of `a log(q)+f(q)`, represented by the pair `(a,f)`. -/
def logarithmicEuler (v : ℂ × PowerSeries ℂ) : PowerSeries ℂ :=
  PowerSeries.C v.1 + formalEulerOp v.2

/-- Every series has a canonical primitive after adjoining one logarithm. -/
theorem logarithmicEuler_primitive (f : PowerSeries ℂ) :
    logarithmicEuler (PowerSeries.constantCoeff f, eulerPrimitive f) = f := by
  rw [logarithmicEuler, formalEulerOp_eulerPrimitive]
  ring

/-- Right Euler factors pull back every differential equation along the canonical primitive. -/
theorem localEulerFactor_primitive (L : PowerSeries ℂ → PowerSeries ℂ) (f : PowerSeries ℂ) :
    L (logarithmicEuler (PowerSeries.constantCoeff f, eulerPrimitive f)) = L f := by
  rw [logarithmicEuler_primitive]

/-- Left Euler factors are exactly constant inhomogeneous equations on regular series. -/
theorem leftEulerFactor_iff (L : PowerSeries ℂ → PowerSeries ℂ) (f : PowerSeries ℂ) :
    formalEulerOp (L f) = 0 ↔ L f = PowerSeries.C (PowerSeries.constantCoeff (L f)) :=
  formalEulerOp_eq_zero_iff _

end GaloisForLFunctions.KodairaParshinAbc.Periods
