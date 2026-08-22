import Mathlib.NumberTheory.SumPrimeReciprocals
import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.Exponential

/-!
# Finite Euler local quartets

The finite Euler factor `1 - p⁻ˢ` is paired with its functional-equation
reflection.  The resulting local quartet is reflection-invariant and is a
strictly positive real number on the critical line.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower

open Complex

/-- The entire finite Euler factor written in exponential coordinates. -/
def finiteEulerLocalFactor (p : ℕ) (s : ℂ) : ℂ :=
  1 - Complex.exp (-s * Real.log p)

/-- The functional-equation-symmetric local Euler quartet. -/
def finiteEulerLocalQuartet (p : ℕ) (s : ℂ) : ℂ :=
  finiteEulerLocalFactor p s * finiteEulerLocalFactor p (1 - s)

/-- Finite Euler local factors commute with complex conjugation. -/
theorem finiteEulerLocalFactor_conj (p : ℕ) (s : ℂ) :
    finiteEulerLocalFactor p (star s) = star (finiteEulerLocalFactor p s) := by
  unfold finiteEulerLocalFactor
  have hreal (x : ℝ) : star (x : ℂ) = (x : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have harg : -star s * (Real.log p : ℂ) =
      starRingEnd ℂ (-s * (Real.log p : ℂ)) := by
    calc
      -star s * (Real.log p : ℂ) = starRingEnd ℂ (-s) *
          starRingEnd ℂ (Real.log p : ℂ) := by
            change -star s * (Real.log p : ℂ) = star (-s) * star (Real.log p : ℂ)
            rw [star_neg, hreal]
      _ = starRingEnd ℂ (-s * (Real.log p : ℂ)) :=
        (map_mul (starRingEnd ℂ) (-s) (Real.log p : ℂ)).symm
  rw [harg, Complex.exp_conj]
  change 1 - star (Complex.exp (-s * (Real.log p : ℂ))) =
    star (1 - Complex.exp (-s * (Real.log p : ℂ)))
  simpa only [star_one] using
    (star_sub (1 : ℂ) (Complex.exp (-s * (Real.log p : ℂ)))).symm

/-- Exponential coordinates agree with the standard complex-power Euler factor. -/
theorem finiteEulerLocalFactor_eq_one_sub_natCast_cpow (p : Nat.Primes) (s : ℂ) :
    finiteEulerLocalFactor p s = 1 - ((p : ℕ) : ℂ) ^ (-s) := by
  unfold finiteEulerLocalFactor
  rw [Complex.cpow_def_of_ne_zero]
  · rw [← Complex.natCast_log]
    congr 2
    ring_nf
  · exact Nat.cast_ne_zero.mpr p.property.ne_zero

/-- A local Euler quartet is invariant under `s ↦ 1 - s`. -/
theorem finiteEulerLocalQuartet_reflection (p : ℕ) (s : ℂ) :
    finiteEulerLocalQuartet p (1 - s) = finiteEulerLocalQuartet p s := by
  unfold finiteEulerLocalQuartet
  ring_nf

/-- A prime Euler factor does not vanish on the critical line. -/
theorem finiteEulerLocalFactor_criticalLine_ne_zero (p : Nat.Primes) (t : ℝ) :
    finiteEulerLocalFactor p (1 / 2 + (t : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  have hfactor : Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p) = 1 := by
    simpa [finiteEulerLocalFactor] using (sub_eq_zero.mp hzero).symm
  have hlog : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by
      simpa using (Nat.cast_lt (α := ℝ)).mpr p.property.one_lt)
  set ell : ℝ := Real.log (p : ℝ)
  have hell : 0 < ell := hlog
  have hre : (-(1 / 2 + (t : ℂ) * Complex.I) * (ell : ℂ)).re =
      -(1 / 2 : ℝ) * ell := by
    simp [Complex.mul_re]
  have hlt : ‖Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)‖ < 1 := by
    change ‖Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * (ell : ℂ))‖ < 1
    rw [Complex.norm_exp, hre, Real.exp_lt_one_iff]
    nlinarith
  rw [hfactor, norm_one] at hlt
  exact lt_irrefl _ hlt

/-- On the critical line, a prime Euler quartet is the squared modulus of one local factor. -/
theorem finiteEulerLocalQuartet_criticalLine_eq_norm_sq (p : Nat.Primes) (t : ℝ) :
    finiteEulerLocalQuartet p (1 / 2 + (t : ℂ) * Complex.I) =
      (‖finiteEulerLocalFactor p (1 / 2 + (t : ℂ) * Complex.I)‖ ^ 2 : ℝ) := by
  rw [finiteEulerLocalQuartet]
  have hline : (1 - (1 / 2 + (t : ℂ) * Complex.I) : ℂ) =
      star (1 / 2 + (t : ℂ) * Complex.I) := by
    simp
    ring_nf
  rw [hline]
  change (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      (1 - Complex.exp (-(star (1 / 2 + (t : ℂ) * Complex.I)) * Real.log p)) =
      (‖1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)‖ ^ 2 : ℝ)
  rw [show (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      (1 - Complex.exp (-(star (1 / 2 + (t : ℂ) * Complex.I)) * Real.log p)) =
      (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
        star (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) by
          rw [← finiteEulerLocalFactor]
          rw [finiteEulerLocalFactor]
          exact congrArg (fun z =>
            (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) * z)
            (finiteEulerLocalFactor_conj p (1 / 2 + (t : ℂ) * Complex.I))]
  change (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) *
      starRingEnd ℂ (1 - Complex.exp (-(1 / 2 + (t : ℂ) * Complex.I) * Real.log p)) = _
  rw [Complex.mul_conj]
  rw [← Complex.sq_norm]

/-- The critical-line local Euler quartet has strictly positive real part. -/
theorem finiteEulerLocalQuartet_criticalLine_re_pos (p : Nat.Primes) (t : ℝ) :
    0 < (finiteEulerLocalQuartet p (1 / 2 + (t : ℂ) * Complex.I)).re := by
  rw [finiteEulerLocalQuartet_criticalLine_eq_norm_sq]
  simp only [ofReal_re]
  exact sq_pos_of_pos
    (norm_pos_iff.mpr (finiteEulerLocalFactor_criticalLine_ne_zero p t))

end GaloisForLFunctions.RHTower

end
