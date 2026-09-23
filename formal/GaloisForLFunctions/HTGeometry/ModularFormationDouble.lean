import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The modular formation double

A positive base density and its reflection factor canonically through their Hellinger midpoint and
a modular half-cocycle.  The tilted family then carries a second, two-valued coordinate — the
formation sheet — on which reflection acts by negating the tilt and toggling the sheet.  Same-sheet
closure at one admitted tilt already forces the cocycle to vanish, that is, the base to be
reflection invariant.
-/

open Real

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*}

/-- The Hellinger midpoint of a base density and its reflection. -/
def hellingerMid (b : X → ℝ) (R : X → X) (x : X) : ℝ := Real.sqrt (b x * b (R x))

/-- The modular half-cocycle of a base density under a reflection. -/
def modularHalfCocycle (b : X → ℝ) (R : X → X) (x : X) : ℝ :=
  Real.log (b x / b (R x)) / 2

variable {b : X → ℝ} {R : X → X} {T : X → ℝ}

theorem hellingerMid_pos (hb : ∀ x, 0 < b x) (x : X) : 0 < hellingerMid b R x :=
  Real.sqrt_pos.2 (mul_pos (hb x) (hb _))

/-- The Hellinger midpoint is reflection invariant. -/
theorem hellingerMid_reflect (hinv : ∀ x, R (R x) = x) (x : X) :
    hellingerMid b R (R x) = hellingerMid b R x := by
  rw [hellingerMid, hellingerMid, hinv, mul_comm]

/-- The modular half-cocycle is reflection odd. -/
theorem modularHalfCocycle_reflect (hinv : ∀ x, R (R x) = x) (x : X) :
    modularHalfCocycle b R (R x) = - modularHalfCocycle b R x := by
  rw [modularHalfCocycle, modularHalfCocycle, hinv]
  rw [show b (R x) / b x = (b x / b (R x))⁻¹ by
    rw [inv_div]]
  rw [Real.log_inv]
  ring

/-- The base density factors as the Hellinger midpoint times the exponentiated cocycle. -/
theorem eq_hellingerMid_mul_exp (hb : ∀ x, 0 < b x) (x : X) :
    b x = hellingerMid b R x * Real.exp (modularHalfCocycle b R x) := by
  have h1 : (0 : ℝ) < b x := hb x
  have h2 : (0 : ℝ) < b (R x) := hb _
  rw [modularHalfCocycle, hellingerMid]
  rw [show Real.log (b x / b (R x)) / 2 = Real.log (Real.sqrt (b x / b (R x))) by
    rw [Real.log_sqrt (le_of_lt (div_pos h1 h2))]]
  rw [Real.exp_log (Real.sqrt_pos.2 (div_pos h1 h2))]
  rw [← Real.sqrt_mul (le_of_lt (mul_pos h1 h2))]
  rw [show b x * b (R x) * (b x / b (R x)) = b x ^ (2 : ℕ) by field_simp]
  exact (Real.sqrt_sq h1.le).symm

/-- The reflected base density factors with the opposite cocycle. -/
theorem reflect_eq_hellingerMid_mul_exp (hb : ∀ x, 0 < b x) (hinv : ∀ x, R (R x) = x) (x : X) :
    b (R x) = hellingerMid b R x * Real.exp (-modularHalfCocycle b R x) := by
  have h := eq_hellingerMid_mul_exp (b := b) (R := R) hb (R x)
  rw [hellingerMid_reflect hinv, modularHalfCocycle_reflect hinv] at h
  exact h

/-- The unnormalized weight of the tilt `a` on the formation sheet `ε ∈ {+1, -1}`. -/
def sheetWeight (b : X → ℝ) (R : X → X) (T : X → ℝ) (a ε : ℝ) (x : X) : ℝ :=
  Real.exp (a * T x + ε * modularHalfCocycle b R x) * hellingerMid b R x

theorem sheetWeight_pos (hb : ∀ x, 0 < b x) (a ε : ℝ) (x : X) :
    0 < sheetWeight b R T a ε x :=
  mul_pos (Real.exp_pos _) (hellingerMid_pos hb x)

/-- On the original sheet at zero tilt the weight is the base density itself. -/
theorem sheetWeight_zero_one (hb : ∀ x, 0 < b x) (x : X) :
    sheetWeight b R T 0 1 x = b x := by
  rw [sheetWeight, eq_hellingerMid_mul_exp (b := b) (R := R) hb x]
  simp [mul_comm]

/-- **Theorem 3.1 — the modular formation double** (FEL.D4).  Reflection negates the tilt and
toggles the formation sheet. -/
theorem sheetWeight_reflect (hinv : ∀ x, R (R x) = x)
    (hodd : ∀ x, T (R x) = -T x) (a ε : ℝ) (x : X) :
    sheetWeight b R T (-a) (-ε) (R x) = sheetWeight b R T a ε x := by
  rw [sheetWeight, sheetWeight, hellingerMid_reflect hinv, modularHalfCocycle_reflect hinv,
    hodd]
  congr 2
  ring

/-- **(FEL.D5).**  Same-sheet closure at one admitted tilt forces the modular cocycle to vanish. -/
theorem modularHalfCocycle_eq_zero_of_sameSheet (hb : ∀ x, 0 < b x) (hinv : ∀ x, R (R x) = x)
    {a c : ℝ} (hc : 0 < c)
    (h : ∀ x, sheetWeight b R T a (-1) x = c * sheetWeight b R T a 1 x) (x : X) :
    modularHalfCocycle b R x = 0 := by
  have hconst : ∀ y : X, Real.exp (-2 * modularHalfCocycle b R y) = c := by
    intro y
    have hy := h y
    rw [sheetWeight, sheetWeight] at hy
    have hs : 0 < hellingerMid b R y := hellingerMid_pos hb y
    have hy' : Real.exp (a * T y + (-1) * modularHalfCocycle b R y)
        = c * Real.exp (a * T y + 1 * modularHalfCocycle b R y) := by
      refine mul_right_cancel₀ (ne_of_gt hs) ?_
      rw [hy]
      ring
    have hexp : Real.exp (a * T y + (-1) * modularHalfCocycle b R y)
        = Real.exp (-2 * modularHalfCocycle b R y)
          * Real.exp (a * T y + 1 * modularHalfCocycle b R y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp] at hy'
    exact mul_right_cancel₀ (ne_of_gt (Real.exp_pos _)) hy'
  have hx := hconst x
  have hRx := hconst (R x)
  rw [modularHalfCocycle_reflect hinv] at hRx
  have hsum : Real.exp (-2 * modularHalfCocycle b R x)
      * Real.exp (-2 * -modularHalfCocycle b R x) = c * c := by
    rw [hx, hRx]
  rw [← Real.exp_add] at hsum
  have hzero : (1 : ℝ) = c * c := by
    rw [← hsum, show -2 * modularHalfCocycle b R x + -2 * -modularHalfCocycle b R x = 0 by ring,
      Real.exp_zero]
  have hc1 : c = 1 := by
    have hfac : (c - 1) * (c + 1) = 0 := by nlinarith [hzero]
    rcases mul_eq_zero.1 hfac with hcc | hcc
    · linarith
    · linarith
  rw [hc1] at hx
  have hzz : -2 * modularHalfCocycle b R x = 0 := (Real.exp_eq_one_iff _).1 hx
  linarith

/-- The cocycle vanishes exactly when the base is reflection invariant. -/
theorem modularHalfCocycle_eq_zero_iff (hb : ∀ x, 0 < b x) :
    (∀ x, modularHalfCocycle b R x = 0) ↔ ∀ x, b (R x) = b x := by
  constructor
  · intro h x
    have h1 : Real.log (b x / b (R x)) = 0 := by
      have := h x
      rw [modularHalfCocycle] at this
      linarith
    have hdiv : b x / b (R x) = 1 := by
      have hpos : (0 : ℝ) < b x / b (R x) := div_pos (hb x) (hb _)
      have := Real.exp_log hpos
      rw [h1, Real.exp_zero] at this
      exact this.symm
    rw [div_eq_one_iff_eq (ne_of_gt (hb (R x)))] at hdiv
    exact hdiv.symm
  · intro h x
    rw [modularHalfCocycle, h, div_self (ne_of_gt (hb x)), Real.log_one]
    norm_num

end

end GaloisForLFunctions.HTGeometry
