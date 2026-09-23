import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-!
# Two Gauss--Bonnet thermodynamic prescriptions

Equations (4), (6)--(8), and (11)--(19) of arXiv:2609.00025v1.
The coupling is `a^(2 : ℕ)`, the reference length is `exp l`, and tested radii are
`exp x`. Both entropy-temperature pairs satisfy the same differentiated mass law.
These are identities for the stated thermodynamic functions, not a derivation of
the gravitational field equations.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry

def egbMass (P Q a r : ℝ) : ℝ :=
  r / 2 + (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (2 * r) + 4 * Real.pi * P * r ^ (3 : ℕ) / 3

def egbEntropyA (a l r : ℝ) : ℝ :=
  Real.pi * r ^ (2 : ℕ) + 4 * Real.pi * a ^ (2 : ℕ) * Real.log (r / Real.exp l)

def egbEntropyB (r : ℝ) : ℝ := Real.pi * r ^ (2 : ℕ)

def egbTemperatureA (P Q a r : ℝ) : ℝ :=
  (8 * Real.pi * P * r ^ (4 : ℕ) + r ^ (2 : ℕ) - Q ^ (2 : ℕ) - a ^ (2 : ℕ)) /
    (4 * Real.pi * r * (r ^ (2 : ℕ) + 2 * a ^ (2 : ℕ)))

def egbTemperatureB (P Q a r : ℝ) : ℝ :=
  (8 * Real.pi * P * r ^ (4 : ℕ) + r ^ (2 : ℕ) - Q ^ (2 : ℕ) - a ^ (2 : ℕ)) / (4 * Real.pi * r ^ (3 : ℕ))

def egbPressureA (T Q a r : ℝ) : ℝ :=
  T / (2 * r) + a ^ (2 : ℕ) * T / r ^ (3 : ℕ) - 1 / (8 * Real.pi * r ^ (2 : ℕ)) +
    (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (8 * Real.pi * r ^ (4 : ℕ))

def egbPressureB (T Q a r : ℝ) : ℝ :=
  T / (2 * r) - 1 / (8 * Real.pi * r ^ (2 : ℕ)) +
    (Q ^ (2 : ℕ) + a ^ (2 : ℕ)) / (8 * Real.pi * r ^ (4 : ℕ))

theorem egbTemperature_compensation (P Q a x : ℝ) :
    egbTemperatureB P Q a (Real.exp x) =
      egbTemperatureA P Q a (Real.exp x) * (1 + 2 * a ^ (2 : ℕ) / (Real.exp x) ^ (2 : ℕ)) := by
  have hn : (Real.exp x) ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) ≠ 0 := by positivity
  unfold egbTemperatureA egbTemperatureB
  field_simp

theorem egbPressureA_temperature (P Q a x : ℝ) :
    egbPressureA (egbTemperatureA P Q a (Real.exp x)) Q a (Real.exp x) = P := by
  have hn : (Real.exp x) ^ (2 : ℕ) + 2 * a ^ (2 : ℕ) ≠ 0 := by positivity
  unfold egbPressureA egbTemperatureA
  field_simp
  all_goals ring

theorem egbPressureB_temperature (P Q a x : ℝ) :
    egbPressureB (egbTemperatureB P Q a (Real.exp x)) Q a (Real.exp x) = P := by
  unfold egbPressureB egbTemperatureB
  field_simp
  all_goals ring

theorem egbMass_derivative (P Q a x : ℝ) :
    HasDerivAt (egbMass P Q a)
      (egbTemperatureB P Q a (Real.exp x) * (2 * Real.pi * Real.exp x)) (Real.exp x) := by
  have h := (((hasDerivAt_id (Real.exp x)).div_const 2).add
    ((hasDerivAt_const (Real.exp x) (Q ^ (2 : ℕ) + a ^ (2 : ℕ))).div
      ((hasDerivAt_id (Real.exp x)).const_mul 2) (by dsimp; positivity))).add
    ((((hasDerivAt_id (Real.exp x)).pow 3).const_mul (4 * Real.pi * P)).div_const 3)
  apply h.congr_deriv
  dsimp [egbTemperatureB]
  field_simp
  all_goals ring

theorem egbEntropyB_derivative (x : ℝ) :
    HasDerivAt egbEntropyB (2 * Real.pi * Real.exp x) (Real.exp x) := by
  apply (((hasDerivAt_id (Real.exp x)).pow 2).const_mul Real.pi).congr_deriv
  dsimp
  ring

theorem egbEntropyA_derivative (a l x : ℝ) :
    HasDerivAt (egbEntropyA a l)
      (2 * Real.pi * Real.exp x + 4 * Real.pi * a ^ (2 : ℕ) / Real.exp x) (Real.exp x) := by
  have hlog := (((hasDerivAt_id (Real.exp x)).div_const (Real.exp l)).log
    (div_ne_zero (Real.exp_ne_zero x) (Real.exp_ne_zero l))).const_mul (4 * Real.pi * a ^ (2 : ℕ))
  apply ((((hasDerivAt_id (Real.exp x)).pow 2).const_mul Real.pi).add hlog).congr_deriv
  dsimp
  field_simp

theorem egb_firstLaw_both_prescriptions (P Q a l x : ℝ) :
    deriv (egbMass P Q a) (Real.exp x) =
      egbTemperatureA P Q a (Real.exp x) * deriv (egbEntropyA a l) (Real.exp x) ∧
    deriv (egbMass P Q a) (Real.exp x) =
      egbTemperatureB P Q a (Real.exp x) * deriv egbEntropyB (Real.exp x) := by
  rw [(egbMass_derivative P Q a x).deriv, (egbEntropyA_derivative a l x).deriv,
    (egbEntropyB_derivative x).deriv]
  constructor
  · rw [egbTemperature_compensation]
    field_simp
    all_goals ring
  · rfl

theorem egbEntropyA_scale_shift (a l c x : ℝ) :
    egbEntropyA a (l + c) (Real.exp x) =
      egbEntropyA a l (Real.exp x) - 4 * Real.pi * a ^ (2 : ℕ) * c := by
  simp only [egbEntropyA, Real.log_div (Real.exp_ne_zero _) (Real.exp_ne_zero _),
    Real.log_exp]
  ring

theorem egbGibbsB_identity (P Q a x : ℝ) :
    egbMass P Q a (Real.exp x) - egbTemperatureB P Q a (Real.exp x) * egbEntropyB (Real.exp x) =
      Real.exp x / 4 + 3 * (a ^ (2 : ℕ) + Q ^ (2 : ℕ)) / (4 * Real.exp x) -
        2 * Real.pi * P * (Real.exp x) ^ (3 : ℕ) / 3 := by
  unfold egbMass egbTemperatureB egbEntropyB
  field_simp
  all_goals ring

theorem egb_effectiveCharge_degeneracy (T Q a r : ℝ) :
    egbPressureB T Q a r = egbPressureB T a Q r := by
  unfold egbPressureB
  ring

end GaloisForLFunctions.HTGeometry
