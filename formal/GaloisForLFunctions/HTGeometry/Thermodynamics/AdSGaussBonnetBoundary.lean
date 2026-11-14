import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Five-dimensional Gauss--Bonnet boundary thermodynamics

The dimensionless energy, entropy, temperature and coupling response of
arXiv:2611.16364, equations (2.5)--(2.8). Energy is measured in units `C/R`
and entropy in units `C`. Positive radii are parameterized by `exp u` and
nonnegative couplings by `a²`, so the first-law identities need no premises.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry.AdSGaussBonnet

def energy (ℓ q x : ℝ) : ℝ := 3 * (x ^ 4 + x ^ 2 + ℓ) + q ^ 2 / x ^ 2

def entropy (ℓ x : ℝ) : ℝ := 4 * Real.pi * (x ^ 3 + 6 * ℓ * x)

def temperature (ℓ q x : ℝ) : ℝ :=
  (6 * x ^ 6 + 3 * x ^ 4 - q ^ 2) /
    (6 * Real.pi * x ^ 3 * (x ^ 2 + 2 * ℓ))

/-- Radius and coupling are independent variables in the reduced potential. -/
def potential (t z ℓ q x : ℝ) : ℝ := energy ℓ q x - t * entropy ℓ x - z * ℓ

/-- Coupling work at fixed entropy, after eliminating the radial variation. -/
def couplingResponse (ℓ q x : ℝ) : ℝ :=
  3 - 24 * Real.pi * x * temperature ℓ q x

theorem entropy_hasDerivAt (ℓ x : ℝ) :
    HasDerivAt (entropy ℓ) (12 * Real.pi * (x ^ 2 + 2 * ℓ)) x := by
  convert (((hasDerivAt_id x).pow 3).add
    ((hasDerivAt_id x).const_mul (6 * ℓ))).const_mul (4 * Real.pi) using 1 <;>
    (try dsimp [entropy]) <;> ring

theorem entropy_pos (a u : ℝ) : 0 < entropy (a ^ 2) (Real.exp u) := by
  unfold entropy
  positivity

theorem entropy_radial_response_pos (a u : ℝ) :
    0 < 12 * Real.pi * (Real.exp u ^ 2 + 2 * a ^ 2) := by positivity

theorem energy_hasDerivAt (ℓ q u : ℝ) :
    HasDerivAt (energy ℓ q)
      (12 * Real.exp u ^ 3 + 6 * Real.exp u - 2 * q ^ 2 / Real.exp u ^ 3)
      (Real.exp u) := by
  have hp := ((((hasDerivAt_id (Real.exp u)).pow 4).add
    ((hasDerivAt_id (Real.exp u)).pow 2)).add_const ℓ).const_mul 3
  have hq := (hasDerivAt_const (Real.exp u) (q ^ 2)).div
    ((hasDerivAt_id (Real.exp u)).pow 2) (by dsimp; positivity)
  apply (hp.add hq).congr_deriv
  dsimp
  field_simp
  <;> ring

/-- The radial first law is an identity of actual derivatives. -/
theorem radial_first_law (a q u : ℝ) :
    deriv (energy (a ^ 2) q) (Real.exp u) =
      temperature (a ^ 2) q (Real.exp u) *
        deriv (entropy (a ^ 2)) (Real.exp u) := by
  rw [(energy_hasDerivAt _ _ _).deriv, (entropy_hasDerivAt _ _).deriv]
  unfold temperature
  have hd : Real.exp u ^ 2 + 2 * a ^ 2 ≠ 0 := by positivity
  field_simp [hd]
  <;> ring

theorem potential_radial_hasDerivAt (a q u t z : ℝ) :
    HasDerivAt (potential t z (a ^ 2) q)
      ((temperature (a ^ 2) q (Real.exp u) - t) *
        (12 * Real.pi * (Real.exp u ^ 2 + 2 * a ^ 2))) (Real.exp u) := by
  have h := ((energy_hasDerivAt (a ^ 2) q u).sub
    ((entropy_hasDerivAt (a ^ 2) (Real.exp u)).const_mul t)).sub_const (z * a ^ 2)
  apply h.congr_deriv
  have hfirst := radial_first_law a q u
  rw [(energy_hasDerivAt _ _ _).deriv, (entropy_hasDerivAt _ _).deriv] at hfirst
  dsimp
  nlinarith only [hfirst]

/-- Radial stationarity is exactly temperature matching. -/
theorem radial_stationary_iff (a q u t z : ℝ) :
    deriv (potential t z (a ^ 2) q) (Real.exp u) = 0 ↔
      temperature (a ^ 2) q (Real.exp u) = t := by
  rw [(potential_radial_hasDerivAt a q u t z).deriv, mul_eq_zero]
  simp only [ne_of_gt (entropy_radial_response_pos a u), or_false, sub_eq_zero]

theorem potential_coupling_hasDerivAt (t z ℓ q x : ℝ) :
    HasDerivAt (fun l => potential t z l q x)
      (3 - 24 * Real.pi * x * t - z) ℓ := by
  have he := (((hasDerivAt_id ℓ).const_add (x ^ 4 + x ^ 2)).const_mul 3).add_const
    (q ^ 2 / x ^ 2)
  have hs := (((hasDerivAt_id ℓ).mul_const (6 * x)).const_add (x ^ 3)).const_mul
    (4 * Real.pi)
  have h := (he.sub (hs.const_mul t)).sub ((hasDerivAt_id ℓ).mul_const z)
  convert h using 1 <;> (try dsimp [potential, energy, entropy]) <;> ring

/-- On a thermal saddle the coupling equation matches the prescribed source. -/
theorem coupling_stationary_iff (z ℓ q x : ℝ) :
    deriv (fun l => potential (temperature ℓ q x) z l q x) ℓ = 0 ↔
      couplingResponse ℓ q x = z := by
  rw [(potential_coupling_hasDerivAt _ _ _ _ _).deriv]
  exact sub_eq_zero

theorem temperature_pos_iff (a q u : ℝ) :
    0 < temperature (a ^ 2) q (Real.exp u) ↔
      q ^ 2 < 6 * Real.exp u ^ 6 + 3 * Real.exp u ^ 4 := by
  have hd : 0 < 6 * Real.pi * Real.exp u ^ 3 * (Real.exp u ^ 2 + 2 * a ^ 2) := by
    positivity
  rw [temperature, div_pos_iff_of_pos_right hd, sub_pos]

theorem entropy_gap (ℓ x y : ℝ) :
    entropy ℓ y - entropy ℓ x =
      4 * Real.pi * (y - x) * (y ^ 2 + y * x + x ^ 2 + 6 * ℓ) := by
  unfold entropy
  ring

/-- Increasing the positive radius always increases entropy at nonnegative coupling. -/
theorem entropy_gap_pos (a u v : ℝ) :
    0 < entropy (a ^ 2) (Real.exp u + Real.exp v) - entropy (a ^ 2) (Real.exp u) := by
  rw [entropy_gap]
  have hgap : Real.exp u + Real.exp v - Real.exp u = Real.exp v := by ring
  rw [hgap]
  positivity

#print axioms radial_first_law
#print axioms radial_stationary_iff
#print axioms coupling_stationary_iff
#print axioms entropy_gap_pos

end GaloisForLFunctions.HTGeometry.AdSGaussBonnet
