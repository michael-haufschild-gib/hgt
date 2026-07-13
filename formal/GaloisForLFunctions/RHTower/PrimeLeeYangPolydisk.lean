import GaloisForLFunctions.RHTower.LeeYangQuadraticBlock
import GaloisForLFunctions.RHTower.PrimePowerCenteredMarkRH

/-!
# The centered prime field sees the critical line as the Lee--Yang torus

For the centered spectral coordinate `XiC z = xi (1/2 + I*z)`, the inhomogeneous activity at a
prime `p` is `exp (-log(p) * I * z)`.  Its norm is `exp (log(p) * Im z)`.  Thus every prime
activity is simultaneously inside the unit disk below the real axis, on the unit circle on the
real axis, and outside the unit disk above the real axis.

This is the finite geometric input for a multivariate Lee--Yang detour.  The independent-spin
partition function is included as the zero-interaction baseline: all its zeros are real in the
centered coordinate.  The new analytic problem is not this selector but the construction of
ferromagnetic interacting partition functions which converge locally uniformly to `XiC` after a
source-defined archimedean renormalization.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Positive logarithmic prime scale. -/
def primeLeeYangLog (p : Nat.Primes) : ℝ :=
  Real.log (((p : ℕ) : ℝ))

/-- Inhomogeneous Lee--Yang activity at prime `p` in the centered `XiC` coordinate. -/
def centeredPrimeLeeYangField (p : Nat.Primes) (z : ℂ) : ℂ :=
  centeredPrimeMark (p : ℕ) (1 / 2 + Complex.I * z)

theorem norm_centeredPrimeLeeYangField (p : Nat.Primes) (z : ℂ) :
    ‖centeredPrimeLeeYangField p z‖ =
      Real.exp (primeLeeYangLog p * z.im) := by
  rw [centeredPrimeLeeYangField, norm_centeredPrimeMark]
  congr 1
  unfold primeLeeYangLog
  simp [Complex.mul_re]

/-- The right half of the original critical strip is the common open prime polydisk. -/
theorem norm_centeredPrimeLeeYangField_lt_one_iff
    (p : Nat.Primes) (z : ℂ) :
    ‖centeredPrimeLeeYangField p z‖ < 1 ↔ z.im < 0 := by
  rw [centeredPrimeLeeYangField,
    centeredPrimeMark_norm_lt_one_iff (by exact p.2.one_lt)]
  simp [Complex.mul_re]

/-- The centered critical line is exactly the common prime unit torus. -/
theorem norm_centeredPrimeLeeYangField_eq_one_iff
    (p : Nat.Primes) (z : ℂ) :
    ‖centeredPrimeLeeYangField p z‖ = 1 ↔ z.im = 0 := by
  rw [centeredPrimeLeeYangField,
    centeredPrimeMark_norm_eq_one_iff (by exact p.2.one_lt)]
  simp [Complex.mul_re]

/-- The left half of the original critical strip is the common exterior prime polydisk. -/
theorem one_lt_norm_centeredPrimeLeeYangField_iff
    (p : Nat.Primes) (z : ℂ) :
    1 < ‖centeredPrimeLeeYangField p z‖ ↔ 0 < z.im := by
  rw [norm_centeredPrimeLeeYangField, ← Real.exp_zero, Real.exp_lt_exp]
  constructor
  · intro h
    have hp : 0 < primeLeeYangLog p := by
      unfold primeLeeYangLog
      exact Real.log_pos (by exact_mod_cast p.2.one_lt)
    exact (mul_pos_iff_of_pos_left hp).mp h
  · intro h
    have hp : 0 < primeLeeYangLog p := by
      unfold primeLeeYangLog
      exact Real.log_pos (by exact_mod_cast p.2.one_lt)
    exact mul_pos hp h

/-- Zero-interaction finite prime-spin partition function. -/
def independentPrimeLeeYangPartition
    (P : Finset Nat.Primes) (z : ℂ) : ℂ :=
  ∏ p ∈ P, (1 + centeredPrimeLeeYangField p z)

private theorem one_add_centeredPrimeLeeYangField_ne_zero_of_norm_ne_one
    (p : Nat.Primes) (z : ℂ)
    (h : ‖centeredPrimeLeeYangField p z‖ ≠ 1) :
    1 + centeredPrimeLeeYangField p z ≠ 0 := by
  intro hzero
  have heq : centeredPrimeLeeYangField p z = -1 :=
    eq_neg_of_add_eq_zero_right hzero
  apply h
  rw [heq, norm_neg, norm_one]

theorem independentPrimeLeeYangPartition_ne_zero_of_im_lt_zero
    (P : Finset Nat.Primes) {z : ℂ} (hz : z.im < 0) :
    independentPrimeLeeYangPartition P z ≠ 0 := by
  rw [independentPrimeLeeYangPartition, Finset.prod_ne_zero_iff]
  intro p _
  apply one_add_centeredPrimeLeeYangField_ne_zero_of_norm_ne_one
  exact ne_of_lt ((norm_centeredPrimeLeeYangField_lt_one_iff p z).mpr hz)

theorem independentPrimeLeeYangPartition_ne_zero_of_im_gt_zero
    (P : Finset Nat.Primes) {z : ℂ} (hz : 0 < z.im) :
    independentPrimeLeeYangPartition P z ≠ 0 := by
  rw [independentPrimeLeeYangPartition, Finset.prod_ne_zero_iff]
  intro p _
  apply one_add_centeredPrimeLeeYangField_ne_zero_of_norm_ne_one
  exact ne_of_gt ((one_lt_norm_centeredPrimeLeeYangField_iff p z).mpr hz)

/-- Every zero of the finite independent prime-spin partition lies on the centered critical line. -/
theorem independentPrimeLeeYangPartition_zero_im
    (P : Finset Nat.Primes) {z : ℂ}
    (hz : independentPrimeLeeYangPartition P z = 0) :
    z.im = 0 := by
  by_contra hne
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · exact independentPrimeLeeYangPartition_ne_zero_of_im_lt_zero P hneg hz
  · exact independentPrimeLeeYangPartition_ne_zero_of_im_gt_zero P hpos hz

end

end RHTower
