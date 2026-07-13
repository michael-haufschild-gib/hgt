import GaloisForLFunctions.RHTower.PrimeLeeYangPolydisk

/-!
# The physical Euler amplitude displaces the Lee--Yang torus

The centered prime character `exp(-log(p) I z)` has unit norm on the centered critical line.
The actual local Euler monomial contains the additional square-root amplitude `p⁻¹⁄²`.  Its norm is

`exp(log(p) (Im z - 1/2))`.

Consequently the physical Euler monomial is strictly inside the unit disk on the centered critical
line and reaches the unit circle only at `Im z=1/2`, the boundary `Re s=0` in the original
coordinate `s=1/2+Iz`.  Raw substitution of Euler monomials into a Lee--Yang partition function
therefore cannot locate the critical line.

The positive successor is exact: a viable completed-source construction must absorb the
square-root amplitude into ferromagnetic interactions or into an independently zero-free
archimedean normalization while keeping the centered character as the field variable.
-/

open Complex

namespace RHTower

noncomputable section

/-- The physical centered Euler field `p⁻¹⁄² exp(-log(p) I z)`, with the square-root amplitude
written exponentially. -/
def physicalCenteredEulerLeeYangField (p : Nat.Primes) (z : ℂ) : ℂ :=
  (Real.exp (-(1 / 2 : ℝ) * primeLeeYangLog p) : ℂ) *
    centeredPrimeLeeYangField p z

theorem norm_physicalCenteredEulerLeeYangField (p : Nat.Primes) (z : ℂ) :
    ‖physicalCenteredEulerLeeYangField p z‖ =
      Real.exp (primeLeeYangLog p * (z.im - 1 / 2)) := by
  rw [physicalCenteredEulerLeeYangField, norm_mul,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), norm_centeredPrimeLeeYangField,
    ← Real.exp_add]
  congr 1
  ring

/-- The physical Euler field remains contractive throughout `Im z<1/2`, not merely below the
centered critical line. -/
theorem norm_physicalCenteredEulerLeeYangField_lt_one_iff
    (p : Nat.Primes) (z : ℂ) :
    ‖physicalCenteredEulerLeeYangField p z‖ < 1 ↔ z.im < 1 / 2 := by
  rw [norm_physicalCenteredEulerLeeYangField, Real.exp_lt_one_iff]
  have hp : 0 < primeLeeYangLog p := by
    unfold primeLeeYangLog
    exact Real.log_pos (by exact_mod_cast p.2.one_lt)
  constructor
  · intro h
    by_contra hz
    exact (not_lt_of_ge (mul_nonneg hp.le (sub_nonneg.mpr (not_lt.mp hz)))) h
  · intro h
    exact mul_neg_of_pos_of_neg hp (sub_neg.mpr h)

/-- The unit torus of the physical local field is the strip boundary `Im z=1/2`. -/
theorem norm_physicalCenteredEulerLeeYangField_eq_one_iff
    (p : Nat.Primes) (z : ℂ) :
    ‖physicalCenteredEulerLeeYangField p z‖ = 1 ↔ z.im = 1 / 2 := by
  rw [norm_physicalCenteredEulerLeeYangField, Real.exp_eq_one_iff]
  have hp : primeLeeYangLog p ≠ 0 := by
    unfold primeLeeYangLog
    exact ne_of_gt (Real.log_pos (by exact_mod_cast p.2.one_lt))
  constructor
  · intro h
    exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hp)
  · intro h
    rw [h, sub_self, mul_zero]

/-- On the centered critical line the physical Euler field is strictly contractive. -/
theorem norm_physicalCenteredEulerLeeYangField_criticalLine_lt_one
    (p : Nat.Primes) (z : ℂ) (hz : z.im = 0) :
    ‖physicalCenteredEulerLeeYangField p z‖ < 1 := by
  rw [norm_physicalCenteredEulerLeeYangField_lt_one_iff, hz]
  norm_num

end

end RHTower
