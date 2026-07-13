import GaloisForLFunctions.RHTower.PrimeLeeYangPolydisk
import GaloisForLFunctions.RHTower.SectorPrimeZeroUniqueness

/-!
# Centered prime characters in Cayley half-plane coordinates

The centered prime field `u_p(z)=exp(-log(p) I z)` lies in the disk below the real centered axis
and in the common exterior above it.  Applying `diskToRight(u)=(1+u)/(1-u)` therefore puts all
prime coordinates in the right half-plane below the axis and in the left half-plane above it.

This is the finite geometric bridge needed by homogeneous half-plane-stable source polynomials.
The denominator cannot vanish off the real centered axis.
-/

open Complex Metric Set

namespace RHTower

noncomputable section

/-- Cayley half-plane coordinate of the centered field at one prime. -/
def centeredPrimeCayley (p : Nat.Primes) (z : ℂ) : ℂ :=
  diskToRight (centeredPrimeLeeYangField p z)

/-- The disk-to-right Cayley transform sends the exterior of the closed unit disk into the open
left half-plane. -/
private theorem diskToRight_re_neg_of_one_lt_norm {u : ℂ} (hu : 1 < ‖u‖) :
    (diskToRight u).re < 0 := by
  have hu1 : u ≠ 1 := by
    intro h
    rw [h, norm_one] at hu
    norm_num at hu
  have hden : 1 - u ≠ 0 := sub_ne_zero.mpr (Ne.symm hu1)
  have hnormsq : 0 < Complex.normSq (1 - u) := Complex.normSq_pos.mpr hden
  have hsq : 1 < u.re ^ 2 + u.im ^ 2 := by
    have hsquare : 1 < ‖u‖ ^ 2 := by
      nlinarith [norm_nonneg u]
    rw [Complex.sq_norm, Complex.normSq_apply] at hsquare
    simpa [pow_two] using hsquare
  rw [diskToRight, Complex.div_re]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im,
    Complex.one_im, zero_add, Complex.sub_im, zero_sub]
  rw [← add_div]
  exact div_neg_of_neg_of_pos (by nlinarith) hnormsq

/-- Below the centered critical line all prime Cayley variables lie in the open right half-plane. -/
theorem centeredPrimeCayley_re_pos_of_im_lt_zero
    (p : Nat.Primes) {z : ℂ} (hz : z.im < 0) :
    0 < (centeredPrimeCayley p z).re := by
  apply diskToRight_re_pos
  simpa [mem_ball, dist_zero_right] using
    (norm_centeredPrimeLeeYangField_lt_one_iff p z).mpr hz

/-- Above the centered critical line all prime Cayley variables lie in the open left half-plane. -/
theorem centeredPrimeCayley_re_neg_of_im_pos
    (p : Nat.Primes) {z : ℂ} (hz : 0 < z.im) :
    (centeredPrimeCayley p z).re < 0 := by
  apply diskToRight_re_neg_of_one_lt_norm
  exact (one_lt_norm_centeredPrimeLeeYangField_iff p z).mpr hz

/-- Cayley denominator clearing introduces no off-line singularity. -/
theorem centeredPrimeCayley_denominator_ne_zero_of_im_ne_zero
    (p : Nat.Primes) {z : ℂ} (hz : z.im ≠ 0) :
    1 - centeredPrimeLeeYangField p z ≠ 0 := by
  intro h
  have heq : centeredPrimeLeeYangField p z = 1 := (eq_of_sub_eq_zero h).symm
  have hnorm : ‖centeredPrimeLeeYangField p z‖ = 1 := by simp [heq]
  exact hz ((norm_centeredPrimeLeeYangField_eq_one_iff p z).mp hnorm)

end


end RHTower
