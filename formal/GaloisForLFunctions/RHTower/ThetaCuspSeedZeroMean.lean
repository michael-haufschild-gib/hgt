import GaloisForLFunctions.RHTower.PrimeArchThetaGaussianApertureColdWatson

/-!
# The theta-cusp seed has exactly vanishing half-line mean

The normalized seed `thetaCuspSeed t = 2π(2πt⁴ − 3t²)e^{−πt²}` integrates to zero on the
half-line: its fourth-moment and second-moment Gaussian contributions cancel exactly
(`4π²·3/(8π²) = 3/2 = 6π·1/(4π)`).  This is the cancellation that upgrades the decay of the
all-integer theta-cusp state at the cusp end: with zero mean, the leading Poisson/Euler–Maclaurin
term of `∑_n e^{x/2}·seed(n·eˣ)` vanishes.

The moments are evaluated through the corpus's cold Gaussian half-moment layer
(`integral_coldGaussianHalfMoment`, `coldGaussianHalfMoment_succ`), so the only special-function
input is `Γ(1/2) = √π` at the recursion base.  The seed's evenness is recorded as a simp lemma.
-/

namespace RHTower

noncomputable section

open MeasureTheory Set

/-- The seed is an even function. -/
@[simp] theorem thetaCuspSeed_neg (t : ℝ) : thetaCuspSeed (-t) = thetaCuspSeed t := by
  unfold thetaCuspSeed
  ring_nf

/-- Half-line integrability of `t^n·e^{−πt²}` for every natural power. -/
theorem integrableOn_pow_mul_exp_neg_pi_sq (n : ℕ) :
    IntegrableOn (fun t : ℝ => t ^ n * Real.exp (-Real.pi * t ^ 2)) (Ioi 0) := by
  have h :=
    (integrable_rpow_mul_exp_neg_mul_sq (b := Real.pi) Real.pi_pos
      (s := (n : ℝ))
      (lt_of_lt_of_le (by norm_num : (-1 : ℝ) < 0) (Nat.cast_nonneg n))).integrableOn
      (s := Ioi 0)
  refine h.congr_fun ?_ measurableSet_Ioi
  intro t ht
  simp only [Real.rpow_natCast]

/-- Base of the half-moment recursion at scale `π`: the zeroth cold moment is `1/2`. -/
theorem coldGaussianHalfMoment_pi_zero :
    coldGaussianHalfMoment Real.pi 0 = 1 / 2 := by
  rw [coldGaussianHalfMoment]
  have hshape : thetaCuspGaussianApertureGammaShape 0 = 1 / 2 := by
    simp [thetaCuspGaussianApertureGammaShape]
  rw [hshape, Real.Gamma_one_half_eq, Real.sqrt_eq_rpow]
  have hmul :
      Real.pi ^ (-(1 / 2) : ℝ) * (1 / 2) * Real.pi ^ ((1 / 2) : ℝ) =
        Real.pi ^ (-(1 / 2) : ℝ) * Real.pi ^ ((1 / 2) : ℝ) * (1 / 2) := by ring
  rw [hmul, ← Real.rpow_add Real.pi_pos]
  norm_num

/-- The second cold moment at scale `π` is `1/(4π)`. -/
theorem coldGaussianHalfMoment_pi_one :
    coldGaussianHalfMoment Real.pi 1 = 1 / (4 * Real.pi) := by
  rw [show (1 : ℕ) = 0 + 1 by norm_num, coldGaussianHalfMoment_succ Real.pi_pos 0,
    coldGaussianHalfMoment_pi_zero]
  have hshape : thetaCuspGaussianApertureGammaShape 0 = 1 / 2 := by
    simp [thetaCuspGaussianApertureGammaShape]
  rw [hshape]
  field_simp
  ring

/-- The fourth cold moment at scale `π` is `3/(8π²)`. -/
theorem coldGaussianHalfMoment_pi_two :
    coldGaussianHalfMoment Real.pi 2 = 3 / (8 * Real.pi ^ 2) := by
  have h := coldGaussianHalfMoment_succ Real.pi_pos 1
  norm_num at h
  rw [h, coldGaussianHalfMoment_pi_one]
  have hshape : thetaCuspGaussianApertureGammaShape 1 = 3 / 2 := by
    simp [thetaCuspGaussianApertureGammaShape]
    norm_num
  rw [hshape]
  field_simp
  ring

/-- The Gaussian second half-moment at scale `π`. -/
theorem integral_sq_mul_exp_neg_pi_sq :
    (∫ t : ℝ in Ioi 0, t ^ 2 * Real.exp (-Real.pi * t ^ 2)) = 1 / (4 * Real.pi) := by
  have h := integral_coldGaussianHalfMoment Real.pi_pos 1
  rw [coldGaussianHalfMoment_pi_one] at h
  simpa using h

/-- The Gaussian fourth half-moment at scale `π`. -/
theorem integral_pow_four_mul_exp_neg_pi_sq :
    (∫ t : ℝ in Ioi 0, t ^ 4 * Real.exp (-Real.pi * t ^ 2)) = 3 / (8 * Real.pi ^ 2) := by
  have h := integral_coldGaussianHalfMoment Real.pi_pos 2
  rw [coldGaussianHalfMoment_pi_two] at h
  simpa using h

/-- **The theta-cusp seed has zero half-line mean.**  The fourth- and second-moment Gaussian
contributions cancel exactly; this is the cancellation behind the cusp-end decay of the
all-integer theta state. -/
theorem integral_thetaCuspSeed_Ioi_eq_zero :
    (∫ t : ℝ in Ioi 0, thetaCuspSeed t) = 0 := by
  have hexp :
      (fun t : ℝ => thetaCuspSeed t) =
        fun t : ℝ =>
          (4 * Real.pi ^ 2) * (t ^ 4 * Real.exp (-Real.pi * t ^ 2)) -
            (6 * Real.pi) * (t ^ 2 * Real.exp (-Real.pi * t ^ 2)) := by
    funext t
    unfold thetaCuspSeed
    ring
  rw [hexp, integral_sub ((integrableOn_pow_mul_exp_neg_pi_sq 4).const_mul _)
      ((integrableOn_pow_mul_exp_neg_pi_sq 2).const_mul _),
    integral_const_mul, integral_const_mul,
    integral_pow_four_mul_exp_neg_pi_sq, integral_sq_mul_exp_neg_pi_sq]
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  field_simp
  ring

end

end RHTower
