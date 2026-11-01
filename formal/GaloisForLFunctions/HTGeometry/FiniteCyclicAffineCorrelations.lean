import GaloisForLFunctions.HTGeometry.FiniteCyclicPairFourier
import GaloisForLFunctions.HTGeometry.GagliardoFourierConstant

/-!
# Affine correlations on the finite residue torus

Cross Parseval and the shear transformation law identify spatial affine correlations
with dual-shear pairings. The unit-translation multiplier has absolute value
`2 |cos(π a.val / n)|`.
-/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
namespace GaloisForLFunctions.HTGeometry
variable {n : ℕ} [NeZero n]

/-- Pairing a shear with its unit translate produces the cosine multiplier in Fourier space. -/
theorem cyclicPairFourier_shearPairX (f : ZMod n × ZMod n → ℂ)
    (s a t : ZMod n) :
    cyclicPairFourier
        (fun p => f (p.1 + s * p.2, p.2) + f (p.1 + s * p.2 + 1, p.2)) (a, t) =
      (1 + ZMod.stdAddChar a) * cyclicPairFourier f (a, t - s * a) := by
  have h := cyclicPairFourier_add
    (fun p => f (p.1 + s * p.2 + 0, p.2))
    (fun p => f (p.1 + s * p.2 + 1, p.2)) (a, t)
  rw [cyclicPairFourier_shearX, cyclicPairFourier_shearX] at h
  simpa only [Pi.add_def, add_zero, zero_mul, one_mul, AddChar.map_zero_eq_one,
    add_mul] using h

/-- The corresponding vertical pair has its phase in the second frequency coordinate. -/
theorem cyclicPairFourier_shearPairY (f : ZMod n × ZMod n → ℂ)
    (s a t : ZMod n) :
    cyclicPairFourier
        (fun p => f (p.1, p.2 + s * p.1) + f (p.1, p.2 + s * p.1 + 1)) (a, t) =
      (1 + ZMod.stdAddChar t) * cyclicPairFourier f (a - s * t, t) := by
  have h := cyclicPairFourier_add
    (fun p => f (p.1, p.2 + s * p.1 + 0))
    (fun p => f (p.1, p.2 + s * p.1 + 1)) (a, t)
  rw [cyclicPairFourier_shearY, cyclicPairFourier_shearY] at h
  simpa only [Pi.add_def, add_zero, zero_mul, one_mul, AddChar.map_zero_eq_one,
    add_mul] using h

/-- Horizontal affine correlations are exactly their dual-shear Fourier pairing. -/
theorem cyclicPairFourier_correlationX (f : ZMod n × ZMod n → ℂ) (s : ZMod n) :
    (n : ℝ) ^ 2 * (∑ p,
      (conj (f p) * (f (p.1 + s * p.2, p.2) + f (p.1 + s * p.2 + 1, p.2))).re) =
      ∑ a : ZMod n × ZMod n,
        (conj (cyclicPairFourier f a) *
          ((1 + ZMod.stdAddChar a.1) * cyclicPairFourier f (a.1, a.2 - s * a.1))).re := by
  rw [← cyclicPairFourier_re_inner]
  apply Finset.sum_congr rfl
  intro a _
  rw [cyclicPairFourier_shearPairX]

/-- Vertical affine correlations are exactly their dual-shear Fourier pairing. -/
theorem cyclicPairFourier_correlationY (f : ZMod n × ZMod n → ℂ) (s : ZMod n) :
    (n : ℝ) ^ 2 * (∑ p,
      (conj (f p) * (f (p.1, p.2 + s * p.1) + f (p.1, p.2 + s * p.1 + 1))).re) =
      ∑ a : ZMod n × ZMod n,
        (conj (cyclicPairFourier f a) *
          ((1 + ZMod.stdAddChar a.2) * cyclicPairFourier f (a.1 - s * a.2, a.2))).re := by
  rw [← cyclicPairFourier_re_inner]
  apply Finset.sum_congr rfl
  intro a _
  rw [cyclicPairFourier_shearPairY]

/-- Translating a unit phase by one yields twice the absolute half-angle cosine. -/
theorem norm_one_add_exp_mul_I (θ : ℝ) :
    ‖1 + Complex.exp ((θ : ℂ) * Complex.I)‖ = 2 * |Real.cos (θ / 2)| := by
  have h := normSq_exp_mul_I_sub_one (θ + Real.pi)
  have he : Complex.exp (((θ + Real.pi : ℝ) : ℂ) * Complex.I) =
      -Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [Complex.ofReal_add, add_mul, Complex.exp_add, Complex.exp_pi_mul_I, mul_neg_one]
  rw [he, show -Complex.exp ((θ : ℂ) * Complex.I) - 1 =
    -(1 + Complex.exp ((θ : ℂ) * Complex.I)) by ring, norm_neg,
    Real.cos_add_pi] at h
  have hc := Real.cos_two_mul (θ / 2)
  rw [show 2 * (θ / 2) = θ by ring] at hc
  nlinarith only [h, hc, sq_abs (Real.cos (θ / 2)),
    norm_nonneg (1 + Complex.exp ((θ : ℂ) * Complex.I)),
    abs_nonneg (Real.cos (θ / 2))]

/-- Absolute phase multiplier of a unit translate on a finite cyclic group. -/
theorem norm_one_add_stdAddChar (a : ZMod n) :
    ‖1 + ZMod.stdAddChar a‖ = 2 * |Real.cos (Real.pi * a.val / n)| := by
  have ha : ZMod.stdAddChar a =
      Complex.exp (((2 * Real.pi * a.val / n : ℝ) : ℂ) * Complex.I) := by
    have h := ZMod.stdAddChar_coe (N := n) (a.val : ℤ)
    simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at h
    rw [h]
    congr 1
    push_cast
    ring
  rw [ha, norm_one_add_exp_mul_I]
  congr 3
  ring


end GaloisForLFunctions.HTGeometry
