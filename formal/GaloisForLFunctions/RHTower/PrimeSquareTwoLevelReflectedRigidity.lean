import GaloisForLFunctions.RHTower.PrimeEulerCommonClockRigidity

/-!
# Two-level reflected rigidity of a prime and its square

The reflected moduli of `1 - r exp(iθ)` at levels one and two cannot agree for two
distinct positive radii whose product is below one. Equality at level one fixes the
cosine to their average; equality at level two and the double-angle identity force
their product to equal one. The physical Euler radii have product `1/p`, so the two
prime-power levels already force zero horizontal displacement.

This sharpens the all-power rigidity theorem without any prime-distribution or
recurrence input. It is a classifier, not an assertion that the literal theta source
supplies reflected-modulus neutrality.
-/

open Complex

namespace RHTower

noncomputable section

/-- Neutrality at the first two levels forces the two radii to have product one. -/
theorem two_level_radius_product_one
    {rminus rplus theta : ℝ} (hm : 0 < rminus) (hp : 0 < rplus)
    (hne : rminus ≠ rplus)
    (h1 : ‖(1 : ℂ) - (rplus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖ =
      ‖(1 : ℂ) - (rminus : ℂ) * Complex.exp ((theta : ℂ) * Complex.I)‖)
    (h2 : ‖(1 : ℂ) - ((rplus ^ 2 : ℝ) : ℂ) *
        Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)‖ =
      ‖(1 : ℂ) - ((rminus ^ 2 : ℝ) : ℂ) *
        Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)‖) :
    rminus * rplus = 1 := by
  have hne2 : rminus ^ 2 ≠ rplus ^ 2 := by
    intro heq
    have hprod : (rminus - rplus) * (rminus + rplus) = 0 := by nlinarith
    have hsum : rminus + rplus ≠ 0 := ne_of_gt (add_pos hm hp)
    exact hne (sub_eq_zero.mp ((mul_eq_zero.mp hprod).resolve_right hsum))
  have hc1 := cos_eq_radius_average_of_norm_one_sub_mul_eq hne h1
  have hc2 := cos_eq_radius_average_of_norm_one_sub_mul_eq hne2 h2
  rw [Real.cos_two_mul, hc1] at hc2
  nlinarith

/-- Reflected neutrality at `p` and `p²` alone forces the horizontal displacement to zero. -/
theorem epsilon_eq_zero_of_prime_and_square_reflected_modulus_neutral
    {p : ℕ} (hp : 1 < p) {epsilon theta : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilonHalf : epsilon < 1 / 2)
    (h1 :
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 + epsilon) : ℝ) : ℂ) *
          Complex.exp ((theta : ℂ) * Complex.I)‖ =
      ‖(1 : ℂ) - (((p : ℝ) ^ (-1 / 2 - epsilon) : ℝ) : ℂ) *
          Complex.exp ((theta : ℂ) * Complex.I)‖)
    (h2 :
      ‖(1 : ℂ) - (((((p : ℝ) ^ (-1 / 2 + epsilon)) ^ 2 : ℝ)) : ℂ) *
          Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)‖ =
      ‖(1 : ℂ) - (((((p : ℝ) ^ (-1 / 2 - epsilon)) ^ 2 : ℝ)) : ℂ) *
          Complex.exp (((2 * theta : ℝ) : ℂ) * Complex.I)‖) :
    epsilon = 0 := by
  by_contra hepsilon
  have hepsilonPos : 0 < epsilon := lt_of_le_of_ne hepsilon0 (Ne.symm hepsilon)
  have hpR : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  let rplus : ℝ := (p : ℝ) ^ (-1 / 2 + epsilon)
  let rminus : ℝ := (p : ℝ) ^ (-1 / 2 - epsilon)
  have hrplusPos : 0 < rplus := Real.rpow_pos_of_pos (by positivity) _
  have hrminusPos : 0 < rminus := Real.rpow_pos_of_pos (by positivity) _
  have hrorder : rminus < rplus := by
    exact Real.rpow_lt_rpow_of_exponent_lt hpR (by linarith)
  have hrplusOne : rplus < 1 := by
    exact Real.rpow_lt_one_of_one_lt_of_neg hpR (by linarith)
  have hprod := two_level_radius_product_one hrminusPos hrplusPos
    (ne_of_lt hrorder) h1 h2
  have hlt : rminus * rplus < 1 := by
    have hstep : rminus * rplus < 1 * rplus :=
      mul_lt_mul_of_pos_right (hrorder.trans hrplusOne) hrplusPos
    nlinarith
  exact (ne_of_lt hlt) hprod

end

end RHTower
