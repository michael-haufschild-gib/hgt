import GaloisForLFunctions.RHTower.Sieve.RouteTWidthUpper

/-!
# The Route-T envelope against a linear majorant

`Sieve/PrimeRangeTwistTail` needs the twisted envelope below `ρ·x`.  Splitting off the factor `3x`
from both regimes of `Sieve/RouteTWidthUpper.routeTTwistEnvelope_le_polylog` turns that into three
independent inequalities — one per regime of the envelope — each of which is a comparison between
`ρ` and an explicit function of `x` and the frequency.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The Route-T twisted envelope below a linear majorant.** -/
theorem routeTTwistEnvelope_le_mul {A delta C τ x ρ : ℝ} (hC : 0 ≤ C) (hx : 1 ≤ x)
    (hτ : 16 * Real.pi / 3 ≤ |τ|)
    (hcontour : 9 * C * ((3 * x) ^ (-(min delta (routeTWidthPolylogLower A τ) / 6))
        * (routeTTwistHeightFactor A τ + Real.log (2 * x))) ≤ ρ)
    (htrunc : 9 * C * ((3 * x) ^ (2 * (1 / (routeTWidthUpperConst
            * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3)
        * (1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ)) / (1 + |τ|) ≤ ρ)
    (hcheb : 6 * Real.log x / Real.sqrt x ≤ ρ) :
    routeTTwistEnvelope A delta C τ x ≤ ρ * x := by
  have hx0 : (0 : ℝ) < x := by linarith
  have h3x : (0 : ℝ) < 3 * x := by linarith
  have hsqrt : (0 : ℝ) < Real.sqrt x := Real.sqrt_pos.2 hx0
  set m : ℝ := min delta (routeTWidthPolylogLower A τ) with hm
  set v : ℝ := 2 * (1 / (routeTWidthUpperConst
      * (Real.log |τ| / Real.log 2) ^ ((9 : ℝ) / 10))) / 3 with hv
  set P : ℝ := routeTTwistHeightFactor A τ + Real.log (2 * x) with hP
  set Q : ℝ := 1 + (Real.log x) ^ 2 + routeTTwistHeightFactor A τ with hQ
  have hτ0 : (0 : ℝ) < 1 + |τ| := by have := abs_nonneg τ; linarith
  have hbase := routeTTwistEnvelope_le_polylog (A := A) (delta := delta) (C := C) (x := x) hC hx hτ
  rw [← hm, ← hv, ← hP, ← hQ] at hbase
  -- split the factor `3x` off both regimes
  have hsplit1 : (3 * x) ^ (1 - m / 2 / 3) = (3 * x) * (3 * x) ^ (-(m / 6)) := by
    rw [show (1 : ℝ) - m / 2 / 3 = 1 + -(m / 6) by ring, Real.rpow_add h3x, Real.rpow_one]
  have hsplit2 : (3 * x) ^ (1 + v) = (3 * x) * (3 * x) ^ v := by
    rw [Real.rpow_add h3x, Real.rpow_one]
  rw [hsplit1, hsplit2] at hbase
  -- the Chebyshev remainder
  have hchebval : 2 * Real.sqrt x * Real.log x = x * (2 * Real.log x / Real.sqrt x) := by
    field_simp
    rw [Real.sq_sqrt hx0.le]
    ring
  -- the three pieces
  have hA1 : C * ((3 * x) * (3 * x) ^ (-(m / 6)) * P) ≤ x * (ρ / 3) := by
    have hstep : C * ((3 * x) * (3 * x) ^ (-(m / 6)) * P)
        = x * (3 * (C * ((3 * x) ^ (-(m / 6)) * P))) := by ring
    rw [hstep]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    linarith [hcontour]
  have hA2 : C * ((3 * x) * (3 * x) ^ v * Q / (1 + |τ|)) ≤ x * (ρ / 3) := by
    have hstep : C * ((3 * x) * (3 * x) ^ v * Q / (1 + |τ|))
        = x * (3 * (C * ((3 * x) ^ v * Q) / (1 + |τ|))) := by
      field_simp
    rw [hstep]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    have : 9 * C * ((3 * x) ^ v * Q) / (1 + |τ|) ≤ ρ := htrunc
    have h9 : 9 * (C * ((3 * x) ^ v * Q)) / (1 + |τ|) ≤ ρ := by
      refine le_trans (le_of_eq ?_) this
      ring_nf
    have hdiv : 3 * (C * ((3 * x) ^ v * Q) / (1 + |τ|))
        = (9 * (C * ((3 * x) ^ v * Q)) / (1 + |τ|)) / 3 := by
      field_simp
      ring
    rw [hdiv]
    linarith [h9]
  have hA3 : 2 * Real.sqrt x * Real.log x ≤ x * (ρ / 3) := by
    rw [hchebval]
    refine mul_le_mul_of_nonneg_left ?_ hx0.le
    have hthree : 6 * Real.log x / Real.sqrt x = 3 * (2 * Real.log x / Real.sqrt x) := by ring
    rw [hthree] at hcheb
    linarith [hcheb]
  have hexp : C * ((3 * x) * (3 * x) ^ (-(m / 6)) * P
        + (3 * x) * (3 * x) ^ v * Q / (1 + |τ|))
      = C * ((3 * x) * (3 * x) ^ (-(m / 6)) * P)
        + C * ((3 * x) * (3 * x) ^ v * Q / (1 + |τ|)) := by ring
  rw [hexp] at hbase
  linarith [hbase, hA1, hA2, hA3]

end

end RHTower.Sieve
