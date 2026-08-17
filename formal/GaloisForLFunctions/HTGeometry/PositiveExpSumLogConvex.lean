import GaloisForLFunctions.HTGeometry.LaguerreRule

/-!
# Positive exponential sums are logarithmically convex

An exponential sum with strictly positive coefficients is the Laplace transform of a positive atomic
measure, hence multiplicatively convex:

`R(θ s + η t) ≤ R(s)^θ R(t)^η`  for `θ, η ≥ 0`, `θ + η = 1`.

The proof is the weighted arithmetic–geometric mean inequality applied termwise after normalising
each of the two evaluation points, so that the two resulting weights sum to `θ + η = 1`.

Equivalently `log R` is convex.  This is the structural fact that replaces sign-change counting once
the comparison function is no longer a real exponential sum: the graph of `log R` is a convex curve,
and a convex curve can be separated from a concave one by a line.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- An exponential sum with positive coefficients and at least one term is positive. -/
theorem expSum_pos {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i) (t : ℝ) :
    0 < expSum c a t := by
  rw [expSum]
  refine Finset.sum_pos (fun i _ => mul_pos (hc i) (Real.exp_pos _)) ?_
  exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hm)

private theorem exp_rpow (z w : ℝ) : Real.exp z ^ w = Real.exp (z * w) := by
  rw [Real.rpow_def_of_pos (Real.exp_pos z), Real.log_exp]

/-- **Multiplicative convexity of a positive exponential sum.** -/
theorem expSum_le_rpow_mul_rpow {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    {s t θ η : ℝ} (hθ : 0 ≤ θ) (hη : 0 ≤ η) (hsum : θ + η = 1) :
    expSum c a (θ * s + η * t) ≤ expSum c a s ^ θ * expSum c a t ^ η := by
  have hX : 0 < expSum c a s := expSum_pos c a hm hc s
  have hY : 0 < expSum c a t := expSum_pos c a hm hc t
  have hXY : (0 : ℝ) < expSum c a s ^ θ * expSum c a t ^ η := by positivity
  have hterm : ∀ i : Fin m, c i * Real.exp (a i * (θ * s + η * t))
      ≤ (θ * (c i * Real.exp (a i * s)) / expSum c a s
          + η * (c i * Real.exp (a i * t)) / expSum c a t)
        * (expSum c a s ^ θ * expSum c a t ^ η) := by
    intro i
    have hp : (0 : ℝ) < c i * Real.exp (a i * s) := mul_pos (hc i) (Real.exp_pos _)
    have hq : (0 : ℝ) < c i * Real.exp (a i * t) := mul_pos (hc i) (Real.exp_pos _)
    have hid : c i * Real.exp (a i * (θ * s + η * t))
        = (c i * Real.exp (a i * s)) ^ θ * (c i * Real.exp (a i * t)) ^ η := by
      rw [Real.mul_rpow (hc i).le (Real.exp_pos _).le,
        Real.mul_rpow (hc i).le (Real.exp_pos _).le, exp_rpow, exp_rpow]
      rw [show c i ^ θ * Real.exp (a i * s * θ) * (c i ^ η * Real.exp (a i * t * η))
          = c i ^ θ * c i ^ η * (Real.exp (a i * s * θ) * Real.exp (a i * t * η)) by ring,
        ← Real.rpow_add (hc i), hsum, Real.rpow_one, ← Real.exp_add]
      congr 2
      ring
    have hamgm := Real.geom_mean_le_arith_mean2_weighted hθ hη
      (div_pos hp hX).le (div_pos hq hY).le hsum
    rw [Real.div_rpow hp.le hX.le, Real.div_rpow hq.le hY.le] at hamgm
    rw [hid, ← div_le_iff₀ hXY]
    calc (c i * Real.exp (a i * s)) ^ θ * (c i * Real.exp (a i * t)) ^ η
          / (expSum c a s ^ θ * expSum c a t ^ η)
        = (c i * Real.exp (a i * s)) ^ θ / expSum c a s ^ θ
            * ((c i * Real.exp (a i * t)) ^ η / expSum c a t ^ η) := by
          field_simp
      _ ≤ θ * (c i * Real.exp (a i * s) / expSum c a s)
            + η * (c i * Real.exp (a i * t) / expSum c a t) := hamgm
      _ = θ * (c i * Real.exp (a i * s)) / expSum c a s
            + η * (c i * Real.exp (a i * t)) / expSum c a t := by ring
  calc expSum c a (θ * s + η * t)
      = ∑ i, c i * Real.exp (a i * (θ * s + η * t)) := rfl
    _ ≤ ∑ i, (θ * (c i * Real.exp (a i * s)) / expSum c a s
          + η * (c i * Real.exp (a i * t)) / expSum c a t)
        * (expSum c a s ^ θ * expSum c a t ^ η) := Finset.sum_le_sum (fun i _ => hterm i)
    _ = ((θ / expSum c a s) * (∑ i, c i * Real.exp (a i * s))
          + (η / expSum c a t) * (∑ i, c i * Real.exp (a i * t)))
        * (expSum c a s ^ θ * expSum c a t ^ η) := by
        rw [← Finset.sum_mul, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl (fun i _ => ?_)
        field_simp
    _ = expSum c a s ^ θ * expSum c a t ^ η := by
        rw [show (∑ i, c i * Real.exp (a i * s)) = expSum c a s from rfl,
          show (∑ i, c i * Real.exp (a i * t)) = expSum c a t from rfl]
        field_simp
        linarith [hsum]

/-- **`log` of a positive exponential sum is convex.** -/
theorem convexOn_log_expSum {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i) :
    ConvexOn ℝ univ (fun t => Real.log (expSum c a t)) := by
  refine ⟨convex_univ, ?_⟩
  intro s _ t _ θ η hθ hη hsum
  have hX : 0 < expSum c a s := expSum_pos c a hm hc s
  have hY : 0 < expSum c a t := expSum_pos c a hm hc t
  have hbound := expSum_le_rpow_mul_rpow c a hm hc hθ hη hsum (s := s) (t := t)
  have hpos : (0 : ℝ) < expSum c a (θ * s + η * t) := expSum_pos c a hm hc _
  have hrhs : Real.log (expSum c a s ^ θ * expSum c a t ^ η)
      = θ * Real.log (expSum c a s) + η * Real.log (expSum c a t) := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hX, Real.log_rpow hY]
  simp only [smul_eq_mul]
  rw [← hrhs]
  exact Real.log_le_log hpos hbound


/-! ## The supporting exponential -/

theorem differentiable_log_expSum {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i) :
    Differentiable ℝ (fun t => Real.log (expSum c a t)) := fun t =>
  ((hasDerivAt_expSum c a t).log (ne_of_gt (expSum_pos c a hm hc t))).differentiableAt

/-- **The supporting exponential.**  A positive exponential sum lies above the exponential of the
tangent line to its logarithm at any point: the logarithmic derivative at `s` is the exponent of the
single exponential touching `R` at `s` from below.  This is the convexity of `log R` in the form the
separation argument uses. -/
theorem exp_supporting_le_expSum {m : ℕ} (c a : Fin m → ℝ) (hm : 0 < m) (hc : ∀ i, 0 < c i)
    (s t : ℝ) :
    Real.exp (Real.log (expSum c a s)
        + expSum (fun i => c i * a i) a s / expSum c a s * (t - s)) ≤ expSum c a t := by
  set f : ℝ → ℝ := fun r => Real.log (expSum c a r) with hf
  set d : ℝ := expSum (fun i => c i * a i) a s / expSum c a s with hd
  have hderiv : HasDerivAt f d s :=
    (hasDerivAt_expSum c a s).log (ne_of_gt (expSum_pos c a hm hc s))
  have hdiff : Differentiable ℝ f := differentiable_log_expSum c a hm hc
  have hconv : ConvexOn ℝ univ f := convexOn_log_expSum c a hm hc
  have htan : f s + d * (t - s) ≤ f t := by
    have hderiv' : deriv f s = d := hderiv.deriv
    rcases lt_trichotomy t s with hts | hts | hts
    · have hslope := hconv.slope_le_deriv (mem_univ t) (mem_univ s) hts (hdiff s)
      rw [slope_def_field, hderiv'] at hslope
      have hpos : (0 : ℝ) < s - t := by linarith
      rw [div_le_iff₀ hpos] at hslope
      linarith
    · rw [hts]; simp
    · have hslope := hconv.deriv_le_slope (mem_univ s) (mem_univ t) hts (hdiff s)
      rw [slope_def_field, hderiv'] at hslope
      have hpos : (0 : ℝ) < t - s := by linarith
      rw [le_div_iff₀ hpos] at hslope
      linarith
  have hRt : 0 < expSum c a t := expSum_pos c a hm hc t
  have := Real.exp_le_exp.mpr htan
  rwa [hf, Real.exp_log hRt] at this

end GaloisForLFunctions.HTGeometry
