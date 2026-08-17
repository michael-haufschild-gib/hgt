import GaloisForLFunctions.RHTower.Sieve.VonMangoldtTwistRouteTSharp

/-!
# The Route-T twisted Chebyshev bound at a scaled smoothing width

The smoothing width of the Perron transfer is a free parameter.  Writing it as `K/D` exposes the
only trade-off in the contour estimate: the smoothing loss is `D²` and the desmoothing loss is
`K log(2K)/D`.  Every collapse of the capstone to a single decaying rate is a choice of `D`.
-/

namespace RHTower.Sieve

open Complex ArithmeticFunction

/-- **The Route-T twisted Chebyshev bound with the smoothing width written as `K/D`.** -/
theorem exists_norm_partialSum_vonMangoldtTwist_routeT_scaled :
    ∃ A Creg delta Ctot τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (K : ℕ) (D τ : ℝ), Real.exp 9 ≤ (K : ℝ) → 1 ≤ D → τ₀ ≤ |τ| →
        ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖
          ≤ Ctot * (K : ℝ) * D ^ 2
                * ((Real.log (K : ℝ)) ^ 2 / |τ|
                    + (1 / |τ| + Real.log (3 * |τ| / 2)
                        / routeTZeroFreeWidth A (3 * |τ| / 2 + 1))
                      * ((3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2)))
                          + 1 / |τ| ^ 2))
              / (2 * Real.pi)
            + Real.log (2 * (K : ℝ)) * ((K : ℝ) / D) := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_le
  refine ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, ?_⟩
  intro K D τ hK hD hτ
  have hK0 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (Real.exp_pos 9) hK
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD
  have hH0 : (0 : ℝ) < (K : ℝ) / D := div_pos hK0 hD0
  have hHK : (K : ℝ) / D ≤ (K : ℝ) := by
    rw [div_le_iff₀ hD0]
    nlinarith
  have h := hbound K ((K : ℝ) / D) τ hK hH0 hHK hτ
  have hratio : (K : ℝ) / ((K : ℝ) / D) = D := by
    field_simp
  rw [hratio] at h
  refine h.trans (add_le_add le_rfl ?_)
  refine mul_le_mul_of_nonneg_right ?_ hH0.le
  refine Real.log_le_log (by linarith) ?_
  linarith

/-- **The Route-T twisted Chebyshev bound at the balanced smoothing width.**  Choosing
`D = (3K)^{w/3}`, with `w` the uniform regularity width, splits the estimate into a part carrying
the full contour saving `(3K)^{-w/3}` and a part carrying only the height decay in `τ`. -/
theorem exists_norm_partialSum_vonMangoldtTwist_routeT_balancedWidth :
    ∃ A Creg delta Ctot τ₀ : ℝ, 0 < Creg ∧ 0 < delta ∧ 0 < Ctot ∧ 2 ≤ τ₀ ∧
      ∀ (K : ℕ) (τ : ℝ), Real.exp 9 ≤ (K : ℝ) → τ₀ ≤ |τ| →
        ‖∑ n ∈ Finset.range (K + 1), vonMangoldtTwist τ n‖
          ≤ Ctot * (K : ℝ)
              * ((3 * (K : ℝ)) ^ (2 * routeTUniformRegWidth A delta (3 * |τ| / 2) / 3)
                    * ((Real.log (K : ℝ)) ^ 2 / |τ|
                      + (1 / |τ| + Real.log (3 * |τ| / 2)
                          / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)) * (1 / |τ| ^ 2))
                  + (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))
                    * (1 / |τ| + Real.log (3 * |τ| / 2)
                        / routeTZeroFreeWidth A (3 * |τ| / 2 + 1)))
              / (2 * Real.pi)
            + Real.log (2 * (K : ℝ))
              * ((K : ℝ)
                * (3 * (K : ℝ)) ^ (-(routeTUniformRegWidth A delta (3 * |τ| / 2) / 3))) := by
  obtain ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, hbound⟩ :=
    exists_norm_partialSum_vonMangoldtTwist_routeT_scaled
  refine ⟨A, Creg, delta, Ctot, τ₀, hCreg, hdelta, hCtot, hτ₀, ?_⟩
  intro K τ hK hτ
  have hK0 : (0 : ℝ) < (K : ℝ) := lt_of_lt_of_le (Real.exp_pos 9) hK
  have h3K : (1 : ℝ) ≤ 3 * (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := le_trans (by
      have := Real.add_one_le_exp (9 : ℝ)
      linarith) hK
    linarith
  have h3K0 : (0 : ℝ) < 3 * (K : ℝ) := by linarith
  set w : ℝ := routeTUniformRegWidth A delta (3 * |τ| / 2) with hw
  have hw0 : 0 < w := by rw [hw]; exact routeTUniformRegWidth_pos hdelta
  set D : ℝ := (3 * (K : ℝ)) ^ (w / 3) with hDdef
  have hD1 : (1 : ℝ) ≤ D := by
    rw [hDdef]
    have h0 : ((3 * (K : ℝ)) : ℝ) ^ (0 : ℝ) = 1 := Real.rpow_zero _
    rw [← h0]
    exact Real.rpow_le_rpow_of_exponent_le h3K (by positivity)
  have hD0 : (0 : ℝ) < D := lt_of_lt_of_le one_pos hD1
  have hDsq : D ^ 2 = (3 * (K : ℝ)) ^ (2 * w / 3) := by
    rw [hDdef, ← Real.rpow_natCast ((3 * (K : ℝ)) ^ (w / 3)) 2, ← Real.rpow_mul h3K0.le]
    congr 1
    push_cast
    ring
  have hDZ : (3 * (K : ℝ)) ^ (2 * w / 3) * (3 * (K : ℝ)) ^ (-w)
      = (3 * (K : ℝ)) ^ (-(w / 3)) := by
    rw [← Real.rpow_add h3K0]
    congr 1
    ring
  have hDinv : (K : ℝ) / D = (K : ℝ) * (3 * (K : ℝ)) ^ (-(w / 3)) := by
    rw [hDdef, Real.rpow_neg h3K0.le, div_eq_mul_inv]
  have h := hbound K D τ hK hD1 hτ
  rw [← hw] at h
  refine h.trans (le_of_eq ?_)
  rw [hDinv, hDsq, ← hDZ]
  ring

end RHTower.Sieve
