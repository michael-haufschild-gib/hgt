import GaloisForLFunctions.RHTower.HermiteEvenCarrier
import GaloisForLFunctions.RHTower.ConstrainedProlateSignedSpectrum
import GaloisForLFunctions.HTGeometry.GreedyCourantFischer

/-!
# The signed prolate spectrum from the step-four Hermite trial space

The constrained transfer is stated for the **signed** eigenvalues of the self-adjoint block
`Tₐ = Pₐ F Pₐ`, through the family `1 − σₙ(a)²`.  The trial-space estimates, by contrast, are
naturally about the greedy constrained norms.  The two are joined by the identity
`|σₙ(a)| = orthSup Tₐ (sgVec Tₐ) n`, so a Courant–Fischer lower bound on the constrained norm is
a lower bound on `|σₙ|`, hence an upper bound on `1 − σₙ²`.  The sign never has to be determined:
squaring erases it, and `1 − σₙ²` is exactly the quantity the transfer consumes.

Feeding the step-four Hermite trial space through this gives, at every fixed index,

```text
1 − σₙ(a)² ≤ (aggregate squared Hermite truncation error) → 0,
```

with an explicit exponential rate.  This is the leakage family of the constrained transfer
contract, bounded above unconditionally on the true operator.
-/

open Filter
open scoped Real

noncomputable section

namespace RHTower

/-- The signed prolate eigenvalues are bounded by one in absolute value, `Tₐ` being a
contraction. -/
theorem abs_evenProlateSignedValue_le_one (a : ℝ) (n : ℕ) :
    |evenProlateSignedValue a n| ≤ 1 := by
  have hval : evenProlateSignedValue a n
      = RCLike.re (inner ℂ (evenProlateSignedMode a n)
          (evenTimeBandFourier a (evenProlateSignedMode a n))) := rfl
  rcases evenProlateSignedMode_norm_zero_or_one a n with h0 | h1
  · rw [hval, h0]
    simp
  · have hre : |RCLike.re (inner ℂ (evenProlateSignedMode a n)
        (evenTimeBandFourier a (evenProlateSignedMode a n)))|
        ≤ ‖inner ℂ (evenProlateSignedMode a n)
            (evenTimeBandFourier a (evenProlateSignedMode a n))‖ := RCLike.abs_re_le_norm _
    have hcs : ‖inner ℂ (evenProlateSignedMode a n)
        (evenTimeBandFourier a (evenProlateSignedMode a n))‖
        ≤ ‖evenProlateSignedMode a n‖
            * ‖evenTimeBandFourier a (evenProlateSignedMode a n)‖ := norm_inner_le_norm _ _
    have hT := norm_evenTimeBandFourier_le a (evenProlateSignedMode a n)
    rw [hval]
    rw [h1] at hcs hT
    linarith

/-- **The signed Courant–Fischer bound.**  A trial subspace of dimension exceeding `n` on which
`Tₐ` retains a fraction `1 − ε` of the squared norm caps `1 − σₙ(a)²` by `ε`.  The sign of `σₙ`
is irrelevant because the conclusion is about its square. -/
theorem one_sub_evenProlateSignedValue_sq_le_of_form_trial (a : ℝ) (ha : 0 < a) (n : ℕ)
    (V : Submodule ℂ evenSubspace) (hV : n < Module.finrank ℂ V)
    {ε : ℝ} (hV2 : ∀ f ∈ V, (1 - ε) * ‖f‖ ^ (2 : ℕ) ≤ ‖evenTimeBandFourier a f‖ ^ (2 : ℕ)) :
    1 - evenProlateSignedValue a n ^ (2 : ℕ) ≤ ε := by
  rcases le_or_gt 1 ε with hbig | hsmall
  · nlinarith [sq_nonneg (evenProlateSignedValue a n)]
  · have hpos : (0 : ℝ) < 1 - ε := by linarith
    have hM : ∀ f ∈ V, Real.sqrt (1 - ε) * ‖f‖ ≤ ‖evenTimeBandFourier a f‖ := by
      intro f hf
      have h := hV2 f hf
      have hsq : (Real.sqrt (1 - ε) * ‖f‖) ^ (2 : ℕ) ≤ ‖evenTimeBandFourier a f‖ ^ (2 : ℕ) := by
        rw [mul_pow, Real.sq_sqrt hpos.le]
        exact h
      nlinarith [hsq, norm_nonneg (evenTimeBandFourier a f),
        mul_nonneg (Real.sqrt_nonneg (1 - ε)) (norm_nonneg f)]
    have hlow := ContinuousLinearMap.le_orthSup_of_trial (evenTimeBandFourier a)
      (ContinuousLinearMap.sgVec (evenTimeBandFourier a)) n V hV hM
    have habs := ContinuousLinearMap.abs_sgVal
      (isCompactOperator_evenTimeBandFourier a ha)
      (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (adjoint_evenTimeBandFourier a)) n
    have hval : evenProlateSignedValue a n
        = ContinuousLinearMap.sgVal (evenTimeBandFourier a) n := rfl
    rw [← habs] at hlow
    have hlow' : Real.sqrt (1 - ε) ≤ |evenProlateSignedValue a n| := by
      rw [hval]
      exact hlow
    have h2 := pow_le_pow_left₀ (Real.sqrt_nonneg (1 - ε)) hlow' 2
    rw [Real.sq_sqrt hpos.le, sq_abs] at h2
    linarith

/-- **The constrained transfer's leakage family is bounded by the Hermite truncation error.** -/
theorem one_sub_evenProlateSignedValue_sq_le_hermite (a : ℝ) (ha : 0 < a) (n : ℕ) :
    1 - evenProlateSignedValue a n ^ (2 : ℕ) ≤ hermiteTrialDefect a n :=
  one_sub_evenProlateSignedValue_sq_le_of_form_trial a ha n (hermiteTrialSpace n)
    (by rw [finrank_hermiteTrialSpace]; omega)
    (fun f hf => hermiteTrialSpace_concentration a n hf)

theorem one_sub_evenProlateSignedValue_sq_nonneg (a : ℝ) (n : ℕ) :
    0 ≤ 1 - evenProlateSignedValue a n ^ (2 : ℕ) := by
  have h := abs_evenProlateSignedValue_le_one a n
  nlinarith [abs_nonneg (evenProlateSignedValue a n), sq_abs (evenProlateSignedValue a n)]

/-- **The leakage family of the constrained transfer decays exponentially at every fixed
index.** -/
theorem exists_one_sub_evenProlateSignedValue_sq_le_exp (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      1 - evenProlateSignedValue a n ^ (2 : ℕ) ≤ C * (Real.exp (-(π * a ^ (2 : ℕ))) / a) := by
  obtain ⟨C, hC0, hC⟩ := exists_hermiteTrialDefect_le_exp n
  exact ⟨C, hC0, fun a ha =>
    le_trans (one_sub_evenProlateSignedValue_sq_le_hermite a ha n) (hC a ha)⟩

/-- **The leakage family of the constrained transfer vanishes at every fixed index.**  This is
the contract's qualitative content, proved on the true signed spectrum. -/
theorem one_sub_evenProlateSignedValue_sq_tendsto_zero (n : ℕ) :
    Tendsto (fun a : ℝ => 1 - evenProlateSignedValue a n ^ (2 : ℕ)) atTop (nhds 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
    (tendsto_hermiteTrialDefect n) ?_ ?_
  · filter_upwards with a
    exact one_sub_evenProlateSignedValue_sq_nonneg a n
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
    exact one_sub_evenProlateSignedValue_sq_le_hermite a ha n

/-- The signed prolate eigenvalues approach the unit circle at every fixed index: their squares
tend to one. -/
theorem evenProlateSignedValue_sq_tendsto_one (n : ℕ) :
    Tendsto (fun a : ℝ => evenProlateSignedValue a n ^ (2 : ℕ)) atTop (nhds 1) := by
  have h := one_sub_evenProlateSignedValue_sq_tendsto_zero n
  have hsub : Tendsto (fun a : ℝ => 1 - (1 - evenProlateSignedValue a n ^ (2 : ℕ))) atTop
      (nhds ((1 : ℝ) - 0)) := tendsto_const_nhds.sub h
  rw [sub_zero] at hsub
  exact Tendsto.congr (fun a => by ring) hsub

end RHTower

end
