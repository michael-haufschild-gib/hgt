import GaloisForLFunctions.RHTower.WeilLogShiftUniformBallGenericity

/-!
# Exponential observation precision and the recovery diagonal

Every damping rate strictly below 4−π leaves the origin inverse diagonal
divergent. Exponentially small bounded-history errors form an affine family
whose continuous linear moment responses retain that divergent diagonal.
-/

open Filter Topology Zeta23 Real
open scoped BoundedContinuousFunction

noncomputable section

namespace RHTower

open WeilExcess

/-- Every strict exponential damping rate below 4−π leaves an unbounded
origin inverse diagonal, in fact one tending to infinity. -/
theorem tendsto_weilLogShiftRecoveryDiagonal_exp_damped {σ : ℝ} (hσ : σ < 4 - π) :
    Tendsto (fun k => exp (-(σ * (k + 2 : ℕ))) *
      weilLogShiftRecoveryMomentResponse 0 (k + 2) k) atTop atTop := by
  obtain ⟨c, γ, hc, hγ, hlower⟩ :=
    exists_weilLogShiftOriginDiagonal_exponential_lower_above hσ
  have hgap : 0 < γ - σ := sub_pos.mpr hγ
  have harg : Tendsto (fun k : ℕ => (γ - σ) * (k + 2 : ℕ)) atTop atTop := by
    apply tendsto_atTop.mpr
    intro B
    have hscaled := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop hgap
    filter_upwards [hscaled.eventually_ge_atTop B] with k hk
    have hk2 : (k : ℝ) ≤ (k + 2 : ℕ) := by
      exact_mod_cast (show k ≤ k + 2 by omega)
    exact hk.trans (mul_le_mul_of_nonneg_left hk2 hgap.le)
  apply tendsto_atTop_mono' atTop ?_ ((tendsto_exp_atTop.comp harg).const_mul_atTop hc)
  filter_upwards [hlower] with k hk
  have he : exp (-(σ * (k + 2 : ℕ))) * exp (γ * (k + 2 : ℕ)) =
      exp ((γ - σ) * (k + 2 : ℕ)) := by
    rw [← exp_add]
    congr 1
    ring
  calc
    c * exp ((γ - σ) * (k + 2 : ℕ)) =
        exp (-(σ * (k + 2 : ℕ))) * (c * exp (γ * (k + 2 : ℕ))) := by rw [← he]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hk (exp_pos _).le

/-- A bounded positive exponential precision envelope on recovery coordinates. -/
def weilLogShiftExponentialEnvelope (σ : ℝ) (hσ : 0 ≤ σ) : ℕ →ᵇ ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (fun k => exp (-(σ * (k + 2 : ℕ))))
    continuous_of_discreteTopology 1 (fun k => by
      rw [Real.norm_eq_abs, abs_of_pos (exp_pos _)]
      calc
        exp (-(σ * (k + 2 : ℕ))) ≤ exp 0 :=
          exp_le_exp.mpr (neg_nonpos.mpr (mul_nonneg hσ (by positivity)))
        _ = 1 := exp_zero)

theorem weilLogShiftExponentialEnvelope_apply (σ : ℝ) (hσ : 0 ≤ σ) (k : ℕ) :
    weilLogShiftExponentialEnvelope σ hσ k = exp (-(σ * (k + 2 : ℕ))) := rfl

/-- Exponentially shrinking observation errors around an arbitrary bounded center. -/
def weilLogShiftExponentialPerturbation (center : ℕ →ᵇ ℝ) (ε σ : ℝ) (hσ : 0 ≤ σ)
    (u : ℕ →ᵇ ℝ) : ℕ →ᵇ ℝ :=
  center + ε • (weilLogShiftExponentialEnvelope σ hσ * u)

theorem weilLogShiftExponentialPerturbation_apply (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hσ : 0 ≤ σ) (u : ℕ →ᵇ ℝ) (k : ℕ) :
    weilLogShiftExponentialPerturbation center ε σ hσ u k =
      center k + ε * (exp (-(σ * (k + 2 : ℕ))) * u k) := rfl

theorem continuous_weilLogShiftExponentialPerturbation (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hσ : 0 ≤ σ) : Continuous (weilLogShiftExponentialPerturbation center ε σ hσ) := by
  change Continuous (fun u : ℕ →ᵇ ℝ => center +
    (ε • ContinuousLinearMap.mul ℝ (ℕ →ᵇ ℝ) (weilLogShiftExponentialEnvelope σ hσ)) u)
  exact continuous_const.add
    (ε • ContinuousLinearMap.mul ℝ (ℕ →ᵇ ℝ) (weilLogShiftExponentialEnvelope σ hσ)).continuous

/-- The linear response of a moment to an exponentially damped error parameter. -/
def weilLogShiftExponentialMomentCLM (ε σ : ℝ) (hσ : 0 ≤ σ) (y : ℝ) (n : ℕ) :
    (ℕ →ᵇ ℝ) →L[ℝ] ℝ :=
  (weilLogShiftRecoveryMomentCLM y n).comp
    (ε • ContinuousLinearMap.mul ℝ (ℕ →ᵇ ℝ) (weilLogShiftExponentialEnvelope σ hσ))

/-- The center contributes only the affine baseline; all error dependence is linear. -/
theorem weilLogShiftExponentialPerturbation_moment (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hσ : 0 ≤ σ) (y : ℝ) (n : ℕ) (u : ℕ →ᵇ ℝ) :
    weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u) n =
      weilLogShiftExponentialMomentCLM ε σ hσ y n u + weilLogShiftRecoveryMoment y center n := by
  have hd := weilLogShiftRecoveryMoment_sub_eq y n
    (weilLogShiftExponentialPerturbation center ε σ hσ u) center
  have heq : weilLogShiftExponentialPerturbation center ε σ hσ u - center =
      ε • (weilLogShiftExponentialEnvelope σ hσ * u) := by
    unfold weilLogShiftExponentialPerturbation
    abel
  rw [heq] at hd
  change weilLogShiftRecoveryMoment y (weilLogShiftExponentialPerturbation center ε σ hσ u) n -
    weilLogShiftRecoveryMoment y center n = weilLogShiftExponentialMomentCLM ε σ hσ y n u at hd
  linarith only [hd]

/-- A coordinate error scales the exact inverse response by its prescribed envelope. -/
theorem weilLogShiftExponentialMomentCLM_unit (ε σ : ℝ) (hσ : 0 ≤ σ) (y : ℝ) (n k : ℕ) :
    weilLogShiftExponentialMomentCLM ε σ hσ y n (weilLogShiftRecoveryUnitHistory k) =
      ε * exp (-(σ * (k + 2 : ℕ))) * weilLogShiftRecoveryMomentResponse y n k := by
  let q := weilLogShiftExponentialEnvelope σ hσ
  have hunit : q * weilLogShiftRecoveryUnitHistory k = q k • weilLogShiftRecoveryUnitHistory k := by
    ext j
    change q j * (if j = k then 1 else 0) = q k * (if j = k then 1 else 0)
    by_cases hj : j = k
    · subst j
      rfl
    · simp only [if_neg hj, mul_zero]
  change weilLogShiftRecoveryMomentCLM y n (ε • (q * weilLogShiftRecoveryUnitHistory k)) = _
  rw [hunit, smul_smul, map_smul, smul_eq_mul]
  rfl

/-- Subcritical exponential precision leaves the origin error-response diagonal divergent. -/
theorem tendsto_weilLogShiftExponentialMomentCLM_diagonal (ε σ : ℝ)
    (hε : 0 < ε) (hσ : 0 ≤ σ) (hrate : σ < 4 - π) :
    Tendsto (fun k => weilLogShiftExponentialMomentCLM ε σ hσ 0 (k + 2)
      (weilLogShiftRecoveryUnitHistory k)) atTop atTop := by
  simpa only [weilLogShiftExponentialMomentCLM_unit, mul_assoc] using
    (tendsto_weilLogShiftRecoveryDiagonal_exp_damped hrate).const_mul_atTop hε

/-- Unit-ball error parameters obey the prescribed pointwise exponential precision. -/
theorem weilLogShiftExponentialPerturbation_bound (center : ℕ →ᵇ ℝ) (ε σ : ℝ)
    (hε : 0 ≤ ε) (hσ : 0 ≤ σ) (u : WeilLogShiftUniformHistoryBall 0 1) (k : ℕ) :
    |weilLogShiftExponentialPerturbation center ε σ hσ u k - center k| ≤
      ε * exp (-(σ * (k + 2 : ℕ))) := by
  have hunorm : ‖(u : ℕ →ᵇ ℝ)‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using u.property
  have hu : |(u : ℕ →ᵇ ℝ) k| ≤ 1 := by
    simpa only [Real.norm_eq_abs] using ((u : ℕ →ᵇ ℝ).norm_coe_le_norm k).trans hunorm
  rw [weilLogShiftExponentialPerturbation_apply, add_sub_cancel_left, abs_mul, abs_mul,
    abs_of_nonneg hε, abs_of_pos (exp_pos _)]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hu (exp_pos _).le) hε

end RHTower
