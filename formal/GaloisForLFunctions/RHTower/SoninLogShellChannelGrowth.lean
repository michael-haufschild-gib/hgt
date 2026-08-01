import GaloisForLFunctions.RHTower.SoninBurnolLogShellChannel

/-!
# The logarithmic shell channel grows with the tower

On the unit vector of the `k`-th layer the channel acts by `log(rᵏa)`, so its operator norm is at
least that logarithm for every layer below the tower height.  Since the layer radii grow
geometrically, the channel norms diverge with the height.

This is what keeps the surviving completion class inhabited: the no-go results rule out bounded
contributions and fixed channels, and the corpus's own conductor channel is a family whose norms do
grow without bound.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology

/-- The logarithm of a tower radius. -/
theorem log_logShellRadius (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ) :
    Real.log (logShellRadius a r k) = k * Real.log r + Real.log a := by
  have hr0 : (0 : ℝ) < r := zero_lt_one.trans hr
  rw [logShellRadius, Real.log_mul (by positivity) ha.ne', Real.log_pow]

/-- **The channel norm sees every layer below the height.** -/
theorem le_norm_evenLogShellChannel (a r : ℝ) (ha : 0 < a) (hr : 1 < r) (n k : ℕ) (hk : k < n) :
    |Real.log (logShellRadius a r k)| ≤ ‖evenLogShellChannel a r n‖ := by
  have haction := evenLogShellChannel_apply_logShellUnit a r ha hr n k hk
  have hle : ‖evenLogShellChannel a r n (logShellUnit a r ha hr k)‖ ≤
      ‖evenLogShellChannel a r n‖ * ‖logShellUnit a r ha hr k‖ :=
    ContinuousLinearMap.le_opNorm _ _
  rw [haction, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    norm_logShellUnit a r ha hr k, mul_one, mul_one] at hle
  exact hle

/-- **The channel norms diverge with the tower height.** -/
theorem tendsto_norm_evenLogShellChannel_atTop (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    Tendsto (fun n => ‖evenLogShellChannel a r n‖) atTop atTop := by
  have hlogr : 0 < Real.log r := Real.log_pos hr
  refine tendsto_atTop.mpr fun M => ?_
  obtain ⟨K, hK⟩ := exists_nat_gt ((M - Real.log a) / Real.log r)
  have hKbound : M ≤ (K : ℝ) * Real.log r + Real.log a := by
    have h := (div_lt_iff₀ hlogr).mp hK
    linarith
  refine eventually_atTop.mpr ⟨K + 1, fun n hn => ?_⟩
  have hk : K < n := lt_of_lt_of_le (Nat.lt_succ_self K) hn
  have hbound := le_norm_evenLogShellChannel a r ha hr n K hk
  have hval : Real.log (logShellRadius a r K) = (K : ℝ) * Real.log r + Real.log a :=
    log_logShellRadius a r ha hr K
  have hself : Real.log (logShellRadius a r K) ≤ |Real.log (logShellRadius a r K)| :=
    le_abs_self _
  rw [hval] at hself hbound
  linarith

/-- **The surviving completion class is inhabited.**  There is a family of channels whose norms
grow without bound: the corpus's own logarithmic shell tower. -/
theorem exists_norm_atTop_channel_family (a r : ℝ) (ha : 0 < a) (hr : 1 < r) :
    ∃ T : ℕ → (evenSubspace →L[ℂ] evenSubspace),
      (∀ n, ContinuousLinearMap.adjoint (T n) = T n) ∧
        Tendsto (fun n => ‖T n‖) atTop atTop :=
  ⟨fun n => evenLogShellChannel a r n, fun n => adjoint_evenLogShellChannel a r n,
    tendsto_norm_evenLogShellChannel_atTop a r ha hr⟩

end RHTower
