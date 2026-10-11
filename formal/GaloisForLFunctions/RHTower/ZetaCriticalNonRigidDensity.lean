import GaloisForLFunctions.RHTower.ZetaCriticalAsymptotics

/-!
# Non-rigid heights have positive density

Call a height `t` *non-rigid* (at scale `h`, radius `8τ`) if some ordered ordinate `γ_k` with
`|γ_k − t| ≤ 8τ` is not `h`-rigid.

**Theorem** (`eventually_volume_nonRigidHeights_gt`). Assume RH. For all large `T`, with
`L = log T`, the heights `t ∈ [3T^{1/2} + 1/2, T − 1/2]` that are non-rigid at scale `10⁶⁰/L` and
radius `8 · 32 · 10¹³/L` have measure `> 10⁻¹⁷ T`.

**Proof.** Rerun the critical-scale anti-crystal argument with rigidity only off the non-rigid
set `N`. The box partition puts `N` into the bad set, at cost `48 · 10¹³ |N| L`
(`sum_norm_critRow_interior_le_of_rigidOff`). If `|N| ≤ 10⁻¹⁷ T`, this is `≤ TL/200`, and
`false_of_critical_bounds` applies. Under RH the bulk zeros are on the line and the explicit-formula
bound holds at every height.
-/

noncomputable section

open Complex Filter Topology Set MeasureTheory

namespace RHTower

/-- The heights near which some ordered ordinate is not `h`-rigid. -/
def nonRigidHeights (h τ : ℝ) : Set ℝ :=
  {t | ∃ k, |xiOrderedPositiveOrdinate k - t| ≤ 8 * τ ∧ ¬ RigidAt h k}

/-- **Under RH, non-rigid heights at the critical scale have positive density.** -/
theorem eventually_volume_nonRigidHeights_gt (hRH : RiemannHypothesis) :
    ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (T / 10 ^ 17) <
      volume (Icc (3 * T ^ (1 / 2 : ℝ) + 1 / 2) (T - 1 / 2) ∩
        nonRigidHeights (10 ^ 60 / Real.log T) (32 * 10 ^ 13 / Real.log T)) := by
  have hzero : ∀ q : XiZeroCopy, (q.1 : ℂ).re = 1 / 2 := fun q =>
    riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH _ (xi_xiZeroCopy_eq_zero q)
  filter_upwards [Real.tendsto_log_atTop.eventually_ge_atTop (10 ^ 25),
    eventually_ge_atTop (2 : ℝ), eventually_narrowMass_bound, eventually_lorentzMassW_le,
    eventually_selbergLength_le,
    eventually_re_averagedMontgomeryForm_ge (α₀ := 1 / 8) (R := 16) (ε := 1 / 2) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num),
    eventually_lowPairs_le, eventually_edges_le, eventually_card_zeroWindow_le]
    with T hL hT2 hV hW hlen hM hlow hedge hcount
  by_contra hcon
  push Not at hcon
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := lt_of_lt_of_le (by norm_num) hL
  have hx1 : 1 < T ^ (1 / 20 : ℝ) := Real.one_lt_rpow (by linarith) (by norm_num)
  have hlx : Real.log (T ^ (1 / 20 : ℝ)) = Real.log T / 20 := by
    rw [Real.log_rpow hT0]; ring
  have hV' := hV fun q _ _ => hzero q
  have hint := sum_norm_critRow_interior_le_of_rigidOff (T := T) (x := T ^ (1 / 20 : ℝ))
    (ν := T / 10 ^ 17) (by linarith) hL hx1 hlx hV' hW (by positivity) hcon
    (fun t ht htN k hk => by
      by_contra hk'
      exact htN ⟨ht, k, hk, hk'⟩) hlen
  have hE₀ : 48 * 10 ^ 13 * (T / 10 ^ 17) * Real.log T ≤ T * Real.log T / 200 := by
    have : 48 * 10 ^ 13 * (T / 10 ^ 17) * Real.log T = (48 / 10 ^ 4) * (T * Real.log T) := by
      ring
    rw [this]
    have hTL : 0 < T * Real.log T := by positivity
    nlinarith
  exact false_of_critical_bounds (by linarith) hL hM hlow hedge hcount
    (fun n _ => hzero _) hE₀ hint

end RHTower
