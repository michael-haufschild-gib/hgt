import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw
import GaloisForLFunctions.ExclusionOfTheCriticalState.TheStateChangesSignOnEveryRay

/-!
# The state has a last zero before the wall

Let `Φ` be the continuous representative of the critical state and `s` the sign of the wall.

* **Nodal set** (`criticalState_nodal_structure`). The state changes sign on every left ray
  (`criticalState_not_eventually_signed`), so by continuity `Φ` takes both strict signs and has a zero
  left of every point: its zero set is unbounded below. Next to the wall `sΦ > 0`, so the zeros stay
  away from the wall, and there is a **last zero** `u₁ < 0`: `Φ(u₁) = 0` and `sΦ > 0` on `(u₁, 0)`
  (the largest point of a compact zero set; between it and the wall the intermediate value theorem
  forbids a sign change).
* **The modulus at the wall is sharp** (`criticalState_not_holder_at_wall`). No bound
  `|Φ(−t)| ≤ C t^α`, `α > 0`, holds near the wall: `|Φ(−t)| √log(1/t)` tends to `√(8aM) > 0` while
  `t^α √log(1/t) → 0`. The state is continuous with modulus exactly `(log 1/t)^{−1/2}` at the wall and
  is not Hölder continuous there.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations _root_.RHTower

/-- A continuous representative takes the sign `σ` strictly somewhere left of every point. -/
private theorem exists_lt_neg_sign {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {Φ : ℝ → ℝ}
    (hFΦ : F =ᵐ[volume] Φ) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (T : ℝ) :
    ∃ v, v < -T ∧ σ * Φ v < 0 := by
  by_contra h
  push Not at h
  apply criticalState_not_eventually_signed hW hthreshold hF hσ T
  rw [ae_restrict_iff' measurableSet_Iio]
  filter_upwards [hFΦ] with u hu hlt
  rw [hu]
  exact h u hlt

/-- **The nodal structure of the state.** The continuous representative has zeros left of every
point, and a last zero `u₁ < 0` before the wall, with `sΦ > 0` on `(u₁, 0)`. -/
theorem criticalState_nodal_structure {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) :
    ∃ s : ℝ, (s = 1 ∨ s = -1) ∧ ∃ Φ : ℝ → ℝ, Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ T : ℝ, ∃ u, u < -T ∧ Φ u = 0) ∧
      ∃ u₁ : ℝ, u₁ < 0 ∧ Φ u₁ = 0 ∧ ∀ u ∈ Ioo u₁ 0, 0 < s * Φ u := by
  obtain ⟨s, hs, Φ, hcont, hFΦ, -, -, -, -, k₀, hk₀, hsign⟩ :=
    criticalState_exists_continuous_representative hW hthreshold hF
  have hs0 : s ≠ 0 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hns : -s = 1 ∨ -s = -1 := by rcases hs with h | h <;> rw [h] <;> norm_num
  have hg : Continuous fun u => s * Φ u := continuous_const.mul hcont
  -- a zero between a nonpositive and a nonnegative value of `sΦ`
  have hivt : ∀ a b : ℝ, a ≤ b → s * Φ a ≤ 0 → 0 ≤ s * Φ b → ∃ u ∈ Icc a b, Φ u = 0 := by
    intro a b hab ha hb
    obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc hab hg.continuousOn ⟨ha, hb⟩
    exact ⟨u, hu, by simpa [hs0] using hu0⟩
  -- zeros left of every point
  have hzeros : ∀ T : ℝ, ∃ u, u < -T ∧ Φ u = 0 := by
    intro T
    obtain ⟨v, hv, hvs⟩ := exists_lt_neg_sign hW hthreshold hF hFΦ hs T
    obtain ⟨w, hw, hws⟩ := exists_lt_neg_sign hW hthreshold hF hFΦ hns T
    have hws' : 0 < s * Φ w := by linarith
    rcases le_total v w with hvw | hwv
    · obtain ⟨u, hu, hu0⟩ := hivt v w hvw hvs.le hws'.le
      exact ⟨u, lt_of_le_of_lt hu.2 hw, hu0⟩
    · obtain ⟨u, hu, hu0⟩ := intermediate_value_Icc' hwv hg.continuousOn ⟨hvs.le, hws'.le⟩
      exact ⟨u, lt_of_le_of_lt hu.2 hv, by simpa [hs0] using hu0⟩
  refine ⟨s, hs, Φ, hcont, hFΦ, hzeros, ?_⟩
  -- the last zero
  obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = -(k₀ / 2) := ⟨_, rfl⟩
  have hb0 : b < 0 := by rw [hbdef]; linarith
  have hbpos : 0 < s * Φ b := by
    have := hsign (k₀ / 2) ⟨by linarith, by linarith⟩
    rwa [← hbdef] at this
  obtain ⟨v, hv, hvs⟩ := exists_lt_neg_sign hW hthreshold hF hFΦ hs (k₀ / 2)
  have hZc : IsCompact (Icc v b ∩ Φ ⁻¹' {0}) :=
    isCompact_Icc.inter_right (isClosed_singleton.preimage hcont)
  obtain ⟨z, hzI, hz0⟩ := hivt v b (by rw [hbdef]; linarith) hvs.le hbpos.le
  obtain ⟨u₁, hu₁Z, hu₁max⟩ := hZc.exists_isGreatest ⟨z, hzI, hz0⟩
  have hu₁b : u₁ ≤ b := hu₁Z.1.2
  refine ⟨u₁, lt_of_le_of_lt hu₁b hb0, hu₁Z.2, fun u hu => ?_⟩
  by_cases hk : -k₀ < u
  · have := hsign (-u) ⟨by linarith [hu.2], by linarith⟩
    rwa [neg_neg] at this
  · push Not at hk
    have hub : u < b := by rw [hbdef]; linarith
    by_contra hneg
    push Not at hneg
    obtain ⟨w, hw, hw0⟩ := hivt u b hub.le hneg hbpos.le
    have hwZ : w ∈ Icc v b ∩ Φ ⁻¹' {0} :=
      ⟨⟨by linarith [hu.1, hu₁Z.1.1, hw.1], hw.2⟩, hw0⟩
    have := hu₁max hwZ
    linarith [hu.1, hw.1]

/-- **The modulus of the state at the wall is sharp.** No Hölder bound `|Φ(−t)| ≤ C t^α` with
`α > 0` holds near the wall. -/
theorem criticalState_not_holder_at_wall {W₀ : ℝ} (hW : 0 < W₀)
    (hthreshold : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {F : ℝ → ℝ} (hF : IsCriticalHalfLineGroundState W₀ F) {Φ : ℝ → ℝ} (hcont : Continuous Φ)
    (hFΦ : F =ᵐ[volume] Φ) {C α δ : ℝ} (hα : 0 < α) (hδ : 0 < δ) :
    ¬ ∀ t ∈ Ioo 0 δ, |Φ (-t)| ≤ C * t ^ α := by
  intro hhol
  obtain ⟨s, hs, Ψ, hΨc, hFΨ, -, -, hlaw, -, -⟩ :=
    criticalState_exists_continuous_representative hW hthreshold hF
  -- two continuous representatives agree
  have hΦΨ : Φ = Ψ := (Continuous.ae_eq_iff_eq volume hcont hΨc).mp (hFΦ.symm.trans hFΨ)
  subst hΦΨ
  have hQ : 0 < 8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u)) :=
    mul_pos (mul_pos (by norm_num) (criticalAliasCoefficient_positive hW))
      (criticalState_exponentialMass_pos hW hF)
  obtain ⟨c, hcdef⟩ : ∃ c : ℝ,
      c = Real.sqrt (8 * criticalAliasCoefficient W₀ * ∫ u : ℝ, F u ^ 2 * Real.exp (-(8 * u))) :=
    ⟨_, rfl⟩
  have hc : 0 < c := by rw [hcdef]; exact Real.sqrt_pos.mpr hQ
  rw [← hcdef] at hlaw
  have habs : Tendsto (fun t : ℝ => |Φ (-t) * Real.sqrt (Real.log (1 / t))|) (𝓝[>] 0) (𝓝 c) := by
    have := (continuous_abs.tendsto _).comp hlaw
    have hsc : |s * c| = c := by
      rw [abs_mul, abs_of_pos hc]; rcases hs with h | h <;> rw [h] <;> norm_num
    rwa [hsc] at this
  -- `t^α √log(1/t) → 0`
  have hsmall : Tendsto (fun t : ℝ => t ^ α * Real.sqrt (Real.log (1 / t))) (𝓝[>] 0) (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => Real.log t * t ^ (2 * α)) (𝓝[>] 0) (𝓝 0) :=
      tendsto_log_mul_rpow_nhdsGT_zero (by linarith)
    have h1' := h1.neg
    rw [neg_zero] at h1'
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1'
    rw [Real.sqrt_zero] at h2
    refine h2.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht0 : (0 : ℝ) < t := ht
    show Real.sqrt (-(Real.log t * t ^ (2 * α))) = t ^ α * Real.sqrt (Real.log (1 / t))
    rw [one_div, Real.log_inv, show -(Real.log t * t ^ (2 * α)) = (t ^ α) ^ 2 * -Real.log t by
      rw [← Real.rpow_natCast, ← Real.rpow_mul ht0.le]; push_cast; ring_nf,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Real.rpow_nonneg ht0.le _)]
  have hev1 := habs.eventually (lt_mem_nhds (half_lt_self hc))
  have hev2 := (hsmall.const_mul C).eventually (gt_mem_nhds (show C * 0 < c / 2 by
    rw [mul_zero]; linarith))
  have hev3 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Ioo 0 (min δ 1) :=
    mem_nhdsGT_iff_exists_Ioo_subset.mpr
      ⟨min δ 1, Set.mem_Ioi.mpr (lt_min hδ one_pos), subset_rfl⟩
  obtain ⟨t, h1, h2, h3⟩ := (hev1.and (hev2.and hev3)).exists
  have htδ : t ∈ Ioo 0 δ := ⟨h3.1, h3.2.trans_le (min_le_left _ _)⟩
  have hlog : 0 ≤ Real.sqrt (Real.log (1 / t)) := Real.sqrt_nonneg _
  have hb := mul_le_mul_of_nonneg_right (hhol t htδ) hlog
  rw [abs_mul, abs_of_nonneg hlog] at h1
  nlinarith

end GaloisForLFunctions.ExclusionOfTheCriticalState
