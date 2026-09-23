import GaloisForLFunctions.RHTower.SoninLogShellChannelGrowth
import GaloisForLFunctions.RHTower.SoninFixedChannelNoFloor
import GaloisForLFunctions.RHTower.ConstrainedProlateOperator

/-!
# On a fixed annulus the channel is bounded, whatever the tower height

The channel is a step multiplier along the geometric tower, so on a vector living inside a fixed
annulus only the finitely many layers meeting that annulus contribute: every layer above the outer
radius acts by the same cutoff on both sides and cancels.  The bound that results depends on the
annulus and the tower ratio, not on the height.

The source packets all live in one fixed annulus — the frequency runs, the support does not — so the
conductor channel's contribution to the packet channel stays bounded even if the tower height is
allowed to grow with the scale.  That closes the logarithmic shell channel as a completion.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter ContinuousLinearMap
open scoped Topology InnerProduct InnerProductSpace

/-- Layers above the outer radius act trivially on a vector supported inside it. -/
theorem evenLogShellChannel_layer_apply_eq_zero
    (a r c : ℝ) (ha : 0 < a) (hr : 1 < r) (k : ℕ) (hk : c ≤ logShellRadius a r k)
    {w : evenSubspace} (hhigh : evenIndicatorCutoff c w = w) :
    (evenIndicatorCutoff (logShellRadius a r (k + 1)) -
      evenIndicatorCutoff (logShellRadius a r k)) w = 0 := by
  have hmono : logShellRadius a r k ≤ logShellRadius a r (k + 1) :=
    (logShellRadius_lt_succ ha hr k).le
  have hfix : ∀ s : ℝ, c ≤ s → evenIndicatorCutoff s w = w := by
    intro s hs
    have hnest := DFunLike.congr_fun (evenIndicatorCutoff_mul_of_le_rev c s hs) w
    rw [mul_apply_eq_comp, hhigh] at hnest
    exact hnest
  rw [sub_apply, hfix _ (hk.trans hmono), hfix _ hk, sub_self]

/-- **Annulus bound.**  On vectors supported inside a fixed outer radius the channel norm is
bounded independently of the tower height. -/
theorem exists_bound_norm_evenLogShellChannel_of_annulus
    (a r c : ℝ) (ha : 0 < a) (hr : 1 < r) (_hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (w : evenSubspace),
      evenIndicatorCutoff c w = w → ‖evenLogShellChannel a r n w‖ ≤ C * ‖w‖ := by
  classical
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt (c / a) hr
  have hcK : c ≤ logShellRadius a r K := by
    have h := (div_lt_iff₀ ha).mp hK
    simpa only [logShellRadius] using h.le
  refine ⟨2 * ∑ k ∈ Finset.range K, |Real.log (logShellRadius a r k)|, by positivity, ?_⟩
  intro n w hhigh
  set g : ℕ → evenSubspace := fun k =>
    ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      ((evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)) w) with hg
  have happly : evenLogShellChannel a r n w = ∑ k ∈ Finset.range n, g k := by
    rw [evenLogShellChannel, sum_apply]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hvanish : ∀ k ∈ Finset.range n, g k ≠ 0 → k < K := by
    intro k _ hne
    by_contra hkK
    push Not at hkK
    have hmono : logShellRadius a r K ≤ logShellRadius a r k :=
      logShellRadius_mono ha hr hkK
    refine hne ?_
    show ((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      ((evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)) w) = 0
    rw [evenLogShellChannel_layer_apply_eq_zero a r c ha hr k (hcK.trans hmono) hhigh, smul_zero]
  have hfilter : ∑ k ∈ (Finset.range n).filter (fun k => k < K), g k =
      ∑ k ∈ Finset.range n, g k :=
    Finset.sum_filter_of_ne hvanish
  have hsub : (Finset.range n).filter (fun k => k < K) ⊆ Finset.range K := by
    intro k hk
    exact Finset.mem_range.mpr (Finset.mem_filter.mp hk).2
  have hterm : ∀ k : ℕ, ‖g k‖ ≤ |Real.log (logShellRadius a r k)| * (2 * ‖w‖) := by
    intro k
    have hcut₁ : ‖evenIndicatorCutoff (logShellRadius a r (k + 1)) w‖ ≤ ‖w‖ :=
      norm_evenIndicatorCutoff_le _ _
    have hcut₂ : ‖evenIndicatorCutoff (logShellRadius a r k) w‖ ≤ ‖w‖ :=
      norm_evenIndicatorCutoff_le _ _
    have hdiff : ‖(evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)) w‖ ≤ 2 * ‖w‖ := by
      rw [sub_apply]
      calc ‖evenIndicatorCutoff (logShellRadius a r (k + 1)) w -
            evenIndicatorCutoff (logShellRadius a r k) w‖
          ≤ ‖evenIndicatorCutoff (logShellRadius a r (k + 1)) w‖ +
            ‖evenIndicatorCutoff (logShellRadius a r k) w‖ := norm_sub_le _ _
        _ ≤ 2 * ‖w‖ := by linarith
    show ‖((Real.log (logShellRadius a r k) : ℝ) : ℂ) •
      ((evenIndicatorCutoff (logShellRadius a r (k + 1)) -
        evenIndicatorCutoff (logShellRadius a r k)) w)‖ ≤
      |Real.log (logShellRadius a r k)| * (2 * ‖w‖)
    simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hdiff (abs_nonneg _)
  calc ‖evenLogShellChannel a r n w‖
      = ‖∑ k ∈ (Finset.range n).filter (fun k => k < K), g k‖ := by rw [hfilter, happly]
    _ ≤ ∑ k ∈ (Finset.range n).filter (fun k => k < K), ‖g k‖ := norm_sum_le _ _
    _ ≤ ∑ k ∈ Finset.range K, ‖g k‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => norm_nonneg _
    _ ≤ ∑ k ∈ Finset.range K, |Real.log (logShellRadius a r k)| * (2 * ‖w‖) :=
        Finset.sum_le_sum fun k _ => hterm k
    _ = (2 * ∑ k ∈ Finset.range K, |Real.log (logShellRadius a r k)|) * ‖w‖ := by
        rw [← Finset.sum_mul]
        ring

/-- **The logarithmic shell channel is closed as a completion.**  Even letting the tower height
grow with the scale, the channel's pairing against the source packets is bounded above, so the
completed packet channel stays unbounded below. -/
theorem not_bddBelow_soninCompletedPacketValueVar_logShellChannelFamily
    (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hab : a < b) (hbc : b < c) (q : ℝ)
    (haq : a < q) (hqb : q < b) (a₀ r₀ : ℝ) (ha₀ : 0 < a₀) (hr₀ : 1 < r₀)
    (height : ℕ → ℕ) :
    ¬ ∃ M : ℝ, ∀ s : Finset ℕ,
        M ≤ soninCompletedPacketValueVar s a b c (soninCrossingClock a c)
          (one_lt_soninCrossingClock a c)
          (fun i => (⟪soninPacketEven b c hb hbc
              (2 * Real.pi * (soninCrossingClock a c i * q)),
            evenLogShellChannel a₀ r₀ (height i) (soninPacketEven b c hb hbc
              (2 * Real.pi * (soninCrossingClock a c i * q)))⟫_ℂ).re) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_norm_evenLogShellChannel_of_annulus a₀ r₀ c ha₀ hr₀
    (hb.trans hbc)
  refine not_bddBelow_soninCompletedPacketValueVar_of_bddAbove a b c ha hb hab hbc q haq hqb
    _ (C * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ)) (fun i => ?_)
  set w : evenSubspace :=
    soninPacketEven b c hb hbc (2 * Real.pi * (soninCrossingClock a c i * q)) with hw
  have hhigh : evenIndicatorCutoff c w = w :=
    evenIndicatorCutoff_soninPacketEven_eq_self b c hb hbc _
  have hbound : ‖w‖ ≤ 2 * ‖soninBumpL2 b c hb hbc‖ :=
    norm_soninPacketL2_le b c hb hbc _
  have hnn : (0 : ℝ) ≤ 2 * ‖soninBumpL2 b c hb hbc‖ := le_trans (norm_nonneg _) hbound
  have hchan : ‖evenLogShellChannel a₀ r₀ (height i) w‖ ≤ C * ‖w‖ := hC (height i) w hhigh
  have hre : (⟪w, evenLogShellChannel a₀ r₀ (height i) w⟫_ℂ).re ≤
      ‖(⟪w, evenLogShellChannel a₀ r₀ (height i) w⟫_ℂ)‖ := Complex.re_le_norm _
  have hinner : ‖(⟪w, evenLogShellChannel a₀ r₀ (height i) w⟫_ℂ)‖ ≤
      ‖w‖ * ‖evenLogShellChannel a₀ r₀ (height i) w‖ := norm_inner_le_norm _ _
  have hstep : ‖w‖ * ‖evenLogShellChannel a₀ r₀ (height i) w‖ ≤ C * ‖w‖ ^ (2 : ℕ) := by
    nlinarith [norm_nonneg w]
  have hsq : ‖w‖ ^ (2 : ℕ) ≤ (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) := by
    have := norm_nonneg w
    nlinarith
  have hfinal : C * ‖w‖ ^ (2 : ℕ) ≤ C * (2 * ‖soninBumpL2 b c hb hbc‖) ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hsq hC0
  linarith

end RHTower
