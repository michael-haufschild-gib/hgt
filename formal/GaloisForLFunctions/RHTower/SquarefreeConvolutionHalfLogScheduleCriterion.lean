import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfCayleyScheduleCeiling
import GaloisForLFunctions.HTGeometry.VitaliConvergence
import Mathlib.Data.Nat.Log

/-!
# Logarithmically rescheduled Cayley--Dirichlet Vitali criterion

Any Cayley-degree schedule tending to infinity preserves compact-open convergence in the Euler
chamber, so local boundedness of its scheduled products still forces `RHLadder 1`.  The explicit
schedule `log_2(N+1)+3` tends to infinity yet stays below the prime-scale divergence obstruction:
its normalized exterior growth is uniformly bounded.

This leaves one concrete source-defined candidate sequence after the same-index and all
superlogarithmic schedules have been retired.  Local boundedness of the logarithmic schedule is
not asserted here.
-/

open Complex Filter Metric Set Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem tendstoLocallyUniformlyOn_comp_index
    {ι κ α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {F : ι → α → β} {f : α → β} {p : Filter ι} {q : Filter κ} {s : Set α}
    (hF : TendstoLocallyUniformlyOn F f p s) {k : κ → ι} (hk : Tendsto k q p) :
    TendstoLocallyUniformlyOn (fun n => F (k n)) f q s := by
  intro u hu x hx
  obtain ⟨t, ht, hF⟩ := hF u hu x hx
  exact ⟨t, ht, hk.eventually hF⟩

private theorem tendstoLocallyUniformlyOn_const_schedule
    {ι α β : Type*} [TopologicalSpace α] [UniformSpace β]
    {p : Filter ι} {s : Set α} (g : α → β) :
    TendstoLocallyUniformlyOn (fun _ : ι => g) g p s := by
  intro u hu x hx
  exact ⟨s, self_mem_nhdsWithin, Eventually.of_forall fun _ y _ =>
    refl_mem_uniformity hu⟩

theorem analyticOnNhd_poleClearedFirstTraceScheduledApprox_rightHalf
    (kappa : ℕ → ℕ) (N : ℕ) :
    AnalyticOnNhd ℂ (poleClearedFirstTraceScheduledApprox kappa N) rightHalf := by
  exact (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa N)).mul
    ((analyticOnNhd_squarefreeHalfDirichletPartialSum N).mono (Set.subset_univ _)) |>.div
      analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf
      (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)

theorem tendstoLocallyUniformlyOn_poleClearedFirstTraceScheduledApprox
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop) :
    TendstoLocallyUniformlyOn (poleClearedFirstTraceScheduledApprox kappa)
      poleClearedFirstTraceSourceLimit atTop farHalf := by
  have hr := tendstoLocallyUniformlyOn_comp_index
    tendstoLocallyUniformlyOn_poleFactorSqrtApprox hkappa
  have hrcont : ContinuousOn poleFactorSqrtCayleyLimit farHalf :=
    hr.continuousOn (Frequently.of_forall fun n =>
      (analyticOnNhd_poleFactorSqrtApprox_rightHalf (kappa n)).continuousOn.mono
        farHalf_subset_rightHalf)
  have hLcont : ContinuousOn (LSeries squarefreeConvolutionHalf) farHalf :=
    analyticOnNhd_LSeries_squarefreeConvolutionHalf.continuousOn
  have hdencont : ContinuousOn squarefreeCarlemanHalfDet farHalf :=
    analyticOnNhd_squarefreeCarlemanHalfDet_rightHalf.continuousOn.mono
      farHalf_subset_rightHalf
  have hnum := hr.mul₀
    tendstoLocallyUniformlyOn_squarefreeConvolutionHalf_partialSums hrcont hLcont
  have hden : TendstoLocallyUniformlyOn
      (fun _ : ℕ => squarefreeCarlemanHalfDet) squarefreeCarlemanHalfDet atTop farHalf :=
    tendstoLocallyUniformlyOn_const_schedule squarefreeCarlemanHalfDet
  have hdiv := hnum.div₀ hden (hrcont.mul hLcont) hdencont
    (fun s _ => squarefreeCarlemanHalfDet_ne_zero s)
  convert hdiv using 1
  · ext N s
    rfl
  · ext s
    rfl

/-- Local boundedness of a rescheduled Cayley--Dirichlet approximation sequence. -/
def PoleClearedFirstTraceScheduledLocallyBounded (kappa : ℕ → ℕ) : Prop :=
  ∀ z ∈ rightHalf, ∃ R : ℝ, 0 < R ∧ ball z R ⊆ rightHalf ∧ ∃ C : ℝ,
    ∀ N, ∀ w ∈ ball z R,
      ‖poleClearedFirstTraceScheduledApprox kappa N w‖ ≤ C

theorem rhLadder_one_of_poleClearedFirstTraceScheduledLocallyBounded
    {kappa : ℕ → ℕ} (hkappa : Tendsto kappa atTop atTop)
    (hloc : PoleClearedFirstTraceScheduledLocallyBounded kappa) : RHLadder 1 := by
  obtain ⟨G, hGdiff, hGlim⟩ :=
    vitali_tendstoLocallyUniformlyOn_of_isPreconnected
      convex_rightHalf.isPreconnected
      (fun N =>
        (analyticOnNhd_poleClearedFirstTraceScheduledApprox_rightHalf kappa N).differentiableOn)
      hloc
      (farHalf_subset_rightHalf two_mem_farHalf)
      (Filter.Eventually.frequently
        (Filter.Eventually.filter_mono nhdsWithin_le_nhds
          (isOpen_farHalf.mem_nhds two_mem_farHalf)))
      (fun s hs => ⟨poleClearedFirstTraceSourceLimit s,
        (tendstoLocallyUniformlyOn_poleClearedFirstTraceScheduledApprox hkappa).tendsto_at hs⟩)
  rw [rhLadder_one_iff_poleClearedFirstTrace_sqrt]
  refine ⟨G, hGdiff.analyticOnNhd isOpen_rightHalf, ?_⟩
  have hGeq : EqOn G poleClearedFirstTraceSourceLimit farHalf := by
    intro s hs
    exact tendsto_nhds_unique
      (hGlim.tendsto_at (farHalf_subset_rightHalf hs))
      ((tendstoLocallyUniformlyOn_poleClearedFirstTraceScheduledApprox hkappa).tendsto_at hs)
  let H : ℂ → ℂ := fun s => G s ^ (2 : ℕ) - poleClearedFirstTraceExponentialContinuation s
  have hHana : AnalyticOnNhd ℂ H rightHalf :=
    ((hGdiff.analyticOnNhd isOpen_rightHalf).pow 2).sub
      analyticOnNhd_poleClearedFirstTraceExponentialContinuation_rightHalf
  have hfreq : ∃ᶠ s in 𝓝[≠] (2 : ℂ), H s = 0 := by
    have hmem : ∀ᶠ s in 𝓝 (2 : ℂ), s ∈ farHalf := isOpen_farHalf.mem_nhds two_mem_farHalf
    have hzero : ∀ᶠ s in 𝓝 (2 : ℂ), H s = 0 := hmem.mono fun s hs => by
      dsimp [H]
      rw [hGeq hs, poleClearedFirstTraceSourceLimit_sq hs, sub_self]
    exact (Filter.Eventually.filter_mono nhdsWithin_le_nhds hzero).frequently
  have hHall := hHana.eqOn_zero_of_preconnected_of_frequently_eq_zero
    convex_rightHalf.isPreconnected (farHalf_subset_rightHalf two_mem_farHalf) hfreq
  intro s hs
  have hzero := hHall hs
  change G s ^ (2 : ℕ) - poleClearedFirstTraceExponentialContinuation s = 0 at hzero
  exact sub_eq_zero.mp hzero

/-- Explicit logarithmic Cayley degree, offset so every degree is at least three. -/
def logarithmicCayleySchedule (N : ℕ) : ℕ := Nat.log 2 (N + 1) + 3

theorem logarithmicCayleySchedule_ge_three (N : ℕ) :
    3 ≤ logarithmicCayleySchedule N := by
  simp [logarithmicCayleySchedule]

theorem tendsto_logarithmicCayleySchedule_atTop :
    Tendsto logarithmicCayleySchedule atTop atTop := by
  rw [Filter.tendsto_atTop_atTop]
  intro b
  refine ⟨2 ^ b, fun N hN => ?_⟩
  have hpow : 2 ^ b ≤ N + 1 := hN.trans (Nat.le_add_right N 1)
  have hblog : b ≤ Nat.log 2 (N + 1) := Nat.le_log_of_pow_le (by norm_num) hpow
  exact hblog.trans (Nat.le_add_right _ 3)

theorem logarithmicCayleySchedule_primeScale_le_eight
    {N : ℕ} (hN : 1 ≤ N) :
    (5 / 4 : ℝ) ^
        min (logarithmicCayleySchedule N - 1)
          (logarithmicCayleySchedule (N + 1) - 1) / N ≤ 8 := by
  let e : ℕ := min (logarithmicCayleySchedule N - 1)
    (logarithmicCayleySchedule (N + 1) - 1)
  have he : e ≤ Nat.log 2 (N + 1) + 2 := by
    calc
      e ≤ logarithmicCayleySchedule N - 1 := min_le_left _ _
      _ = Nat.log 2 (N + 1) + 2 := by simp [logarithmicCayleySchedule]
  have hdegree : (5 / 4 : ℝ) ^ e ≤ (5 / 4 : ℝ) ^ (Nat.log 2 (N + 1) + 2) :=
    pow_le_pow_right₀ (by norm_num) he
  have hbase :
      (5 / 4 : ℝ) ^ (Nat.log 2 (N + 1) + 2) ≤
        (2 : ℝ) ^ (Nat.log 2 (N + 1) + 2) :=
    pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have hnat : 2 ^ Nat.log 2 (N + 1) ≤ N + 1 :=
    Nat.pow_log_le_self 2 (by omega)
  have hnatReal : (2 : ℝ) ^ Nat.log 2 (N + 1) ≤ N + 1 := by
    exact_mod_cast hnat
  have hnum : (5 / 4 : ℝ) ^ e ≤ 4 * (N + 1) := by
    calc
      (5 / 4 : ℝ) ^ e ≤ (5 / 4 : ℝ) ^ (Nat.log 2 (N + 1) + 2) := hdegree
      _ ≤ (2 : ℝ) ^ (Nat.log 2 (N + 1) + 2) := hbase
      _ = 4 * (2 : ℝ) ^ Nat.log 2 (N + 1) := by rw [pow_add]; norm_num; ring
      _ ≤ 4 * (N + 1) := mul_le_mul_of_nonneg_left hnatReal (by norm_num)
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hmul : (5 / 4 : ℝ) ^ e ≤ 8 * N := by
    calc
      (5 / 4 : ℝ) ^ e ≤ 4 * (N + 1) := hnum
      _ ≤ 8 * N := by nlinarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  change (5 / 4 : ℝ) ^ e / N ≤ 8
  exact (div_le_iff₀ hNpos).2 (by nlinarith)

theorem not_logarithmicCayleySchedule_primeScaleDiverges :
    ¬ CayleySchedulePrimeScaleDiverges logarithmicCayleySchedule := by
  intro hdiv
  have heventually : ∀ᶠ N : ℕ in atTop,
      8 < (5 / 4 : ℝ) ^
        min (logarithmicCayleySchedule N - 1)
          (logarithmicCayleySchedule (N + 1) - 1) / N :=
    hdiv.eventually_gt_atTop 8
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp heventually
  let N := max N₀ 1
  have hlarge := hN₀ N (le_max_left _ _)
  have hsmall := logarithmicCayleySchedule_primeScale_le_eight
    (N := N) (le_max_right _ _)
  exact (not_lt_of_ge hsmall) hlarge

theorem rhLadder_one_of_logarithmicCayleySchedule_locallyBounded
    (hloc : PoleClearedFirstTraceScheduledLocallyBounded logarithmicCayleySchedule) :
    RHLadder 1 :=
  rhLadder_one_of_poleClearedFirstTraceScheduledLocallyBounded
    tendsto_logarithmicCayleySchedule_atTop hloc

end

end RHTower
