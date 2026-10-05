import GaloisForLFunctions.RHTower.LiEvenCrossActualClockScoreBudget
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockLogHistoryAnalytic
import GaloisForLFunctions.RHTower.LiEvenCrossActualClockDampedCutoffEscape

/-!
# Finite guarded zeros of the log history and the terminal-history laws

`D(t) = ∫₀ᵗ P(s)/s ds` is the undamped (`a = 0`) cutoff.  Under RH it is positive at every
positive clock; otherwise it escapes to `-∞` along a clock sequence with the exact integrated
top-packet coefficient.  Since `D` is real analytic with isolated zeros, the guarded-zero set
`Z = {t > 20 : D(t) = 0, D ≥ 0 on [0,t]}` is finite, empty iff RH, and under not-RH it consists
of even-order tangencies followed by its largest element `τ = inf{s > 0 : D(s) < 0}`, a crossing
of odd order.  Every eventually-guarded statement therefore holds vacuously, and no cofinal
guarded sequence exists.

On the normalized outer history, the lag density `h_t(r) = (t-r)D(t-r)U(r)/I_U` has
`h_t(0) = 0`, `h_t'(0) = -P(t)U(0)/I_U ≥ 0` with `U(0) = 17/2`, and
`ρ_t - β_t = 303A_near/I_U + (606/17)h_t'(0)`.  The relative terminal mass at the adaptive
cutoff for `a ≤ ηβ_t` exceeds `(1-η)/θ`; cutoffs for vanishing thresholds escape to infinity;
and at each fixed guarded zero of order `k` the terminal mass has the endpoint law
`Π_t(t-s < R) = tU(0)c_tR^{k+1}/((k+1)I_U) + O(R^{k+2})`.
-/

open MeasureTheory Set Filter Topology Asymptotics
namespace RHTower
noncomputable section
local notation "K" => deriv liEvenCrossActualClockBorelKernel
local notation "K1" => deriv (deriv liEvenCrossActualClockBorelKernel)
local notation "P" => liEvenCrossActualClockPrimitive
local notation "D" => liEvenCrossActualClockLogHistory
local notation "Dens" => liEvenCrossActualClockLogHistoryDensity
local notation "ell" => liEvenCrossActualClockHistoryScale
local notation "Cout" => liEvenCrossActualClockHistoryOutsideCorrelation
local notation "U" => liClockThetaScoreCostProfile
local notation "IU" => liEvenCrossActualClockScoreCostIntegral
local notation "IK" => liEvenCrossActualClockScoreKernelIntegral
local notation "V" => liEvenCrossActualClockScoreHistoryBudget
local notation "Anear" => liEvenCrossActualClockHistoryNearReserve
local notation "zeta" => liEvenCrossActualClockHistoryEarlyReserve
local notation "thc" => liClockThetaScoreCeiling
local notation "aS" => liClockThetaScoreSlopeRatio
local notation "Pi" => liEvenCrossActualClockOuterHistoryMeasure
local notation "rho" => liEvenCrossActualClockOuterScoreRatio
local notation "beta" => liEvenCrossActualClockOuterBudgetRatio
local notation "bmax" => liEvenCrossActualClockMaxGrowthRate
local notation "uq" => liEvenCrossActualClockReciprocalFrequency
local notation "vq" => liEvenCrossActualClockReciprocalGrowthRate

/-- The undamped cutoff is the log history. -/
theorem liEvenCrossActualClockDampedCutoff_zero_eq_logHistory :
    liEvenCrossActualClockDampedCutoff 0 = D := by
  funext T
  simp only [liEvenCrossActualClockDampedCutoff, liEvenCrossActualClockLogHistory,
    liEvenCrossActualClockLogHistoryDensity, neg_zero, zero_mul, Real.exp_zero, one_mul]

/-- **(T13)**  Under RH the history is positive at every positive clock. -/
theorem liEvenCrossActualClockLogHistory_pos_of_rh (hRH : RiemannHypothesis) {t : ℝ}
    (ht : 0 < t) : 0 < D t := by
  rw [← liEvenCrossActualClockDampedCutoff_zero_eq_logHistory]
  exact liEvenCrossActualClockDampedCutoff_pos_of_rh hRH 0 ht

/-- **(T14)**  If RH fails, the top rate `b ∈ (0, 1/300)` is attained on a finite nonempty
packet `S` with a strict gap below it, and along clocks `T_n ≥ n+1`,
`T_n e^{-bT_n} D(T_n) → -½ ∑_{q∈S} b/(b² + u_q²) < 0`, so `D(T_n) → -∞`. -/
theorem exists_liEvenCrossActualClockLogHistory_negative_escape_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    0 < bmax ∧ bmax < 1/300 ∧ ∃ S : Finset XiZeroCopy, S.Nonempty ∧
      (∀ q, q ∈ S ↔ vq q = bmax) ∧ (∃ b₂ : ℝ, 0 ≤ b₂ ∧ b₂ < bmax ∧ ∀ q, q ∉ S → vq q ≤ b₂) ∧
      ∃ T : ℕ → ℝ, (∀ n : ℕ, (n:ℝ) + 1 ≤ T n) ∧ Tendsto T atTop atTop ∧
        Tendsto (fun n => T n * Real.exp (-(bmax * T n)) * D (T n)) atTop
          (𝓝 (-(1/2) * ∑ q ∈ S, bmax/(bmax^2 + uq q^2))) ∧
        -(1/2) * ∑ q ∈ S, bmax/(bmax^2 + uq q^2) < 0 ∧
        Tendsto (fun n => D (T n)) atTop atBot := by
  obtain ⟨hβ, -, -, b₂, hb₂, hb₂β, hgap⟩ := liEvenCrossActualClockMaxGrowthRate_top_of_not_rh hnot
  obtain ⟨S, hSne, hS, T, hT1, hT, hlim, hneg, hbot⟩ :=
    liEvenCrossActualClockDampedCutoff_escape_of_not_rh hnot (a := 0) hβ
  simp only [liEvenCrossActualClockDampedCutoff_zero_eq_logHistory, sub_zero] at hlim hneg hbot
  refine ⟨hβ, liEvenCrossActualClockMaxGrowthRate_lt, S, hSne, hS,
    ⟨b₂, hb₂, hb₂β, fun q hq => hgap q fun h => hq ((hS q).2 h)⟩, T, hT1, hT, hlim, hneg, hbot⟩

private theorem th_D_cont : Continuous D :=
  continuous_iff_continuousAt.mpr fun t =>
    (hasDerivAt_liEvenCrossActualClockLogHistory t).continuousAt

private theorem th_D_early_pos {t : ℝ} (ht : 0 < t) (ht20 : t ≤ 20) : 0 < D t := by
  have h := (liEvenCrossActualClockLogHistory_local_corridor ht.le ht20).2.2
  have hA := xiShiftAbsoluteMass_pos 0
  have : 0 < (1051/2184 : ℝ)*xiShiftAbsoluteMass 0*t^2/4 := by positivity
  linarith

private theorem th_exists_neg (hnot : ¬RiemannHypothesis) : ∃ T, 20 < T ∧ D T < 0 := by
  obtain ⟨-, -, S, -, -, -, T, hT1, -, -, -, hbot⟩ :=
    exists_liEvenCrossActualClockLogHistory_negative_escape_of_not_rh hnot
  obtain ⟨n, hn⟩ := (hbot.eventually (eventually_lt_atBot 0)).exists
  refine ⟨T n, ?_, hn⟩
  by_contra h
  push Not at h
  have : 0 < T n := by linarith [hT1 n, (Nat.cast_nonneg n : (0:ℝ) ≤ n)]
  linarith [th_D_early_pos this h]

/-- The guarded-zero set `{t > 20 : D(t) = 0, D ≥ 0 on [0,t]}`. -/
def liEvenCrossActualClockGuardedZeroSet : Set ℝ :=
  {t | 20 < t ∧ D t = 0 ∧ ∀ s ∈ Icc 0 t, 0 ≤ D s}

local notation "ZS" => liEvenCrossActualClockGuardedZeroSet

/-- **(T15), ordered form.**  If RH fails, `τ = inf{s > 0 : D(s) < 0}` is the largest guarded
zero; it is a crossing of odd order (`D > 0` just before, `D < 0` just after), and every other
guarded zero is a tangency of even order `≥ 2`. -/
theorem liEvenCrossActualClockGuardedZeroSet_ordered_of_not_rh (hnot : ¬RiemannHypothesis) :
    ∃ τ : ℝ, τ ∈ ZS ∧ τ = sInf {s : ℝ | 0 < s ∧ D s < 0} ∧ (∀ t ∈ ZS, t ≤ τ) ∧
      Odd (analyticOrderNatAt D τ) ∧
      (∀ t ∈ ZS, t < τ → 2 ≤ analyticOrderNatAt D t ∧ Even (analyticOrderNatAt D t)) ∧
      ∃ δ : ℝ, 0 < δ ∧ (∀ s ∈ Ioo (τ - δ) τ, 0 < D s) ∧ (∀ s ∈ Ioo τ (τ + δ), D s < 0) := by
  obtain ⟨T, hT, hTneg⟩ := th_exists_neg hnot
  have hNne : ({s : ℝ | 0 < s ∧ D s < 0}).Nonempty := ⟨T, by linarith, hTneg⟩
  have hNbdd : BddBelow {s : ℝ | 0 < s ∧ D s < 0} := ⟨0, fun s hs => hs.1.le⟩
  obtain ⟨τ, hτdef⟩ : ∃ τ, τ = sInf {s : ℝ | 0 < s ∧ D s < 0} := ⟨_, rfl⟩
  have hN20 : ∀ s ∈ {s : ℝ | 0 < s ∧ D s < 0}, 20 < s := fun s hs => by
    by_contra h; push Not at h; exact absurd hs.2 (not_lt.2 (th_D_early_pos hs.1 h).le)
  have hτ20 : 20 ≤ τ := hτdef ▸ le_csInf hNne fun s hs => (hN20 s hs).le
  have hτ0 : 0 < τ := by linarith
  have hlow : ∀ s ∈ {s : ℝ | 0 < s ∧ D s < 0}, τ ≤ s := fun s hs => hτdef ▸ csInf_le hNbdd hs
  have hbelow : ∀ s, 0 < s → s < τ → 0 ≤ D s := fun s hs hsτ => by
    by_contra h; push Not at h; exact absurd (hlow s ⟨hs, h⟩) (not_le.2 hsτ)
  have hcloser : ∀ x, τ < x → ∃ s, (0 < s ∧ D s < 0) ∧ s < x := fun x hx => by
    obtain ⟨s, hs, hsx⟩ := exists_lt_of_csInf_lt hNne (hτdef ▸ hx)
    exact ⟨s, hs, hsx⟩
  have hDτle : D τ ≤ 0 := by
    have hcl : τ ∈ closure {s : ℝ | 0 < s ∧ D s < 0} := hτdef ▸ csInf_mem_closure hNne hNbdd
    exact closure_minimal (fun s hs => (show D s ≤ 0 from hs.2.le))
      (isClosed_le th_D_cont continuous_const) hcl
  have hDτge : 0 ≤ D τ := by
    have h : Tendsto D (𝓝[<] τ) (𝓝 (D τ)) := th_D_cont.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto h ?_
    filter_upwards [Ioo_mem_nhdsLT hτ0] with s hs using hbelow s hs.1 hs.2
  have hDτ : D τ = 0 := le_antisymm hDτle hDτge
  have hτ20' : 20 < τ := by
    refine lt_of_le_of_ne hτ20 fun h => ?_
    have := th_D_early_pos (show (0:ℝ) < 20 by norm_num) le_rfl
    rw [h, hDτ] at this
    exact lt_irrefl 0 this
  have hτZ : τ ∈ ZS := by
    refine ⟨hτ20', hDτ, fun s hs => ?_⟩
    rcases hs.1.eq_or_lt with h0 | h0
    · rw [← h0, liEvenCrossActualClockLogHistory_origin.2]
    rcases hs.2.eq_or_lt with h1 | h1
    · rw [h1, hDτ]
    · exact hbelow s h0 h1
  have hmax : ∀ t ∈ ZS, t ≤ τ := fun t ⟨_, _, hh⟩ => by
    by_contra hlt; push Not at hlt
    obtain ⟨s, hsN, hst⟩ := hcloser t hlt
    exact absurd (hh s ⟨hsN.1.le, hst.le⟩) (not_le.2 hsN.2)
  -- local factorization at τ
  obtain ⟨-, hk0, w, hwan, hwτ, hfac⟩ := liEvenCrossActualClockLogHistory_zero_factor τ hDτ
  have hwc : ContinuousAt w τ := hwan.continuousAt
  have hwneg : w τ < 0 := by
    rcases lt_or_gt_of_ne hwτ with h | h
    · exact h
    obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (hfac.and (hwc.eventually (lt_mem_nhds h)))
    obtain ⟨s, hsN, hs⟩ := hcloser (τ + ε) (by linarith)
    have hτs : τ < s := lt_of_le_of_ne (hlow s hsN) fun h => by rw [← h, hDτ] at hsN; linarith [hsN.2]
    have hd : dist s τ < ε := by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith
    obtain ⟨hD, hw⟩ := hεP hd
    have : 0 < D s := by rw [hD]; exact mul_pos (pow_pos (by linarith) _) hw
    linarith [hsN.2]
  obtain ⟨ε, hε, hεP⟩ := Metric.eventually_nhds_iff.1 (hfac.and (hwc.eventually (gt_mem_nhds hwneg)))
  have hδ : 0 < min ε τ := lt_min hε hτ0
  have hin : ∀ s, |s - τ| < min ε τ → dist s τ < ε := fun s hs => by
    rw [Real.dist_eq]; exact lt_of_lt_of_le hs (min_le_left _ _)
  have hodd : Odd (analyticOrderNatAt D τ) := by
    rcases Nat.even_or_odd (analyticOrderNatAt D τ) with he | ho
    · exfalso
      have hm := min_le_right ε τ
      have hs0 : 0 < τ - min ε τ/2 := by linarith
      have hsτ : τ - min ε τ/2 < τ := by linarith
      obtain ⟨hD, hw⟩ := hεP (hin (τ - min ε τ/2) (by rw [abs_of_neg (by linarith)]; linarith))
      have hpos : 0 < (τ - min ε τ/2 - τ)^analyticOrderNatAt D τ := he.pow_pos (by linarith)
      have : D (τ - min ε τ/2) < 0 := by rw [hD]; exact mul_neg_of_pos_of_neg hpos hw
      linarith [hbelow _ hs0 hsτ]
    · exact ho
  have hearlier : ∀ t ∈ ZS, t < τ → 2 ≤ analyticOrderNatAt D t ∧ Even (analyticOrderNatAt D t) := by
    intro t ⟨ht20, hzt, hht⟩ htτ
    obtain ⟨-, hkt, w', hwan', hwt', hfac'⟩ := liEvenCrossActualClockLogHistory_zero_factor t hzt
    have hwc' : ContinuousAt w' t := hwan'.continuousAt
    have hright : ∀ s, t < s → s < τ → 0 ≤ D s := fun s hts hsτ => hbelow s (by linarith) hsτ
    have hwpos : 0 < w' t := by
      rcases lt_or_gt_of_ne hwt' with h | h
      · exfalso
        obtain ⟨ε', hε', hP'⟩ := Metric.eventually_nhds_iff.1 (hfac'.and (hwc'.eventually (gt_mem_nhds h)))
        have hm := min_le_left ε' (τ - t)
        have hm' := min_le_right ε' (τ - t)
        have hm0 : 0 < min ε' (τ - t) := lt_min hε' (by linarith)
        have hts : t < t + min ε' (τ - t)/2 := by linarith
        have hsτ : t + min ε' (τ - t)/2 < τ := by linarith
        obtain ⟨hD, hw⟩ := hP' (y := t + min ε' (τ - t)/2)
          (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith)
        have : D (t + min ε' (τ - t)/2) < 0 := by
          rw [hD]; exact mul_neg_of_pos_of_neg (pow_pos (by linarith) _) hw
        linarith [hright _ hts hsτ]
      · exact h
    obtain ⟨ε', hε', hP'⟩ := Metric.eventually_nhds_iff.1 (hfac'.and (hwc'.eventually (lt_mem_nhds hwpos)))
    have heven : Even (analyticOrderNatAt D t) := by
      rcases Nat.even_or_odd (analyticOrderNatAt D t) with he | ho
      · exact he
      · exfalso
        have hm := min_le_left ε' t
        have hm' := min_le_right ε' t
        have hm0 : 0 < min ε' t := lt_min hε' (by linarith)
        have hs0 : 0 ≤ t - min ε' t/2 := by linarith
        have hst : t - min ε' t/2 < t := by linarith
        obtain ⟨hD, hw⟩ := hP' (y := t - min ε' t/2)
          (by rw [Real.dist_eq, abs_of_neg (by linarith)]; linarith)
        have : D (t - min ε' t/2) < 0 := by
          rw [hD]; exact mul_neg_of_neg_of_pos (ho.pow_neg (by linarith)) hw
        linarith [hht _ ⟨hs0, hst.le⟩]
    refine ⟨?_, heven⟩
    obtain ⟨m, hm⟩ := heven
    omega
  refine ⟨τ, hτZ, hτdef, hmax, hodd, hearlier, min ε τ, hδ, fun s hs => ?_, fun s hs => ?_⟩
  · obtain ⟨hD, hw⟩ := hεP (hin s (by rw [abs_of_neg (by linarith [hs.2])]; linarith [hs.1]))
    rw [hD]
    exact mul_pos_of_neg_of_neg (hodd.pow_neg (by linarith [hs.2])) hw
  · obtain ⟨hD, hw⟩ := hεP (hin s (by rw [abs_of_pos (by linarith [hs.1])]; linarith [hs.2]))
    rw [hD]
    exact mul_neg_of_pos_of_neg (pow_pos (by linarith [hs.1]) _) hw

/-- **(T15)**  The guarded-zero set is empty exactly under RH and nonempty exactly otherwise. -/
theorem liEvenCrossActualClockGuardedZeroSet_rh_iff :
    (RiemannHypothesis ↔ ZS = ∅) ∧ (¬RiemannHypothesis ↔ Set.Nonempty ZS) := by
  have h1 : RiemannHypothesis → ZS = ∅ := fun hRH => by
    ext t
    simp only [mem_empty_iff_false, iff_false]
    rintro ⟨ht, hz, -⟩
    exact (liEvenCrossActualClockLogHistory_pos_of_rh hRH (by linarith)).ne' hz
  have h2 : ¬RiemannHypothesis → Set.Nonempty ZS := fun hnot => by
    obtain ⟨τ, hτ, -⟩ := liEvenCrossActualClockGuardedZeroSet_ordered_of_not_rh hnot
    exact ⟨τ, hτ⟩
  refine ⟨⟨h1, fun hZ => by_contra fun hnot => ?_⟩, ⟨h2, fun hne hRH => ?_⟩⟩
  · obtain ⟨t, ht⟩ := h2 hnot
    rw [hZ] at ht
    exact ht
  · obtain ⟨t, ht⟩ := hne
    rw [h1 hRH] at ht
    exact ht

/-- **(T15)**  The guarded-zero set is finite, unconditionally. -/
theorem finite_liEvenCrossActualClockGuardedZeroSet : Set.Finite ZS := by
  by_cases hRH : RiemannHypothesis
  · rw [liEvenCrossActualClockGuardedZeroSet_rh_iff.1.1 hRH]
    exact finite_empty
  · obtain ⟨τ, -, -, hmax, -⟩ := liEvenCrossActualClockGuardedZeroSet_ordered_of_not_rh hRH
    exact (finite_liEvenCrossActualClockLogHistory_zeros 20 τ).subset
      fun t ⟨ht, hz, hh⟩ => ⟨⟨ht.le, hmax t ⟨ht, hz, hh⟩⟩, hz⟩

/-- **(T16)**  Beyond some clock there are no guarded zeros. -/
theorem exists_forall_ge_not_mem_liEvenCrossActualClockGuardedZeroSet :
    ∃ Tstar : ℝ, ∀ t, Tstar ≤ t → t ∉ ZS := by
  obtain ⟨M, hM⟩ := finite_liEvenCrossActualClockGuardedZeroSet.bddAbove
  exact ⟨M + 1, fun t ht hZ => by linarith [hM hZ]⟩

/-- **(T16)**  No sequence of guarded zeros tends to infinity. -/
theorem not_exists_tendsto_atTop_liEvenCrossActualClockGuardedZero :
    ¬ ∃ T : ℕ → ℝ, Tendsto T atTop atTop ∧ ∀ n, T n ∈ ZS := by
  rintro ⟨T, hT, hZ⟩
  obtain ⟨M, hM⟩ := exists_forall_ge_not_mem_liEvenCrossActualClockGuardedZeroSet
  obtain ⟨n, hn⟩ := (hT.eventually (eventually_ge_atTop M)).exists
  exact hM _ hn (hZ n)

/-- **(T16)**  The eventually-guarded outside budget and normalized order hold vacuously. -/
theorem exists_liEvenCrossActualClockGuardedZero_budget :
    ∃ Tstar : ℝ, ∀ t, Tstar ≤ t → t ∈ ZS → Cout t ≤ V t ∧ rho t ≤ beta t := by
  obtain ⟨M, hM⟩ := exists_forall_ge_not_mem_liEvenCrossActualClockGuardedZeroSet
  exact ⟨M, fun t ht hZ => absurd hZ (hM t ht)⟩

private theorem th_U_hasDerivAt (r : ℝ) :
    HasDerivAt (fun x : ℝ => (U (x:ℂ)).re) (deriv U (r:ℂ)).re r :=
  (liClockThetaScoreProfiles_analyticAt (r:ℂ)).2.2.2.1.differentiableAt.hasDerivAt.real_of_complex

/-- `U(0) = 17/2`. -/
theorem liClockThetaScoreCostProfile_zero : U 0 = 17/2 := by
  unfold liClockThetaScoreCostProfile
  rw [tsum_eq_single 0 fun j hj => by simp [hj]]
  norm_num [Nat.factorial]

private theorem th_U0 : (U ((0:ℝ):ℂ)).re = 17/2 := by
  rw [Complex.ofReal_zero, liClockThetaScoreCostProfile_zero]; norm_num

/-- The real cost profile is even, so `U'(0) = 0`. -/
theorem deriv_liClockThetaScoreCostProfile_real_zero :
    deriv (fun x : ℝ => (U (x:ℂ)).re) 0 = 0 := by
  have hf := th_U_hasDerivAt 0
  have hrefl := (th_U_hasDerivAt (0 - 0)).comp_const_sub 0 0
  have he : (fun x : ℝ => (U ((0 - x : ℝ):ℂ)).re) = fun x : ℝ => (U (x:ℂ)).re := by
    funext x
    rw [zero_sub, Complex.ofReal_neg, (liClockThetaScoreProfiles_even _).2.2.2.1]
  rw [he, sub_zero] at hrefl
  rw [hf.deriv]
  linarith [hf.unique hrefl]

/-- The slope ratio at zero lag: `a(0) = 303ν₁/17`. -/
theorem liClockThetaScoreSlopeRatio_zero : aS 0 = 303*thetaCuspNormalizedEvenMoment 1/17 := by
  unfold liClockThetaScoreSlopeRatio
  obtain ⟨-, hK1, hb, -⟩ := liEvenCrossActualClockHistory_origin
  rw [hK1, hb, normalizedPrimeArchMoment_zero_eq_thetaCuspNormalizedEvenMoment, th_U0]
  ring

/-- The lag-coordinate weight `h_t(r) = (t-r)D(t-r)U(r)/I_U`. -/
def liEvenCrossActualClockTerminalLagDensity (t r : ℝ) : ℝ :=
  (t-r)*D (t-r)*(U (r:ℂ)).re/IU t

private theorem th_mul_density (s : ℝ) : s*Dens s = P s := by
  rcases eq_or_ne s 0 with rfl | hs
  · simp [liEvenCrossActualClockPrimitive_origin_even.1]
  · rw [liEvenCrossActualClockLogHistoryDensity]; field_simp

/-- **Boundary slope (T9).**  At a guarded zero, `h_t(0) = 0`, `h_t'(0) = -P(t)U(0)/I_U ≥ 0`
with `U(0) = 17/2`, and `ρ_t - β_t = 303 A_near/I_U + (606/17) h_t'(0)`. -/
theorem liEvenCrossActualClockTerminalLagDensity_boundary_slope {t : ℝ} (ht : 20 < t)
    (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    liEvenCrossActualClockTerminalLagDensity t 0 = 0 ∧
      HasDerivAt (liEvenCrossActualClockTerminalLagDensity t) (-P t*(17/2)/IU t) 0 ∧
      0 ≤ deriv (liEvenCrossActualClockTerminalLagDensity t) 0 ∧
      rho t - beta t =
        303*Anear t/IU t + (606/17)*deriv (liEvenCrossActualClockTerminalLagDensity t) 0 := by
  obtain ⟨hIU, -, -, -, hdiff, -⟩ := liEvenCrossActualClockOuterHistory_order ht hz hHist
  have hP := (liEvenCrossActualClockHistory_guarded_zero_slope (by linarith) hz hHist).2
  have hd : HasDerivAt (liEvenCrossActualClockTerminalLagDensity t) (-P t*(17/2)/IU t) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => t - r) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub t
    have h2 : HasDerivAt (fun r : ℝ => D (t - r)) (-Dens (t - 0)) 0 :=
      (hasDerivAt_liEvenCrossActualClockLogHistory (t - 0)).comp_const_sub t 0
    have h := ((h1.mul h2).mul (th_U_hasDerivAt 0)).div_const (IU t)
    refine h.congr_deriv ?_
    simp only [Pi.mul_apply, th_U0, sub_zero, hz]
    rw [← th_mul_density t]
    ring
  refine ⟨by simp [liEvenCrossActualClockTerminalLagDensity, hz], hd, ?_, ?_⟩
  · rw [hd.deriv]
    exact div_nonneg (mul_nonneg (neg_nonneg.2 hP) (by norm_num)) hIU.le
  · rw [hd.deriv, hdiff]
    field_simp
    ring

/-- **Adaptive relative barrier (T11).**  At a guarded zero and `η ∈ (0,1)`, a cutoff `R` with
`a ≤ ηβ_t` beyond `R` exists, and
`Π_t(t-s < R)/β_t ≥ [1-η+(A_near-P)/(I_K+V)]/(θ-ηβ_t) ≥ [1-η+ζ_t/(I_K+V)]/(θ-ηβ_t) > (1-η)/θ`. -/
theorem liEvenCrossActualClockOuterHistory_adaptive_reserve {t : ℝ} (ht : 20 < t)
    (hz : D t = 0) (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) {η : ℝ} (hη : 0 < η) (hη1 : η < 1) :
    ∃ R : ℝ, 0 < R ∧ (∀ r, R ≤ r → aS r ≤ η*beta t) ∧
      (1 - η + (Anear t - P t)/(IK t + V t))/(thc - η*beta t) ≤
        (Pi t).real (Ioi (t-R))/beta t ∧
      (1 - η + zeta t/(IK t + V t))/(thc - η*beta t) ≤
        (1 - η + (Anear t - P t)/(IK t + V t))/(thc - η*beta t) ∧
      (1 - η)/thc < (1 - η + zeta t/(IK t + V t))/(thc - η*beta t) := by
  obtain ⟨hIU, -, -, -, hdiff, -, hβ, hβρ, hρθ, -⟩ :=
    liEvenCrossActualClockOuterHistory_order ht hz hHist
  obtain ⟨-, -, hlim⟩ := liClockThetaScoreSlopeRatio_spec
  have hx := liEvenCrossActualClockHistory_guarded_zero_outside_excess (by linarith) hz hHist
  have hζ : zeta t ≤ Anear t - P t := by rw [← hx.1]; exact hx.2.1
  have hY : 0 < IK t + V t := by
    have h := (div_pos_iff_of_pos_right hIU).1 (show 0 < 303*(IK t + V t)/IU t from hβ)
    linarith
  have hηβ : 0 < η*beta t := mul_pos hη hβ
  have hηβ' : η*beta t < beta t := mul_lt_of_lt_one_left hβ hη1
  have hden : 0 < thc - η*beta t := by linarith
  obtain ⟨R0, hR0⟩ := eventually_atTop.1 (hlim.eventually (gt_mem_nhds hηβ))
  have hcut : ∀ r, max R0 1 ≤ r → aS r ≤ η*beta t := fun r hr =>
    (hR0 r ((le_max_left _ _).trans hr)).le
  refine ⟨max R0 1, lt_max_of_lt_right one_pos, hcut, ?_, ?_, ?_⟩
  · have hm := ((liEvenCrossActualClockOuterHistory_terminal_mass ht hz hHist).1
      (η*beta t) (max R0 1) (by linarith) hcut).1
    have hq : (Anear t - P t)/(IK t + V t) = (rho t - beta t)/beta t := by
      rw [hdiff, liEvenCrossActualClockOuterBudgetRatio]
      field_simp
    rw [hq, div_le_div_iff₀ hden hβ]
    have e : (1 - η + (rho t - beta t)/beta t)*beta t = rho t - η*beta t := by
      field_simp; ring
    rw [e]
    linarith
  · apply div_le_div_of_nonneg_right _ hden.le
    linarith [div_le_div_of_nonneg_right hζ hY.le]
  · have h1 : (1 - η)/thc ≤ (1 - η)/(thc - η*beta t) :=
      div_le_div_of_nonneg_left (by linarith) hden (by linarith)
    have h2 : (1 - η)/(thc - η*beta t) < (1 - η + zeta t/(IK t + V t))/(thc - η*beta t) :=
      div_lt_div_of_pos_right (by linarith [div_pos hx.2.2 hY]) hden
    linarith

/-- A cutoff below a value of the slope ratio lies beyond that lag. -/
theorem lt_of_liClockThetaScoreSlopeRatio_cutoff {ε R M : ℝ} (hε : ε < aS M)
    (hcut : ∀ r, R ≤ r → aS r ≤ ε) : M < R := by
  by_contra h
  push Not at h
  linarith [hcut M h]

/-- Cutoffs for thresholds tending to `0` escape to infinity. -/
theorem tendsto_atTop_of_liClockThetaScoreSlopeRatio_cutoffs (eps R : ℕ → ℝ)
    (heps : Tendsto eps atTop (𝓝 0)) (hcut : ∀ n r, R n ≤ r → aS r ≤ eps n) :
    Tendsto R atTop atTop := by
  obtain ⟨-, hb, -⟩ := liClockThetaScoreSlopeRatio_spec
  refine tendsto_atTop.2 fun M => ?_
  filter_upwards [heps.eventually (gt_mem_nhds (hb M).1)] with n hn
  exact (lt_of_liClockThetaScoreSlopeRatio_cutoff hn (hcut n)).le

/-- The outer-history probability has no atoms. -/
theorem liEvenCrossActualClockOuterHistoryMeasure_singleton (t x : ℝ) : Pi t {x} = 0 :=
  (withDensity_absolutelyContinuous _ _) (by
    rw [Measure.restrict_apply (measurableSet_singleton x)]
    exact measure_mono_null inter_subset_left Real.volume_singleton)

private theorem th_Pi_terminal {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) {R : ℝ} (hR : 0 ≤ R) (hRt : R ≤ t - ell t) :
    (Pi t).real (Ioi (t-R)) = (∫ r in (0:ℝ)..R, (t-r)*D (t-r)*(U (r:ℂ)).re)/IU t := by
  have h := integral_liEvenCrossActualClockOuterHistoryMeasure ht hz hHist ((Ioi (t-R)).indicator 1)
  rw [integral_indicator_one measurableSet_Ioi] at h
  rw [h]
  congr 1
  have e1 : (fun s => s*D s*(U ((t-s):ℂ)).re*(Ioi (t-R)).indicator 1 s) =
      (Ioi (t-R)).indicator (fun s => s*D s*(U ((t-s):ℂ)).re) := by
    funext s
    by_cases hs : s ∈ Ioi (t-R) <;> simp [hs]
  rw [e1, setIntegral_indicator measurableSet_Ioi]
  have e2 : Icc (ell t) t ∩ Ioi (t-R) = Ioc (t-R) t := by
    ext s
    simp only [mem_inter_iff, mem_Icc, mem_Ioi, mem_Ioc]
    constructor
    · rintro ⟨⟨-, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨⟨by linarith, h2⟩, h1⟩
  rw [e2, ← intervalIntegral.integral_of_le (by linarith)]
  have e3 : (∫ r in (0:ℝ)..R, (t-r)*D (t-r)*(U (r:ℂ)).re) =
      ∫ r in (0:ℝ)..R, (fun s => s*D s*(U ((t-s):ℂ)).re) (t - r) := by
    congr 1; funext r
    simp only [Complex.ofReal_sub, sub_sub_cancel]
  rw [e3, intervalIntegral.integral_comp_sub_left (fun s => s*D s*(U ((t-s):ℂ)).re) t, sub_zero]

/-- **Fixed-clock endpoint law (T12).**  At a guarded zero of order `k ≥ 1` there is `c_t > 0`
with `D(t-r) = c_t r^k + O(r^{k+1})`; `P(t) = -tc_t` if `k = 1` and `P(t) = 0` if `k ≥ 2`;
and as `R ↓ 0`, `Π_t(t-s < R) = tU(0)c_tR^{k+1}/((k+1)I_U) + O(R^{k+2})`,
`Π_t(t-s < R)/β_t = tU(0)c_tR^{k+1}/(303(k+1)(I_K+V)) + O(R^{k+2}) → 0`, with `U(0) = 17/2`. -/
theorem liEvenCrossActualClockTerminalHistory_fixed_order {t : ℝ} (ht : 20 < t) (hz : D t = 0)
    (hHist : ∀ s ∈ Icc 0 t, 0 ≤ D s) :
    ∃ c : ℝ, 0 < c ∧ 1 ≤ analyticOrderNatAt D t ∧
      (fun r : ℝ => D (t - r) - c*r^(analyticOrderNatAt D t)) =O[𝓝[>] 0]
        (fun r => r^(analyticOrderNatAt D t + 1)) ∧
      P t = (if analyticOrderNatAt D t = 1 then -t*c else 0) ∧
      (fun R : ℝ => (Pi t).real (Ioi (t-R)) -
          t*(17/2)*c*R^(analyticOrderNatAt D t + 1)/((analyticOrderNatAt D t + 1 : ℝ)*IU t))
        =O[𝓝[>] 0] (fun R => R^(analyticOrderNatAt D t + 2)) ∧
      (fun R : ℝ => (Pi t).real (Ioi (t-R))/beta t -
          t*(17/2)*c*R^(analyticOrderNatAt D t + 1)/
            (303*(analyticOrderNatAt D t + 1 : ℝ)*(IK t + V t)))
        =O[𝓝[>] 0] (fun R => R^(analyticOrderNatAt D t + 2)) ∧
      Tendsto (fun R : ℝ => (Pi t).real (Ioi (t-R))/beta t) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨-, hk0, w, hwan, hwt, hfac⟩ := liEvenCrossActualClockLogHistory_zero_factor t hz
  obtain ⟨hIU, -, -, -, -, -, hβ, -⟩ := liEvenCrossActualClockOuterHistory_order ht hz hHist
  set k := analyticOrderNatAt D t with hk
  have hc : Tendsto (fun r : ℝ => t - r) (𝓝 0) (𝓝 t) := by
    have h := (continuous_sub_left t).tendsto 0
    rw [sub_zero] at h
    exact h
  have hfac0 : ∀ᶠ r in 𝓝 (0:ℝ), D (t - r) = r^k*((-1)^k*w (t - r)) := by
    filter_upwards [hc.eventually hfac] with r hr
    rw [hr, show t - r - t = -r by ring, neg_pow]
    ring
  set c := (-1)^k*w t with hcdef
  have hwcont : Tendsto (fun r : ℝ => (-1)^k*w (t - r)) (𝓝 0) (𝓝 c) :=
    (hwan.continuousAt.tendsto.comp hc).const_mul _
  have hcpos : 0 < c := by
    rcases lt_or_gt_of_ne (show c ≠ 0 from mul_ne_zero (pow_ne_zero _ (by norm_num)) hwt) with h | h
    · exfalso
      obtain ⟨δ, hδ, hP⟩ := Metric.eventually_nhds_iff.1 (hfac0.and (hwcont.eventually (gt_mem_nhds h)))
      have hr0 : 0 < min (δ/2) t := lt_min (by linarith) (by linarith)
      have hrt : min (δ/2) t ≤ t := min_le_right _ _
      have hrd : min (δ/2) t < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
      obtain ⟨hD, hneg⟩ := hP (y := min (δ/2) t) (by rw [Real.dist_eq, sub_zero, abs_of_pos hr0]; exact hrd)
      have hneg' : D (t - min (δ/2) t) < 0 := by rw [hD]; exact mul_neg_of_pos_of_neg (pow_pos hr0 _) hneg
      linarith [hHist (t - min (δ/2) t) ⟨by linarith, by linarith⟩]
    · exact h
  -- the local expansion of `D(t-r)`
  have hwd : HasDerivAt w (deriv w (t - 0)) (t - 0) := by
    rw [sub_zero]; exact hwan.differentiableAt.hasDerivAt
  have hwr := hwd.comp_const_sub t 0
  have hW : (fun r : ℝ => w (t - r) - w t) =O[𝓝 0] (fun r : ℝ => r) := by
    have h := hwr.isBigO_sub
    simp only [sub_zero] at h
    exact h
  have hexp : (fun r : ℝ => D (t - r) - c*r^k) =O[𝓝[>] 0] (fun r => r^(k+1)) := by
    have hm : (fun r : ℝ => (-1)^k*r^k*(w (t - r) - w t)) =O[𝓝 0] (fun r : ℝ => r^k*r) :=
      ((isBigO_refl (fun r : ℝ => r^k) _).const_mul_left ((-1)^k)).mul hW
    have hm' : (fun r : ℝ => D (t - r) - c*r^k) =O[𝓝 0] (fun r : ℝ => r^(k+1)) := by
      refine (hm.congr' ?_ (Eventually.of_forall fun r => by ring)).trans (isBigO_refl _ _)
      filter_upwards [hfac0] with r hr
      rw [hr, hcdef]; ring
    exact hm'.mono nhdsWithin_le_nhds
  -- the primitive at `t`
  have hPt : P t = (if k = 1 then -t*c else 0) := by
    have hF := (((hasDerivAt_id' t).sub_const t).pow k).mul hwan.differentiableAt.hasDerivAt
    have hD := hF.congr_of_eventuallyEq hfac
    have hu := (hasDerivAt_liEvenCrossActualClockLogHistory t).unique hD
    rw [← th_mul_density t, hu]
    split_ifs with h1
    · rw [hcdef, h1]; simp
    · have hk2 : k - 1 ≠ 0 := by omega
      simp [zero_pow hk2, zero_pow (show k ≠ 0 by omega)]
  -- terminal-mass expansion
  have hU0 := th_U0
  set g : ℝ → ℝ := fun r => (t-r)*D (t-r)*(U (r:ℂ)).re with hg
  set vv : ℝ → ℝ := fun r => (t-r)*((-1)^k*w (t-r))*(U (r:ℂ)).re with hvv
  have hvv0 : vv 0 = t*(17/2)*c := by simp only [hvv, sub_zero, hU0, hcdef]; ring
  have hvvd : HasDerivAt vv
      (((-1)*((-1)^k*w (t-0)) + (t-0)*((-1)^k*(-deriv w (t - 0))))*(U ((0:ℝ):ℂ)).re +
        (t-0)*((-1)^k*w (t-0))*(deriv U ((0:ℝ):ℂ)).re) 0 := by
    have h1 : HasDerivAt (fun r : ℝ => t - r) (-1) 0 := by
      simpa using (hasDerivAt_id (0:ℝ)).const_sub t
    exact (h1.mul (hwr.const_mul ((-1)^k))).mul (th_U_hasDerivAt 0)
  obtain ⟨L, hL, hLb⟩ := (by simpa only [sub_zero] using hvvd.isBigO_sub :
    (fun r : ℝ => vv r - vv 0) =O[𝓝 0] fun r => r).exists_pos
  obtain ⟨δ, hδ, hδP⟩ := Metric.eventually_nhds_iff.1 (hfac0.and hLb.bound)
  have hgc : Continuous g := by
    simp only [hg]
    exact ((continuous_const.sub continuous_id).mul (th_D_cont.comp (continuous_const.sub continuous_id))).mul
      (Complex.continuous_re.comp ((continuous_iff_continuousAt.mpr fun z =>
        (liClockThetaScoreProfiles_analyticAt z).2.2.2.1.continuousAt).comp Complex.continuous_ofReal))
  have hgeo := liEvenCrossActualClockHistory_geometry (show 0 < t by linarith)
  have hgap : 0 < t - ell t := by linarith [hgeo.2.2.2]
  have hnear : ∀ᶠ R in 𝓝[>] (0:ℝ), 0 < R ∧ R < min δ (t - ell t) := by
    filter_upwards [Ioo_mem_nhdsGT (lt_min hδ hgap)] with R hR using hR
  have hmass : (fun R : ℝ => (Pi t).real (Ioi (t-R)) -
      t*(17/2)*c*R^(k + 1)/((k + 1 : ℝ)*IU t)) =O[𝓝[>] 0] (fun R => R^(k + 2)) := by
    refine IsBigO.of_bound (L/IU t) ?_
    filter_upwards [hnear] with R ⟨hR0, hRm⟩
    have hRδ : R < δ := lt_of_lt_of_le hRm (min_le_left _ _)
    have hRt : R ≤ t - ell t := (lt_of_lt_of_le hRm (min_le_right _ _)).le
    rw [th_Pi_terminal ht hz hHist hR0.le hRt]
    have hint : (∫ r in (0:ℝ)..R, g r) - vv 0*(R^(k+1)/(k+1)) =
        ∫ r in (0:ℝ)..R, (g r - vv 0*r^k) := by
      rw [intervalIntegral.integral_sub (hgc.intervalIntegrable _ _)
        (by exact (continuous_const.mul (continuous_pow k)).intervalIntegrable _ _ :
          IntervalIntegrable (fun r : ℝ => vv 0*r^k) volume 0 R),
        intervalIntegral.integral_const_mul, integral_pow]
      simp
    have hbound : ‖∫ r in (0:ℝ)..R, (g r - vv 0*r^k)‖ ≤ L*R^(k+1)*|R - 0| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun r hr => ?_
      rw [uIoc_of_le hR0.le] at hr
      have hrδ : dist r 0 < δ := by
        rw [Real.dist_eq, sub_zero, abs_of_pos hr.1]; linarith [hr.2]
      obtain ⟨hD, hvb⟩ := hδP hrδ
      have hgr : g r - vv 0*r^k = r^k*(vv r - vv 0) := by
        simp only [hg, hvv]; rw [hD]; ring
      rw [hgr, norm_mul, norm_pow, Real.norm_eq_abs, abs_of_pos hr.1]
      rw [Real.norm_eq_abs r, abs_of_pos hr.1] at hvb
      calc r^k*‖vv r - vv 0‖ ≤ r^k*(L*r) := mul_le_mul_of_nonneg_left hvb (pow_pos hr.1 _).le
        _ = L*r^(k+1) := by ring
        _ ≤ L*R^(k+1) := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr.1.le hr.2 _) hL.le
    have e : (∫ r in (0:ℝ)..R, (t-r)*D (t-r)*(U (r:ℂ)).re)/IU t -
        t*(17/2)*c*R^(k+1)/((k+1:ℝ)*IU t) =
        (∫ r in (0:ℝ)..R, (g r - vv 0*r^k))/IU t := by
      rw [← hint, hvv0]
      field_simp
      simp only [hg]
      ring
    rw [e, norm_div, Real.norm_eq_abs (IU t), abs_of_pos hIU, Real.norm_eq_abs (R^(k+2)),
      abs_of_pos (pow_pos hR0 _)]
    rw [sub_zero, abs_of_pos hR0] at hbound
    rw [div_le_iff₀ hIU]
    calc ‖∫ r in (0:ℝ)..R, (g r - vv 0*r^k)‖ ≤ L*R^(k+1)*R := hbound
      _ = L/IU t*R^(k+2)*IU t := by field_simp; ring
  have hβne : beta t ≠ 0 := hβ.ne'
  have hratio : (fun R : ℝ => (Pi t).real (Ioi (t-R))/beta t -
      t*(17/2)*c*R^(k + 1)/(303*(k + 1 : ℝ)*(IK t + V t))) =
      fun R => (1/beta t)*((Pi t).real (Ioi (t-R)) -
        t*(17/2)*c*R^(k + 1)/((k + 1 : ℝ)*IU t)) := by
    funext R
    have hY : IK t + V t ≠ 0 := by
      intro h0
      simp only [liEvenCrossActualClockOuterBudgetRatio, h0, mul_zero, zero_div] at hβne
      exact hβne rfl
    simp only [liEvenCrossActualClockOuterBudgetRatio] at hβne ⊢
    field_simp
  have hmassβ := hratio ▸ hmass.const_mul_left (1/beta t)
  refine ⟨c, hcpos, hk0, hexp, hPt, hmass, hmassβ, ?_⟩
  have hmain : Tendsto (fun R : ℝ => t*(17/2)*c*R^(k + 1)/(303*(k + 1 : ℝ)*(IK t + V t)))
      (𝓝[>] 0) (𝓝 0) := by
    have h : Tendsto (fun R : ℝ => t*(17/2)*c*R^(k + 1)/(303*(k + 1 : ℝ)*(IK t + V t))) (𝓝 0)
        (𝓝 (t*(17/2)*c*0^(k + 1)/(303*(k + 1 : ℝ)*(IK t + V t)))) :=
      ((continuous_const.mul (continuous_pow (k+1))).div_const _).tendsto 0
    rw [zero_pow (by omega), mul_zero, zero_div] at h
    exact h.mono_left nhdsWithin_le_nhds
  have herr : Tendsto (fun R : ℝ => (Pi t).real (Ioi (t-R))/beta t -
      t*(17/2)*c*R^(k + 1)/(303*(k + 1 : ℝ)*(IK t + V t))) (𝓝[>] 0) (𝓝 0) := by
    refine hmassβ.trans_tendsto ?_
    have h : Tendsto (fun R : ℝ => R^(k + 2)) (𝓝 0) (𝓝 (0^(k+2))) := (continuous_pow (k+2)).tendsto 0
    rw [zero_pow (by omega)] at h
    exact h.mono_left nhdsWithin_le_nhds
  simpa using hmain.add herr

end
end RHTower
