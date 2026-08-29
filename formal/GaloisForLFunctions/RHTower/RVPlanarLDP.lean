import GaloisForLFunctions.RHTower.RVDeviationLower
import GaloisForLFunctions.HTGeometry.SteinhausRotationInvariance
import GaloisForLFunctions.RHTower.SteinhausExtendedRate

/-!
# The planar large-deviation principle

Part `1` of the card.  Lean's `Real.log 0 = 0` makes the classical `limsup (1/d) log μ(F)`
formulation false at null sets, so the principle is stated in the equivalent exponential form: for
every closed `F` and every `c` strictly below the rate on `F` the mass is eventually at most
`e^{−c d_X}`, and for every open `G`, every point of `G` and every `c` strictly above its rate the
mass is eventually at least `e^{−c d_X}`.
-/

open MeasureTheory Filter Topology HTGeometry

namespace RHTower

local instance phaseCirclePositiveLDP : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

noncomputable section

/-- The law of the model. -/
def rvLaw (α : ℝ) (L : ℝ → ℝ) (X : ℝ) : Measure ℂ :=
  Measure.map (steinhausSum (rvWeightFun α L X))
    (Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle)

theorem measurable_steinhausSum {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    Measurable (steinhausSum a) :=
  (continuous_finsetSum _ fun i _ =>
    continuous_const.mul (continuous_steinhausPhase.comp (continuous_apply i))).measurable

theorem rvLaw_apply {α : ℝ} {L : ℝ → ℝ} {X : ℝ} {S : Set ℂ} (hS : MeasurableSet S) :
    rvLaw α L X S
      = (Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle)
        {x | steinhausSum (rvWeightFun α L X) x ∈ S} := by
  rw [rvLaw, Measure.map_apply (measurable_steinhausSum _) hS]
  rfl

instance isProbabilityMeasure_rvLaw (α : ℝ) (L : ℝ → ℝ) (X : ℝ) :
    IsProbabilityMeasure (rvLaw α L X) :=
  Measure.isProbabilityMeasure_map (measurable_steinhausSum _).aemeasurable

/-- The large deviation principle, exponential form. -/
structure IsLDP (μ : ℝ → Measure ℂ) (d : ℝ → ℝ) (J : ℂ → ENNReal) : Prop where
  upper : ∀ F : Set ℂ, IsClosed F → ∀ c : ℝ, (∀ z ∈ F, ENNReal.ofReal c < J z) →
    ∀ᶠ X in atTop, (μ X F).toReal ≤ Real.exp (-(c * d X))
  lower : ∀ G : Set ℂ, IsOpen G → ∀ z ∈ G, ∀ c : ℝ, J z < ENNReal.ofReal c →
    ∀ᶠ X in atTop, Real.exp (-(c * d X)) ≤ (μ X G).toReal


theorem rvDeviationProb_le_exp {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {c : ℝ}
    (hc : c < rvRate α q) :
    ∀ᶠ X in atTop, rvDeviationProb α L X q ≤ Real.exp (-(c * rvPrimeCount X)) := by
  have hε : 0 < (rvRate α q - c) / 2 := by linarith
  have hWpos : ∀ᶠ X in atTop, rvWeightSum α L X ≠ 0 := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX.ne'
  filter_upwards [eventually_log_rvDeviationProb_le hα0 hα1 hL hq0 hq1 hε, hWpos,
    tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with X hX hXW hXd
  have hPpos : 0 < rvDeviationProb α L X q := rvDeviationProb_pos hq1 hXW
  rw [div_le_iff₀ hXd] at hX
  have hkey : Real.log (rvDeviationProb α L X q) ≤ -(c * rvPrimeCount X) := by
    nlinarith only [hX, hXd, hc]
  calc rvDeviationProb α L X q = Real.exp (Real.log (rvDeviationProb α L X q)) :=
        (Real.exp_log hPpos).symm
    _ ≤ Real.exp (-(c * rvPrimeCount X)) := Real.exp_le_exp.2 hkey

theorem exp_le_rvDeviationProb {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) {c : ℝ}
    (hc : rvRate α q < c) :
    ∀ᶠ X in atTop, Real.exp (-(c * rvPrimeCount X)) ≤ rvDeviationProb α L X q := by
  have hε : 0 < (c - rvRate α q) / 2 := by linarith
  have hWpos : ∀ᶠ X in atTop, rvWeightSum α L X ≠ 0 := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX.ne'
  filter_upwards [eventually_le_log_rvDeviationProb hα0 hα1 hL hq0 hq1 hε, hWpos,
    tendsto_rvPrimeCount_atTop.eventually_gt_atTop 0] with X hX hXW hXd
  have hPpos : 0 < rvDeviationProb α L X q := rvDeviationProb_pos hq1 hXW
  rw [le_div_iff₀ hXd] at hX
  have hkey : -(c * rvPrimeCount X) ≤ Real.log (rvDeviationProb α L X q) := by
    nlinarith only [hX, hXd, hc]
  calc Real.exp (-(c * rvPrimeCount X))
      ≤ Real.exp (Real.log (rvDeviationProb α L X q)) := Real.exp_le_exp.2 hkey
    _ = rvDeviationProb α L X q := Real.exp_log hPpos


/-- The model lives in the closed unit disk. -/
theorem norm_steinhausSum_le_one {α : ℝ} {L : ℝ → ℝ} (hL : IsSlowlyVarying L) {X : ℝ}
    (hW : 0 < rvWeightSum α L X) (x : ↥(rvPrimeFinset X) → PhaseCircle) :
    ‖steinhausSum (rvWeightFun α L X) x‖ ≤ 1 := by
  have hsum := sum_rvWeightFun (α := α) (L := L) (X := X) hW.ne'
  calc ‖steinhausSum (rvWeightFun α L X) x‖
      ≤ ∑ i : ↥(rvPrimeFinset X), ‖((rvWeightFun α L X i : ℂ)) * steinhausPhase (x i)‖ :=
        norm_sum_le _ _
    _ = ∑ i : ↥(rvPrimeFinset X), rvWeightFun α L X i := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [norm_mul, norm_steinhausPhase, mul_one, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (rvWeightFun_nonneg hL hW i)]
    _ = 1 := hsum

/-- **The large-deviation upper bound for closed sets.** -/
theorem rvLaw_upper {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (F : Set ℂ) (hF : IsClosed F) (c : ℝ)
    (hc : ∀ z ∈ F, ENNReal.ofReal c < rvPlanarRate α z) :
    ∀ᶠ X in atTop, (rvLaw α L X F).toReal ≤ Real.exp (-(c * rvPrimeCount X)) := by
  have hWpos : ∀ᶠ X in atTop, 0 < rvWeightSum α L X := by
    have hα' : (0 : ℝ) < 1 - α := by linarith
    have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
      (show (0 : ℝ) < 1 / (1 - α) by positivity)
    filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
    have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
    have hLX : 0 < L X := hL.pos _ hX0
    have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
    have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
    rw [lt_div_iff₀ hden, zero_mul] at hX
    exact hX
  by_cases hempty : (F ∩ Metric.closedBall (0 : ℂ) 1) = ∅
  · filter_upwards [hWpos] with X hXW
    have hset : {x : ↥(rvPrimeFinset X) → PhaseCircle
        | steinhausSum (rvWeightFun α L X) x ∈ F} = ∅ := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro hmem
      have hball : steinhausSum (rvWeightFun α L X) x ∈ Metric.closedBall (0 : ℂ) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_steinhausSum_le_one hL hXW x
      exact Set.eq_empty_iff_forall_notMem.1 hempty _ ⟨hmem, hball⟩
    have hzero : rvLaw α L X F = 0 := by
      rw [rvLaw_apply hF.measurableSet, hset, measure_empty]
    rw [hzero]
    simp only [ENNReal.toReal_zero]
    exact (Real.exp_pos _).le
  · -- the minimal modulus on the compact part
    rw [← Ne, ← Set.nonempty_iff_ne_empty] at hempty
    have hcompact : IsCompact (F ∩ Metric.closedBall (0 : ℂ) 1) :=
      (isCompact_closedBall (0 : ℂ) 1).inter_left hF
    obtain ⟨w₀, hw₀mem, hw₀min⟩ := hcompact.exists_isMinOn hempty
      (continuous_norm.continuousOn)
    set r₀ : ℝ := ‖w₀‖ with hr₀
    have hr₀0 : 0 < r₀ := by
      rcases eq_or_lt_of_le (norm_nonneg w₀) with h0 | hpos
      · exfalso
        have hJ := hc w₀ hw₀mem.1
        have hn : ‖w₀‖ = 0 := h0.symm
        have hlt : ‖w₀‖ < 1 := by rw [hn]; norm_num
        rw [rvPlanarRate_of_norm_lt_one hlt, hn, rvRate_zero hα1] at hJ
        simp at hJ
      · exact hpos
    obtain ⟨q, hq0, hq1, hqr, hqc⟩ : ∃ q : ℝ, 0 < q ∧ q < 1 ∧ q ≤ r₀ ∧ c < rvRate α q := by
      rcases lt_or_ge r₀ 1 with hlt | hge
      · refine ⟨r₀, hr₀0, hlt, le_rfl, ?_⟩
        have hJ := hc w₀ hw₀mem.1
        rw [rvPlanarRate_of_norm_lt_one hlt, ← hr₀] at hJ
        have hpos : 0 < rvRate α r₀ := rvRate_pos hα0 hα1 hr₀0 hlt
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).1 hJ
      · have hev := (tendsto_rvRate_atTop hα1).eventually_gt_atTop c
        have hev2 : ∀ᶠ x in 𝓝[<] (1 : ℝ), (0 : ℝ) < x :=
          (eventually_gt_nhds (by norm_num : (0 : ℝ) < 1)).filter_mono nhdsWithin_le_nhds
        obtain ⟨q, ⟨hqc', hq0'⟩, hq1'⟩ := ((hev.and hev2).and self_mem_nhdsWithin).exists
        exact ⟨q, hq0', hq1', le_trans hq1'.le hge, hqc'⟩
    filter_upwards [rvDeviationProb_le_exp hα0 hα1 hL hq0 hq1 hqc, hWpos] with X hX hXW
    have hsub : {x : ↥(rvPrimeFinset X) → PhaseCircle
        | steinhausSum (rvWeightFun α L X) x ∈ F}
        ⊆ {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} := by
      intro x hmem
      rw [Set.mem_setOf_eq] at hmem ⊢
      have hball : steinhausSum (rvWeightFun α L X) x ∈ Metric.closedBall (0 : ℂ) 1 := by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact norm_steinhausSum_le_one hL hXW x
      have hmin := hw₀min ⟨hmem, hball⟩
      exact le_trans hqr hmin
    have hle : rvLaw α L X F
        ≤ (Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle)
          {x | q ≤ ‖steinhausSum (rvWeightFun α L X) x‖} := by
      rw [rvLaw_apply hF.measurableSet]
      exact measure_mono hsub
    have htoReal : (rvLaw α L X F).toReal ≤ rvDeviationProb α L X q := by
      rw [rvDeviationProb]
      exact ENNReal.toReal_le_toReal (by
        rw [rvLaw_apply hF.measurableSet]
        exact measure_ne_top _ _) (measure_ne_top _ _) |>.2 hle
    linarith [htoReal, hX]


/-- Rotating the centre of a ball does not change the mass. -/
theorem measure_ball_rot {ι : Type*} [Fintype ι] (a : ι → ℝ) (z : ℂ) (r : ℝ) (θ : ℝ) :
    (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x | steinhausSum a x ∈ Metric.ball (Complex.exp ((θ : ℝ) * Complex.I) * z) r}
      = (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x | steinhausSum a x ∈ Metric.ball z r} := by
  have hrot := measure_steinhausSum_rot a (Metric.isOpen_ball (x := z) (ε := r)).measurableSet
    (-θ)
  rw [← hrot]
  congr 1
  ext x
  simp only [Set.mem_setOf_eq, Metric.mem_ball, Complex.dist_eq]
  have hunit : ‖Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    push_cast
    rw [show -(θ : ℂ) * Complex.I = ((-θ : ℝ) : ℂ) * Complex.I by push_cast; ring]
    exact Complex.norm_exp_ofReal_mul_I _
  have hid : Complex.exp (((-θ : ℝ) : ℂ) * Complex.I) * steinhausSum a x - z
      = Complex.exp (((-θ : ℝ) : ℂ) * Complex.I)
        * (steinhausSum a x - Complex.exp (((θ : ℝ) : ℂ) * Complex.I) * z) := by
    rw [mul_sub, ← mul_assoc, ← Complex.exp_add]
    push_cast
    rw [show -(θ : ℂ) * Complex.I + (θ : ℂ) * Complex.I = 0 by ring, Complex.exp_zero, one_mul]
  rw [hid, norm_mul, hunit, one_mul]


/-- The annulus mass is at most `K` times the ball mass. -/
theorem measure_annulus_le_nsmul {ι : Type*} [Fintype ι] (a : ι → ℝ) {z : ℂ} (hz : z ≠ 0)
    {r : ℝ} (hr : 0 < r) {K : ℕ} (hK : 0 < K) (hKb : 4 * Real.pi * ‖z‖ / r < K) :
    (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x | ‖z‖ ≤ ‖steinhausSum a x‖ ∧ ‖steinhausSum a x‖ ≤ ‖z‖ + r / 2}
      ≤ K * (Measure.pi fun _ : ι => AddCircle.haarAddCircle)
        {x | steinhausSum a x ∈ Metric.ball z r} := by
  set μ : Measure (ι → PhaseCircle) := Measure.pi fun _ : ι => AddCircle.haarAddCircle with hμ
  have hcover := annulus_subset_iUnion_balls hz hr hK hKb
  have hsub : {x : ι → PhaseCircle
      | ‖z‖ ≤ ‖steinhausSum a x‖ ∧ ‖steinhausSum a x‖ ≤ ‖z‖ + r / 2}
      ⊆ ⋃ k ∈ Finset.range K, {x : ι → PhaseCircle | steinhausSum a x ∈
          Metric.ball (Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z) r} := by
    intro x hx
    have hmem := hcover (Set.mem_setOf_eq ▸ hx)
    rw [Set.mem_iUnion₂] at hmem ⊢
    obtain ⟨k, hk, hk2⟩ := hmem
    exact ⟨k, hk, hk2⟩
  calc μ {x | ‖z‖ ≤ ‖steinhausSum a x‖ ∧ ‖steinhausSum a x‖ ≤ ‖z‖ + r / 2}
      ≤ μ (⋃ k ∈ Finset.range K, {x : ι → PhaseCircle | steinhausSum a x ∈
          Metric.ball (Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z) r}) :=
        measure_mono hsub
    _ ≤ ∑ k ∈ Finset.range K, μ {x : ι → PhaseCircle | steinhausSum a x ∈
          Metric.ball (Complex.exp (((-Real.pi + 2 * Real.pi * k / K) : ℝ) * Complex.I) * z) r} :=
        measure_biUnion_finset_le _ _
    _ = ∑ _k ∈ Finset.range K, μ {x : ι → PhaseCircle | steinhausSum a x ∈ Metric.ball z r} := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hμ]
        exact measure_ball_rot a z r _
    _ = K * μ {x | steinhausSum a x ∈ Metric.ball z r} := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]


theorem eventually_rvWeightSum_pos {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) : ∀ᶠ X in atTop, 0 < rvWeightSum α L X := by
  have hα' : (0 : ℝ) < 1 - α := by linarith
  have hlim := (tendsto_rvWeightSum hα0 hα1 hL).eventually_const_lt
    (show (0 : ℝ) < 1 / (1 - α) by positivity)
  filter_upwards [hlim, eventually_gt_atTop (1 : ℝ)] with X hX hX1
  have hX0 : (0 : ℝ) < X := lt_trans one_pos hX1
  have hLX : 0 < L X := hL.pos _ hX0
  have hXpow : (0 : ℝ) < X ^ (1 - α) := Real.rpow_pos_of_pos hX0 _
  have hden : (0 : ℝ) < X ^ (1 - α) * L X := mul_pos hXpow hLX
  rw [lt_div_iff₀ hden, zero_mul] at hX
  exact hX

/-- The mass of a ball around the origin. -/
theorem one_sub_le_rvLaw_ball_zero {α : ℝ} {L : ℝ → ℝ} {X r : ℝ} :
    1 - rvDeviationProb α L X r ≤ (rvLaw α L X (Metric.ball (0 : ℂ) r)).toReal := by
  set μ : Measure (↥(rvPrimeFinset X) → PhaseCircle) :=
    Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle with hμ
  have hcomp : {x : ↥(rvPrimeFinset X) → PhaseCircle
      | steinhausSum (rvWeightFun α L X) x ∈ Metric.ball (0 : ℂ) r}
      = {x | r ≤ ‖steinhausSum (rvWeightFun α L X) x‖}ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Metric.mem_ball, dist_zero_right, not_le]
  rw [rvLaw_apply Metric.isOpen_ball.measurableSet, hcomp,
    prob_compl_eq_one_sub (measurableSet_normGe _ r), rvDeviationProb, ← hμ]
  have hle : μ {x | r ≤ ‖steinhausSum (rvWeightFun α L X) x‖} ≤ 1 := prob_le_one
  rw [ENNReal.toReal_sub_of_le hle ENNReal.one_ne_top, ENNReal.toReal_one]

/-- **The lower bound at the origin.** -/
theorem rvLaw_lower_zero {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ}
    (hL : IsSlowlyVarying L) (G : Set ℂ) (hG : IsOpen G) (hz : (0 : ℂ) ∈ G) {c : ℝ}
    (hc : 0 < c) :
    ∀ᶠ X in atTop, Real.exp (-(c * rvPrimeCount X)) ≤ (rvLaw α L X G).toReal := by
  obtain ⟨r', hr'0, hr'⟩ := Metric.isOpen_iff.1 hG 0 hz
  set r : ℝ := min r' (1 / 2) with hrdef
  have hr0 : 0 < r := lt_min hr'0 (by norm_num)
  have hr1 : r < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hball : Metric.ball (0 : ℂ) r ⊆ G :=
    le_trans (Metric.ball_subset_ball (min_le_left _ _)) hr'
  obtain ⟨c₁, hc₁0, hc₁⟩ : ∃ c₁ : ℝ, 0 < c₁ ∧ c₁ < rvRate α r :=
    ⟨rvRate α r / 2, by
      have := rvRate_pos hα0 hα1 hr0 hr1
      linarith, by
      have := rvRate_pos hα0 hα1 hr0 hr1
      linarith⟩
  have hsmall : ∀ᶠ X in atTop, Real.exp (-(c₁ * rvPrimeCount X)) ≤ 1 / 2 := by
    have hlim : Tendsto (fun X : ℝ => Real.exp (-(c₁ * rvPrimeCount X))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have := tendsto_rvPrimeCount_atTop.const_mul_atTop hc₁0
      exact tendsto_neg_atTop_atBot.comp this
    exact hlim.eventually_le_const (by norm_num)
  have hcsmall : ∀ᶠ X in atTop, Real.exp (-(c * rvPrimeCount X)) ≤ 1 / 2 := by
    have hlim : Tendsto (fun X : ℝ => Real.exp (-(c * rvPrimeCount X))) atTop (𝓝 0) := by
      refine Real.tendsto_exp_atBot.comp ?_
      have := tendsto_rvPrimeCount_atTop.const_mul_atTop hc
      exact tendsto_neg_atTop_atBot.comp this
    exact hlim.eventually_le_const (by norm_num)
  filter_upwards [rvDeviationProb_le_exp hα0 hα1 hL hr0 hr1 hc₁, hsmall, hcsmall] with
    X hX hXs hXc
  have hP : rvDeviationProb α L X r ≤ 1 / 2 := le_trans hX hXs
  have hballmass : 1 - rvDeviationProb α L X r
      ≤ (rvLaw α L X (Metric.ball (0 : ℂ) r)).toReal := one_sub_le_rvLaw_ball_zero
  have hmono : (rvLaw α L X (Metric.ball (0 : ℂ) r)).toReal ≤ (rvLaw α L X G).toReal := by
    refine ENNReal.toReal_le_toReal (measure_ne_top _ _) (measure_ne_top _ _) |>.2 ?_
    exact measure_mono hball
  linarith [hP, hballmass, hmono, hXc]


/-- **The large-deviation lower bound for open sets.** -/
theorem rvLaw_lower {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ} (hL : IsSlowlyVarying L)
    (G : Set ℂ) (hG : IsOpen G) (z : ℂ) (hz : z ∈ G) (c : ℝ)
    (hc : rvPlanarRate α z < ENNReal.ofReal c) :
    ∀ᶠ X in atTop, Real.exp (-(c * rvPrimeCount X)) ≤ (rvLaw α L X G).toReal := by
  have hzlt : ‖z‖ < 1 := rvPlanarRate_ne_top_iff.1 (by
    intro htop
    rw [htop] at hc
    exact absurd hc (by simp))
  rw [rvPlanarRate_of_norm_lt_one hzlt] at hc
  have hcpos : 0 < c := by
    have h0 : (0 : ENNReal) < ENNReal.ofReal c :=
      lt_of_le_of_lt (bot_le : (0 : ENNReal) ≤ ENNReal.ofReal (rvRate α ‖z‖)) hc
    exact ENNReal.ofReal_pos.1 h0
  have hIc : rvRate α ‖z‖ < c := (ENNReal.ofReal_lt_ofReal_iff hcpos).1 hc
  by_cases hz0 : z = 0
  · subst hz0
    exact rvLaw_lower_zero hα0 hα1 hL G hG hz hcpos
  · have hr₀0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
    obtain ⟨r', hr'0, hr'⟩ := Metric.isOpen_iff.1 hG z hz
    set r : ℝ := min r' (1 - ‖z‖) with hrdef
    have hr0 : 0 < r := lt_min hr'0 (by linarith)
    have hrle : r ≤ 1 - ‖z‖ := min_le_right _ _
    have hball : Metric.ball z r ⊆ G := le_trans (Metric.ball_subset_ball (min_le_left _ _)) hr'
    have hmid1 : ‖z‖ < ‖z‖ + r / 2 := by linarith
    have hmid2 : ‖z‖ + r / 2 < 1 := by linarith
    have hstrict : rvRate α ‖z‖ < rvRate α (‖z‖ + r / 2) :=
      rvRate_strictMono hα0 hα1 hr₀0.le hmid1 hmid2
    obtain ⟨c₁, hc₁a, hc₁b⟩ := exists_between (lt_min hIc hstrict)
    have hc₁c : c₁ < c := lt_of_lt_of_le hc₁b (min_le_left _ _)
    have hc₁d : c₁ < rvRate α (‖z‖ + r / 2) := lt_of_lt_of_le hc₁b (min_le_right _ _)
    obtain ⟨c₂, hc₂a, hc₂b⟩ := exists_between hc₁d
    set K : ℕ := ⌈4 * Real.pi * ‖z‖ / r⌉₊ + 1 with hKdef
    have hK0 : 0 < K := Nat.succ_pos _
    have hKR : (0 : ℝ) < (K : ℝ) := by exact_mod_cast hK0
    have hKb : 4 * Real.pi * ‖z‖ / r < K := by
      have h1 : 4 * Real.pi * ‖z‖ / r ≤ (⌈4 * Real.pi * ‖z‖ / r⌉₊ : ℝ) := Nat.le_ceil _
      rw [hKdef]
      push_cast
      linarith
    have hhalf : ∀ᶠ X in atTop,
        Real.exp (-(c₂ * rvPrimeCount X)) ≤ (1 / 2) * Real.exp (-(c₁ * rvPrimeCount X)) := by
      have hlim : Tendsto (fun X : ℝ => Real.exp ((c₁ - c₂) * rvPrimeCount X)) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have hneg : c₁ - c₂ < 0 := by linarith
        simpa [mul_comm] using tendsto_rvPrimeCount_atTop.atTop_mul_const_of_neg hneg
      have hev := hlim.eventually_le_const (show (0:ℝ) < 1/2 by norm_num)
      filter_upwards [hev] with X hX
      have hid : Real.exp (-(c₂ * rvPrimeCount X))
          = Real.exp ((c₁ - c₂) * rvPrimeCount X) * Real.exp (-(c₁ * rvPrimeCount X)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hid]
      exact mul_le_mul_of_nonneg_right hX (Real.exp_pos _).le
    have hbig : ∀ᶠ X in atTop,
        (2 * K : ℝ) * Real.exp (-(c * rvPrimeCount X)) ≤ Real.exp (-(c₁ * rvPrimeCount X)) := by
      have hlim : Tendsto (fun X : ℝ => Real.exp ((c₁ - c) * rvPrimeCount X)) atTop (𝓝 0) := by
        refine Real.tendsto_exp_atBot.comp ?_
        have hneg : c₁ - c < 0 := by linarith
        simpa [mul_comm] using tendsto_rvPrimeCount_atTop.atTop_mul_const_of_neg hneg
      have hev := hlim.eventually_le_const (show (0:ℝ) < 1 / (2 * K) by positivity)
      filter_upwards [hev] with X hX
      have hid : Real.exp (-(c₁ * rvPrimeCount X))
          = Real.exp ((c - c₁) * rvPrimeCount X) * Real.exp (-(c * rvPrimeCount X)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [hid]
      have hinv : (2 * K : ℝ) ≤ Real.exp ((c - c₁) * rvPrimeCount X) := by
        have hpos : (0 : ℝ) < Real.exp ((c₁ - c) * rvPrimeCount X) := Real.exp_pos _
        have hneg : Real.exp ((c - c₁) * rvPrimeCount X)
            = (Real.exp ((c₁ - c) * rvPrimeCount X))⁻¹ := by
          rw [← Real.exp_neg]
          congr 1
          ring
        rw [hneg, le_inv_comm₀ (by positivity) hpos]
        rw [inv_eq_one_div]
        exact hX
      exact mul_le_mul_of_nonneg_right hinv (Real.exp_pos _).le
    filter_upwards [exp_le_rvDeviationProb hα0 hα1 hL hr₀0 hzlt hc₁a,
      rvDeviationProb_le_exp hα0 hα1 hL (by linarith : (0:ℝ) < ‖z‖ + r / 2) hmid2 hc₂b,
      hhalf, hbig, eventually_rvWeightSum_pos hα0 hα1 hL] with X hXlow hXup hXhalf hXbig hXW
    set μ : Measure (↥(rvPrimeFinset X) → PhaseCircle) :=
      Measure.pi fun _ : ↥(rvPrimeFinset X) => AddCircle.haarAddCircle with hμ
    set Y : (↥(rvPrimeFinset X) → PhaseCircle) → ℂ := steinhausSum (rvWeightFun α L X) with hY
    set A : Set (↥(rvPrimeFinset X) → PhaseCircle) :=
      {x | ‖z‖ ≤ ‖Y x‖ ∧ ‖Y x‖ ≤ ‖z‖ + r / 2} with hA
    have hsplit : {x | ‖z‖ ≤ ‖Y x‖} ⊆ A ∪ {x | ‖z‖ + r / 2 < ‖Y x‖} := by
      intro x hx
      rcases le_or_gt (‖Y x‖) (‖z‖ + r / 2) with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr h
    have hAle : μ {x | ‖z‖ ≤ ‖Y x‖} ≤ μ A + μ {x | ‖z‖ + r / 2 < ‖Y x‖} :=
      le_trans (measure_mono hsplit) (measure_union_le _ _)
    have hmono2 : μ {x | ‖z‖ + r / 2 < ‖Y x‖} ≤ μ {x | ‖z‖ + r / 2 ≤ ‖Y x‖} :=
      measure_mono (fun x hx => by
        rw [Set.mem_setOf_eq] at hx ⊢
        exact le_of_lt hx)
    have hAreal : rvDeviationProb α L X ‖z‖ - rvDeviationProb α L X (‖z‖ + r / 2)
        ≤ (μ A).toReal := by
      have h1 : (μ {x | ‖z‖ ≤ ‖Y x‖}).toReal
          ≤ (μ A).toReal + (μ {x | ‖z‖ + r / 2 ≤ ‖Y x‖}).toReal := by
        have hsum : μ {x | ‖z‖ ≤ ‖Y x‖} ≤ μ A + μ {x | ‖z‖ + r / 2 ≤ ‖Y x‖} :=
          le_trans hAle (add_le_add le_rfl hmono2)
        have := ENNReal.toReal_le_toReal (measure_ne_top μ _)
          (by exact ENNReal.add_ne_top.2 ⟨measure_ne_top μ _, measure_ne_top μ _⟩) |>.2 hsum
        rwa [ENNReal.toReal_add (measure_ne_top μ _) (measure_ne_top μ _)] at this
      rw [rvDeviationProb, rvDeviationProb, ← hμ, ← hY]
      linarith
    have hballK : (μ A).toReal ≤ (K : ℝ) * (μ {x | Y x ∈ Metric.ball z r}).toReal := by
      have hle := measure_annulus_le_nsmul (rvWeightFun α L X) hz0 hr0 hK0 hKb
      rw [← hμ, ← hY, ← hA] at hle
      have hfin : ((K : ENNReal) * μ {x | Y x ∈ Metric.ball z r}) ≠ ⊤ :=
        ENNReal.mul_ne_top (by simp) (measure_ne_top μ _)
      have := ENNReal.toReal_le_toReal (measure_ne_top μ _) hfin |>.2 hle
      rwa [ENNReal.toReal_mul, ENNReal.toReal_natCast] at this
    have hGmass : (μ {x | Y x ∈ Metric.ball z r}).toReal ≤ (rvLaw α L X G).toReal := by
      refine ENNReal.toReal_le_toReal (measure_ne_top μ _) (measure_ne_top _ _) |>.2 ?_
      rw [rvLaw_apply hG.measurableSet, ← hμ, ← hY]
      exact measure_mono fun x hx => hball hx
    have hchain : Real.exp (-(c * rvPrimeCount X)) ≤ (μ {x | Y x ∈ Metric.ball z r}).toReal := by
      have hmid : (1 / 2) * Real.exp (-(c₁ * rvPrimeCount X)) ≤ (μ A).toReal := by
        linarith [hAreal, hXlow, hXup, hXhalf]
      have hKpos : (0 : ℝ) < (K : ℝ) := hKR
      have hstep : Real.exp (-(c * rvPrimeCount X)) ≤ (μ A).toReal / K := by
        rw [le_div_iff₀ hKpos]
        have h2K : (2 * K : ℝ) * Real.exp (-(c * rvPrimeCount X))
            ≤ Real.exp (-(c₁ * rvPrimeCount X)) := hXbig
        nlinarith only [hmid, h2K, hKpos]
      have hdiv : (μ A).toReal / K ≤ (μ {x | Y x ∈ Metric.ball z r}).toReal := by
        rw [div_le_iff₀ hKpos]
        linarith [hballK]
      linarith [hstep, hdiv]
    linarith [hchain, hGmass]

/-- **The card's part `1`: the planar large deviation principle.** -/
theorem isLDP_rvLaw {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) {L : ℝ → ℝ} (hL : IsSlowlyVarying L) :
    IsLDP (rvLaw α L) rvPrimeCount (rvPlanarRate α) where
  upper := fun F hF c hc => rvLaw_upper hα0 hα1 hL F hF c hc
  lower := fun G hG z hz c hc => rvLaw_lower hα0 hα1 hL G hG z hz c hc

end

end RHTower
