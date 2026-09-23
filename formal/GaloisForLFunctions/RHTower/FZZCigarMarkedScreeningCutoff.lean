import GaloisForLFunctions.RHTower.FZZCigarContinuedScreeningMark

/-!
# Original marked screening cutoffs and derivative interchange

For both exponents in the first continuation strip, the original marked plane
integral is absolutely integrable at every pair of finite collision cutoffs.
Polar integration gives the exact logarithmic annulus primitive and its forced
local correction. Dominated convergence removes the two cutoffs independently
and retains the fixed exterior, recovering the original continued insertion.

An open exponential-moment interval then differentiates the actual finite-cutoff
family. Differentiating its two explicit power corrections and comparing the
original limits proves that the first exponent derivative commutes with this
fixed subtraction prescription. No interchange is assumed.

These results concern the displayed two-puncture position sector in (-3,-2).
Higher collision subtractions, the complete screening source, its physical
momentum identification, and the framed mixed Ward identity remain separate.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

private def radialMarkedPrimitive (q r : ℝ) : ℝ := r^q*(Real.log r/q-1/q^(2 : ℕ))

private theorem radialMarkedPrimitive_hasDerivAt (q r : ℝ) (hq : q ≠ 0) (hr : 0 < r) :
    HasDerivAt (radialMarkedPrimitive q) (r^(q-1)*Real.log r) r := by
  have hp : HasDerivAt (fun t : ℝ => t^q) (q*r^(q-1)) r :=
    Real.hasDerivAt_rpow_const (Or.inl hr.ne')
  have hl := ((Real.hasDerivAt_log hr.ne').div_const q).sub_const (1/q^(2 : ℕ))
  have hd := hp.mul hl
  have he : r^q = r^(q-1)*r := by
    calc
      r^q = r^((q-1)+1) := by congr 1; ring
      _ = r^(q-1)*r := by rw [Real.rpow_add hr, Real.rpow_one]
  convert! hd using 1
  rw [he]
  field_simp [hq,hr.ne']
  ring

private theorem radial_log_integral (q ε R : ℝ) (hq : q ≠ 0) (hε : 0 < ε) (hR : ε ≤ R) :
    (∫ r : ℝ in ε..R, r^(q-1)*Real.log r) =
      radialMarkedPrimitive q R-radialMarkedPrimitive q ε := by
  have hc : ContinuousOn (fun r : ℝ => r^(q-1)*Real.log r) (Icc ε R) := by
    intro r hr
    have hr0 : 0 < r := lt_of_lt_of_le hε hr.1
    have hp : HasDerivAt (fun t : ℝ => t^(q-1)) ((q-1)*r^(q-1-1)) r :=
      Real.hasDerivAt_rpow_const (Or.inl hr0.ne')
    exact (hp.continuousAt.mul (Real.hasDerivAt_log hr0.ne').continuousAt).continuousWithinAt
  have hi : IntervalIntegrable (fun r : ℝ => r^(q-1)*Real.log r) volume ε R :=
    hc.intervalIntegrable_of_Icc hR
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt _ hi
  intro r hr
  rw [uIcc_of_le hR] at hr
  exact radialMarkedPrimitive_hasDerivAt q r hq (lt_of_lt_of_le hε hr.1)


private theorem annular_marked_power_integral (α r : ℝ) (hr : 0 < r)
    (hrR : r ≤ 1/2) (ha : α+2 ≠ 0) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, Real.log ‖z‖*‖z‖^α) =
      2*Real.pi*(radialMarkedPrimitive (α+2) (1/2)-radialMarkedPrimitive (α+2) r) := by
  rw [← integral_indicator (measurableSet_ball.diff measurableSet_closedBall)]
  have he : ((ball 0 (1/2) \ closedBall 0 r).indicator
      (fun z : ℂ => Real.log ‖z‖*‖z‖^α)) =
      fun z : ℂ => (Ioo r (1/2)).indicator (fun y : ℝ => Real.log y*y^α) ‖z‖ := by
    funext z
    have hm : z ∈ ball (0 : ℂ) (1/2) \ closedBall 0 r ↔ ‖z‖ ∈ Ioo r (1/2) := by
      simp only [Set.mem_sdiff, mem_ball_zero_iff, mem_closedBall_zero_iff, not_le, mem_Ioo, and_comm]
    by_cases hz : z ∈ ball (0 : ℂ) (1/2) \ closedBall 0 r
    · rw [indicator_of_mem hz, indicator_of_mem (hm.mp hz)]
    · rw [indicator_of_notMem hz, indicator_of_notMem (mt hm.mpr hz)]
  rw [he, integral_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul, nsmul_eq_mul]
  have hv : (volume : Measure ℂ).real (ball 0 1) = Real.pi := by
    simp [Measure.real, Complex.volume_ball]
  rw [hv]
  have hf : (fun y : ℝ => y*(Ioo r (1/2)).indicator (fun t : ℝ => Real.log t*t^α) y) =
      (Ioo r (1/2)).indicator (fun y : ℝ => y^((α+2)-1)*Real.log y) := by
    funext y
    by_cases hy : y ∈ Ioo r (1/2)
    · simp only [indicator_of_mem hy]
      rw [show α+2-1=α+1 by ring, Real.rpow_add (hr.trans hy.1), Real.rpow_one]
      ring
    · simp only [indicator_of_notMem hy, mul_zero]
  rw [hf, setIntegral_indicator measurableSet_Ioo]
  have hs : Ioi (0 : ℝ) ∩ Ioo r (1/2) = Ioo r (1/2) :=
    inter_eq_right.mpr (fun y hy => hr.trans hy.1)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR,
    radial_log_integral (α+2) r (1/2) ha hr hrR]
  ring

private theorem marked_annular_integrable (α β r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel α β z)
      (ball 0 (1/2) \ closedBall 0 r) ∧
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*‖z‖^α)
      (ball 0 (1/2) \ closedBall 0 r) := by
  let K : Set ℂ := closedBall 0 (1/2) \ ball 0 r
  have hk : IsCompact K := (isCompact_closedBall (0 : ℂ) (1/2)).diff isOpen_ball
  have hn : ∀ z ∈ K, ‖z‖ ≠ 0 := by
    intro z hz he
    have hz0 : z = 0 := norm_eq_zero.mp he
    subst z
    exact hz.2 (by simpa using hr)
  have hc : ContinuousOn (fun z : ℂ => ‖z‖^α) K :=
    continuous_norm.continuousOn.rpow_const (fun z hz => Or.inl (hn z hz))
  have hl : ContinuousOn (fun z : ℂ => Real.log ‖z‖) K :=
    continuous_norm.continuousOn.log hn
  have hc' : ContinuousOn (fun z : ℂ => ‖z-1‖^β) K := by
    apply ContinuousOn.rpow_const (by fun_prop)
    intro z hz
    left
    intro he
    have hz1 : z = 1 := sub_eq_zero.mp (norm_eq_zero.mp he)
    have hz0 := hz.1
    rw [hz1] at hz0
    norm_num [mem_closedBall, dist_eq_norm] at hz0
  have hs : ball (0 : ℂ) (1/2) \ closedBall 0 r ⊆ K := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
  exact ⟨((hl.mul (hc.mul hc')).integrableOn_compact hk).mono_set hs,
    ((hl.mul hc).integrableOn_compact hk).mono_set hs⟩

private theorem marked_cutoff_split (α β r : ℝ) (hr : 0 < r) (hrR : r ≤ 1/2)
    (ha : α+2 ≠ 0) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, Real.log ‖z‖*fzzScreeningPlaneKernel α β z) +
      2*Real.pi*radialMarkedPrimitive (α+2) r =
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, Real.log ‖z‖*fzzScreeningZeroSubtracted α β z) +
      2*Real.pi*radialMarkedPrimitive (α+2) (1/2) := by
  have hi := marked_annular_integrable α β r hr
  have he : (fun z => Real.log ‖z‖*fzzScreeningZeroSubtracted α β z) =
      fun z => Real.log ‖z‖*fzzScreeningPlaneKernel α β z - Real.log ‖z‖*‖z‖^α := by
    funext z
    dsimp [fzzScreeningZeroSubtracted, fzzScreeningPlaneKernel]
    ring
  rw [he, integral_sub hi.1 hi.2, annular_marked_power_integral α r hr hrR ha]
  ring

private theorem marked_shrinking_hole (f : ℂ → ℝ) (c : ℂ)
    (hi : IntegrableOn f (ball c (1/2))) (hc : f c = 0) :
    Tendsto (fun T : ℝ => ∫ z : ℂ in ball c (1/2) \ closedBall c (Real.exp (-T)), f z)
      atTop (𝓝 (∫ z : ℂ in ball c (1/2), f z)) := by
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.restrict (ball c (1/2)))
    (F := fun T : ℝ => (closedBall c (Real.exp (-T)))ᶜ.indicator f)
    (f := f) (fun z => ‖f z‖)
    (Eventually.of_forall (fun T => hi.aestronglyMeasurable.indicator measurableSet_closedBall.compl))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun z => by
      by_cases hz : z ∈ (closedBall c (Real.exp (-T)))ᶜ
      · simp [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]))) hi.norm ?_
  · simpa only [setIntegral_indicator measurableSet_closedBall.compl, ← Set.sdiff_eq] using hd
  · apply Eventually.of_forall
    intro z
    by_cases hz : z = c
    · subst z
      have he : (fun T : ℝ => (closedBall c (Real.exp (-T)))ᶜ.indicator f c) = fun _ => (0 : ℝ) := by
        funext T
        by_cases hm : c ∈ (closedBall c (Real.exp (-T)))ᶜ
        · rw [indicator_of_mem hm, hc]
        · rw [indicator_of_notMem hm]
      rw [he, hc]
      exact tendsto_const_nhds
    · have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < dist z c :=
        Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (dist_pos.mpr hz))
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with T hT
      rw [indicator_of_mem]
      simpa only [mem_compl_iff, mem_closedBall, not_le] using hT


private theorem first_power_lt (u : ℝ) : fzzScreeningFirstContinuationPower u < -2 := by
  unfold fzzScreeningFirstContinuationPower
  have h : 0 < (1+Real.exp u)⁻¹ := inv_pos.mpr (by positivity)
  linarith

/-- The original marked plane integral with two independent collision cutoffs. -/
def fzzScreeningPlaneMarkedCutoff (α β T U : ℝ) : ℝ :=
  ∫ z : ℂ in fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U)),
    Real.log ‖z‖*fzzScreeningPlaneKernel α β z

/-- Every finite original marked cutoff is absolutely integrable. -/
theorem fzzScreeningPlaneMarkedCutoff_integrable (u v T U : ℝ) :
    IntegrableOn (fun z : ℂ => Real.log ‖z‖*fzzScreeningPlaneKernel
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
      (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U))) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have h0 := (marked_annular_integrable α β (Real.exp (-T)) (Real.exp_pos _)).1
  have h1 := (fzzScreeningPlaneContinuedMark_integrable u v).2.1
  have he := (fzzScreeningPlaneContinuedMark_integrable u v).2.2
  apply ((h0.union h1).union he).mono_set
  intro z hz
  by_cases hz0 : z ∈ ball (0 : ℂ) (1/2)
  · exact Or.inl (Or.inl ⟨hz0, fun h => hz (Or.inl h)⟩)
  · by_cases hz1 : z ∈ ball (1 : ℂ) (1/2)
    · exact Or.inl (Or.inr hz1)
    · exact Or.inr (by rintro (h|h); exact hz0 h; exact hz1 h)

/-- The zero-collision logarithmic integral has the stated corrected original cutoff limit after
retaining the differentiated local power correction. -/
theorem fzzScreeningZeroMark_cutoff_limit (u v : ℝ) :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
        Real.log ‖z‖*fzzScreeningPlaneKernel
          (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) +
      fzzScreeningPowerCountertermMark (Real.exp (-T)) (fzzScreeningFirstContinuationPower u))
      atTop (𝓝 ((∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningZeroSubtracted
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) +
        fzzScreeningPowerCountertermMark (1/2) (fzzScreeningFirstContinuationPower u))) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have hi := (fzzScreeningPlaneContinuedMark_integrable u v).1
  have h := (marked_shrinking_hole (fun z => Real.log ‖z‖*fzzScreeningZeroSubtracted α β z)
    0 hi (by simp)).add_const (fzzScreeningPowerCountertermMark (1/2) α)
  apply h.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < 1/2 :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [he] with T hT
  have hs := marked_cutoff_split α β (Real.exp (-T)) (Real.exp_pos _) hT.le
    (by have hα := first_power_lt u; dsimp [α]; linarith)
  simpa only [radialMarkedPrimitive, fzzScreeningPowerCountertermMark, mul_assoc] using hs.symm

/-- The mark vanishes to first order at the other puncture, so no alpha derivative
of its beta-only counterterm is needed. -/
theorem fzzScreeningOneMark_cutoff_limit (u v : ℝ) :
    Tendsto (fun U : ℝ =>
      ∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-U)),
        Real.log ‖z‖*fzzScreeningPlaneKernel
          (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
      atTop (𝓝 (∫ z : ℂ in ball 1 (1/2), Real.log ‖z‖*fzzScreeningPlaneKernel
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)) :=
  marked_shrinking_hole _ 1 (fzzScreeningPlaneContinuedMark_integrable u v).2.1 (by simp)

private theorem marked_disks_disjoint :
    Disjoint (ball (0 : ℂ) (1/2)) (ball 1 (1/2)) :=
  ball_disjoint_ball (by norm_num [dist_eq_norm])

private theorem marked_domain_split (r s : ℝ) (hr : r < 1/2) (hs : s < 1/2) :
    fzzScreeningPlaneCutoffDomain r s =
      ((ball 0 (1/2) \ closedBall 0 r) ∪ (ball 1 (1/2) \ closedBall 1 s)) ∪
        fzzScreeningPlaneExterior := by
  have h0 : closedBall (0 : ℂ) r ⊆ ball 0 (1/2) := closedBall_subset_ball hr
  have h1 : closedBall (1 : ℂ) s ⊆ ball 1 (1/2) := closedBall_subset_ball hs
  have hd := Set.disjoint_left.mp marked_disks_disjoint
  ext z
  constructor
  · intro hz
    by_cases hz0 : z ∈ ball (0 : ℂ) (1/2)
    · exact Or.inl (Or.inl ⟨hz0, fun h => hz (Or.inl h)⟩)
    · by_cases hz1 : z ∈ ball (1 : ℂ) (1/2)
      · exact Or.inl (Or.inr ⟨hz1, fun h => hz (Or.inr h)⟩)
      · exact Or.inr (by rintro (h|h); exact hz0 h; exact hz1 h)
  · rintro ((hz|hz)|hz) (h|h)
    · exact hz.2 h
    · exact hd hz.1 (h1 h)
    · exact hd (h0 h) hz.1
    · exact hz.2 h
    · exact hz (Or.inl (h0 h))
    · exact hz (Or.inr (h1 h))

private theorem marked_integral_split (u v T U : ℝ)
    (hT : Real.exp (-T) < 1/2) (hU : Real.exp (-U) < 1/2) :
    fzzScreeningPlaneMarkedCutoff (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v) T U =
      ((∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)), Real.log ‖z‖*
        fzzScreeningPlaneKernel (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) +
       (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-U)), Real.log ‖z‖*
        fzzScreeningPlaneKernel (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)) +
       (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*
        fzzScreeningPlaneKernel (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) := by
  unfold fzzScreeningPlaneMarkedCutoff
  rw [marked_domain_split _ _ hT hU]
  have ha := (marked_annular_integrable (fzzScreeningFirstContinuationPower u)
    (fzzScreeningFirstContinuationPower v) (Real.exp (-T)) (Real.exp_pos _)).1
  have hb := (fzzScreeningPlaneContinuedMark_integrable u v).2.1.mono_set
    (Set.sdiff_subset : ball (1 : ℂ) (1/2) \ closedBall 1 (Real.exp (-U)) ⊆ ball 1 (1/2))
  have hd : Disjoint ((ball (0 : ℂ) (1/2) \ closedBall 0 (Real.exp (-T))) ∪
      (ball 1 (1/2) \ closedBall 1 (Real.exp (-U)))) fzzScreeningPlaneExterior := by
    apply Set.disjoint_left.mpr
    rintro z (hz|hz) he
    · exact he (Or.inl hz.1)
    · exact he (Or.inr hz.1)
  rw [setIntegral_union hd ((measurableSet_ball.union measurableSet_ball).compl)
    (ha.union hb) (fzzScreeningPlaneContinuedMark_integrable u v).2.2]
  rw [setIntegral_union (marked_disks_disjoint.mono Set.sdiff_subset Set.sdiff_subset)
    (measurableSet_ball.diff measurableSet_closedBall) ha hb]

/-- Independent removal of both original marked collision cutoffs recovers the
actual continued derivative, with its differentiated subtraction term. -/
theorem fzzScreeningPlaneContinuedMark_independent_cutoff_limit (u v : ℝ) :
    Tendsto (fun p : ℝ × ℝ =>
      fzzScreeningPlaneMarkedCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) p.1 p.2 +
      fzzScreeningPowerCountertermMark (Real.exp (-p.1)) (fzzScreeningFirstContinuationPower u))
      (atTop ×ˢ atTop) (𝓝 (fzzScreeningPlaneContinuedMark
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v))) := by
  have hf : Tendsto (Prod.fst : ℝ × ℝ → ℝ) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hg : Tendsto (Prod.snd : ℝ × ℝ → ℝ) (atTop ×ˢ atTop) atTop := tendsto_snd
  have h0 := (fzzScreeningZeroMark_cutoff_limit u v).comp hf
  have h1 := (fzzScreeningOneMark_cutoff_limit u v).comp hg
  have h := (h0.add h1).add_const (∫ z : ℂ in fzzScreeningPlaneExterior,
    Real.log ‖z‖*fzzScreeningPlaneKernel
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)
  have hlim : ((∫ z : ℂ in ball 0 (1/2), Real.log ‖z‖*fzzScreeningZeroSubtracted
      (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) +
      fzzScreeningPowerCountertermMark (1/2) (fzzScreeningFirstContinuationPower u) +
      (∫ z : ℂ in ball 1 (1/2), Real.log ‖z‖*fzzScreeningPlaneKernel
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z)) +
      (∫ z : ℂ in fzzScreeningPlaneExterior, Real.log ‖z‖*fzzScreeningPlaneKernel
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) z) =
      fzzScreeningPlaneContinuedMark (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) := by
    unfold fzzScreeningPlaneContinuedMark
    ring
  rw [hlim] at h
  apply h.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < 1/2 :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hf.eventually he, hg.eventually he] with p hp0 hp1
  dsimp only [Function.comp_apply]
  rw [marked_integral_split u v p.1 p.2 hp0 hp1]
  ring

set_option maxHeartbeats 800000 in
/-- The synchronized cutoff is a specialization of the independent two-cutoff limit. -/
theorem fzzScreeningPlaneContinuedMark_cutoff_limit (u v : ℝ) :
    Tendsto (fun T : ℝ =>
      fzzScreeningPlaneMarkedCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) T T +
      fzzScreeningPowerCountertermMark (Real.exp (-T)) (fzzScreeningFirstContinuationPower u))
      atTop (𝓝 (fzzScreeningPlaneContinuedMark
        (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v))) :=
by
  have hd : Tendsto (fun T : ℝ => (T,T)) atTop (atTop ×ˢ atTop) :=
    tendsto_id.prodMk tendsto_id
  have h := (fzzScreeningPlaneContinuedMark_independent_cutoff_limit u v).comp hd
  simpa only [Function.comp_def] using h


private def markedCutoffMeasure (α β T U : ℝ) : Measure ℂ :=
  (volume.restrict (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U)))).withDensity
    (fun z => ENNReal.ofReal (fzzScreeningPlaneKernel α β z))

private theorem marked_kernel_nonneg (α β : ℝ) (z : ℂ) :
    0 ≤ fzzScreeningPlaneKernel α β z := by
  unfold fzzScreeningPlaneKernel
  positivity

private theorem markedCutoffMeasure_integrable_iff (α β T U : ℝ) (f : ℂ → ℝ) :
    Integrable f (markedCutoffMeasure α β T U) ↔
      IntegrableOn (fun z => fzzScreeningPlaneKernel α β z*f z)
        (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U))) := by
  rw [markedCutoffMeasure, integrable_withDensity_iff_integrable_smul'
    (by unfold fzzScreeningPlaneKernel; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  simp only [ENNReal.toReal_ofReal (marked_kernel_nonneg α β _),
    smul_eq_mul]
  rfl

private theorem markedCutoffMeasure_integral (α β T U : ℝ) (f : ℂ → ℝ) :
    (∫ z, f z ∂markedCutoffMeasure α β T U) =
      ∫ z : ℂ in fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U)),
        fzzScreeningPlaneKernel α β z*f z := by
  rw [markedCutoffMeasure, integral_withDensity_eq_integral_toReal_smul
    (by unfold fzzScreeningPlaneKernel; fun_prop)
    (by filter_upwards with z; exact ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards with z
  rw [ENNReal.toReal_ofReal (show 0 ≤ fzzScreeningPlaneKernel α β z
    from mul_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _)), smul_eq_mul]

private theorem marked_kernel_shift (α β δ : ℝ) {z : ℂ} (hz : z ≠ 0) :
    fzzScreeningPlaneKernel α β z*Real.exp (δ*Real.log ‖z‖) =
      fzzScreeningPlaneKernel (α+δ) β z := by
  unfold fzzScreeningPlaneKernel
  rw [Real.rpow_add (norm_pos_iff.mpr hz), Real.rpow_def_of_pos (norm_pos_iff.mpr hz) δ]
  rw [mul_comm (Real.log ‖z‖) δ]
  ring

private theorem marked_first_range (u : ℝ) :
    -3 < fzzScreeningFirstContinuationPower u ∧ fzzScreeningFirstContinuationPower u < -2 := by
  have hden : 0 < 1+Real.exp u := by positivity
  have hp := inv_pos.mpr hden
  have hlt : (1+Real.exp u)⁻¹ < 1 := (inv_lt_one₀ hden).mpr (by linarith [Real.exp_pos u])
  unfold fzzScreeningFirstContinuationPower
  constructor <;> linarith

private theorem marked_first_surjective (α : ℝ) (ha : -3 < α) (ha2 : α < -2) :
    ∃ u : ℝ, fzzScreeningFirstContinuationPower u = α := by
  have hp : 0 < (α+3)/(-α-2) := div_pos (by linarith) (by linarith)
  refine ⟨Real.log ((α+3)/(-α-2)), ?_⟩
  unfold fzzScreeningFirstContinuationPower
  rw [Real.exp_log hp]
  have hh : 1+(α+3)/(-α-2) = 1/(-α-2) := by
    field_simp [show -α-2 ≠ 0 by linarith]; ring
  rw [hh, one_div, inv_inv]
  ring

private theorem markedCutoff_exp_interior (u v T U : ℝ) :
    (0 : ℝ) ∈ interior (ProbabilityTheory.integrableExpSet (fun z : ℂ => Real.log ‖z‖)
      (markedCutoffMeasure (fzzScreeningFirstContinuationPower u) (fzzScreeningFirstContinuationPower v) T U)) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have ha := marked_first_range u
  have hn : ∀ᶠ δ : ℝ in 𝓝 0, α+δ ∈ Ioo (-3) (-2) :=
    (isOpen_Ioo.preimage (show Continuous (fun δ : ℝ => α+δ) by fun_prop)).mem_nhds
      (by simpa using ha)
  apply mem_interior_iff_mem_nhds.mpr
  filter_upwards [hn] with δ hδ
  change Integrable (fun z : ℂ => Real.exp (δ*Real.log ‖z‖)) (markedCutoffMeasure α β T U)
  rw [markedCutoffMeasure_integrable_iff]
  obtain ⟨w,hw⟩ := marked_first_surjective (α+δ) hδ.1 hδ.2
  have hi := fzzScreeningPlaneCutoff_integrable w v T U
  rw [hw] at hi
  apply hi.congr
  filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
  exact (marked_kernel_shift α β δ hz).symm

/-- The original finite-cutoff family differentiates to the admitted original mark. -/
theorem fzzScreeningPlaneCutoff_hasDerivAt (u v T U : ℝ) :
    HasDerivAt (fun a => fzzScreeningPlaneCutoff a (fzzScreeningFirstContinuationPower v) T U)
      (fzzScreeningPlaneMarkedCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) T U) (fzzScreeningFirstContinuationPower u) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have hd := ProbabilityTheory.hasDerivAt_mgf (markedCutoff_exp_interior u v T U)
  have he : ProbabilityTheory.mgf (fun z : ℂ => Real.log ‖z‖) (markedCutoffMeasure α β T U) =
      fun δ => fzzScreeningPlaneCutoff (α+δ) β T U := by
    funext δ
    rw [ProbabilityTheory.mgf, markedCutoffMeasure_integral]
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae (volume.ae_ne (0 : ℂ))] with z hz
    exact marked_kernel_shift α β δ hz
  change HasDerivAt (ProbabilityTheory.mgf (fun z : ℂ => Real.log ‖z‖)
    (markedCutoffMeasure α β T U)) _ 0 at hd
  rw [he, markedCutoffMeasure_integral] at hd
  simp only [zero_mul, Real.exp_zero, mul_one] at hd
  have hemark : (∫ z : ℂ in fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U)),
      fzzScreeningPlaneKernel α β z*Real.log ‖z‖) = fzzScreeningPlaneMarkedCutoff α β T U := by
    apply integral_congr_ae
    filter_upwards with z
    exact mul_comm _ _
  rw [hemark] at hd
  have hsub : HasDerivAt (fun a : ℝ => a-α) 1 α := by
    simpa using (hasDerivAt_id α).sub_const α
  have h := hd.comp_of_eq α hsub (sub_self α).symm
  convert! h using 1
  · ext a
    dsimp only [Function.comp_apply]
    congr 1
    ring
  · simp only [mul_one]
    rfl

private theorem marked_power_counterterm_hasDerivAt (r α : ℝ) (hr : 0 < r) (ha : α+2 ≠ 0) :
    HasDerivAt (fun a => 2*Real.pi*r^(a+2)/(a+2))
      (fzzScreeningPowerCountertermMark r α) α := by
  have hi : HasDerivAt (fun a : ℝ => a+2) 1 α := by
    simpa using (hasDerivAt_id α).add_const 2
  have hd := ((HasDerivAt.const_rpow hr hi).const_mul (2*Real.pi)).div hi ha
  convert! hd using 1
  unfold fzzScreeningPowerCountertermMark
  field_simp

/-- The finite corrected original source retains both unmarked collision counterterms. -/
def fzzScreeningPlaneCorrectedCutoff (α β T U : ℝ) : ℝ :=
  fzzScreeningPlaneCutoff α β T U + 2*Real.pi*(Real.exp (-T))^(α+2)/(α+2) +
    2*Real.pi*(Real.exp (-U))^(β+2)/(β+2)

/-- Differentiate the actual finite corrected source before taking its limit. -/
theorem fzzScreeningPlaneCorrectedCutoff_hasDerivAt (u v T U : ℝ) :
    HasDerivAt (fun a => fzzScreeningPlaneCorrectedCutoff a (fzzScreeningFirstContinuationPower v) T U)
      (fzzScreeningPlaneMarkedCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) T U +
        fzzScreeningPowerCountertermMark (Real.exp (-T)) (fzzScreeningFirstContinuationPower u))
      (fzzScreeningFirstContinuationPower u) := by
  have ha : fzzScreeningFirstContinuationPower u+2 ≠ 0 := by
    have hu := first_power_lt u
    linarith
  exact ((fzzScreeningPlaneCutoff_hasDerivAt u v T U).add
    (marked_power_counterterm_hasDerivAt (Real.exp (-T)) _ (Real.exp_pos _) ha)).add_const _

/-- For the original source and its fixed counterterms, taking the independent cutoff
limit commutes with the first exponent derivative. No interchange is assumed. -/
theorem fzzScreeningPlaneCorrectedCutoff_deriv_limit (u v : ℝ) :
    Tendsto (fun p : ℝ × ℝ => deriv (fun a =>
      fzzScreeningPlaneCorrectedCutoff a (fzzScreeningFirstContinuationPower v) p.1 p.2)
      (fzzScreeningFirstContinuationPower u)) (atTop ×ˢ atTop)
      (𝓝 (deriv (fun a => fzzScreeningPlaneFinitePart a (fzzScreeningFirstContinuationPower v))
        (fzzScreeningFirstContinuationPower u))) := by
  simp_rw [(fzzScreeningPlaneCorrectedCutoff_hasDerivAt u v _ _).deriv,
    (fzzScreeningPlaneFinitePart_hasDerivAt u v).deriv]
  exact fzzScreeningPlaneContinuedMark_independent_cutoff_limit u v

end GaloisForLFunctions.RHTower
