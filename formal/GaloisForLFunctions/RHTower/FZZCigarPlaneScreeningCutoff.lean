import GaloisForLFunctions.RHTower.FZZCigarScreeningCollisionFinitePart
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Whole-plane screening cutoffs with both collision terms

The original two-puncture plane kernel is integrable outside the fixed collision
circles whenever its total radial power is below -2. Every positive pair of
collision cutoffs gives an ordinary integrable whole-plane source in the first
continuation strip. The exact domain split retains the exterior and both annuli.

For independent exponents in (-3,-2), the original whole-plane cutoff integral,
plus the two previously proved local power counterterms, converges as the two
cutoffs shrink independently. Its limit is the sum of both local finite parts and
the unchanged exterior integral. Equal-radius removal follows by composition.

This identifies the actual global cutoff prescription. It does not yet identify
it with the analytically continued Gamma ratio, justify parameter derivatives
through that continuation, or produce the complete FZZ Ward identity. No RH
statement, source stationarity, or physical phase-frame assumption is used.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.RHTower

/-- The whole exterior of the two fixed collision disks. -/
def fzzScreeningPlaneExterior : Set ℂ := (ball 0 (1/2) ∪ ball 1 (1/2))ᶜ

private theorem exterior_closed : IsClosed fzzScreeningPlaneExterior :=
  (isOpen_ball.union isOpen_ball).isClosed_compl

private theorem exterior_ne {z : ℂ} (hz : z ∈ fzzScreeningPlaneExterior) : z ≠ 0 ∧ z ≠ 1 := by
  constructor
  · intro h
    subst z
    simp [fzzScreeningPlaneExterior] at hz
  · intro h
    subst z
    simp [fzzScreeningPlaneExterior] at hz

private theorem plane_tail_power (q : ℝ) (hq : q < -2) :
    IntegrableOn (fun z : ℂ => ‖z‖^q) {z | 2 < ‖z‖} := by
  have hm : MeasurableSet {z : ℂ | 2 < ‖z‖} := isOpen_lt continuous_const continuous_norm |>.measurableSet
  rw [← integrable_indicator_iff hm]
  have he : ({z : ℂ | 2 < ‖z‖}.indicator (fun z : ℂ => ‖z‖^q)) =
      fun z : ℂ => (Ioi (2 : ℝ)).indicator (fun r : ℝ => r^q) ‖z‖ := by
    funext z
    rfl
  rw [he, integrable_fun_norm_addHaar (volume : Measure ℂ)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  have hh : (fun r : ℝ => r*(Ioi (2 : ℝ)).indicator (fun r : ℝ => r^q) r) =
      (Ioi (2 : ℝ)).indicator (fun r : ℝ => r^(q+1)) := by
    funext r
    by_cases hr : r ∈ Ioi (2 : ℝ)
    · rw [indicator_of_mem hr, indicator_of_mem hr]
      rw [Real.rpow_add (by linarith [show 2 < r from hr]), Real.rpow_one, mul_comm]
    · rw [indicator_of_notMem hr, indicator_of_notMem hr, mul_zero]
  rw [hh, integrableOn_indicator_iff measurableSet_Ioi]
  have hs : Ioi (2 : ℝ) ∩ Ioi 0 = Ioi 2 := inter_eq_left.mpr (by intro r hr; change 0 < r; linarith [show 2 < r from hr])
  rw [hs]
  exact integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)

private theorem tail_kernel_bound (α β : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 2 < ‖z‖ →
      ‖fzzScreeningPlaneKernel α β z‖ ≤ C*‖z‖^(α+β) := by
  by_cases hb : 0 ≤ β
  · refine ⟨(2 : ℝ)^β, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    intro z hz
    have hn : 0 < ‖z‖ := by linarith
    have hupper : ‖z-1‖ ≤ 2*‖z‖ := by
      have h := norm_sub_le z (1 : ℂ)
      simp only [norm_one] at h
      linarith
    have hp := Real.rpow_le_rpow (norm_nonneg (z-1)) hupper hb
    have hk : 0 ≤ fzzScreeningPlaneKernel α β z := by unfold fzzScreeningPlaneKernel; positivity
    rw [Real.norm_of_nonneg hk, fzzScreeningPlaneKernel]
    calc
      _ ≤ ‖z‖^α*(2*‖z‖)^β := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hn.le, Real.rpow_add hn]; ring
  · refine ⟨(1/2 : ℝ)^β, Real.rpow_pos_of_pos (by norm_num) _, ?_⟩
    intro z hz
    have hn : 0 < ‖z‖ := by linarith
    have hlower : (1/2 : ℝ)*‖z‖ ≤ ‖z-1‖ := by
      have h := norm_sub_norm_le z (1 : ℂ)
      simp only [norm_one] at h
      linarith
    have hp := Real.rpow_le_rpow_of_nonpos (mul_pos (by norm_num) hn) hlower (le_of_not_ge hb)
    have hk : 0 ≤ fzzScreeningPlaneKernel α β z := by unfold fzzScreeningPlaneKernel; positivity
    rw [Real.norm_of_nonneg hk, fzzScreeningPlaneKernel]
    calc
      _ ≤ ‖z‖^α*((1/2 : ℝ)*‖z‖)^β := mul_le_mul_of_nonneg_left hp (Real.rpow_nonneg hn.le _)
      _ = _ := by rw [Real.mul_rpow (by norm_num) hn.le, Real.rpow_add hn]; ring

private theorem exterior_integrable (α β : ℝ) (hs : α+β < -2) :
    IntegrableOn (fzzScreeningPlaneKernel α β) fzzScreeningPlaneExterior := by
  obtain ⟨C,hC,hbound⟩ := tail_kernel_bound α β
  have hi : IntegrableOn (fzzScreeningPlaneKernel α β) {z : ℂ | 2 < ‖z‖} := by
    apply ((plane_tail_power (α+β) hs).const_mul C).mono' (by unfold fzzScreeningPlaneKernel; fun_prop)
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz
    exact hbound z hz
  let K := closedBall (0 : ℂ) 3 ∩ fzzScreeningPlaneExterior
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 3).inter_right exterior_closed
  have hc : ContinuousOn (fzzScreeningPlaneKernel α β) K := by
    apply ContinuousOn.mul
    · apply continuous_norm.continuousOn.rpow_const
      intro z hz
      exact Or.inl (norm_ne_zero_iff.mpr (exterior_ne hz.2).1)
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro z hz
      exact Or.inl (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (exterior_ne hz.2).2))
  have hk : IntegrableOn (fzzScreeningPlaneKernel α β) K (volume : Measure ℂ) := hc.integrableOn_compact hK
  apply (hk.union hi).mono_set
  intro z hz
  by_cases hn : ‖z‖ ≤ 3
  · exact Or.inl ⟨by simpa [mem_closedBall, dist_eq_norm] using hn, hz⟩
  · exact Or.inr (by change 2 < ‖z‖; have hn' := lt_of_not_ge hn; linarith)



/-- The actual plane with two independently removed closed collision disks. -/
def fzzScreeningPlaneCutoffDomain (r s : ℝ) : Set ℂ :=
  (closedBall 0 r ∪ closedBall 1 s)ᶜ

private theorem cutoff_integrable (α β r s : ℝ) (hs : α+β < -2)
    (hr : 0 < r) (ht : 0 < s) :
    IntegrableOn (fzzScreeningPlaneKernel α β) (fzzScreeningPlaneCutoffDomain r s) := by
  obtain ⟨C,hC,hbound⟩ := tail_kernel_bound α β
  have hi : IntegrableOn (fzzScreeningPlaneKernel α β) {z : ℂ | 2 < ‖z‖} := by
    apply ((plane_tail_power (α+β) hs).const_mul C).mono' (by unfold fzzScreeningPlaneKernel; fun_prop)
    filter_upwards [ae_restrict_mem (isOpen_lt continuous_const continuous_norm).measurableSet] with z hz
    exact hbound z hz
  let K := closedBall (0 : ℂ) 3 \ (ball 0 r ∪ ball 1 s)
  have hK : IsCompact K := (isCompact_closedBall (0 : ℂ) 3).diff (isOpen_ball.union isOpen_ball)
  have hn : ∀ z ∈ K, z ≠ 0 ∧ z ≠ 1 := by
    intro z hz
    constructor
    · intro he
      subst z
      exact hz.2 (Or.inl (by simpa using hr))
    · intro he
      subst z
      exact hz.2 (Or.inr (by simpa using ht))
  have hc : ContinuousOn (fzzScreeningPlaneKernel α β) K := by
    apply ContinuousOn.mul
    · exact continuous_norm.continuousOn.rpow_const
        (fun z hz => Or.inl (norm_ne_zero_iff.mpr (hn z hz).1))
    · apply ContinuousOn.rpow_const (by fun_prop)
      intro z hz
      exact Or.inl (norm_ne_zero_iff.mpr (sub_ne_zero.mpr (hn z hz).2))
  have hk : IntegrableOn (fzzScreeningPlaneKernel α β) K (volume : Measure ℂ) := hc.integrableOn_compact hK
  apply (hk.union hi).mono_set
  intro z hz
  by_cases hz3 : ‖z‖ ≤ 3
  · refine Or.inl ⟨by simpa [mem_closedBall, dist_eq_norm] using hz3, ?_⟩
    rintro (h0|h1)
    · exact hz (Or.inl (ball_subset_closedBall h0))
    · exact hz (Or.inr (ball_subset_closedBall h1))
  · exact Or.inr (by change 2 < ‖z‖; have h := lt_of_not_ge hz3; linarith)

private theorem collision_disks_disjoint :
    Disjoint (ball (0 : ℂ) (1/2)) (ball 1 (1/2)) :=
  ball_disjoint_ball (by norm_num [dist_eq_norm])

private theorem cutoff_domain_split (r s : ℝ) (hr : r < 1/2) (hs : s < 1/2) :
    fzzScreeningPlaneCutoffDomain r s =
      ((ball 0 (1/2) \ closedBall 0 r) ∪ (ball 1 (1/2) \ closedBall 1 s)) ∪
        fzzScreeningPlaneExterior := by
  have h0 : closedBall (0 : ℂ) r ⊆ ball 0 (1/2) := closedBall_subset_ball hr
  have h1 : closedBall (1 : ℂ) s ⊆ ball 1 (1/2) := closedBall_subset_ball hs
  have hd := Set.disjoint_left.mp collision_disks_disjoint
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

private theorem cutoff_integral_split (α β r s : ℝ) (hsum : α+β < -2)
    (hr : 0 < r) (hs : 0 < s) (hrR : r < 1/2) (hsR : s < 1/2) :
    (∫ z : ℂ in fzzScreeningPlaneCutoffDomain r s, fzzScreeningPlaneKernel α β z) =
      ((∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, fzzScreeningPlaneKernel α β z) +
       (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 s, fzzScreeningPlaneKernel α β z)) +
       (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z) := by
  have he := cutoff_domain_split r s hrR hsR
  have hi := cutoff_integrable α β r s hsum hr hs
  rw [he] at hi ⊢
  have ha := hi.mono_set (show ball (0 : ℂ) (1/2) \ closedBall 0 r ⊆
      ((ball 0 (1/2) \ closedBall 0 r) ∪ (ball 1 (1/2) \ closedBall 1 s)) ∪
      fzzScreeningPlaneExterior from fun z hz => Or.inl (Or.inl hz))
  have hb := hi.mono_set (show ball (1 : ℂ) (1/2) \ closedBall 1 s ⊆
      ((ball 0 (1/2) \ closedBall 0 r) ∪ (ball 1 (1/2) \ closedBall 1 s)) ∪
      fzzScreeningPlaneExterior from fun z hz => Or.inl (Or.inr hz))
  have hd : Disjoint ((ball (0 : ℂ) (1/2) \ closedBall 0 r) ∪
      (ball 1 (1/2) \ closedBall 1 s)) fzzScreeningPlaneExterior := by
    apply Set.disjoint_left.mpr
    rintro z (hz|hz) he
    · exact he (Or.inl hz.1)
    · exact he (Or.inr hz.1)
  rw [setIntegral_union hd exterior_closed.measurableSet (ha.union hb)
    (exterior_integrable α β hsum)]
  rw [setIntegral_union (collision_disks_disjoint.mono Set.sdiff_subset Set.sdiff_subset)
    (measurableSet_ball.diff measurableSet_closedBall) ha hb]

private theorem continuation_power_lt (u : ℝ) :
    fzzScreeningFirstContinuationPower u < -2 := by
  unfold fzzScreeningFirstContinuationPower
  have h : 0 < (1+Real.exp u)⁻¹ := inv_pos.mpr (by positivity)
  linarith

/-- Exterior admission whenever the total radial power is below the two-dimensional threshold. -/
theorem fzzScreeningPlaneExterior_integrable (p q : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel p (-2-p-Real.exp q)) fzzScreeningPlaneExterior :=
  exterior_integrable _ _ (by linarith [Real.exp_pos q])

/-- The complete finite part retains the exterior and both collision prescriptions. -/
def fzzScreeningPlaneFinitePart (α β : ℝ) : ℝ :=
  fzzScreeningZeroFinitePart α β + fzzScreeningOneFinitePart α β +
    ∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z

/-- Original unrenormalized whole-plane cutoff integral; its two cutoffs are independent. -/
def fzzScreeningPlaneCutoff (α β T U : ℝ) : ℝ :=
  ∫ z : ℂ in fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U)),
    fzzScreeningPlaneKernel α β z

/-- The whole-plane cutoff is an ordinary integrable source at every pair of cutoffs. -/
theorem fzzScreeningPlaneCutoff_integrable (u v T U : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel (fzzScreeningFirstContinuationPower u)
      (fzzScreeningFirstContinuationPower v))
      (fzzScreeningPlaneCutoffDomain (Real.exp (-T)) (Real.exp (-U))) :=
  cutoff_integrable _ _ _ _ (by linarith [continuation_power_lt u, continuation_power_lt v])
    (Real.exp_pos _) (Real.exp_pos _)

/-- Both original collision cutoffs may tend to zero independently, with the exact local terms. -/
theorem fzzScreeningPlaneFinitePart_independent_cutoff_limit (u v : ℝ) :
    Tendsto (fun P : ℝ × ℝ =>
      fzzScreeningPlaneCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) P.1 P.2 +
      2*Real.pi*(Real.exp (-P.1))^(fzzScreeningFirstContinuationPower u+2)/
        (fzzScreeningFirstContinuationPower u+2) +
      2*Real.pi*(Real.exp (-P.2))^(fzzScreeningFirstContinuationPower v+2)/
        (fzzScreeningFirstContinuationPower v+2)) (atTop ×ˢ atTop)
      (𝓝 (fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v))) := by
  let α := fzzScreeningFirstContinuationPower u
  let β := fzzScreeningFirstContinuationPower v
  have hf : Tendsto (fun P : ℝ × ℝ => P.1) (atTop ×ˢ atTop) atTop := tendsto_fst
  have hg : Tendsto (fun P : ℝ × ℝ => P.2) (atTop ×ˢ atTop) atTop := tendsto_snd
  have h0 := (fzzScreeningZeroFinitePart_cutoff_limit u β).comp hf
  have h1 := (fzzScreeningOneFinitePart_cutoff_limit α v).comp hg
  have h := (h0.add h1).add_const
    (∫ z : ℂ in fzzScreeningPlaneExterior, fzzScreeningPlaneKernel α β z)
  apply h.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < (1/2 : ℝ) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hf.eventually he, hg.eventually he] with P hP hQ
  dsimp only [Function.comp_def, fzzScreeningPlaneCutoff]
  have hsum : α+β < -2 := by
    dsimp [α, β]
    linarith [continuation_power_lt u, continuation_power_lt v]
  rw [cutoff_integral_split α β _ _ hsum (Real.exp_pos _) (Real.exp_pos _) hP hQ]
  dsimp [α, β]
  ring

/-- Equal-radius removal is a specialization of the independently convergent original cutoffs. -/
theorem fzzScreeningPlaneFinitePart_cutoff_limit (u v : ℝ) :
    Tendsto (fun T : ℝ =>
      fzzScreeningPlaneCutoff (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v) T T +
      2*Real.pi*(Real.exp (-T))^(fzzScreeningFirstContinuationPower u+2)/
        (fzzScreeningFirstContinuationPower u+2) +
      2*Real.pi*(Real.exp (-T))^(fzzScreeningFirstContinuationPower v+2)/
        (fzzScreeningFirstContinuationPower v+2)) atTop
      (𝓝 (fzzScreeningPlaneFinitePart (fzzScreeningFirstContinuationPower u)
        (fzzScreeningFirstContinuationPower v))) := by
  have hd : Tendsto (fun T : ℝ => (T, T)) atTop (atTop ×ˢ atTop) :=
    tendsto_id.prodMk tendsto_id
  have h := (fzzScreeningPlaneFinitePart_independent_cutoff_limit u v).comp hd
  exact h

end GaloisForLFunctions.RHTower
