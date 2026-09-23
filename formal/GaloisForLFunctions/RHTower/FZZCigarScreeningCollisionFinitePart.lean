import GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedSourceContact
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Screening collisions and their original cutoff finite parts

The opposite-winding position factor has two distinct collisions. Its first-order
replica exponent changes the collision at zero while leaving the one at one fixed.
The exact two-factor local integrability criteria show why this deformation alone
never gives an ordinary whole-plane integral at any physical level k > 2.

The constructive result retains the other position factor and subtracts its value
at the collision. A C¹ bound gains one integrable power. For -3 < alpha < -2,
polar integration and dominated convergence give the exact original cutoff finite
part, including its coefficient. Within leading power corrections, convergence
forces that coefficient and uniquely determines the limit. Reflection proves the
corresponding result at the second puncture.

These are local prescriptions for the displayed source factor. The exterior
region, simultaneous collisions, higher screening depths, analytic dependence of
the continued family, and its integrated replica derivative remain separate work.
The linear extension in the deficit does not assert a finite-deficit CFT action.
No RH statement or complete physical Ward identity is assumed or proved here.
-/

open MeasureTheory Set Metric Filter
open scoped Topology
namespace GaloisForLFunctions.RHTower
noncomputable section


def fzzScreeningPlaneKernel (α β : ℝ) (z : ℂ) : ℝ := ‖z‖^α * ‖z-1‖^β

private theorem plane_power_threshold (α : ℝ) :
    IntegrableOn (fun z : ℂ => ‖z‖^α) (ball 0 (1/2)) ↔ -2 < α := by
  rw [integrableOn_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => y^α) (r := 1/2)]
  simp only [Complex.finrank_real_complex, Nat.reduceSub, pow_one, smul_eq_mul]
  have he : (fun y : ℝ => y*y^α) =ᶠ[ae (volume.restrict (Ioo 0 (1/2)))]
      (fun y : ℝ => y^(α+1)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    rw [Real.rpow_add hy.1, Real.rpow_one, mul_comm]
  change Integrable _ (volume.restrict (Ioo 0 (1/2))) ↔ _
  rw [integrable_congr he]
  change IntegrableOn (fun y : ℝ => y^(α+1)) (Ioo 0 (1/2)) ↔ _
  rw [intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num)]
  constructor <;> intro h <;> linarith

private theorem away_one {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) (1/2)) : z-1 ≠ 0 := by
  intro he
  have he' : z = 1 := sub_eq_zero.mp he
  rw [he'] at hz
  norm_num [mem_closedBall, dist_eq_norm] at hz

private theorem second_power_continuous (β : ℝ) :
    ContinuousOn (fun z : ℂ => ‖z-1‖^β) (closedBall 0 (1/2)) := by
  apply ContinuousOn.rpow_const (by fun_prop)
  intro z hz
  exact Or.inl (norm_ne_zero_iff.mpr (away_one hz))

theorem fzzScreeningPlaneKernel_integrable_zero_iff (α β : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel α β) (ball 0 (1/2)) ↔ -2 < α := by
  rw [← plane_power_threshold α]
  constructor
  · intro hi
    have hh := hi.mul_continuousOn_of_subset (second_power_continuous (-β))
      measurableSet_ball (isCompact_closedBall (0 : ℂ) (1/2)) ball_subset_closedBall
    apply hh.congr_fun _ measurableSet_ball
    intro z hz
    dsimp [fzzScreeningPlaneKernel]
    rw [mul_assoc, ← Real.rpow_add (norm_pos_iff.mpr (away_one (ball_subset_closedBall hz))),
      add_neg_cancel, Real.rpow_zero, mul_one]
  · intro hi
    exact hi.mul_continuousOn_of_subset (second_power_continuous β)
      measurableSet_ball (isCompact_closedBall (0 : ℂ) (1/2)) ball_subset_closedBall


theorem fzzScreeningPlaneKernel_reflection (α β : ℝ) (z : ℂ) :
    fzzScreeningPlaneKernel α β (1-z) = fzzScreeningPlaneKernel β α z := by
  simp only [fzzScreeningPlaneKernel, sub_sub_cancel_left, norm_neg, norm_sub_rev (1 : ℂ) z]
  ring

private theorem reflection_preimage :
    (fun z : ℂ => 1-z) ⁻¹' ball 1 (1/2) = ball 0 (1/2) := by
  ext z
  simp [mem_ball, dist_eq_norm]

theorem fzzScreeningPlaneKernel_integrable_one_iff (α β : ℝ) :
    IntegrableOn (fzzScreeningPlaneKernel α β) (ball 1 (1/2)) ↔ -2 < β := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integrableOn_comp_preimage
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding
    (f := fzzScreeningPlaneKernel α β) (s := ball 1 (1/2))
  rw [reflection_preimage] at h
  have he : fzzScreeningPlaneKernel α β ∘ (fun z : ℂ => 1-z) =
      fzzScreeningPlaneKernel β α := by
    funext z
    exact fzzScreeningPlaneKernel_reflection α β z
  rw [he] at h
  exact h.symm.trans (fzzScreeningPlaneKernel_integrable_zero_iff β α)

def fzzScreeningReplicaKernel (u δ : ℝ) (z : ℂ) : ℝ :=
  fzzScreeningPlaneKernel
    (2*(1-fzzTwoMarkedPhysicalLevel u + (2*fzzTwoMarkedPhysicalLevel u/(fzzTwoMarkedPhysicalLevel u-2))*δ))
    (2*(1-fzzTwoMarkedPhysicalLevel u)) z

theorem fzzScreeningReplicaKernel_integrable_zero_iff (u δ : ℝ) :
    IntegrableOn (fzzScreeningReplicaKernel u δ) (ball 0 (1/2)) ↔
      (fzzTwoMarkedPhysicalLevel u-2)^(2 : ℕ)/(2*fzzTwoMarkedPhysicalLevel u) < δ := by
  unfold fzzScreeningReplicaKernel
  rw [fzzScreeningPlaneKernel_integrable_zero_iff]
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  have hd : 0 < fzzTwoMarkedPhysicalLevel u-2 := by linarith
  rw [div_lt_iff₀ (by linarith : 0 < 2*fzzTwoMarkedPhysicalLevel u)]
  have he : 2*fzzTwoMarkedPhysicalLevel u/(fzzTwoMarkedPhysicalLevel u-2)*δ*
      (fzzTwoMarkedPhysicalLevel u-2) = 2*fzzTwoMarkedPhysicalLevel u*δ := by
    field_simp
  constructor <;> intro h <;> nlinarith

theorem fzzScreeningReplicaKernel_not_integrable_one (u δ : ℝ) :
    ¬ IntegrableOn (fzzScreeningReplicaKernel u δ) (ball 1 (1/2)) := by
  unfold fzzScreeningReplicaKernel
  rw [fzzScreeningPlaneKernel_integrable_one_iff]
  have hk := fzzTwoMarkedPhysicalLevel_gt_two u
  linarith

theorem fzzScreeningReplicaKernel_not_integrable (u δ : ℝ) :
    ¬ Integrable (fzzScreeningReplicaKernel u δ) := by
  intro h
  exact fzzScreeningReplicaKernel_not_integrable_one u δ h.integrableOn


private theorem second_power_smooth (β : ℝ) :
    ContDiffOn ℝ 1 (fun z : ℂ => ‖z-1‖^β) (closedBall 0 (1/2)) := by
  apply ContDiffOn.rpow_const_of_ne
  · exact ((contDiffOn_id.sub contDiffOn_const).norm ℂ (fun z hz => away_one hz))
  · intro z hz
    exact norm_ne_zero_iff.mpr (away_one hz)

def fzzScreeningZeroSubtracted (α β : ℝ) (z : ℂ) : ℝ :=
  ‖z‖^α * (‖z-1‖^β-1)

private theorem zero_subtracted_integrable (α β : ℝ) (ha : -3 < α) :
    IntegrableOn (fzzScreeningZeroSubtracted α β) (ball 0 (1/2)) := by
  obtain ⟨C,hC⟩ := (second_power_smooth β).exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ℂ) (1/2)) (isCompact_closedBall (0 : ℂ) (1/2))
  have hi := ((plane_power_threshold (α+1)).mpr (by linarith)).const_mul (C : ℝ)
  apply hi.mono' (by unfold fzzScreeningZeroSubtracted; fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
  have hb : ‖‖z-1‖^β-1‖ ≤ (C : ℝ)*‖z‖ := by
    simpa [dist_eq_norm] using hC.dist_le_mul z (ball_subset_closedBall hz) 0
      (show (0 : ℂ) ∈ closedBall 0 (1/2) by simp)
  by_cases h0 : z = 0
  · subst z
    simp only [fzzScreeningZeroSubtracted, zero_sub, norm_neg, norm_one, Real.one_rpow,
      sub_self, mul_zero, norm_zero]
    positivity
  · have hn := norm_pos_iff.mpr h0
    calc
      ‖fzzScreeningZeroSubtracted α β z‖ = ‖z‖^α*‖‖z-1‖^β-1‖ := by
        rw [fzzScreeningZeroSubtracted, norm_mul, Real.norm_eq_abs,
          abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
      _ ≤ ‖z‖^α*((C : ℝ)*‖z‖) := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hn.le _)
      _ = (C : ℝ)*‖z‖^(α+1) := by rw [Real.rpow_add hn, Real.rpow_one]; ring

theorem fzzScreeningZeroSubtracted_integrable (a β : ℝ) :
    IntegrableOn (fzzScreeningZeroSubtracted (-3+Real.exp a) β) (ball 0 (1/2)) :=
  zero_subtracted_integrable _ _ (by linarith [Real.exp_pos a])


private theorem annular_power_integral (α r : ℝ) (hr : 0 < r) (hrR : r ≤ 1/2)
    (ha : α ≠ -2) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, ‖z‖^α) =
      2*Real.pi*((1/2 : ℝ)^(α+2)-r^(α+2))/(α+2) := by
  rw [← integral_indicator (measurableSet_ball.diff measurableSet_closedBall)]
  have he : ((ball 0 (1/2) \ closedBall 0 r).indicator (fun z : ℂ => ‖z‖^α)) =
      fun z : ℂ => (Ioo r (1/2)).indicator (fun y : ℝ => y^α) ‖z‖ := by
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
  have hf : (fun y : ℝ => y*(Ioo r (1/2)).indicator (fun t : ℝ => t^α) y) =
      (Ioo r (1/2)).indicator (fun y : ℝ => y^(α+1)) := by
    funext y
    by_cases hy : y ∈ Ioo r (1/2)
    · simp only [indicator_of_mem hy]
      rw [Real.rpow_add (hr.trans hy.1), Real.rpow_one, mul_comm]
    · simp only [indicator_of_notMem hy, mul_zero]
  rw [hf, setIntegral_indicator measurableSet_Ioo]
  have hs : Ioi (0 : ℝ) ∩ Ioo r (1/2) = Ioo r (1/2) :=
    inter_eq_right.mpr (fun y hy => hr.trans hy.1)
  rw [hs, ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hrR,
    integral_rpow (Or.inr ⟨by intro h; apply ha; linarith,
      by rw [uIcc_of_le hrR]; intro h; linarith [h.1]⟩)]
  rw [show α+1+1 = α+2 by ring]
  ring


private theorem annular_integrable (α β r : ℝ) (hr : 0 < r) :
    IntegrableOn (fzzScreeningPlaneKernel α β) (ball 0 (1/2) \ closedBall 0 r) ∧
      IntegrableOn (fun z : ℂ => ‖z‖^α) (ball 0 (1/2) \ closedBall 0 r) := by
  let K : Set ℂ := closedBall 0 (1/2) \ ball 0 r
  have hk : IsCompact K := (isCompact_closedBall (0 : ℂ) (1/2)).diff isOpen_ball
  have hn : ∀ z ∈ K, ‖z‖ ≠ 0 := by
    intro z hz he
    have hz0 : z = 0 := norm_eq_zero.mp he
    subst z
    exact hz.2 (by simpa using hr)
  have hc : ContinuousOn (fun z : ℂ => ‖z‖^α) K :=
    continuous_norm.continuousOn.rpow_const (fun z hz => Or.inl (hn z hz))
  have hc' : ContinuousOn (fun z : ℂ => ‖z-1‖^β) K :=
    (second_power_continuous β).mono (fun z hz => hz.1)
  have hs : ball (0 : ℂ) (1/2) \ closedBall 0 r ⊆ K := by
    intro z hz
    exact ⟨ball_subset_closedBall hz.1, fun h => hz.2 (ball_subset_closedBall h)⟩
  exact ⟨((hc.mul hc').integrableOn_compact hk).mono_set hs,
    (hc.integrableOn_compact hk).mono_set hs⟩

private theorem cutoff_split (α β r : ℝ) (hr : 0 < r) (hrR : r ≤ 1/2) (ha : α ≠ -2) :
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, fzzScreeningPlaneKernel α β z) +
      2*Real.pi*r^(α+2)/(α+2) =
    (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, fzzScreeningZeroSubtracted α β z) +
      2*Real.pi*(1/2 : ℝ)^(α+2)/(α+2) := by
  have hi := annular_integrable α β r hr
  have he : fzzScreeningZeroSubtracted α β =
      fun z => fzzScreeningPlaneKernel α β z - ‖z‖^α := by
    funext z
    dsimp [fzzScreeningZeroSubtracted, fzzScreeningPlaneKernel]
    ring
  rw [he, integral_sub hi.1 hi.2, annular_power_integral α r hr hrR ha]
  ring

private theorem subtracted_cutoff_limit (α β : ℝ) (ha : -3 < α) :
    Tendsto (fun T : ℝ => ∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
      fzzScreeningZeroSubtracted α β z) atTop
      (𝓝 (∫ z : ℂ in ball 0 (1/2), fzzScreeningZeroSubtracted α β z)) := by
  have hi := zero_subtracted_integrable α β ha
  have hd := tendsto_integral_filter_of_dominated_convergence
    (l := atTop) (μ := volume.restrict (ball (0 : ℂ) (1/2)))
    (F := fun T : ℝ => (closedBall 0 (Real.exp (-T)))ᶜ.indicator (fzzScreeningZeroSubtracted α β))
    (f := fzzScreeningZeroSubtracted α β) (fun z => ‖fzzScreeningZeroSubtracted α β z‖)
    (Eventually.of_forall (fun T => hi.aestronglyMeasurable.indicator measurableSet_closedBall.compl))
    (Eventually.of_forall (fun T => Eventually.of_forall (fun z => by
      by_cases hz : z ∈ (closedBall (0 : ℂ) (Real.exp (-T)))ᶜ
      · simp [indicator_of_mem hz]
      · simp [indicator_of_notMem hz]))) hi.norm ?_
  · simpa only [setIntegral_indicator measurableSet_closedBall.compl, ← Set.sdiff_eq] using hd
  · apply Eventually.of_forall
    intro z
    by_cases hz : z = 0
    · subst z
      have hf : fzzScreeningZeroSubtracted α β 0 = 0 := by
        simp [fzzScreeningZeroSubtracted]
      have he : (fun T : ℝ => (closedBall (0 : ℂ) (Real.exp (-T)))ᶜ.indicator
          (fzzScreeningZeroSubtracted α β) 0) = fun _ => (0 : ℝ) := by
        funext T
        by_cases hm : (0 : ℂ) ∈ (closedBall 0 (Real.exp (-T)))ᶜ
        · rw [indicator_of_mem hm, hf]
        · rw [indicator_of_notMem hm]
      rw [he, hf]
      exact tendsto_const_nhds
    · have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < ‖z‖ :=
        Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (norm_pos_iff.mpr hz))
      apply tendsto_const_nhds.congr'
      filter_upwards [he] with T hT
      rw [indicator_of_mem]
      simpa only [mem_compl_iff, mem_closedBall_zero_iff, not_le] using hT

/-- The local finite part includes the exact integrated constant Taylor term. -/
def fzzScreeningZeroFinitePart (α β : ℝ) : ℝ :=
  (∫ z : ℂ in ball 0 (1/2), fzzScreeningZeroSubtracted α β z) +
    2*Real.pi*(1/2 : ℝ)^(α+2)/(α+2)

/-- A chart for the first nonintegrable strip, -3 < alpha < -2. -/
def fzzScreeningFirstContinuationPower (u : ℝ) : ℝ := -2-(1+Real.exp u)⁻¹

private theorem continuation_power_range (u : ℝ) :
    -3 < fzzScreeningFirstContinuationPower u ∧ fzzScreeningFirstContinuationPower u < -2 := by
  have hp := Real.exp_pos u
  have hden : 0 < 1+Real.exp u := by positivity
  have hinv : (1+Real.exp u)⁻¹ < 1 := (inv_lt_one₀ hden).mpr (by linarith)
  have hpos := inv_pos.mpr hden
  dsimp [fzzScreeningFirstContinuationPower]
  constructor <;> linarith

theorem fzzScreeningZeroFinitePart_cutoff_limit (u β : ℝ) :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)),
        fzzScreeningPlaneKernel (fzzScreeningFirstContinuationPower u) β z) +
      2*Real.pi*(Real.exp (-T))^(fzzScreeningFirstContinuationPower u+2)/
        (fzzScreeningFirstContinuationPower u+2)) atTop
      (𝓝 (fzzScreeningZeroFinitePart (fzzScreeningFirstContinuationPower u) β)) := by
  have hr := continuation_power_range u
  have h := (subtracted_cutoff_limit _ β hr.1).add_const
    (2*Real.pi*(1/2 : ℝ)^(fzzScreeningFirstContinuationPower u+2)/
      (fzzScreeningFirstContinuationPower u+2))
  apply h.congr'
  have he : ∀ᶠ T : ℝ in atTop, Real.exp (-T) < (1/2 : ℝ) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [he] with T hT
  exact (cutoff_split _ β _ (Real.exp_pos _) hT.le hr.2.ne).symm

/-- The second collision retains the first position factor before subtracting its value. -/
def fzzScreeningOneSubtracted (α β : ℝ) (z : ℂ) : ℝ :=
  ‖z-1‖^β * (‖z‖^α-1)

theorem fzzScreeningOneSubtracted_reflection (α β : ℝ) (z : ℂ) :
    fzzScreeningOneSubtracted α β (1-z) = fzzScreeningZeroSubtracted β α z := by
  simp only [fzzScreeningOneSubtracted, fzzScreeningZeroSubtracted,
    sub_sub_cancel_left, norm_neg, norm_sub_rev (1 : ℂ) z]

theorem fzzScreeningOneSubtracted_integrable (α a : ℝ) :
    IntegrableOn (fzzScreeningOneSubtracted α (-3+Real.exp a)) (ball 1 (1/2)) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).integrableOn_comp_preimage
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding
    (f := fzzScreeningOneSubtracted α (-3+Real.exp a)) (s := ball 1 (1/2))
  rw [reflection_preimage] at h
  apply h.mp
  have he : fzzScreeningOneSubtracted α (-3+Real.exp a) ∘ (fun z : ℂ => 1-z) =
      fzzScreeningZeroSubtracted (-3+Real.exp a) α := by
    funext z
    exact fzzScreeningOneSubtracted_reflection _ _ z
  rw [he]
  exact fzzScreeningZeroSubtracted_integrable a α

private theorem reflected_zero_integral (f : ℂ → ℝ) :
    (∫ z : ℂ in ball 1 (1/2), f z) = ∫ z : ℂ in ball 0 (1/2), f (1-z) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding f (ball 1 (1/2))
  rw [reflection_preimage] at h
  exact h.symm

private theorem reflected_annular_integral (f : ℂ → ℝ) (r : ℝ) :
    (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 r, f z) =
      ∫ z : ℂ in ball 0 (1/2) \ closedBall 0 r, f (1-z) := by
  have h := (Measure.measurePreserving_sub_left (volume : Measure ℂ) 1).setIntegral_preimage_emb
    (Homeomorph.subLeft (1 : ℂ)).measurableEmbedding f (ball 1 (1/2) \ closedBall 1 r)
  have he : (fun z : ℂ => 1-z) ⁻¹' (ball 1 (1/2) \ closedBall 1 r) =
      ball 0 (1/2) \ closedBall 0 r := by
    ext z
    simp [mem_ball, mem_closedBall, dist_eq_norm]
  rw [he] at h
  exact h.symm

def fzzScreeningOneFinitePart (α β : ℝ) : ℝ :=
  (∫ z : ℂ in ball 1 (1/2), fzzScreeningOneSubtracted α β z) +
    2*Real.pi*(1/2 : ℝ)^(β+2)/(β+2)

theorem fzzScreeningOneFinitePart_reflection (α β : ℝ) :
    fzzScreeningOneFinitePart α β = fzzScreeningZeroFinitePart β α := by
  unfold fzzScreeningOneFinitePart fzzScreeningZeroFinitePart
  rw [reflected_zero_integral]
  simp only [fzzScreeningOneSubtracted_reflection]

theorem fzzScreeningOneFinitePart_cutoff_limit (α u : ℝ) :
    Tendsto (fun T : ℝ =>
      (∫ z : ℂ in ball 1 (1/2) \ closedBall 1 (Real.exp (-T)),
        fzzScreeningPlaneKernel α (fzzScreeningFirstContinuationPower u) z) +
      2*Real.pi*(Real.exp (-T))^(fzzScreeningFirstContinuationPower u+2)/
        (fzzScreeningFirstContinuationPower u+2)) atTop
      (𝓝 (fzzScreeningOneFinitePart α (fzzScreeningFirstContinuationPower u))) := by
  simp_rw [reflected_annular_integral, fzzScreeningPlaneKernel_reflection,
    fzzScreeningOneFinitePart_reflection]
  exact fzzScreeningZeroFinitePart_cutoff_limit u α

/-- Original unrenormalized integral with the collision disk removed. -/
def fzzScreeningZeroCutoff (α β T : ℝ) : ℝ :=
  ∫ z : ℂ in ball 0 (1/2) \ closedBall 0 (Real.exp (-T)), fzzScreeningPlaneKernel α β z

/-- The leading power counterterm and its resulting finite limit are forced by the original source. -/
theorem fzzScreeningZeroCutoff_counterterm_iff (u β D L : ℝ) :
    Tendsto (fun T : ℝ => fzzScreeningZeroCutoff (fzzScreeningFirstContinuationPower u) β T +
      D*(Real.exp (-T))^(fzzScreeningFirstContinuationPower u+2)) atTop (𝓝 L) ↔
    D = 2*Real.pi/(fzzScreeningFirstContinuationPower u+2) ∧
      L = fzzScreeningZeroFinitePart (fzzScreeningFirstContinuationPower u) β := by
  let α := fzzScreeningFirstContinuationPower u
  have hq : α+2 < 0 := by have h := (continuation_power_range u).2; dsimp [α]; linarith
  have hb : Tendsto (fun T : ℝ => fzzScreeningZeroCutoff α β T +
      (2*Real.pi/(α+2))*(Real.exp (-T))^(α+2)) atTop (𝓝 (fzzScreeningZeroFinitePart α β)) := by
    convert fzzScreeningZeroFinitePart_cutoff_limit u β using 1
    funext T
    dsimp [fzzScreeningZeroCutoff, α]
    ring
  change Tendsto (fun T : ℝ => fzzScreeningZeroCutoff α β T +
      D*(Real.exp (-T))^(α+2)) atTop (𝓝 L) ↔
    D = 2*Real.pi/(α+2) ∧ L = fzzScreeningZeroFinitePart α β
  constructor
  · intro h
    have hd : Tendsto (fun T : ℝ => Real.exp (T*(α+2))) atTop (𝓝 0) :=
      Real.tendsto_exp_atBot.comp ((tendsto_mul_const_atBot_of_neg hq).mpr tendsto_id)
    have hp := (h.sub hb).mul hd
    have he (T : ℝ) :
        ((fzzScreeningZeroCutoff α β T + D*(Real.exp (-T))^(α+2)) -
          (fzzScreeningZeroCutoff α β T + (2*Real.pi/(α+2))*(Real.exp (-T))^(α+2))) *
          Real.exp (T*(α+2)) = D-2*Real.pi/(α+2) := by
      rw [← Real.exp_mul]
      calc
        _ = (D-2*Real.pi/(α+2)) * (Real.exp (-T*(α+2))*Real.exp (T*(α+2))) := by ring
        _ = D-2*Real.pi/(α+2) := by rw [← Real.exp_add]; simp
    have hz : Tendsto (fun _ : ℝ => D-2*Real.pi/(α+2)) atTop (𝓝 0) := by
      simpa only [he, mul_zero] using hp
    have hD : D = 2*Real.pi/(α+2) :=
      sub_eq_zero.mp (tendsto_nhds_unique tendsto_const_nhds hz)
    refine ⟨hD, ?_⟩
    rw [hD] at h
    exact tendsto_nhds_unique h hb
  · rintro ⟨rfl,rfl⟩
    exact hb

end
end GaloisForLFunctions.RHTower
