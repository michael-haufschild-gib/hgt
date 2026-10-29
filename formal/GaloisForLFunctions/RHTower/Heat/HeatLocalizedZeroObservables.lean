import GaloisForLFunctions.RHTower.Heat.HeatZeroSumContinuity
import GaloisForLFunctions.RHTower.Heat.LocalizedHeatPacketFlux
import GaloisForLFunctions.HTGeometry.PhasePacketOrderReflection

/-!
# Continuous observables of localized heat zeros

Compact horizontal weights make the multiplicity-weighted zero sums finite.
Continuous vertical tests remain continuous through collisions. Truncated
nonreal indicators eventually recover every member of a fixed finite packet,
while the outer cutoff controls the packet's full squared-height energy.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower.DeBruijn

/-- Bounded support on the actual zero set makes the multiplicity-weighted series finite. -/
theorem summable_heatWeightedZeroSum_of_support {Ψ : ℂ → ℝ} {t : ℝ}
    (ht : 0 ≤ t) (R₀ : ℝ)
    (hsupport : ∀ z, riemannHeat t z = 0 → R₀ ≤ ‖z‖ → Ψ z = 0) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * Ψ z) := by
  classical
  have hf := differentiable_riemannHeat ht
  have hnotlocal (z : ℂ) : ¬ ∀ᶠ w in 𝓝 z, riemannHeat t w = 0 :=
    fun h => analyticOrderAt_riemannHeat_ne_top ht z (analyticOrderAt_eq_top.mpr h)
  obtain ⟨R, hRlo, _, hRsph⟩ := exists_radius_no_boundary_zero (c := (0 : ℂ))
    (hf.differentiableOn.analyticOnNhd isOpen_univ) hnotlocal (max 1 R₀)
  have hR : 0 < R := zero_lt_one.trans_le ((le_max_left _ _).trans hRlo)
  have hR₀ : R₀ ≤ R := (le_max_right _ _).trans hRlo
  obtain ⟨S, _, hSz, _⟩ := exists_zeroSet_zeroSumBall hR
    (by linarith only [hR] : R < 2 * R) isOpen_univ (subset_univ _)
    hf.differentiableOn hRsph
  refine (hasSum_sum_of_ne_finset_zero
    (f := fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * Ψ z) (s := S) ?_).summable
  intro z hz
  by_cases hzero : riemannHeat t z = 0
  · by_cases hΨ : Ψ z = 0
    · rw [hΨ, mul_zero]
    exfalso
    have hn : ‖z‖ < R₀ := lt_of_not_ge fun h => hΨ (hsupport z hzero h)
    have hb : z ∈ Metric.ball (0 : ℂ) R := by
      rw [Metric.mem_ball, dist_zero_right]
      exact hn.trans_le hR₀
    exact hz ((hSz z hb).mp hzero)
  · rw [zeroMult_riemannHeat_eq_zero ht hzero, Nat.cast_zero, zero_mul]

/-- A horizontal cutoff and a vertical observable applied to actual heat zeros,
with their analytic multiplicities. -/
def heatLocalizedZeroObservable (X : ℝ) (w u : ℝ → ℝ) (t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => w (z.re - X) * u z.im) t

private theorem exists_heat_observable_support_bound {w : ℝ → ℝ}
    (hcompact : HasCompactSupport w) (u : ℝ → ℝ) (X : ℝ) :
    ∃ R₀ : ℝ, ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, riemannHeat s z = 0 → R₀ ≤ ‖z‖ →
      w (z.re - X) * u z.im = 0 := by
  obtain ⟨B, hB⟩ := hcompact.isCompact.isBounded.exists_norm_le
  refine ⟨|X| + |B| + 1, ?_⟩
  intro s hs z hz hnorm
  by_cases hwz : w (z.re - X) = 0
  · rw [hwz, zero_mul]
  exfalso
  have hb := hB (z.re - X) ((subset_tsupport w) hwz)
  rw [Real.norm_eq_abs] at hb
  have hre := abs_add_le (z.re - X) X
  rw [sub_add_cancel] at hre
  have him := abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg hs hz
  have hle := Complex.norm_le_abs_re_add_abs_im z
  have hBabs := le_abs_self B
  linarith only [hnorm, hb, hre, him, hle, hBabs]

/-- Every compact horizontal observable is an actual finite weighted series. -/
theorem summable_heatLocalizedZeroObservable {w : ℝ → ℝ}
    (hcompact : HasCompactSupport w) (u : ℝ → ℝ) (X : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) *
      (w (z.re - X) * u z.im)) := by
  obtain ⟨R₀, hR⟩ := exists_heat_observable_support_bound hcompact u X
  exact summable_heatWeightedZeroSum_of_support ht R₀ (hR t ht)

/-- Continuous vertical observables remain continuous through heat-zero collisions. -/
theorem continuous_heatLocalizedZeroObservable_clamped {w u : ℝ → ℝ}
    (hw : Continuous w) (hu : Continuous u) (hcompact : HasCompactSupport w) (X : ℝ) :
    Continuous (fun t => heatLocalizedZeroObservable X w u (max t 0)) := by
  obtain ⟨R₀, hR⟩ := exists_heat_observable_support_bound hcompact u X
  have hΨ : Continuous (fun z : ℂ => w (z.re - X) * u z.im) := by fun_prop
  exact continuous_heatWeightedZeroSum_clamped_of_support hΨ R₀ hR

/-- A continuous outer cutoff equal to one throughout the radius-two force packet. -/
def heatOuterCutoff : ℝ → ℝ := PhaseKernel.tentCutoff 2

theorem continuous_heatOuterCutoff : Continuous heatOuterCutoff :=
  PhaseKernel.continuous_tentCutoff 2

theorem heatOuterCutoff_nonneg (x : ℝ) : 0 ≤ heatOuterCutoff x :=
  PhaseKernel.tentCutoff_nonneg 2 x

theorem heatOuterCutoff_eq_one {x : ℝ} (hx : |x| ≤ 2) : heatOuterCutoff x = 1 :=
  PhaseKernel.tentCutoff_eq_one hx

theorem hasCompactSupport_heatOuterCutoff : HasCompactSupport heatOuterCutoff := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 3)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact PhaseKernel.tentCutoff_eq_zero (by simpa only [show (2 : ℝ) + 1 = 3 by norm_num] using hx)

/-- A finite packet covering the cutoff gives an exact multiplicity-weighted sum. -/
theorem heatLocalizedZeroObservable_eq_sum {t X : ℝ} (ht : 0 ≤ t)
    (w u : ℝ → ℝ) (hsupp : ∀ x, 1 ≤ |x| → w x = 0) (S : Finset ℂ)
    (hcover : ∀ z, riemannHeat t z = 0 → |z.re - X| < 1 → z ∈ S) :
    heatLocalizedZeroObservable X w u t =
      ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (w (z.re - X) * u z.im) := by
  classical
  unfold heatLocalizedZeroObservable heatWeightedZeroSum
  apply tsum_eq_sum
  intro z hz
  change (zeroMult (riemannHeat t) z : ℝ) * (w (z.re - X) * u z.im) = 0
  by_cases hzero : riemannHeat t z = 0
  · have hout : 1 ≤ |z.re - X| := le_of_not_gt fun h => hz (hcover z hzero h)
    rw [hsupp _ hout, zero_mul, mul_zero]
  · rw [zeroMult_riemannHeat_eq_zero ht hzero, Nat.cast_zero, zero_mul]

/-- Continuous increasing approximants to the nonreal indicator. -/
def heatNonrealTruncation (n : ℕ) (y : ℝ) : ℝ := min 1 ((((n : ℝ) + 1) * y)^2)

theorem continuous_heatNonrealTruncation (n : ℕ) : Continuous (heatNonrealTruncation n) := by
  unfold heatNonrealTruncation
  fun_prop

theorem heatNonrealTruncation_nonneg (n : ℕ) (y : ℝ) : 0 ≤ heatNonrealTruncation n y :=
  le_min zero_le_one (sq_nonneg _)

theorem heatNonrealTruncation_le_indicator (n : ℕ) (y : ℝ) :
    heatNonrealTruncation n y ≤ if y = 0 then 0 else 1 := by
  by_cases hy : y = 0
  · simp [hy, heatNonrealTruncation]
  · simpa only [heatNonrealTruncation, if_neg hy] using
      (min_le_left (1 : ℝ) ((((n : ℝ) + 1) * y)^2))

theorem eventually_heatNonrealTruncation_eq_indicator (y : ℝ) :
    ∀ᶠ n : ℕ in atTop, heatNonrealTruncation n y = if y = 0 then 0 else 1 := by
  by_cases hy : y = 0
  · filter_upwards [] with n
    simp [heatNonrealTruncation, hy]
  have hyp : 0 < |y| := abs_pos.mpr hy
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / |y|)
  refine Filter.eventually_atTop.mpr ⟨N, ?_⟩
  intro n hn
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlarge : 1 / |y| < (n : ℝ) + 1 := by linarith only [hN, hNn]
  have hprod : 1 ≤ ((n : ℝ) + 1) * |y| := ((div_lt_iff₀ hyp).mp hlarge).le
  have habs : |((n : ℝ) + 1) * y| = ((n : ℝ) + 1) * |y| := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ (n : ℝ) + 1)]
  have hsq : 1 ≤ (((n : ℝ) + 1) * y)^2 := by
    rw [← sq_abs, habs]
    nlinarith only [hprod]
  simp only [heatNonrealTruncation, min_eq_left hsq, if_neg hy]

/-- The actual localized nonreal count, retaining multiplicity. -/
def heatLocalizedNonrealCount (X : ℝ) (w : ℝ → ℝ) (t : ℝ) : ℝ :=
  heatLocalizedZeroObservable X w (fun y => if y = 0 then 0 else 1) t

/-- At a fixed finite packet, one truncation already captures every nonreal member. -/
theorem eventually_heatLocalizedZeroObservable_eq_nonrealCount
    {t X : ℝ} (ht : 0 ≤ t) (w : ℝ → ℝ)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0) (S : Finset ℂ)
    (hcover : ∀ z, riemannHeat t z = 0 → |z.re - X| < 1 → z ∈ S) :
    ∀ᶠ n : ℕ in atTop,
      heatLocalizedZeroObservable X w (heatNonrealTruncation n) t =
        heatLocalizedNonrealCount X w t := by
  filter_upwards [(Filter.eventually_all_finset S).mpr
    (fun z _ => eventually_heatNonrealTruncation_eq_indicator z.im)] with n hn
  rw [heatLocalizedNonrealCount,
    heatLocalizedZeroObservable_eq_sum ht w _ hsupp S hcover,
    heatLocalizedZeroObservable_eq_sum ht w _ hsupp S hcover]
  exact Finset.sum_congr rfl fun z hz => by rw [hn z hz]

end RHTower.DeBruijn

namespace RHTower.DeBruijn

/-- The unit support condition itself gives compact horizontal support. -/
theorem hasCompactSupport_heat_cutoff {w : ℝ → ℝ}
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0) : HasCompactSupport w := by
  apply HasCompactSupport.intro (isCompact_closedBall (0 : ℝ) 1)
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs, not_le] at hx
  exact hsupp x hx.le

theorem heatLocalizedZeroObservable_nonneg {X t : ℝ} {w u : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ w x) (hu : ∀ y, 0 ≤ u y) :
    0 ≤ heatLocalizedZeroObservable X w u t :=
  tsum_nonneg fun _ => mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (hw _) (hu _))

/-- Pointwise order of vertical observables passes to the actual zero sum. -/
theorem heatLocalizedZeroObservable_mono {X t : ℝ} {w u v : ℝ → ℝ}
    (ht : 0 ≤ t) (hcompact : HasCompactSupport w) (hw : ∀ x, 0 ≤ w x)
    (huv : ∀ y, u y ≤ v y) :
    heatLocalizedZeroObservable X w u t ≤ heatLocalizedZeroObservable X w v t := by
  exact Summable.tsum_le_tsum (fun z => mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left (huv _) (hw _)) (Nat.cast_nonneg _))
    (summable_heatLocalizedZeroObservable hcompact u X ht)
    (summable_heatLocalizedZeroObservable hcompact v X ht)

/-- The actual packet's degree bounds every observable between zero and one. -/
theorem heatLocalizedZeroObservable_le_packet_degree {t X W K : ℝ}
    (ht : 0 ≤ t) (hW : 0 ≤ W) {w u : ℝ → ℝ}
    (hw : ∀ x, 0 ≤ w x ∧ w x ≤ W) (hu : ∀ y, 0 ≤ u y ∧ u y ≤ 1)
    (hsupp : ∀ x, 1 ≤ |x| → w x = 0) (S : Finset ℂ)
    (hcover : ∀ z, riemannHeat t z = 0 → |z.re - X| < 1 → z ∈ S)
    (hdegree : ((∑ z ∈ S, zeroMult (riemannHeat t) z : ℕ) : ℝ) ≤ K) :
    heatLocalizedZeroObservable X w u t ≤ W * K := by
  rw [heatLocalizedZeroObservable_eq_sum ht w u hsupp S hcover]
  calc
    _ ≤ ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * W := by
      refine Finset.sum_le_sum fun z _ => mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
      exact (mul_le_mul_of_nonneg_left (hu z.im).2 (hw _).1).trans
        (by simpa only [mul_one] using (hw (z.re - X)).2)
    _ = W * ((∑ z ∈ S, zeroMult (riemannHeat t) z : ℕ) : ℝ) := by
      rw [Nat.cast_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
    _ ≤ W * K := mul_le_mul_of_nonneg_left hdegree hW

/-- The outer cutoff majorizes all squared heights of the force packet,
including multiplicities at collisions. -/
theorem heatPacketVerticalEnergy_le_outer {t X : ℝ} (ht : 0 ≤ t) {S : Finset ℂ}
    (hpacket : ∀ a ∈ S, riemannHeat t a = 0 ∧ |a.re - X| ≤ 2) :
    heatPacketVerticalEnergy S ≤ heatLocalizedVerticalEnergy X heatOuterCutoff t := by
  have hsum := summable_heatLocalizedZeroObservable hasCompactSupport_heatOuterCutoff
    (fun y => y^2) X ht
  calc
    _ ≤ ∑ a ∈ S, (zeroMult (riemannHeat t) a : ℝ) *
        (heatOuterCutoff (a.re - X) * a.im^2) := by
      refine Finset.sum_le_sum fun a ha => ?_
      rw [heatOuterCutoff_eq_one (hpacket a ha).2, one_mul]
      have hm : (1 : ℝ) ≤ zeroMult (riemannHeat t) a := by
        exact_mod_cast one_le_zeroMult_riemannHeat ht (hpacket a ha).1
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hm (sq_nonneg a.im)
    _ ≤ _ := Summable.sum_le_tsum S
      (fun a _ => mul_nonneg (Nat.cast_nonneg _)
        (mul_nonneg (heatOuterCutoff_nonneg _) (sq_nonneg _))) hsum

end RHTower.DeBruijn

#print axioms RHTower.DeBruijn.continuous_heatLocalizedZeroObservable_clamped
#print axioms RHTower.DeBruijn.eventually_heatLocalizedZeroObservable_eq_nonrealCount
#print axioms RHTower.DeBruijn.heatLocalizedZeroObservable_le_packet_degree
#print axioms RHTower.DeBruijn.heatPacketVerticalEnergy_le_outer
