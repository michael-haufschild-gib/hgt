import GaloisForLFunctions.ArithmeticElectrostatics.TheGlobalHeatDepthDissipates
import GaloisForLFunctions.RHTower.DeBruijnNewmanEnergyUnitTime
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountRightLimit

/-!
# The initial trace of heat depth energy

The upper-half squared-depth energy has an exact initial trace: the sum of
squared upper depths of the original ξ divisor, possibly infinite. Heat
majorization gives the upper bound. Compact zero sums recover every finite
initial packet and prevent energy from disappearing at time zero.
Finite initial mass also forces `t N(t) → 0`, by dissipation on `[t/2,t]`.
-/

noncomputable section
set_option autoImplicit false

open Complex Filter Topology Set Metric MeasureTheory
open RHTower RHTower.DeBruijn
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.ArithmeticElectrostatics

/-- The squared upper depth of one initial multiplicity copy. -/
def xiUpperSquaredDepth (q : XiZeroCopy) : ℝ := (max (xiSpectralPoint q).im 0) ^ 2

/-- Upper-half heat energy. Its initial trace is taken from positive times;
the real-valued `tsum` at zero is not used when the initial series diverges. -/
def heatUpperDepthEnergy (t : ℝ) : ℝ :=
  heatWeightedZeroSum (fun z => (max z.im 0) ^ 2) t

private theorem upper_weight_zero_off_nonreal {t : ℝ} (ht : 0 ≤ t)
    (z : ℂ) (hz : ¬ (riemannHeat t z = 0 ∧ z.im ≠ 0)) :
    (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 = 0 := by
  by_cases hf : riemannHeat t z = 0
  · have hi : z.im = 0 := by simpa only [hf, true_and, not_not] using hz
    rw [hi, max_self, zero_pow two_ne_zero, mul_zero]
  · rw [zeroMult_riemannHeat_eq_zero ht hf, Nat.cast_zero, zero_mul]

private theorem summable_upper_heat_weight {t : ℝ} (ht : 0 < t) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2) := by
  classical
  apply summable_of_ne_finset_zero (s := (riemannHeat_nonreal_zeros_finite ht).toFinset)
  intro z hz
  exact upper_weight_zero_off_nonreal ht.le z (by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hz)

private theorem heatUpperDepthEnergy_eq_sum {t : ℝ} (ht : 0 < t) :
    heatUpperDepthEnergy t = ∑ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
      (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 := by
  classical
  apply tsum_eq_sum
  intro z hz
  exact upper_weight_zero_off_nonreal ht.le z (by
    simpa only [Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hz)

private theorem summable_compact_heat_weight {t : ℝ} (ht : 0 ≤ t)
    (Ψ : ℂ → ℝ) (R : ℝ) (hsupp : ∀ z, R ≤ ‖z‖ → Ψ z = 0) :
    Summable (fun z : ℂ => (zeroMult (riemannHeat t) z : ℝ) * Ψ z) := by
  have hfin := finite_zeros_closedBall
    (fun z (_ : z ∈ closedBall (0 : ℂ) R) => riemannHeat_analytic ht z (mem_univ z))
    (fun z _ h => analyticOrderAt_riemannHeat_ne_top ht z (analyticOrderAt_eq_top.mpr h))
  apply summable_of_hasFiniteSupport
  apply hfin.subset
  intro z hz
  change (zeroMult (riemannHeat t) z : ℝ) * Ψ z ≠ 0 at hz
  have hf : riemannHeat t z = 0 := by
    by_contra hf
    exact hz (by rw [zeroMult_riemannHeat_eq_zero ht hf, Nat.cast_zero, zero_mul])
  have hn : ‖z‖ < R := lt_of_not_ge fun h => hz (by rw [hsupp z h, mul_zero])
  exact ⟨by simpa only [mem_closedBall, dist_zero_right] using hn.le, hf⟩

/-- Initial finite sums control every positive-time upper energy with the same constant. -/
theorem heatUpperDepthEnergy_le_of_initial_sums {K : ℝ}
    (hK : ∀ T : Finset XiZeroCopy, ∑ q ∈ T, xiUpperSquaredDepth q ≤ K)
    {t : ℝ} (ht : 0 < t) : heatUpperDepthEnergy t ≤ K := by
  classical
  have hK0 : 0 ≤ K := by simpa only [Finset.sum_empty] using hK ∅
  rw [heatUpperDepthEnergy_eq_sum ht]
  by_cases ht1 : t ≤ 1
  · have hb (T : Finset XiZeroCopy) :
        ∑ q ∈ T.filter (fun q => 0 < (xiSpectralPoint q).im),
          max ((xiSpectralPoint q).im ^ 2 - 2 * t - 0) 0 ≤ K := by
      apply le_trans _ (hK T)
      rw [Finset.sum_filter]
      apply Finset.sum_le_sum
      intro q _
      by_cases hq : 0 < (xiSpectralPoint q).im
      · rw [if_pos hq, xiUpperSquaredDepth, max_eq_left hq.le]
        exact max_le (by linarith only [ht]) (sq_nonneg _)
      · rw [if_neg hq]
        exact sq_nonneg _
    have h := riemannHeat_upper_energy_le_of_le_one ht ht1 (c := 0) le_rfl hb
      (riemannHeat_nonreal_zeros_finite ht).toFinset
    simpa only [sub_zero, max_eq_left (sq_nonneg _)] using h
  · have hz : ∀ z ∈ (riemannHeat_nonreal_zeros_finite ht).toFinset,
        (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 = 0 := by
      intro z hz
      have hf := (Set.Finite.mem_toFinset _).mp hz
      have hi := riemannHeat_zeros_real (show 1 / 8 ≤ t by linarith only [ht1]) hf.1
      rw [hi, max_self, zero_pow two_ne_zero, mul_zero]
    rw [Finset.sum_eq_zero hz]
    exact hK0

private theorem copy_sum_le_zero_sum (T : Finset XiZeroCopy)
    (Ψ : ℂ → ℝ) (hΨ : ∀ z, 0 ≤ Ψ z) :
    ∑ q ∈ T, Ψ (xiSpectralPoint q) ≤
      ∑ z ∈ T.image xiSpectralPoint, (zeroMult (riemannHeat 0) z : ℝ) * Ψ z := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to'
    (fun q hq => Finset.mem_image_of_mem xiSpectralPoint hq) Ψ]
  apply Finset.sum_le_sum
  intro z hz
  obtain ⟨q₀, _, rfl⟩ := Finset.mem_image.mp hz
  have hsub : T.filter (fun q => xiSpectralPoint q = xiSpectralPoint q₀) ⊆
      ({q₀.1} : Finset XiDivisorSupport).sigma (fun _ => Finset.univ) := by
    intro q hq
    exact Finset.mem_sigma.mpr ⟨Finset.mem_singleton.mpr
      ((xiSpectralPoint_eq_iff q q₀).mp (Finset.mem_filter.mp hq).2), Finset.mem_univ _⟩
  have hcard : (T.filter (fun q => xiSpectralPoint q = xiSpectralPoint q₀)).card ≤
      zeroMult (riemannHeat 0) (xiSpectralPoint q₀) := by
    simpa only [Finset.card_sigma, Finset.sum_singleton, Finset.card_univ,
      Fintype.card_fin, zeroMult_riemannHeat_zero_xiSpectralPoint] using Finset.card_le_card hsub
  rw [Finset.sum_const, nsmul_eq_mul]
  exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hcard) (hΨ _)

/-- A compact continuous zero sum captures any prescribed finite initial packet. -/
private theorem exists_initial_packet_cutoff (T : Finset XiZeroCopy) :
    ∃ (Ψ : ℂ → ℝ) (R : ℝ), Continuous Ψ ∧ (∀ z, 0 ≤ Ψ z) ∧
      (∀ z, Ψ z ≤ (max z.im 0) ^ 2) ∧ (∀ z, R ≤ ‖z‖ → Ψ z = 0) ∧
      (∑ q ∈ T, xiUpperSquaredDepth q) ≤ heatWeightedZeroSum Ψ 0 := by
  classical
  let R : ℝ := ∑ q ∈ T, ‖xiSpectralPoint q‖
  let χ : ℂ → ℝ := fun z => max 0 (min 1 (R + 1 - ‖z‖))
  let Ψ : ℂ → ℝ := fun z => χ z * (max z.im 0) ^ 2
  have hχ0 (z : ℂ) : 0 ≤ χ z := le_max_left _ _
  have hχ1 (z : ℂ) : χ z ≤ 1 := max_le zero_le_one (min_le_left _ _)
  have hΨ0 (z : ℂ) : 0 ≤ Ψ z := mul_nonneg (hχ0 z) (sq_nonneg _)
  have hsupp (z : ℂ) (hz : R + 1 ≤ ‖z‖) : Ψ z = 0 := by
    have hm : min 1 (R + 1 - ‖z‖) ≤ 0 := (min_le_right _ _).trans (by linarith only [hz])
    simp only [Ψ, χ, max_eq_left hm, zero_mul]
  refine ⟨Ψ, R + 1, by fun_prop, hΨ0, fun z => ?_, hsupp, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (hχ1 z) (sq_nonneg _)).trans_eq (one_mul _)
  · have he (q : XiZeroCopy) (hq : q ∈ T) : Ψ (xiSpectralPoint q) = xiUpperSquaredDepth q := by
      have hn : ‖xiSpectralPoint q‖ ≤ R :=
        Finset.single_le_sum (f := fun q => ‖xiSpectralPoint q‖) (fun _ _ => norm_nonneg _) hq
      have h1 : 1 ≤ R + 1 - ‖xiSpectralPoint q‖ := by linarith only [hn]
      simp only [Ψ, χ, min_eq_left h1, max_eq_right zero_le_one, one_mul, xiUpperSquaredDepth]
    calc
      (∑ q ∈ T, xiUpperSquaredDepth q) = ∑ q ∈ T, Ψ (xiSpectralPoint q) :=
        Finset.sum_congr rfl fun q hq => (he q hq).symm
      _ ≤ ∑ z ∈ T.image xiSpectralPoint, (zeroMult (riemannHeat 0) z : ℝ) * Ψ z :=
        copy_sum_le_zero_sum T Ψ hΨ0
      _ ≤ heatWeightedZeroSum Ψ 0 :=
        Summable.sum_le_tsum _ (fun z _ => mul_nonneg (Nat.cast_nonneg _) (hΨ0 z))
          (summable_compact_heat_weight le_rfl Ψ (R + 1) hsupp)

private theorem eventually_initial_packet_lt_heat_energy
    (T : Finset XiZeroCopy) {a : ℝ} (ha : a < ∑ q ∈ T, xiUpperSquaredDepth q) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), a < heatUpperDepthEnergy t := by
  obtain ⟨Ψ, R, hΨ, hΨ0, hΨle, hsupp, hT⟩ := exists_initial_packet_cutoff T
  have hc := continuous_heatWeightedZeroSum_clamped_of_support hΨ R
    (fun _ _ z _ hz => hsupp z hz)
  have h0 : Tendsto (fun t : ℝ => heatWeightedZeroSum Ψ (max t 0)) (𝓝 (0 : ℝ))
      (𝓝 (heatWeightedZeroSum Ψ (max (0 : ℝ) 0))) := hc.tendsto 0
  have hlim : Tendsto (fun t => heatWeightedZeroSum Ψ (max t 0)) (𝓝[>] (0 : ℝ))
      (𝓝 (heatWeightedZeroSum Ψ 0)) := by
    simpa only [max_self] using h0.mono_left
      (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
  filter_upwards [hlim.eventually (Ioi_mem_nhds (ha.trans_le hT)), self_mem_nhdsWithin]
    with t hlow ht
  change 0 < t at ht
  rw [max_eq_left ht.le] at hlow
  apply hlow.trans_le
  exact Summable.tsum_le_tsum
    (fun z => mul_le_mul_of_nonneg_left (hΨle z) (Nat.cast_nonneg _))
    (summable_compact_heat_weight ht.le Ψ R hsupp) (summable_upper_heat_weight ht)

/-- Even a bound only near time zero controls every initial finite packet. -/
theorem initial_sums_le_of_eventually_heatUpperDepthEnergy_le {K : ℝ}
    (hK : ∀ᶠ t in 𝓝[>] (0 : ℝ), heatUpperDepthEnergy t ≤ K)
    (T : Finset XiZeroCopy) : ∑ q ∈ T, xiUpperSquaredDepth q ≤ K := by
  by_contra h
  obtain ⟨t, ht, hKt⟩ :=
    ((eventually_initial_packet_lt_heat_energy T (lt_of_not_ge h)).and hK).exists
  exact (not_lt_of_ge hKt) ht

/-- The initial divisor and the whole positive heat family have exactly the same energy bounds. -/
theorem initial_depth_bound_iff_heat_energy_bound (K : ℝ) :
    (∀ T : Finset XiZeroCopy, ∑ q ∈ T, xiUpperSquaredDepth q ≤ K) ↔
      ∀ t : ℝ, 0 < t → heatUpperDepthEnergy t ≤ K := by
  constructor
  · exact fun h _ ht => heatUpperDepthEnergy_le_of_initial_sums h ht
  · intro h
    apply initial_sums_le_of_eventually_heatUpperDepthEnergy_le
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact h t ht

/-- A bounded initial trace is exactly square summability of upper off-line depths. -/
theorem summable_initial_depth_iff_eventually_bounded_heat_energy :
    Summable xiUpperSquaredDepth ↔
      ∃ K : ℝ, ∀ᶠ t in 𝓝[>] (0 : ℝ), heatUpperDepthEnergy t ≤ K := by
  constructor
  · intro hs
    refine ⟨∑' q, xiUpperSquaredDepth q, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact heatUpperDepthEnergy_le_of_initial_sums
      (fun T => Summable.sum_le_tsum T (fun _ _ => sq_nonneg _) hs) ht
  · rintro ⟨K, hK⟩
    exact summable_of_sum_le (fun _ => sq_nonneg _)
      (initial_sums_le_of_eventually_heatUpperDepthEnergy_le hK)

/-- In the finite-energy case, no squared depth is lost in the initial heat limit. -/
theorem tendsto_heatUpperDepthEnergy_of_summable (hs : Summable xiUpperSquaredDepth) :
    Tendsto heatUpperDepthEnergy (𝓝[>] (0 : ℝ)) (𝓝 (∑' q, xiUpperSquaredDepth q)) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨T, hT⟩ := (hs.hasSum.eventually (Ioi_mem_nhds ha)).exists
    exact eventually_initial_packet_lt_heat_energy T hT
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (heatUpperDepthEnergy_le_of_initial_sums
      (fun T => Summable.sum_le_tsum T (fun _ _ => sq_nonneg _) hs) ht).trans_lt hb

/-- If initial squared depths are not summable, heat energy tends to infinity at zero. -/
theorem tendsto_heatUpperDepthEnergy_atTop_of_not_summable (hs : ¬ Summable xiUpperSquaredDepth) :
    Tendsto heatUpperDepthEnergy (𝓝[>] (0 : ℝ)) atTop := by
  rw [Filter.tendsto_atTop]
  intro M
  have hex : ∃ T : Finset XiZeroCopy, M < ∑ q ∈ T, xiUpperSquaredDepth q := by
    by_contra h
    push_neg at h
    exact hs (summable_of_sum_le (fun _ => sq_nonneg _) h)
  obtain ⟨T, hT⟩ := hex
  exact (eventually_initial_packet_lt_heat_energy T hT).mono fun _ h => h.le

/-- Conjugation identifies total energy with twice upper-half energy. -/
theorem heatGlobalVerticalEnergy_eq_two_mul_upper {t : ℝ} (ht : 0 < t) :
    heatGlobalVerticalEnergy t = 2 * heatUpperDepthEnergy t := by
  classical
  let S := (riemannHeat_nonreal_zeros_finite ht).toFinset
  have hconj (z : ℂ) (hz : z ∈ S) : (starRingEnd ℂ) z ∈ S := by
    have hh := (Set.Finite.mem_toFinset _).mp hz
    apply (Set.Finite.mem_toFinset _).mpr
    constructor
    · rw [riemannHeat_conj ht.le, hh.1, map_zero]
    · simpa only [Complex.conj_im, neg_ne_zero] using hh.2
  have hsym : (∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (max (-z.im) 0) ^ 2) =
      ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2 := by
    apply Finset.sum_bij (fun z _ => (starRingEnd ℂ) z) hconj
    · intro z hz w hw he
      have h := congrArg (starRingEnd ℂ) he
      simpa only [Complex.conj_conj] using h
    · intro z hz
      exact ⟨(starRingEnd ℂ) z, hconj z hz, Complex.conj_conj z⟩
    · intro z _
      rw [zeroMult_riemannHeat_conj ht.le, Complex.conj_im]
  have hfull : heatGlobalVerticalEnergy t =
      ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * z.im ^ 2 := by
    rw [heatGlobalVerticalEnergy_eq_weightedSum ht]
    apply tsum_eq_sum
    intro z hz
    have hn : ¬ (riemannHeat t z = 0 ∧ z.im ≠ 0) := by
      simpa only [S, Set.Finite.mem_toFinset, Set.mem_setOf_eq] using hz
    by_cases hf : riemannHeat t z = 0
    · have hi : z.im = 0 := by simpa only [hf, true_and, not_not] using hn
      rw [hi, zero_pow two_ne_zero, mul_zero]
    · rw [zeroMult_riemannHeat_eq_zero ht.le hf, Nat.cast_zero, zero_mul]
  have hsplit (x : ℝ) : x ^ 2 = (max x 0) ^ 2 + (max (-x) 0) ^ 2 := by
    rcases le_total 0 x with hx | hx
    · simp only [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx),
        zero_pow two_ne_zero, add_zero]
    · simp only [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx),
        zero_pow two_ne_zero, neg_sq, zero_add]
  rw [hfull, heatUpperDepthEnergy_eq_sum ht]
  change (∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * z.im ^ 2) =
    2 * ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2
  calc
    _ = (∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (max z.im 0) ^ 2) +
        ∑ z ∈ S, (zeroMult (riemannHeat t) z : ℝ) * (max (-z.im) 0) ^ 2 := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun z _ => by rw [hsplit z.im, mul_add]
    _ = _ := by rw [hsym]; ring

/-- Total heat energy has the same finite initial trace, with both conjugate halves counted. -/
theorem tendsto_heatGlobalVerticalEnergy_of_summable (hs : Summable xiUpperSquaredDepth) :
    Tendsto heatGlobalVerticalEnergy (𝓝[>] (0 : ℝ))
      (𝓝 (2 * ∑' q, xiUpperSquaredDepth q)) := by
  have h : Tendsto (fun t : ℝ => 2 * heatUpperDepthEnergy t) (𝓝[>] (0 : ℝ))
      (𝓝 (2 * ∑' q, xiUpperSquaredDepth q)) :=
    tendsto_const_nhds.mul (tendsto_heatUpperDepthEnergy_of_summable hs)
  apply Tendsto.congr' _ h
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heatGlobalVerticalEnergy_eq_two_mul_upper ht).symm

/-- The surviving count is paid by the energy lost over a doubling interval. -/
theorem time_mul_nonrealZeroCount_le_energy_drop {t : ℝ} (ht : 0 < t) :
    t * (nonrealZeroCount t : ℝ) ≤ heatGlobalVerticalEnergy (t / 2) - heatGlobalVerticalEnergy t := by
  have hh : t / 2 ≤ t := half_le_self ht.le
  have hanti : AntitoneOn (fun s : ℝ => (nonrealZeroCount s : ℝ)) (uIcc (t / 2) t) := by
    rw [uIcc_of_le hh]
    intro a ha b hb hab
    exact_mod_cast nonrealZeroCount_antitoneOn ((half_pos ht).trans_le ha.1)
      ((half_pos ht).trans_le hb.1) hab
  have hInt : (t - t / 2) * (nonrealZeroCount t : ℝ) ≤
      ∫ s in (t / 2)..t, (nonrealZeroCount s : ℝ) := by
    have h := intervalIntegral.integral_mono_on hh
      (f := fun _ : ℝ => (nonrealZeroCount t : ℝ))
      (g := fun s : ℝ => (nonrealZeroCount s : ℝ))
      intervalIntegrable_const hanti.intervalIntegrable (fun s hs => by
        exact_mod_cast nonrealZeroCount_antitoneOn ((half_pos ht).trans_le hs.1) ht hs.2)
    simpa only [intervalIntegral.integral_const, smul_eq_mul] using h
  have hE := heatGlobalVerticalEnergy_add_integral_count_le (half_pos ht) hh
  nlinarith only [hInt, hE]

/-- Finite initial squared-depth mass forces strictly sub-reciprocal heat-count growth. -/
theorem tendsto_time_mul_nonrealZeroCount_zero_of_summable (hs : Summable xiUpperSquaredDepth) :
    Tendsto (fun t : ℝ => t * (nonrealZeroCount t : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hhalf : Tendsto (fun t : ℝ => t / 2) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : Continuous (fun t : ℝ => t / 2) := continuous_id.div_const 2
      simpa only [zero_div] using (hc.tendsto 0).mono_left
        (nhdsWithin_le_nhds : (𝓝[>] (0 : ℝ)) ≤ 𝓝 (0 : ℝ))
    · filter_upwards [self_mem_nhdsWithin] with t ht
      exact half_pos ht
  have hE := tendsto_heatGlobalVerticalEnergy_of_summable hs
  have hdrop : Tendsto (fun t : ℝ => heatGlobalVerticalEnergy (t / 2) - heatGlobalVerticalEnergy t)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [sub_self] using (hE.comp hhalf).sub hE
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact ha.trans_le (mul_nonneg (le_of_lt ht) (Nat.cast_nonneg _))
  · intro b hb
    filter_upwards [hdrop.eventually (Iio_mem_nhds hb), self_mem_nhdsWithin] with t h ht
    exact (time_mul_nonrealZeroCount_le_energy_drop ht).trans_lt h

#print axioms initial_depth_bound_iff_heat_energy_bound
#print axioms summable_initial_depth_iff_eventually_bounded_heat_energy
#print axioms tendsto_heatUpperDepthEnergy_of_summable
#print axioms tendsto_heatUpperDepthEnergy_atTop_of_not_summable
#print axioms heatGlobalVerticalEnergy_eq_two_mul_upper
#print axioms tendsto_heatGlobalVerticalEnergy_of_summable
#print axioms time_mul_nonrealZeroCount_le_energy_drop
#print axioms tendsto_time_mul_nonrealZeroCount_zero_of_summable

end GaloisForLFunctions.ArithmeticElectrostatics
