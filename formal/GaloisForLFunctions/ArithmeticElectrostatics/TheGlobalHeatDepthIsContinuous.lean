import GaloisForLFunctions.ArithmeticElectrostatics.TheRealExteriorDissipatesHeatDepth
import GaloisForLFunctions.RHTower.Heat.HeatZeroSumContinuity

/-!
# Continuity of the global vertical heat energy

At positive time the nonreal divisor is finite. Uniform confinement on
positive-time intervals turns its squared-depth sum into a compactly supported
zero sum. Multiplicity conservation makes this energy continuous through
collisions.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.HTGeometry
open RHTower.DeBruijn

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section


private theorem divisor_toNat_eq_zeroMult {f : ℂ → ℂ}
    (hf : AnalyticOnNhd ℂ f univ) (z : ℂ) :
    ((MeromorphicOn.divisor f univ) z).toNat = zeroMult f z := by
  rw [divisor_univ_eq_analyticOrder hf, zeroMult]
  by_cases htop : analyticOrderAt f z = ⊤
  · rw [htop]
    rfl
  · obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
    rw [← hn]
    rfl

/-- Total squared imaginary depth of the positive-time divisor, with multiplicity. -/
def heatGlobalVerticalEnergy (t : ℝ) : ℝ :=
  ∑ q ∈ heatNonrealCopies t, (zeroCopyPoint (riemannHeat t) q).im ^ 2

theorem heatGlobalVerticalEnergy_nonneg (t : ℝ) : 0 ≤ heatGlobalVerticalEnergy t :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem summable_heatDepthCopies {t : ℝ} (ht : 0 < t) :
    Summable (fun q : ZeroCopy (riemannHeat t) => (zeroCopyPoint (riemannHeat t) q).im ^ 2) := by
  apply summable_of_hasFiniteSupport
  refine (heatNonrealCopies t).finite_toSet.subset ?_
  intro q hq
  apply (mem_heatNonrealCopies ht q).mpr
  intro hz
  exact hq (by
    change (zeroCopyPoint (riemannHeat t) q).im ^ 2 = 0
    rw [hz, zero_pow two_ne_zero])

/-- Copy indexing and analytic zero multiplicities give the same energy. -/
theorem heatGlobalVerticalEnergy_eq_weightedSum {t : ℝ} (ht : 0 < t) :
    heatGlobalVerticalEnergy t = heatWeightedZeroSum (fun z => z.im ^ 2) t := by
  classical
  have hs := summable_heatDepthCopies ht
  have hsum : heatGlobalVerticalEnergy t =
      ∑' q : ZeroCopy (riemannHeat t), (zeroCopyPoint (riemannHeat t) q).im ^ 2 := by
    symm
    apply tsum_eq_sum
    intro q hq
    have hi : (zeroCopyPoint (riemannHeat t) q).im = 0 := by
      by_contra h
      exact hq ((mem_heatNonrealCopies ht q).mpr h)
    rw [hi, zero_pow two_ne_zero]
  let g : ℂ → ℝ := fun z => (zeroMult (riemannHeat t) z : ℝ) * z.im ^ 2
  have hsupport : Function.support g ⊆ (MeromorphicOn.divisor (riemannHeat t) univ).support := by
    intro z hz hd
    have hm : zeroMult (riemannHeat t) z = 0 := by
      rw [← divisor_toNat_eq_zeroMult (riemannHeat_analytic ht.le), hd]
      rfl
    exact hz (by simp only [g, hm, Nat.cast_zero, zero_mul])
  rw [hsum, hs.tsum_sigma]
  change _ = ∑' z : ℂ, g z
  rw [← tsum_subtype_eq_of_support_subset hsupport]
  apply tsum_congr
  intro z
  simp only [zeroCopyPoint, tsum_fintype, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]
  rw [divisor_toNat_eq_zeroMult (riemannHeat_analytic ht.le)]

/-- Every interval bounded away from zero has one bounded region containing all nonreal zeros. -/
theorem exists_heat_nonreal_norm_bound {a : ℝ} (ha : 0 < a) :
    ∃ R : ℝ, ∀ t : ℝ, a ≤ t → ∀ z : ℂ,
      riemannHeat t z = 0 → z.im ≠ 0 → ‖z‖ < R := by
  obtain ⟨X, hX⟩ := exists_riemannHeat_zeros_real_uniform ha
  refine ⟨max X 0 + 1, fun t hat z hz hi => ?_⟩
  by_cases ht8 : t ≤ 1 / 8
  · have hr : |z.re| < X := lt_of_not_ge fun h => hi (hX t ⟨hat, ht8⟩ z hz h)
    have him := abs_im_le_half_of_riemannHeat_eq_zero (ha.trans_le hat) hz
    have hn := Complex.norm_le_abs_re_add_abs_im z
    linarith only [hr, him, hn, le_max_left X 0]
  · exact False.elim (hi (riemannHeat_zeros_real (le_of_not_ge ht8) hz))

/-- Collisions preserve the global squared-depth energy continuously. -/
theorem continuousOn_heatGlobalVerticalEnergy : ContinuousOn heatGlobalVerticalEnergy (Ioi 0) := by
  intro t ht
  change 0 < t at ht
  obtain ⟨R, hR⟩ := exists_heat_nonreal_norm_bound (half_pos ht)
  let Ψ : ℂ → ℝ := fun z => max 0 (min 1 (R + 1 - ‖z‖)) * z.im ^ 2
  have hΨ : Continuous Ψ := by fun_prop
  have hsupp : ∀ s : ℝ, 0 ≤ s → ∀ z : ℂ, riemannHeat s z = 0 → R + 1 ≤ ‖z‖ → Ψ z = 0 := by
    intro s _ z _ hz
    have h : min 1 (R + 1 - ‖z‖) ≤ 0 := (min_le_right _ _).trans (by linarith only [hz])
    simp only [Ψ, max_eq_left h, zero_mul]
  have hc := continuous_heatWeightedZeroSum_clamped_of_support hΨ (R + 1) hsupp
  have heq : ∀ s : ℝ, t / 2 ≤ s → heatGlobalVerticalEnergy s = heatWeightedZeroSum Ψ (max s 0) := by
    intro s hs
    have hs0 : 0 < s := (half_pos ht).trans_le hs
    rw [max_eq_left hs0.le, heatGlobalVerticalEnergy_eq_weightedSum hs0, heatWeightedZeroSum,
      heatWeightedZeroSum]
    apply tsum_congr
    intro z
    by_cases hz : riemannHeat s z = 0
    · by_cases hi : z.im = 0
      · simp only [Ψ, hi, zero_pow two_ne_zero, mul_zero]
      · have hn := hR s hs z hz hi
        have h1 : 1 ≤ R + 1 - ‖z‖ := by linarith only [hn]
        simp only [Ψ, min_eq_left h1, max_eq_right zero_le_one, one_mul]
    · rw [zeroMult_riemannHeat_eq_zero hs0.le hz, Nat.cast_zero, zero_mul, zero_mul]
  have hevent : heatGlobalVerticalEnergy =ᶠ[𝓝 t] (fun s => heatWeightedZeroSum Ψ (max s 0)) := by
    filter_upwards [Ioi_mem_nhds (show t / 2 < t by linarith only [ht])] with s hs
    exact heq s hs.le
  exact (hc.continuousAt.congr hevent.symm).continuousWithinAt

#print axioms continuousOn_heatGlobalVerticalEnergy

end

end GaloisForLFunctions.ArithmeticElectrostatics

