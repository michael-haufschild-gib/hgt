import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheTiltedSplineHasFourthOrderSynthesis
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleAtEveryRoot
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheGevreyProfile

/-!
# The eighth-root receiver for the tilted spline

Fourth-order synthesis transfers negative smooth tests to the normalized
tilted spline whenever the eighth-power overlap error tends to zero.
-/

noncomputable section

set_option autoImplicit false

open MeasureTheory Set Filter Topology RHTower
open scoped Real ContDiff

namespace GaloisForLFunctions.SpacingScaleHarmonicAnalysis

open ArithmeticElectrostatics RenormalizedArithmeticPotentialTheory

/-- The tilted spline detects Weil negativity under eighth-order overlap growth. -/
theorem riemannHypothesis_iff_tiltedSpline_atomicFamilies_nonneg_of_growthEight
    {κ : ℕ → ℝ} (hκ : OverlapGrowthPow 8 κ) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N x (dilate (κ N) (recentredProfile tiltedUnitSpline))) := by
  let φ := recentredProfile tiltedUnitSpline
  have hφ : ContDiff ℝ 2 φ := contDiff_recentredProfile contDiff_tiltedUnitSpline
  have hφ1 : VanishesOff φ := vanishesOff_recentredProfile tiltedUnitSpline_eq_zero
  have hφint : ∫ s, φ s = 1 := integral_recentredProfile integral_tiltedUnitSpline_ne_zero
  obtain ⟨A, -, hAint, happrox⟩ := exists_recentred_tiltedUnitSpline_regularization_bounds
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact WeilSpectral.riemannHypothesis_iff_real_weilPositive.mp hRH _ h2 hc
  · intro H
    by_contra hRH
    rw [WeilSpectral.riemannHypothesis_iff_real_weilPositive] at hRH
    push Not at hRH
    obtain ⟨g, hg, hgc, hneg⟩ := hRH
    change weilQuad g < 0 at hneg
    obtain ⟨G, hG, hGc, hGneg⟩ := exists_smooth_weilQuad_neg contDiff_gevreyProfile
      gevreyProfile_vanishesOff integral_gevreyProfile hg hgc hneg
    obtain ⟨R, -, -, hR, hGR, -, -⟩ :=
      exists_test_bounds (hG.of_le (natCast_le_infty 2)) hGc
    obtain ⟨M, hM0, hM⟩ := exists_iteratedDeriv_bounds hG hGc
    let B := blockSize R
    have hB : 1 ≤ B := one_le_blockSize R
    obtain ⟨he, hV, -, -⟩ := tendsto_em (m := 1) hκ hB (M := M) (A := A) (R' := R + 1)
    have hErr := tendsto_weilErr G (R + 1) he hV
    have h1 := hErr.eventually (gt_mem_nhds (show (0 : ℝ) < -weilQuad G by linarith))
    have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
      tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
    obtain ⟨n, hn1, hn2, hk, hn3⟩ :=
      (h1.and ((hNB.eventually H).and ((hNB.eventually
        (hκ.1.eventually_ge_atTop 1)).and (eventually_ge_atTop 2)))).exists
    obtain ⟨x, D, hx, hD2, hDR, hsup, hlip⟩ :=
      exists_fourthOrderSynthesis hφ hφ1 hφint hAint happrox hG hGR hM hM0 hn3 hk
    have hpert := weilQuad_add_le_of_lip (hG.of_le (natCast_le_infty 2)) hGc
      (fun u hu => hGR u (by linarith)) hD2 hDR (by linarith) hsup hlip hk
    have hpos := hn2 x
    rw [hx, weilQuad_comp_sub (fun u => G u + D u)] at hpos
    linarith

/-- At overlap `2(log N)^α`, every exponent above `1/8` detects RH. -/
theorem riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_log_eighth
    {α : ℝ} (hα : 1 / 8 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop,
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        0 ≤ completeWeilEnergy tiltedUnitSpline (2 * Real.log N ^ α) N x := by
  have hg := overlapGrowthPow_log (q := 8) (show 0 < α by linarith)
    (show 1 < (8 : ℝ) * α by linarith)
  rw [riemannHypothesis_iff_tiltedSpline_atomicFamilies_nonneg_of_growthEight hg]
  have hc : ∀ᶠ N : ℕ in atTop, 0 < 2 * Real.log N ^ α := by
    filter_upwards [eventually_ge_atTop 2] with N hN
    have : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN)
    positivity
  have hk : ∀ N : ℕ, 2 / (2 * Real.log N ^ α / N) = (N : ℝ) / Real.log N ^ α := by
    intro N
    rw [div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]
  constructor
  · intro H
    filter_upwards [H, hc, eventually_ge_atTop 1] with N hN hcN h1
    apply (forall_completeWeilEnergy_nonneg_iff contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      integral_tiltedUnitSpline_ne_zero hcN h1).mpr
    rwa [hk]
  · intro H
    filter_upwards [H, hc, eventually_ge_atTop 1] with N hN hcN h1
    have h := (forall_completeWeilEnergy_nonneg_iff contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos
      integral_tiltedUnitSpline_ne_zero hcN h1).mp hN
    rwa [hk] at h

/-- Smooth pole-free negativity survives fourth-order tilted-spline synthesis. -/
theorem frequently_tiltedSpline_poleHyperplane_markov_neg {κ : ℕ → ℝ}
    (hκ : OverlapGrowthPow 8 κ) {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G)
    (hGc : HasCompactSupport G) (hG0 : poleMomentNeg G = 0) (hneg : markovQuad G < 0) :
    ∃ᶠ N : ℕ in atTop, ∃ x : ℕ → ℝ,
      poleMomentNeg (atomicTest N x (dilate (κ N) (recentredProfile tiltedUnitSpline))) = 0 ∧
      markovQuad (atomicTest N x (dilate (κ N) (recentredProfile tiltedUnitSpline))) < 0 := by
  let φ := recentredProfile tiltedUnitSpline
  have hφ : ContDiff ℝ 2 φ := contDiff_recentredProfile contDiff_tiltedUnitSpline
  have hφ1 : VanishesOff φ := vanishesOff_recentredProfile tiltedUnitSpline_eq_zero
  have hφint : ∫ s, φ s = 1 := integral_recentredProfile integral_tiltedUnitSpline_ne_zero
  obtain ⟨A, -, hAint, happrox⟩ := exists_recentred_tiltedUnitSpline_regularization_bounds
  obtain ⟨h, hh, hhc, hh0⟩ := exists_smooth_bump_poleMomentNeg_pos
  have hG2 : ContDiff ℝ 2 G := hG.of_le (natCast_le_infty 2)
  have hh2 : ContDiff ℝ 2 h := hh.of_le (natCast_le_infty 2)
  obtain ⟨RG, -, -, hRG, hGR, -, -⟩ := exists_test_bounds hG2 hGc
  obtain ⟨Rh, -, -, hRh, hhR, -, -⟩ := exists_test_bounds hh2 hhc
  set R := max RG Rh
  have hR : 0 ≤ R := hRG.trans (le_max_left _ _)
  have hGR' : SupportedIn R G := fun v hv => hGR v (lt_of_le_of_lt (le_max_left _ _) hv)
  have hhR' : SupportedIn R h := fun v hv => hhR v (lt_of_le_of_lt (le_max_right _ _) hv)
  obtain ⟨MG, hMG0, hMG⟩ := exists_iteratedDeriv_bounds hG hGc
  obtain ⟨Mh, hMh0, hMh⟩ := exists_iteratedDeriv_bounds hh hhc
  obtain ⟨hhsup, hhlip⟩ := sup_lip_of_iteratedDeriv_bounds hh hMh
  obtain ⟨Err, hErr, hle⟩ := stableForm_markovQuad.2 G hG2 hGc (R + 1) (by linarith)
    (fun v hv => hGR' v (by linarith))
  set B := blockSize R
  have hB : 1 ≤ B := one_le_blockSize R
  obtain ⟨he₁, -, hlog, hℓ₁⟩ := tendsto_em (m := 1) hκ hB (M := MG) (A := A) (R' := R + 1)
  obtain ⟨he₂, -, -, hℓ₂⟩ := tendsto_em (m := 1) hκ hB (M := Mh) (A := A) (R' := R + 1)
  have hNB : Tendsto (fun n : ℕ => n * B) atTop atTop :=
    tendsto_atTop_mono (fun n => Nat.le_mul_of_pos_right n hB) tendsto_id
  set C := 2 * (Real.exp ((R + 1) / 2) * (2 * (R + 1))) / poleMomentNeg h
  obtain ⟨hE, hV⟩ := tendsto_comb (R' := R + 1) (C := C) (Mh := Mh 0) (Lh := Mh 1)
    (k := fun n => κ (n * B)) (hκ.1.comp hNB) he₁ he₂ hlog hℓ₁ hℓ₂
  have h1 := (hErr _ _ hE hV).eventually (gt_mem_nhds (show (0 : ℝ) < -markovQuad G by linarith))
  have hc0 : 0 < poleMomentNeg h / 2 / (Real.exp ((R + 1) / 2) * (2 * (R + 1))) := by
    have := Real.exp_pos ((R + 1) / 2); positivity
  have h2 := he₂.eventually (gt_mem_nhds hc0)
  have h3 := hNB.eventually (hκ.1.eventually_ge_atTop 1)
  rw [Filter.frequently_atTop]
  intro a
  obtain ⟨n, hn1, hn2, hk, hn3, hna⟩ :=
    (h1.and (h2.and (h3.and ((eventually_ge_atTop 2).and (eventually_ge_atTop a))))).exists
  refine ⟨n * B, hna.trans (Nat.le_mul_of_pos_right n hB), ?_⟩
  obtain ⟨xG, DG, hxG, hDG2, hDGR, hDGs, hDGl⟩ :=
    exists_fourthOrderSynthesis hφ hφ1 hφint hAint happrox hG hGR' hMG hMG0 hn3 hk
  obtain ⟨xh, Dh, hxh, hDh2, hDhR, hDhs, hDhl⟩ :=
    exists_fourthOrderSynthesis hφ hφ1 hφint hAint happrox hh hhR' hMh hMh0 hn3 hk
  have hsmall : Real.exp ((R + 1) / 2) * (2 * (R + 1) * emErr Mh A 1 (κ (n * B)) n) ≤
      poleMomentNeg h / 2 := by
    have hpos : 0 < Real.exp ((R + 1) / 2) * (2 * (R + 1)) := by
      have := Real.exp_pos ((R + 1) / 2); positivity
    have := (lt_div_iff₀ hpos).mp hn2
    linarith
  obtain ⟨t, ht, ht0⟩ := exists_pole_correction hG2.continuous hGc hG0 hh2.continuous hhc hh0
    hDG2.continuous hDGR hDGs hDh2.continuous hDhR hDhs (by linarith) hsmall
  have hT : |t| ≤ C * emErr MG A 1 (κ (n * B)) n := by
    refine ht.trans (le_of_eq ?_); simp only [C]; ring
  obtain ⟨hD2, hDR, hsup, hlip⟩ := comb_perturbation hh2 (fun v hv => hhR' v (by linarith))
    hhsup hhlip hDG2 hDGR hDGs hDGl hDh2 hDhR hDhs hDhl hT
  set D : ℝ → ℝ := fun v => DG v - t * (h v + Dh v)
  set c := Real.log n + R
  refine ⟨fun j => xG j - t * xh j, ?_⟩
  have hx : atomicTest (n * B) (fun j => xG j - t * xh j) (dilate (κ (n * B)) φ) =
      fun v => (fun w => G w + D w) (v - c) := by
    rw [atomicTest_sub_const_mul, hxG, hxh]
    funext v
    simp only [D]
    ring
  have hGD2 : ContDiff ℝ 2 fun w => G w + D w := hG2.add hD2
  have hGDc : HasCompactSupport fun w => G w + D w :=
    hGc.add (hasCompactSupport_of_vanishes hDR)
  rw [hx, poleMomentNeg_comp_sub (fun w => G w + D w) c, markovQuad_comp_sub hGD2 hGDc c]
  refine ⟨by rw [ht0, mul_zero], ?_⟩
  have := hle D _ _ _ hD2 hDR hsup hlip hk
  linarith

/-- The pole-hyperplane receiver for the tilted spline has growth order eight. -/
theorem riemannHypothesis_iff_tiltedSpline_poleHyperplane_nonneg_of_growthEight
    {κ : ℕ → ℝ} (hκ : OverlapGrowthPow 8 κ) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : ℕ → ℝ,
      poleMomentNeg (atomicTest N x (dilate (κ N) (recentredProfile tiltedUnitSpline))) = 0 →
        0 ≤ markovQuad (atomicTest N x (dilate (κ N) (recentredProfile tiltedUnitSpline))) := by
  have hφ := contDiff_recentredProfile contDiff_tiltedUnitSpline
  have hφ1 := vanishesOff_recentredProfile tiltedUnitSpline_eq_zero
  constructor
  · intro hRH
    filter_upwards [hκ.1.eventually_gt_atTop 0] with N hk x h0
    obtain ⟨h2, hc⟩ := atomicTest_dilate_mem hφ hφ1 hk N x
    exact riemannHypothesis_iff_forall_exp_neg_half_moment_zero_markovEnergy_nonneg.mp hRH _ h2 hc
      h0
  intro H
  by_contra hRH
  obtain ⟨u, hu, huc, -, hpole, hneg⟩ := exists_even_poleFree_negative_of_not_riemannHypothesis hRH
  have hu0 : poleMomentNeg u = 0 := by
    rw [paperFT_ofReal_I_half] at hpole
    exact_mod_cast hpole
  have hQu : weilQuad u < 0 := by
    rw [zeta_W_eq_weilFullFunctional (f := fun x => (u x : ℂ)) (Complex.ofRealCLM.contDiff.comp hu)
      (huc.comp_left Complex.ofReal_zero)] at hneg
    exact hneg
  have hMu : markovQuad u < 0 := by
    rw [markovQuad_eq hu huc, hu0, zero_mul, mul_zero, sub_zero]
    exact hQu
  obtain ⟨G, hG, hGc, hG0, hGneg⟩ := exists_smooth_poleFree_markov_neg contDiff_gevreyProfile
    gevreyProfile_vanishesOff integral_gevreyProfile hu huc hu0 hMu
  obtain ⟨N, ⟨x, hx0, hxM⟩, hN⟩ :=
    ((frequently_tiltedSpline_poleHyperplane_markov_neg hκ hG hGc hG0 hGneg).and_eventually
      H).exists
  exact absurd (hN x hx0) (not_le.mpr hxM)

#print axioms riemannHypothesis_iff_tiltedSpline_atomicFamilies_nonneg_of_growthEight
#print axioms riemannHypothesis_iff_tiltedSpline_completeWeil_nonneg_log_eighth
#print axioms riemannHypothesis_iff_tiltedSpline_poleHyperplane_nonneg_of_growthEight

end GaloisForLFunctions.SpacingScaleHarmonicAnalysis
