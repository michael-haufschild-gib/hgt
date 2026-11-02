import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheHorizonLayerBecomesWeilsForm
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFlipThresholdGrowsLikeAPowerOfThePrime
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.RHTower.WeilMarkovOnePoleHyperplane
import GaloisForLFunctions.RHTower.WeilDecayClassRHCriterion
import GaloisForLFunctions.RHTower.WeilFullConeRiemannKernelRigidity

/-!
# The horizon criterion

For the tilted spline (`β = 7`) the atom transform decays like `(1 + |u|)^{−8}`, so the horizon
theorem applies with `p = 8`: past the critical curve `c⁸ ≫ log N` the horizon layer of the complete
Weil family, divided by the overlap, is `κ Q(H)` with `κ = (∫φ)²/∫φ² > 0`, and at `c⁸ ≍ K log N` it is
`κ Q(H)` up to `O(1/K)`.

* **Decay of the tilted spline** (`tiltedUnitSpline_decay`): `‖φ̂(u)‖² ≤ C (1 + |u|)^{−8}`.
* **Weil's criterion on window profiles** (`riemannHypothesis_iff_halfWeight_nonneg`): RH holds iff
  `Q(e^{y/2} h) ≥ 0` for every `C²` profile `h` supported in some `[−A, 0]`.
* **The horizon criterion** (`riemannHypothesis_iff_horizon_layer`): RH holds iff, for every window
  profile and every schedule past the critical curve, the horizon block of the tilted spline is
  eventually `≥ −ε` after division by the overlap.

The horizon layer of the complete family carries the whole of Weil's criterion; the degenerating
bulk carries none of it (`TheZeroLedgerOfTheBulk`).
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory

/-- The tilted spline vanishes off `[0, 1]`. -/
theorem tiltedUnitSpline_support : ∀ u, u ∉ Set.Icc 0 1 → tiltedUnitSpline u = 0 := fun u hu => by
  have := tiltedUnitSpline_atom_support (w := 1) one_pos u hu
  simpa [atomDilate] using this

/-- The decay constant `128⁴ cosh⁸ 1/64`. -/
def tiltedDecayConst : ℝ := 128 ^ 4 * Real.cosh 1 ^ 8 / 64

/-- **Decay of the tilted spline**: `‖φ̂(u)‖² ≤ C (1 + |u|)^{−8}`. -/
theorem tiltedUnitSpline_decay (u : ℝ) :
    ‖paperFT (cx tiltedUnitSpline) u‖ ^ 2 ≤ tiltedDecayConst * (1 + |u|) ^ (-(8 : ℝ)) := by
  have h1 := norm_paperFT_tiltedUnitSpline_eq u
  have h2 := BiScaleUncertainty.ChebyshevGauge.norm_paperFT_splineProbe_ofReal_le (u / 8)
  have hq : 0 < 1 + (u / 8) ^ 2 := by positivity
  have hp : 0 < 1 + |u| := by positivity
  have hc : 0 ≤ Real.cosh 1 ^ 4 := by positivity
  have hle : ‖paperFT (cx tiltedUnitSpline) u‖ ≤ (1 / 8) * (Real.cosh 1 ^ 4 / (1 + (u / 8) ^ 2) ^ 2) := by
    rw [h1]; exact mul_le_mul_of_nonneg_left h2 (by norm_num)
  have hsq := pow_le_pow_left₀ (norm_nonneg _) hle 2
  have hbase : (1 + |u|) ^ 2 ≤ 128 * (1 + (u / 8) ^ 2) := by
    nlinarith [sq_abs u, sq_nonneg (|u| - 1)]
  have hbase8 : (1 + |u|) ^ 8 ≤ 128 ^ 4 * ((1 + (u / 8) ^ 2) ^ 2) ^ 2 := by
    have := pow_le_pow_left₀ (by positivity) hbase 4
    calc (1 + |u|) ^ 8 = ((1 + |u|) ^ 2) ^ 4 := by ring
      _ ≤ (128 * (1 + (u / 8) ^ 2)) ^ 4 := this
      _ = 128 ^ 4 * ((1 + (u / 8) ^ 2) ^ 2) ^ 2 := by ring
  rw [Real.rpow_neg hp.le, show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  refine hsq.trans ?_
  have hq0 : 0 < ((1 + (u / 8) ^ 2) ^ 2) ^ 2 := by positivity
  have hp8 : 0 < (1 + |u|) ^ 8 := by positivity
  have hfin : (((1 + (u / 8) ^ 2) ^ 2) ^ 2)⁻¹ ≤ 128 ^ 4 * ((1 + |u|) ^ 8)⁻¹ := by
    rw [← one_div, ← div_eq_mul_inv, div_le_div_iff₀ hq0 hp8, one_mul]; exact hbase8
  rw [tiltedDecayConst]
  calc ((1 / 8) * (Real.cosh 1 ^ 4 / (1 + (u / 8) ^ 2) ^ 2)) ^ 2
      = Real.cosh 1 ^ 8 / 64 * (((1 + (u / 8) ^ 2) ^ 2) ^ 2)⁻¹ := by
        generalize (1 + (u / 8) ^ 2) ^ 2 = q
        rw [div_eq_mul_inv (Real.cosh 1 ^ 4), mul_pow, mul_pow, inv_pow]
        ring
    _ ≤ Real.cosh 1 ^ 8 / 64 * (128 ^ 4 * ((1 + |u|) ^ 8)⁻¹) :=
        mul_le_mul_of_nonneg_left hfin (by positivity)
    _ = 128 ^ 4 * Real.cosh 1 ^ 8 / 64 * ((1 + |u|) ^ 8)⁻¹ := by ring

/-! ### Weil's criterion on window profiles -/

/-- RH holds iff Weil's quadratic form is nonnegative on every real `C²` test of compact support. -/
theorem riemannHypothesis_iff_weilQuad_nonneg :
    RiemannHypothesis ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g → 0 ≤ weilQuad g := by
  constructor
  · intro hRH g hg hgc
    rw [LogCells.weilQuad_eq_zetaW hg hgc]
    exact RHTower.W_re_nonneg_of_riemannHypothesis hRH (Complex.ofRealCLM.contDiff.comp hg)
      (hgc.comp_left Complex.ofReal_zero)
  · intro hW
    refine RHTower.WeilSpectral.riemannHypothesis_iff_real_weilPositive.mpr fun g hg hgc => ?_
    have hcx : ContDiff ℝ 2 (fun u => (g u : ℂ)) := Complex.ofRealCLM.contDiff.comp hg
    rw [← RHTower.zeta_W_eq_weilFullFunctional hcx (hgc.comp_left Complex.ofReal_zero)]
    have := hW g hg hgc
    rwa [LogCells.weilQuad_eq_zetaW hg hgc] at this

/-- **Weil's criterion on window profiles**: RH holds iff `Q(e^{y/2} h) ≥ 0` for every `C²` profile
`h` supported in some `[−A, 0]`. -/
theorem riemannHypothesis_iff_halfWeight_nonneg :
    RiemannHypothesis ↔ ∀ (A : ℝ) (h : ℝ → ℝ), 0 ≤ A → ContDiff ℝ 2 h →
      (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) → 0 ≤ weilQuad (halfWeight h) := by
  rw [riemannHypothesis_iff_weilQuad_nonneg]
  constructor
  · intro hW A h hA hh hsupp
    exact hW _ (contDiff_halfWeight hh) (hasCompactSupport_halfWeight
      (hasCompactSupport_of_window hsupp))
  · intro hW g hg hgc
    obtain ⟨R, hR⟩ := hgc.isCompact.isBounded.subset_closedBall 0
    set R' := max R 0 with hR'
    have hR0 : 0 ≤ R' := le_max_right _ _
    have hgR : ∀ u, R' < |u| → g u = 0 := fun u hu => by
      by_contra hne
      have := hR (subset_tsupport g hne)
      rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
      linarith [le_max_left R 0]
    set h : ℝ → ℝ := fun y => Real.exp (-(y / 2)) * g (y + R') with hh
    have hhd : ContDiff ℝ 2 h :=
      (Real.contDiff_exp.comp ((contDiff_id.div_const 2).neg)).mul
        (hg.comp (contDiff_id.add contDiff_const))
    have hsupp : ∀ y, y ∉ Set.Icc (-(2 * R')) 0 → h y = 0 := by
      intro y hy
      simp only [hh]
      rw [hgR (y + R') ?_, mul_zero]
      simp only [Set.mem_Icc, not_and_or, not_le] at hy
      rcases hy with hy | hy
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
    have hhalf : halfWeight h = fun y => g (y - (-R')) := by
      funext y
      simp only [halfWeight, hh, sub_neg_eq_add, ← mul_assoc, ← Real.exp_add, add_neg_cancel,
        Real.exp_zero, one_mul]
    have := hW (2 * R') h (by linarith) hhd hsupp
    rwa [hhalf, weilQuad_comp_sub] at this

/-! ### The horizon criterion -/

theorem tendsto_sqrt_div : Tendsto (fun N : ℕ => Real.sqrt (N + 1) / N) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => Real.sqrt 2 / Real.sqrt N) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop ((Real.tendsto_sqrt_atTop).comp tendsto_natCast_atTop_atTop)
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ h1
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  rw [div_le_div_iff₀ hN0 (Real.sqrt_pos.mpr hN0)]
  calc Real.sqrt (N + 1) * Real.sqrt N ≤ Real.sqrt (2 * N) * Real.sqrt N := by
        gcongr; have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith
    _ = Real.sqrt 2 * N := by
        rw [Real.sqrt_mul (by norm_num), mul_assoc, Real.mul_self_sqrt hN0.le]

theorem tendsto_log_div_pow_eight :
    Tendsto (fun N : ℕ => (1 + Real.log N) / Real.sqrt (N + 1) ^ (8 : ℝ)) atTop (𝓝 0) := by
  have h1 : Tendsto (fun N : ℕ => ((N : ℝ) + 1)⁻¹) atTop (𝓝 0) :=
    (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).inv_tendsto_atTop
  refine squeeze_zero' (Eventually.of_forall fun N => ?_) ?_ h1
  · have : 0 ≤ 1 + Real.log N := by
      rcases Nat.eq_zero_or_pos N with h0 | h0
      · subst h0; simp
      · have := Real.log_nonneg (show (1 : ℝ) ≤ N by exact_mod_cast h0); linarith
    positivity
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hp : Real.sqrt (N + 1) ^ (8 : ℝ) = ((N : ℝ) + 1) ^ 4 := by
    rw [show (8 : ℝ) = ((8 : ℕ) : ℝ) by norm_num, Real.rpow_natCast,
      show (8 : ℕ) = 2 * 4 by norm_num, pow_mul, Real.sq_sqrt (by positivity)]
  rw [hp, div_le_iff₀ (by positivity)]
  have hlog : Real.log N ≤ N := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
  have : ((N : ℝ) + 1)⁻¹ * ((N : ℝ) + 1) ^ 4 = ((N : ℝ) + 1) ^ 3 := by
    field_simp
  rw [this]
  nlinarith [pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) (show (1 : ℝ) ≤ N + 1 by linarith) 3,
    one_le_pow₀ (show (1 : ℝ) ≤ N + 1 by linarith) (n := 2)]

/-- **The horizon criterion.** RH holds iff, for every window profile `h` and every schedule past
the critical curve, the horizon block of the tilted spline, divided by the overlap, is eventually
at least `−ε` for every `ε > 0`. -/
theorem riemannHypothesis_iff_horizon_layer :
    RiemannHypothesis ↔ ∀ (A : ℝ) (h : ℝ → ℝ) (c : ℕ → ℝ), 0 ≤ A → ContDiff ℝ 2 h →
      (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) → (∀ N, 0 < c N) →
      Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => (1 + Real.log N) / c N ^ (8 : ℝ)) atTop (𝓝 0) →
      ∀ ε > 0, ∀ᶠ N : ℕ in atTop, -ε ≤ (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2) := by
  have hκ : 0 < (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) :=
    div_pos (lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 integral_tiltedUnitSpline_ne_zero)))
      integral_tiltedUnitSpline_sq_pos
  have hdecay := tiltedUnitSpline_decay
  have hC : 0 ≤ tiltedDecayConst := by unfold tiltedDecayConst; positivity
  have hlim : ∀ (A : ℝ) (h : ℝ → ℝ) (c : ℕ → ℝ), 0 ≤ A → ContDiff ℝ 2 h →
      (∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) → (∀ N, 0 < c N) →
      Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => (1 + Real.log N) / c N ^ (8 : ℝ)) atTop (𝓝 0) →
      Tendsto (fun N : ℕ => (c N)⁻¹ * (weilQuad (atomicTest N (horizonWeights h N)
        (atomDilate tiltedUnitSpline (c N / N))) / ∫ u, atomDilate tiltedUnitSpline (c N / N) u ^ 2))
        atTop (𝓝 ((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
          weilQuad (halfWeight h))) :=
    fun A h c hA hh hsupp hc hcN hsup => tendsto_horizon_layer_supercritical
      contDiff_tiltedUnitSpline tiltedUnitSpline_support integral_tiltedUnitSpline_sq_pos
      (by norm_num : (1 : ℝ) < 8) hC hdecay hh hA hsupp hc hcN hsup
  rw [riemannHypothesis_iff_halfWeight_nonneg]
  constructor
  · intro hW A h c hA hh hsupp hc hcN hsup ε hε
    have hL := hlim A h c hA hh hsupp hc hcN hsup
    have hnn : 0 ≤ (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) := mul_nonneg hκ.le (hW A h hA hh hsupp)
    filter_upwards [hL.eventually (lt_mem_nhds (show -ε < _ by linarith))] with N hN
    exact hN.le
  · intro hH A h hA hh hsupp
    have hc : ∀ N : ℕ, 0 < Real.sqrt (N + 1) := fun N => Real.sqrt_pos.mpr (by positivity)
    have hL := hlim A h (fun N => Real.sqrt (N + 1)) hA hh hsupp hc tendsto_sqrt_div
      tendsto_log_div_pow_eight
    have hge : ∀ ε > 0, -ε ≤ (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) := fun ε hε =>
      ge_of_tendsto hL (hH A h _ hA hh hsupp hc tendsto_sqrt_div tendsto_log_div_pow_eight ε hε)
    have hprod : 0 ≤ (∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h) := by
      by_contra hneg
      push Not at hneg
      have := hge (-((∫ u, tiltedUnitSpline u) ^ 2 / (∫ u, tiltedUnitSpline u ^ 2) *
        weilQuad (halfWeight h)) / 2) (by linarith)
      linarith
    exact nonneg_of_mul_nonneg_right (by linarith) hκ |> fun h' => by
      rcases le_or_gt 0 (weilQuad (halfWeight h)) with h0 | h0
      · exact h0
      · nlinarith

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
