import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarMatrixRowHasItsStrongProfile
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePolarSampleProfileAdmitsLipschitzApproximation
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.LogarithmicCutoffsPreserveCollarDualBounds
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.AtomicSynthesisRecoversLipschitzTests
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PolarWindowsHaveTheirPhysicalPairings
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.StrongSquareMeansPreservePairings
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.PhysicalWindowWeightsRecoverTheirProfiles
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheCriticalPositivityThresholdLaw

/-!
# Polar rows transfer to strong physical limits

Sampled row convergence and lower-strip dual bounds give compact Lipschitz
approximation on every bounded collar ball. Smooth-window identification then
extends to finite-Gamma profiles by one-sided mollification and weighted source continuity.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Finset RHTower
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
open CriticalArithmeticCorrelationTheory RenormalizedArithmeticPotentialTheory
  SpacingScaleHarmonicAnalysis ArithmeticCastelnuovoSeveri WindowTowerOfSpecZ


/-- The normalized explicit polar row has the sampling normalization of adjoint synthesis. -/
theorem normalized_polarSample_eq_logSample {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N) :
    (Real.sqrt (Real.log N) / c) •
      polarSampleVector c N (fun n => polarMatrixSampleProfile ((n : ℝ) / N)) =
    horizonProfileVector (fun n => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      polarLogSampleProfile ((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2))
        (Real.log ((n : ℝ) / N))) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hI₂ := integral_tiltedUnitSpline_sq_pos
  ext i
  have hn0 : (0 : ℝ) < i.1 := by exact_mod_cast (mem_Icc.mp i.2).1
  change (Real.sqrt (Real.log N) / c) *
    ((c / N) * Real.sqrt i.1 * polarMatrixSampleProfile ((i.1 : ℝ) / N) /
      Real.sqrt (Real.log N)) = _
  change _ = (∫ u, tiltedUnitSpline u) / Real.sqrt N *
    polarLogSampleProfile ((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2))
      (Real.log ((i.1 : ℝ) / N))
  unfold polarLogSampleProfile polarMatrixSampleProfile
  rw [Real.exp_log (div_pos hn0 hN0), Real.sqrt_div hn0.le]
  field_simp [hc.ne', hN0.ne', hI₂.ne', (Real.sqrt_pos.mpr hL).ne', (Real.sqrt_pos.mpr hN0).ne']
  rw [Real.sq_sqrt hN0.le]
  ring

/-- A fixed compact Lipschitz test approximates the polar residual in its full normalized dual
collar norm, to arbitrary precision along each positive critical curve. -/
theorem exists_polar_residual_weighted_lipschitz_approximation
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      ∀ᶠ N : ℕ in atTop,
      topCollarDualSeventhMass (N / linearDefectCutoff (c N)) N
        ((Real.sqrt (Real.log N) / c N) • conductorResidualVector (c N) 1 N -
          horizonProfileVector (fun n => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
            f (Real.log ((n : ℝ) / N))) N) ≤ ε := by
  obtain ⟨C, hC, hbottom⟩ := eventually_normalized_truncated_residual_bound hc hR hcrit
  let δ := min 1 (ε / (16 * C))
  have hδ : 0 < δ := lt_min zero_lt_one (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hCδ : C * δ ≤ ε / 16 := by
    have hh := mul_le_mul_of_nonneg_left (min_le_right 1 (ε / (16 * C))) hC.le
    exact hh.trans_eq (by field_simp [hC.ne'])
  let a := Real.log δ - 2
  have hea : Real.exp (a + 2) = δ := by
    dsimp only [a]
    rw [sub_add_cancel, Real.exp_log hδ]
  let I₁ := ∫ u, tiltedUnitSpline u
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  have hI₁ : I₁ ≠ 0 := integral_tiltedUnitSpline_ne_zero
  have hI₁sq : 0 < I₁ ^ 2 := sq_pos_of_ne_zero hI₁
  obtain ⟨f, K, hfc, hLip, _, hf⟩ := exists_polarLogSampleProfile_lipschitz_approximation
    a (I₁ / I₂) (by positivity : 0 < ε / (16 * I₁ ^ 2))
  refine ⟨f, K, hfc, hLip, ?_⟩
  have htop := tendsto_topWindow_polar_residual_profile (Real.exp_pos a) hc hR hcrit
  filter_upwards [eventually_ge_atTop 2, hbottom, hf,
    htop.eventually (gt_mem_nhds (by positivity : 0 < ε / 16))]
    with N hN hbottomN hfN htopN
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : 1 ≤ N := by omega
  let M := N / linearDefectCutoff (c N)
  let α := Real.sqrt (Real.log N) / c N
  let r := conductorResidualVector (c N) 1 N
  let p := polarSampleVector (c N) N (fun n => polarMatrixSampleProfile ((n : ℝ) / N))
  let v := horizonProfileVector (fun n => I₁ / Real.sqrt N * f (Real.log ((n : ℝ) / N))) N
  let u₀ := α • r - horizonLogCutoff a (α • r)
  let u₁ := horizonLogCutoff a (α • (r - p))
  let u₂ := horizonLogCutoff a (α • p) - v
  have hα : α ^ 2 = Real.log N / c N ^ 2 := by
    dsimp only [α]
    rw [div_pow, Real.sq_sqrt (Real.log_natCast_nonneg N)]
  have h₀ : topCollarDualSeventhMass M N u₀ ≤ ε / 16 := by
    have hh := topCollarDualSeventhMass_sub_logCutoff_le (M := M) a hN1 (α • r)
    rw [hea, truncatedCollarDualSeventhMass_smul, hα] at hh
    have hb := hbottomN (m := 1) one_pos hδ.le hδ1
    simp only [Nat.cast_one, one_pow, mul_one] at hb
    exact hh.trans (hb.trans hCδ)
  have h₁ : topCollarDualSeventhMass M N u₁ ≤ ε / 16 := by
    have hh := topCollarDualSeventhMass_logCutoff_le_topWindow (M := M) a hN1 (α • (r - p))
    rw [topWindowResidualMass_smul, hα] at hh
    exact hh.trans htopN.le
  have h₂ : topCollarDualSeventhMass M N u₂ ≤ ε / 16 := by
    let E : ℕ → ℝ := fun n => leftProfileCutoff a (Real.log ((n : ℝ) / N)) *
      polarLogSampleProfile (I₁ / I₂) (Real.log ((n : ℝ) / N)) - f (Real.log ((n : ℝ) / N))
    have he : u₂ = horizonProfileVector (fun n => I₁ / Real.sqrt N * E n) N := by
      dsimp only [u₂, α, p]
      rw [normalized_polarSample_eq_logSample hc0 hN]
      ext i
      simp only [PiLp.sub_apply, horizonLogCutoff_apply]
      change _ * (I₁ / Real.sqrt N * _) - I₁ / Real.sqrt N * _ = I₁ / Real.sqrt N * E i.1
      dsimp only [E]
      ring
    have hnorm : ‖u₂‖ ^ 2 = I₁ ^ 2 * ((∑ n ∈ Icc 1 N, E n ^ 2) / N) := by
      rw [he, horizonProfileVector_norm_sq]
      calc
        _ = ∑ n ∈ Icc 1 N, I₁ ^ 2 * (E n ^ 2 / N) := by
          refine sum_congr rfl fun n _ => ?_
          rw [mul_pow, div_pow, Real.sq_sqrt hN0.le]
          ring
        _ = _ := by rw [← mul_sum, ← sum_div]
    have hh := mul_le_mul_of_nonneg_left hfN (sq_nonneg I₁)
    have hb : ‖u₂‖ ^ 2 ≤ ε / 16 := by
      rw [hnorm]
      exact hh.trans_eq (by field_simp [hI₁])
    exact (topCollarDualSeventhMass_le_norm_sq M N u₂).trans hb
  have hsplit : α • r - v = (u₀ + u₁) + u₂ := by
    dsimp only [u₀, u₁, u₂]
    rw [smul_sub, horizonLogCutoff_sub]
    abel
  change topCollarDualSeventhMass M N (α • r - v) ≤ ε
  rw [hsplit]
  have houter := topCollarDualSeventhMass_add_le M N (u₀ + u₁) u₂
  have hinner := topCollarDualSeventhMass_add_le M N u₀ u₁
  linarith only [houter, hinner, h₀, h₁, h₂, hε]

#print axioms normalized_polarSample_eq_logSample
#print axioms exists_polar_residual_weighted_lipschitz_approximation

/-- The normalized polar functional is uniformly approximated by one compact Lipschitz pairing
on every bounded seventh-mass collar ball. -/
theorem exists_uniform_polar_functional_lipschitz_approximation
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      ∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) →
      topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ M →
      |Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
        ∫ u, normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N u * f u| ≤ ε := by
  let η := ε ^ 2 / (8 * M)
  have hη : 0 < η := by dsimp only [η]; positivity
  obtain ⟨f, K, hfc, hLip, hrow⟩ := exists_polar_residual_weighted_lipschitz_approximation hc hR hcrit hη
  refine ⟨f, K, hfc, hLip, ?_⟩
  let Iabs := ∫ u, |tiltedUnitSpline u|
  have hIabs : 0 ≤ Iabs := integral_nonneg fun _ => abs_nonneg _
  have hw : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
    simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
  have herr : Tendsto (fun N : ℕ => c N / N * (K : ℝ) * Iabs * Real.sqrt M) atTop (𝓝 0) := by
    simpa only [zero_mul] using ((hw.mul_const (K : ℝ)).mul_const Iabs).mul_const (Real.sqrt M)
  filter_upwards [eventually_ge_atTop 1, hrow, herr.eventually (gt_mem_nhds (half_pos hε))]
    with N hN hrowN herrN z hz0 hzM
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  let m := N / linearDefectCutoff (c N)
  let v := horizonProfileVector (fun n => (∫ u, tiltedUnitSpline u) / Real.sqrt N *
    f (Real.log ((n : ℝ) / N))) N
  let e := (Real.sqrt (Real.log N) / c N) • conductorResidualVector (c N) 1 N - v
  have hprefix : (∑ n ∈ Icc 1 m, primeHorizonExtension z n ^ 2) = 0 := by
    apply sum_eq_zero
    intro n hn
    rw [hz0 n (mem_Icc.mp hn).2, zero_pow (by decide : 2 ≠ 0)]
  have hinnerSq := inner_sq_le_prefix_add_topCollarSeventh (M := m)
    (Nat.div_le_self N (linearDefectCutoff (c N))) e z
  rw [hprefix, mul_zero, zero_add] at hinnerSq
  have hmul := mul_le_mul hrowN hzM (topCollarSeventhMass_nonneg m N _) hη.le
  have hsmall : 2 * η * M = (ε / 2) ^ 2 := by dsimp only [η]; field_simp [hM.ne']; ring
  have hsq : ⟪e, z⟫ ^ 2 ≤ (ε / 2) ^ 2 := by
    calc
      _ ≤ 2 * topCollarDualSeventhMass m N e * topCollarSeventhMass m N (primeHorizonExtension z) := hinnerSq
      _ ≤ 2 * η * M := by nlinarith only [hmul]
      _ = _ := hsmall
  have hinner : |⟪e, z⟫| ≤ ε / 2 :=
    (sq_le_sq₀ (abs_nonneg _) (half_pos hε).le).mp (by simpa only [sq_abs] using hsq)
  have hcoef : (∑ n ∈ Icc 1 N, primeHorizonExtension z n ^ 2) ≤ M := by
    have hsub : Ioc m N ⊆ Icc 1 N := fun n hn =>
      mem_Icc.mpr ⟨Nat.succ_le_of_lt ((Nat.zero_le m).trans_lt (mem_Ioc.mp hn).1),
        (mem_Ioc.mp hn).2⟩
    have heq : (∑ n ∈ Ioc m N, primeHorizonExtension z n ^ 2) =
        ∑ n ∈ Icc 1 N, primeHorizonExtension z n ^ 2 := by
      apply sum_subset hsub
      intro n hn hnC
      have hnm : n ≤ m := by
        by_contra hlt
        exact hnC (mem_Ioc.mpr ⟨by omega, (mem_Icc.mp hn).2⟩)
      rw [hz0 n hnm, zero_pow (by decide : 2 ≠ 0)]
    rw [← heq]
    exact (sum_sq_Ioc_le_topCollarSeventhMass m N _).trans hzM
  have hAdj := abs_integral_normalizedCentredAtomicTest_mul_sub_le
    contDiff_tiltedUnitSpline.continuous tiltedUnitSpline_eq_zero hLip hc0 hN (primeHorizonExtension z)
  have hAdjSmall : |(∫ u, normalizedCentredAtomicTest tiltedUnitSpline
        (primeHorizonExtension z) (c N) N u * f u) -
      (∫ u, tiltedUnitSpline u) / Real.sqrt N *
        ∑ n ∈ Icc 1 N, primeHorizonExtension z n * f (Real.log n - Real.log N)| ≤ ε / 2 := by
    have hsqrt := Real.sqrt_le_sqrt hcoef
    exact (hAdj.trans (mul_le_mul_of_nonneg_left hsqrt (by positivity))).trans herrN.le
  have hvinner : ⟪v, z⟫ = (∫ u, tiltedUnitSpline u) / Real.sqrt N *
      ∑ n ∈ Icc 1 N, primeHorizonExtension z n * f (Real.log n - Real.log N) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    change (∑ i : PrimeHorizonIndex N, z i * ((∫ u, tiltedUnitSpline u) / Real.sqrt N *
      f (Real.log ((i.1 : ℝ) / N)))) = _
    rw [mul_sum, ← sum_coe_sort (Icc 1 N)]
    refine sum_congr rfl fun i _ => ?_
    have hi0 : (0 : ℝ) < i.1 := by exact_mod_cast (mem_Icc.mp i.2).1
    rw [primeHorizonExtension_coe, Real.log_div hi0.ne' hN0.ne']
    ring
  have heinner : ⟪e, z⟫ = Real.sqrt (Real.log N) / c N *
      ⟪conductorResidualVector (c N) 1 N, z⟫ - ⟪v, z⟫ := by
    dsimp only [e]
    rw [inner_sub_left, real_inner_smul_left]
  rw [← hvinner] at hAdjSmall
  have heq : Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
      (∫ u, normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N u * f u) =
      ⟪e, z⟫ - ((∫ u, normalizedCentredAtomicTest tiltedUnitSpline
        (primeHorizonExtension z) (c N) N u * f u) - ⟪v, z⟫) := by rw [heinner]; ring
  rw [heq]
  exact ((abs_sub _ _).trans (add_le_add hinner hAdjSmall)).trans_eq (add_halves ε)

#print axioms exists_uniform_polar_functional_lipschitz_approximation

/-- One compact Lipschitz test simultaneously approximates the polar functional on a collar
ball and the signed source of every window with bounded seventh weighted coefficient mass. -/
theorem exists_uniform_polar_test_and_window_identification
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {M W ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      (∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) →
        topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ M →
        |Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
          ∫ u, normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N u * f u| ≤ ε) ∧
      ∀ {h : ℝ → ℝ} {A : ℝ}, ContDiff ℝ 2 h → 0 ≤ A →
        (∀ u, u ∉ Set.Icc (-A) 0 → h u = 0) →
        (∫ u, Real.exp (-(7 * u)) * h u ^ 2) ≤ W →
        |generalTerminalPolarSource A h -
          ∫ u, ((∫ v, tiltedUnitSpline v) * halfWeight h u) * f u| ≤ ε := by
  let B := max M (W + 1)
  have hB : 0 < B := hM.trans_le (le_max_left _ _)
  obtain ⟨f, K, hfc, hLip, hf⟩ :=
    exists_uniform_polar_functional_lipschitz_approximation hc hR hcrit hB hε
  refine ⟨f, K, hfc, hLip, ?_, ?_⟩
  · exact hf.mono fun N hN z hz0 hzM => hN z hz0 (hzM.trans (le_max_left _ _))
  · intro h A hh hA hsupp hW
    have hcinf := (criticalCurve_facts hc hR hcrit).1
    have hwidth : Tendsto (fun N : ℕ => c N / N) atTop (𝓝 0) := by
      simpa only [pow_one, pow_zero, mul_one] using criticalCurve_pow_log_div_natCast hc hR hcrit 1 0
    have hweak := tendsto_polar_residual_window_pairing hh hA hsupp hc hR hcrit
    have hp := tendsto_horizonWindow_atomic_pairing hh.continuous hA hsupp hLip
      (fun N => zero_lt_one.trans_le (hc N)) hwidth
    have hlim := (hweak.sub hp).abs
    apply le_of_tendsto hlim
    have hwlim := tendsto_weighted_sum_horizonWeights_sq hh.continuous hsupp hA 7
    have hWlt : (∫ u, Real.exp (-(7 * u)) * h u ^ 2) < B :=
      (lt_of_le_of_lt hW (lt_add_one W)).trans_le (le_max_right _ _)
    filter_upwards [hf, eventually_horizonWindow_prefix_zero hsupp hc hcinf,
      hwlim.eventually (gt_mem_nhds hWlt)] with N hfN hz0 hmass
    exact hfN _ hz0 ((topCollarSeventhMass_horizonWindow_le h _ N).trans hmass.le)

#print axioms exists_uniform_polar_test_and_window_identification

/-- On bounded collar balls, the polar functional is uniformly continuous in physical `L²`
when compared with a smooth window of bounded seventh weighted coefficient mass. -/
theorem exists_uniform_polar_window_L2_transfer
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {M W ε : ℝ} (hM : 0 < M) (hε : 0 < ε) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {h : ℝ → ℝ} {A : ℝ}, ContDiff ℝ 2 h → 0 ≤ A →
      (∀ u, u ∉ Set.Icc (-A) 0 → h u = 0) →
      (∫ u, Real.exp (-(7 * u)) * h u ^ 2) ≤ W →
      ∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
      (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) →
      topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ M →
      |Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
        generalTerminalPolarSource A h| ≤ B * Real.sqrt (∫ u,
          (normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N u -
            (∫ v, tiltedUnitSpline v) * halfWeight h u) ^ 2) + ε := by
  obtain ⟨f, K, hfc, hLip, hf, hwin⟩ :=
    exists_uniform_polar_test_and_window_identification (W := W) hc hR hcrit hM (half_pos hε)
  let B := Real.sqrt (∫ u, f u ^ 2)
  refine ⟨B, Real.sqrt_nonneg _, ?_⟩
  intro h A hh hA hsupp hW
  have hsource := hwin hh hA hsupp hW
  let H := fun u => (∫ v, tiltedUnitSpline v) * halfWeight h u
  have hHcont : Continuous H :=
    continuous_const.mul ((Real.continuous_exp.comp (continuous_id.div_const 2)).mul hh.continuous)
  have hHc : HasCompactSupport H := (hasCompactSupport_of_window hsupp).mul_left.mul_left
  have hf2 : Integrable (fun u => f u ^ 2) :=
    (hLip.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).integrable_sq
  filter_upwards [eventually_ge_atTop 1, hf] with N hN hfN z hz0 hzM
  let U := normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N
  have hc0 : 0 < c N := zero_lt_one.trans_le (hc N)
  have hUc : HasCompactSupport U :=
    hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero hc0 hN _
  have hUcont : Continuous U :=
    (contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline hc0 hN _).continuous
  have hdcont : Continuous (fun u => U u - H u) := hUcont.sub hHcont
  have hd2 : Integrable (fun u => (U u - H u) ^ 2) :=
    (hdcont.memLp_of_hasCompactSupport (hUc.sub hHc) :
      MemLp (fun u => U u - H u) 2 volume).integrable_sq
  have hcs := HTGeometry.sq_integral_mul_le hdcont.aestronglyMeasurable
    hLip.continuous.aestronglyMeasurable hd2 hf2
  have hbound : |∫ u, (U u - H u) * f u| ≤ B * Real.sqrt (∫ u, (U u - H u) ^ 2) := by
    apply (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))).mp
    rw [sq_abs, mul_pow, Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    dsimp only [B]
    rw [Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)]
    exact hcs.trans_eq (mul_comm _ _)
  have hsplit : (∫ u, U u * f u) - (∫ u, H u * f u) = ∫ u, (U u - H u) * f u := by
    simp only [sub_mul]
    exact (integral_sub
      ((hUcont.mul hLip.continuous).integrable_of_hasCompactSupport hfc.mul_left)
      ((hHcont.mul hLip.continuous).integrable_of_hasCompactSupport hfc.mul_left)).symm
  have hpolar := hfN z hz0 hzM
  have he : Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
      generalTerminalPolarSource A h =
      (Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ - ∫ u, U u * f u) +
      ((∫ u, U u * f u) - ∫ u, H u * f u) -
      (generalTerminalPolarSource A h - ∫ u, H u * f u) := by ring
  rw [he]
  apply ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans
  rw [hsplit]
  exact (add_le_add (add_le_add hpolar hbound) hsource).trans_eq (by ring)

#print axioms exists_uniform_polar_window_L2_transfer

/-- Bounded Gamma profiles inherit the same compact-test identification as their smooth windows. -/
theorem exists_uniform_polar_test_and_limit_identification
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {M ε : ℝ} (hM : 0 < M) (hε : 0 < ε)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hF2 : Integrable (fun u => F u ^ 2))
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))))
    (hFzero : ∀ u, 0 ≤ u → F u = 0) {B : ℝ}
    (hGamma : ∀ T : ℝ, Real.exp ArithmeticPositivityTheory.factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ B) :
    ∃ f : ℝ → ℝ, ∃ K : NNReal, HasCompactSupport f ∧ LipschitzWith K f ∧
      (∀ᶠ N : ℕ in atTop, ∀ z : EuclideanSpace ℝ (PrimeHorizonIndex N),
        (∀ n, n ≤ N / linearDefectCutoff (c N) → primeHorizonExtension z n = 0) →
        topCollarSeventhMass (N / linearDefectCutoff (c N)) N (primeHorizonExtension z) ≤ M →
        |Real.sqrt (Real.log N) / c N * ⟪conductorResidualVector (c N) 1 N, z⟫ -
          ∫ u, normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension z) (c N) N u * f u| ≤ ε) ∧
      |((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2)) *
        (∫ u, F u * polarSourceProfile u) - ∫ u, F u * f u| ≤ ε := by
  let I₁ := ∫ u, tiltedUnitSpline u
  let I₂ := ∫ u, tiltedUnitSpline u ^ 2
  let I₈ := ∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u))
  have hI₈ : 0 ≤ I₈ := setIntegral_nonneg measurableSet_Iio (fun _ _ => by positivity)
  obtain ⟨C, A, H, _, hwin, _, hweighted, hL2, hweightedLim, _⟩ :=
    exists_window_sequence_of_gammaLiminf_bound (Rstar := R) (B := B)
      hFm hFi hF2 hF8 le_rfl hFzero hGamma
  let W := Real.exp 8 * I₈ / I₁ ^ 2
  obtain ⟨f, K, hfc, hLip, hf, hwindow⟩ :=
    exists_uniform_polar_test_and_window_identification (W := W) hc hR hcrit hM hε
  refine ⟨f, K, hfc, hLip, hf, ?_⟩
  have hHd : ∀ k, ContDiff ℝ 2 (H k) := fun k => (hwin k).2.contDiff
  have hHc : ∀ k, HasCompactSupport (H k) := fun k => (hwin k).2.hasCompactSupport
  have hHs : ∀ k u, 1 < u → H k u = 0 := fun k u hu =>
    (hwin k).2.vanish u (fun hm => by linarith only [hu, hm.2])
  have hHW : ∀ k, WeightedTwo (H k) := fun k =>
    (weightedTwo_of_support (hHd k).continuous (hHc k) (hHs k)).1
  have hFW : WeightedTwo F :=
    (exponentialSourceMass_le_of_support zero_le_one hFm.aestronglyMeasurable hF2 hF8
      (Eventually.of_forall fun u hu => hFzero u (zero_lt_one.trans hu).le)).1
  have hsource := (tendsto_integral_mul_polarSourceProfile hHW hFW hweightedLim).const_mul (I₁ / I₂)
  have htest := tendsto_integral_mul_of_square_mean
    (fun k => (hHd k).continuous.aestronglyMeasurable) hFm.aestronglyMeasurable
    hLip.continuous.aestronglyMeasurable
    (fun k => ((hHd k).continuous.memLp_of_hasCompactSupport (hHc k) : MemLp (H k) 2 volume).integrable_sq)
    hF2 (hLip.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).integrable_sq hL2
  apply le_of_tendsto (hsource.sub htest).abs
  exact Eventually.of_forall fun k => by
    have hexp : Real.exp (8 / ((k : ℝ) + 1)) ≤ Real.exp 8 := by
      apply Real.exp_le_exp.mpr
      have hd : 1 / ((k : ℝ) + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith only [Nat.cast_nonneg (α := ℝ) k]) (by positivity)
      simpa only [mul_one_div, mul_one] using
        mul_le_mul_of_nonneg_left hd (by norm_num : (0 : ℝ) ≤ 8)
    have hWk : (∫ u, Real.exp (-(7 * u)) * physicalWindowWeights (H k) u ^ 2) ≤ W := by
      rw [integral_weighted_physicalWindowWeights_sq]
      exact div_le_div_of_nonneg_right
        ((hweighted k).trans (mul_le_mul_of_nonneg_right hexp hI₈)) (sq_nonneg I₁)
    have hh := hwindow (contDiff_physicalWindowWeights (hHd k)) (hwin k).1
      (physicalWindowWeights_vanish (hwin k).2.vanish) hWk
    rw [generalTerminalPolarSource_physicalWindowWeights (hHd k) (hwin k).1 (hwin k).2.vanish] at hh
    simpa only [physicalWindowWeights_halfWeight] using hh

#print axioms exists_uniform_polar_test_and_limit_identification

/-- Along a critical sequence, bounded collar mass and strong physical convergence determine
its signed polar pairing, provided the limit has a finite Gamma upper bound. -/
theorem tendsto_polar_residual_pairing_of_strong_limit
    {c : ℕ → ℝ} (hc : ∀ N, 1 ≤ c N) {R : ℝ} (hR : 0 < R)
    (hcrit : Tendsto (fun N : ℕ => c N ^ 8 / Real.log N) atTop (𝓝 R))
    {N_seq : ℕ → ℕ} (hstrict : StrictMono N_seq) (hN : ∀ k, 1 ≤ N_seq k)
    (z : (k : ℕ) → EuclideanSpace ℝ (PrimeHorizonIndex (N_seq k)))
    (hz0 : ∀ k n, n ≤ N_seq k / linearDefectCutoff (c (N_seq k)) → primeHorizonExtension (z k) n = 0)
    {M : ℝ} (hM : 0 < M)
    (hzM : ∀ k, topCollarSeventhMass (N_seq k / linearDefectCutoff (c (N_seq k)))
      (N_seq k) (primeHorizonExtension (z k)) ≤ M)
    {F : ℝ → ℝ} (hFm : Measurable F) (hFi : Integrable F)
    (hF2 : Integrable (fun u => F u ^ 2))
    (hF8 : Integrable (fun u => F u ^ 2 * Real.exp (-(8 * u))))
    (hFzero : ∀ u, 0 ≤ u → F u = 0) {B : ℝ}
    (hGamma : ∀ T : ℝ, Real.exp ArithmeticPositivityTheory.factorialSpanGammaOffset ≤ T →
      truncatedWeilForm F T + criticalAliasCoefficient R *
        (∫ u in Set.Iio 0, F u ^ 2 * Real.exp (-(8 * u))) ≤ B)
    (hL2 : Tendsto (fun k => ∫ u,
      (normalizedCentredAtomicTest tiltedUnitSpline (primeHorizonExtension (z k))
        (c (N_seq k)) (N_seq k) u - F u) ^ 2) atTop (𝓝 0)) :
    Tendsto (fun k => Real.sqrt (Real.log (N_seq k)) / c (N_seq k) *
      ⟪conductorResidualVector (c (N_seq k)) 1 (N_seq k), z k⟫) atTop
      (𝓝 (((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2)) *
        ∫ u, F u * polarSourceProfile u)) := by
  let U := fun k => normalizedCentredAtomicTest tiltedUnitSpline
    (primeHorizonExtension (z k)) (c (N_seq k)) (N_seq k)
  have hUc : ∀ k, HasCompactSupport (U k) := fun k =>
    hasCompactSupport_normalizedCentredAtomicTest tiltedUnitSpline_eq_zero
      (zero_lt_one.trans_le (hc (N_seq k))) (hN k) _
  have hUcont : ∀ k, Continuous (U k) := fun k =>
    (contDiff_normalizedCentredAtomicTest contDiff_tiltedUnitSpline
      (zero_lt_one.trans_le (hc (N_seq k))) (hN k) _).continuous
  rw [Metric.tendsto_nhds]
  intro ε hε
  have he : 0 < ε / 3 := by positivity
  obtain ⟨f, K, hfc, hLip, hf, hsource⟩ :=
    exists_uniform_polar_test_and_limit_identification hc hR hcrit hM he hFm hFi hF2 hF8 hFzero hGamma
  have htest := tendsto_integral_mul_of_square_mean
    (fun k => (hUcont k).aestronglyMeasurable) hFm.aestronglyMeasurable
    hLip.continuous.aestronglyMeasurable
    (fun k => ((hUcont k).memLp_of_hasCompactSupport (hUc k) : MemLp (U k) 2 volume).integrable_sq)
    hF2 (hLip.continuous.memLp_of_hasCompactSupport hfc : MemLp f 2 volume).integrable_sq hL2
  have hnorm := tendsto_iff_norm_sub_tendsto_zero.mp htest
  filter_upwards [hstrict.tendsto_atTop.eventually hf, hnorm.eventually (gt_mem_nhds he)]
    with k hfN hsmall
  have hp := hfN (z k) (hz0 k) (hzM k)
  rw [Real.dist_eq]
  rw [Real.norm_eq_abs] at hsmall
  have heq : Real.sqrt (Real.log (N_seq k)) / c (N_seq k) *
      ⟪conductorResidualVector (c (N_seq k)) 1 (N_seq k), z k⟫ -
      ((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2)) *
        (∫ u, F u * polarSourceProfile u) =
      (Real.sqrt (Real.log (N_seq k)) / c (N_seq k) *
        ⟪conductorResidualVector (c (N_seq k)) 1 (N_seq k), z k⟫ - ∫ u, U k u * f u) +
      ((∫ u, U k u * f u) - ∫ u, F u * f u) -
      (((∫ u, tiltedUnitSpline u) / (∫ u, tiltedUnitSpline u ^ 2)) *
        (∫ u, F u * polarSourceProfile u) - ∫ u, F u * f u) := by ring
  rw [heq]
  apply lt_of_le_of_lt ((abs_sub _ _).trans (add_le_add (abs_add_le _ _) le_rfl))
  linarith only [hp, hsmall, hsource]

#print axioms tendsto_polar_residual_pairing_of_strong_limit

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
