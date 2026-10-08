import GaloisForLFunctions.RHTower.WeilWorkQuantizationAnnulusLog

/-!
# The arithmetic half of periodic phase winding rigidity

The actual represented phase supplies its analytic nonzero symbol and an
annular logarithm after removing an integer monomial. Positive winding would
produce the strictly positive factorization already excluded by its q-chain.
Thus its winding is nonpositive, with all analytic factors constructed here.
-/

open Complex Set Filter MeasureTheory Metric
open scoped Topology ENNReal
noncomputable section
namespace RHTower.WeilSpectral
open Bottcher GaloisForLFunctions.HTGeometry

/-- The outer Laurent factor is analytic on its full disc of definition. -/
theorem analyticOnNhd_quantization_laurentOuter {f : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hf : ContinuousOn f (sphere 0 R)) :
    AnalyticOnNhd ℂ (laurentOuter f 0 R) (ball 0 R) := by
  have hs := laurentOuter_hasFPowerSeriesOnBall
    (R := (⟨R, hR.le⟩ : NNReal)) (by exact_mod_cast hR) (hf.circleIntegrable hR.le)
  intro z hz
  apply hs.analyticOnNhd z
  rw [mem_eball_zero_iff]
  have hn : ‖z‖ < R := by simpa only [mem_ball, dist_zero_right] using hz
  exact_mod_cast hn

/-- The actual arithmetic source excludes positive winding of its represented symbol. -/
theorem quantization_phase_winding_nonpos
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I))
    {a b : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hb : 1 < b) {N : ℤ} {L : ℂ → ℂ}
    (hL : AnalyticOnNhd ℂ L (annulusSet a b))
    (he : ∀ z ∈ annulusSet a b, quantizationPeriodicSymbol p z = z ^ N * cexp (L z)) : N ≤ 0 := by
  by_contra! hN
  obtain ⟨r, har, hr1⟩ := exists_between ha1
  obtain ⟨R, h1R, hRb⟩ := exists_between hb
  have hr0 : 0 < r := ha0.trans har
  have hR0 : 0 < R := zero_lt_one.trans h1R
  have hrR : r < R := hr1.trans h1R
  have hdiff : DifferentiableOn ℂ L (annulusAt 0 a b) := by
    simpa only [annulusAt, annulusSet, sub_zero] using hL.differentiableOn
  have hcr : ContinuousOn L (sphere 0 r) :=
    hdiff.continuousOn.mono (sphere_subset_annulusAt har (hrR.trans hRb))
  have hcR : ContinuousOn L (sphere 0 R) :=
    hdiff.continuousOn.mono (sphere_subset_annulusAt (ha1.trans h1R) hRb)
  obtain ⟨M, hM, hbound⟩ := exists_bound_on_sphere hr0.le hcr
  have hri : 1 < r⁻¹ := (one_lt_inv₀ hr0).mpr hr1
  obtain ⟨S, hS1, hS⟩ := exists_between hri
  have hout := analyticOnNhd_quantization_laurentOuter hR0 hcR
  let n : ℕ := (N - 1).toNat
  have hn : (n : ℤ) + 1 = N := by dsimp [n]; omega
  let H : ℂ → ℂ := fun z => z ^ n * cexp (laurentOuter L 0 R z)
  have hH : DiffContOnCl ℂ H (ball 0 1) := by
    have hd : DifferentiableOn ℂ H (closedBall 0 1) := by
      intro z hz
      have hzR : z ∈ ball (0 : ℂ) R := by
        have hz1 : ‖z‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz
        simpa only [mem_ball, dist_zero_right] using hz1.trans_lt h1R
      exact ((analyticAt_id.pow n).mul (hout z hzR).cexp).differentiableAt.differentiableWithinAt
    exact (hd.mono closure_ball_subset_closedBall).diffContOnCl
  have hfactor (z : ℂ) (hz : z ∈ sphere (0 : ℂ) 1) :
      quantizationExteriorInverse L r z⁻¹ * (∑' k : ℤ, p k * z ^ k) = z * H z := by
    have hnorm : ‖z‖ = 1 := by simpa only [mem_sphere_iff_norm, sub_zero] using hz
    have hza : z ∈ annulusSet a b := by
      change a < ‖z‖ ∧ ‖z‖ < b
      simpa only [hnorm] using And.intro ha1 hb
    have hz0 : z ≠ 0 := norm_pos_iff.mp (by rw [hnorm]; norm_num)
    change quantizationExteriorInverse L r z⁻¹ * quantizationPeriodicSymbol p z = z * H z
    rw [he z hza]
    calc
      _ = z ^ N * (quantizationExteriorInverse L r z⁻¹ * cexp (L z)) := by ring
      _ = z ^ N * cexp (laurentOuter L 0 R z) := by
        rw [quantization_laurent_factorization ha0 har hrR hRb hdiff
          (by simpa only [hnorm] using hr1) (by simpa only [hnorm] using h1R)]
      _ = z * H z := by
        have hpow : z ^ N = z * z ^ n := by
          rw [← hn, zpow_add₀ hz0, zpow_natCast, zpow_one, mul_comm]
        rw [hpow]
        dsimp [H]
        ring
  exact quantization_phase_no_positive_exterior_factor hW hq hp hphase hr0 hM hbound
    hS1 hS ⟨H, hH, hfactor⟩

/-- The actual phase supplies a logarithm whose winding is nonpositive. -/
theorem quantization_phase_exists_nonpos_winding_log
    {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {q : ℕ} (hq : 2 ≤ q) {p : ℤ → ℂ}
    (hp : Summable fun k => ‖p k‖ * (q : ℝ) ^ k.natAbs)
    (hphase : ∀ x : ℝ, 0 < x →
      cexp (((2 * Real.pi * quantizationResidualCumulative hW x : ℝ) : ℂ) * I) =
        ∑' k : ℤ, p k * cexp (((2 * (k : ℝ) * Real.log q * x : ℝ) : ℂ) * I)) :
    ∃ (a b : ℝ) (N : ℤ) (L : ℂ → ℂ), 0 < a ∧ a < 1 ∧ 1 < b ∧ N ≤ 0 ∧
      AnalyticOnNhd ℂ L (annulusSet a b) ∧
      ∀ z ∈ annulusSet a b, quantizationPeriodicSymbol p z = z ^ N * cexp (L z) := by
  obtain ⟨a, b, ha0, ha1, hb, hP, hne⟩ :=
    exists_nonzero_annulus_quantizationPeriodicSymbol hW hq hp hphase
  have hPa : AnalyticOnNhd ℂ (quantizationPeriodicSymbol p) (annulusSet a b) := by
    simpa only [annulusAt, annulusSet, sub_zero] using hP
  have hnea : ∀ z ∈ annulusSet a b, quantizationPeriodicSymbol p z ≠ 0 := by
    simpa only [annulusAt, annulusSet, sub_zero] using hne
  obtain ⟨N, L, hL, he⟩ := quantization_exists_annulus_log ha0 ha1 hb hPa hnea
  exact ⟨a, b, N, L, ha0, ha1, hb,
    quantization_phase_winding_nonpos hW hq hp hphase ha0 ha1 hb hL he, hL, he⟩

end RHTower.WeilSpectral
