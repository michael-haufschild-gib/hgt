import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.TripleBoxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Sampling.Summability
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.RepeatedGates.PhysicalBlocks.CollectiveSignals.Calibration.SmallAngles

/-! # A growing number of calibrated triples at reciprocal physical dates -/

open MeasureTheory Filter Finset Real Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
open RepeatedGates.PhysicalBlocks
open RepeatedGates.PhysicalBlocks.CollectiveSignals
noncomputable section

/-- At date 1/j the smallest tested prefix already contains order j²⁰⁸
calibrated boxes. Extending the same draw preserves all these boxes. -/
theorem gaussian_moving_triples :
    ∃ c>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop,
      ∀ m : ℕ, j^256 ≤ m → c*(j:ℝ)^208≤((goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω m).card:ℝ) := by
  classical
  obtain ⟨c,hc,hp⟩ := calibrated_small_time_mass
  let p (j : ℕ) := boxProbability (1/sqrt 2) ((1/(j:ℝ))/10000)
  let E (j : ℕ) := {ω | ((goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω (j^256)).card:ℝ)≤p j*(j:ℝ)^256/4}
  have hmean (j : ℕ) (hj : 0<j) : c*(j:ℝ)^208≤p j*(j:ℝ)^256 := by
    have hJ : (0:ℝ)<j := Nat.cast_pos.mpr hj
    have ht : 1/(j:ℝ)∈Ioc (0:ℝ) 1 := ⟨one_div_pos.mpr hJ,(div_le_one hJ).mpr (by exact_mod_cast hj)⟩
    have he := mul_le_mul_of_nonneg_right (hp _ ht) (pow_nonneg hJ.le 256)
    exact (show c*(j:ℝ)^208=c*(1/(j:ℝ))^48*(j:ℝ)^256 by
      field_simp [hJ.ne']).le.trans he
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  have hrare : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ j : ℕ in atTop, ω∉E j := by
    apply avoid_exponential_windows pathPauliDisorderLaw E 0 2 (c:=c/4) (by positivity)
    filter_upwards [eventually_gt_atTop (0:ℕ)] with j hj
    have h := few_triple_boxes (1/sqrt 2) ((1/(j:ℝ))/10000) (j^256)
    rw [Nat.cast_pow] at h
    apply h.trans
    rw [pow_zero,one_mul]
    apply mul_le_mul_of_nonneg_left (exp_le_exp.mpr _) zero_le_two
    have hJ : 1≤(j:ℝ) := by exact_mod_cast hj
    have hpoly : (j:ℝ)≤(j:ℝ)^208 := by simpa only [pow_one] using pow_le_pow_right₀ hJ (by decide : 1≤208)
    change -(p j*(j:ℝ)^256)/4≤ -(c/4)*(j:ℝ)
    linarith only [hmean j hj,mul_le_mul_of_nonneg_left hpoly hc.le]
  refine ⟨c/4,by positivity,?_⟩
  filter_upwards [hrare] with ω hw
  filter_upwards [hw,eventually_gt_atTop (0:ℕ)] with j hgood hj
  intro m hm
  have hg : p j*(j:ℝ)^256/4<((goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω (j^256)).card:ℝ) :=
    lt_of_not_ge hgood
  have hsub : goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω (j^256)⊆
      goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω m := filter_subset_filter _ (range_mono hm)
  calc
    _ ≤ ((goodBoxes (1/sqrt 2) ((1/(j:ℝ))/10000) ω (j^256)).card:ℝ) := by
      linarith only [hmean j hj,hg]
    _ ≤ _ := Nat.cast_le.mpr (Finset.card_le_card hsub)

#print axioms gaussian_moving_triples
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
