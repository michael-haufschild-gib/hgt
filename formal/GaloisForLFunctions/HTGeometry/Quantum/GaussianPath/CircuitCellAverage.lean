import GaloisForLFunctions.HTGeometry.Quantum.FirstCircuitSaturationBoundary
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Circuit certificates from symmetric time averages

The phase-saturated circuit distance is Lipschitz in Hamiltonian time. Integrating
that bound over a cell gives a smaller error at the midpoint and a uniform margin
which certifies affordability or exclusion throughout the cell.
-/

open Set MeasureTheory
open scoped Interval Matrix.Norms.L2Operator

namespace GaloisForLFunctions.HTGeometry

noncomputable section

private abbrev Reg (n : ℕ) := Matrix (Fin n → Bool) (Fin n → Bool) ℂ
private abbrev CellRadius := Set.Ioi (0 : ℝ)

/-- Distance to the entire budget-allowed circuit set changes at most as fast as
the operator evolution. -/
theorem orbitCircuitDistance_lipschitz {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ) :
    LipschitzWith ⟨‖(H : Reg n)‖, norm_nonneg _⟩ (orbitCircuitDistance H P) := by
  apply LipschitzWith.of_dist_le_mul
  intro u v
  let U := unitaryEvolution (H : Reg n)
  calc
    _ ≤ dist (U u) (U v) := by
      change dist (Metric.infDist (U u) (phaseCircuitMatrixImageAtMost n P))
        (Metric.infDist (U v) (phaseCircuitMatrixImageAtMost n P)) ≤ dist (U u) (U v)
      simpa only [NNReal.coe_one, one_mul] using
        (Metric.lipschitz_infDist_pt (phaseCircuitMatrixImageAtMost n P)).dist_le_mul (U u) (U v)
    _ ≤ _ := by
      rw [dist_eq_norm, Real.dist_eq]
      exact norm_unitaryEvolution_time_sub_le H.2 u v

/-- Average distance to the physical circuit family over a symmetric time cell. -/
def orbitCircuitCellMean {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) : ℝ :=
  (∫ u in x - (h : ℝ)..x + (h : ℝ), orbitCircuitDistance H P u) / (2 * (h : ℝ))

private theorem integral_abs_distance {a b t : ℝ} (ht : t ∈ Icc a b) :
    (∫ u in a..b, |u - t|) = ((t - a) ^ 2 + (b - t) ^ 2) / 2 := by
  have hc : Continuous (fun u : ℝ => |u - t|) := (continuous_id.sub continuous_const).abs
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable a t) (hc.intervalIntegrable t b)]
  have hl : (∫ u in a..t, |u - t|) = ∫ u in a..t, t - u := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.1] at hu
    rw [abs_of_nonpos (sub_nonpos.mpr hu.2), neg_sub]
  have hr : (∫ u in t..b, |u - t|) = ∫ u in t..b, u - t := by
    refine intervalIntegral.integral_congr fun u hu => ?_
    rw [uIcc_of_le ht.2] at hu
    rw [abs_of_nonneg (sub_nonneg.mpr hu.1)]
  have hid : Continuous (fun u : ℝ => u) := continuous_id
  have hconst : Continuous (fun _ : ℝ => t) := continuous_const
  rw [hl, hr,
    intervalIntegral.integral_sub (hconst.intervalIntegrable a t) (hid.intervalIntegrable a t),
    intervalIntegral.integral_sub (hid.intervalIntegrable t b) (hconst.intervalIntegrable t b)]
  simp only [integral_id, intervalIntegral.integral_const, smul_eq_mul]
  ring

/-- The pointwise sampling margin is the mean time distance to the sample. -/
theorem orbitCircuitCellMean_error {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    |orbitCircuitCellMean H P x h - orbitCircuitDistance H P t| ≤
      ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + ((t : ℝ) - x) ^ 2) / (2 * (h : ℝ)) := by
  let f := orbitCircuitDistance H P
  let a := x - (h : ℝ)
  let b := x + (h : ℝ)
  have hf := orbitCircuitDistance_lipschitz H P
  have hf' : Continuous f := hf.continuous
  have hpos : 0 < (h : ℝ) := h.2
  have hab : a ≤ b := t.2.1.trans t.2.2
  have hd : 0 < 2 * (h : ℝ) := by positivity
  have heq : orbitCircuitCellMean H P x h - f t =
      (∫ u in a..b, f u - f t) / (2 * (h : ℝ)) := by
    rw [orbitCircuitCellMean, intervalIntegral.integral_sub (hf'.intervalIntegrable a b)
      (continuous_const.intervalIntegrable a b), intervalIntegral.integral_const, smul_eq_mul]
    simp only [a, b]
    field_simp [hd.ne', hpos.ne']
    ring
  have hdiff : Continuous (fun u => f u - f t) := hf'.sub continuous_const
  have habs : Continuous (fun u : ℝ => ‖(H : Reg n)‖ * |u - (t : ℝ)|) :=
    continuous_const.mul (continuous_id.sub continuous_const).abs
  have hpoint (u : ℝ) : |f u - f t| ≤ ‖(H : Reg n)‖ * |u - (t : ℝ)| := by
    have he := hf.dist_le_mul u (t : ℝ)
    change dist (f u) (f t) ≤ ‖(H : Reg n)‖ * dist u (t : ℝ) at he
    simpa only [Real.dist_eq] using he
  change |orbitCircuitCellMean H P x h - f t| ≤ _
  rw [heq, abs_div, abs_of_pos hd]
  apply div_le_div_of_nonneg_right _ hd.le
  calc
    _ ≤ ∫ u in a..b, |f u - f t| := intervalIntegral.abs_integral_le_integral_abs hab
    _ ≤ ∫ u in a..b, ‖(H : Reg n)‖ * |u - (t : ℝ)| :=
      intervalIntegral.integral_mono_on hab (hdiff.abs.intervalIntegrable a b)
        (habs.intervalIntegrable a b) fun u _ => hpoint u
    _ = _ := by
      rw [intervalIntegral.integral_const_mul, integral_abs_distance t.2]
      ring

/-- At the cell center the worst-case error is half the edge margin. -/
theorem orbitCircuitCellMean_center_error {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) :
    |orbitCircuitCellMean H P x h - orbitCircuitDistance H P x| ≤
      ‖(H : Reg n)‖ * (h : ℝ) / 2 := by
  have hh : 0 < (h : ℝ) := h.2
  let t : Icc (x - (h : ℝ)) (x + (h : ℝ)) :=
    ⟨x, sub_le_self _ hh.le, le_add_of_nonneg_right hh.le⟩
  have he := orbitCircuitCellMean_error H P x h t
  change _ ≤ ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + (x - x) ^ 2) / (2 * (h : ℝ)) at he
  have heq : ‖(H : Reg n)‖ * (h : ℝ) ^ 2 / (2 * (h : ℝ)) =
      ‖(H : Reg n)‖ * (h : ℝ) / 2 := by
    field_simp [hh.ne']
  rw [sub_self, zero_pow two_ne_zero, add_zero, heq] at he
  exact he

/-- A cell whose mean lies outside the error band is classified throughout:
below the band every time is affordable, above it every time is excluded. -/
theorem orbitCircuitCellMean_certifies {n : ℕ} (H : selfAdjoint (Reg n)) (P : ℕ)
    (x : ℝ) (h : CellRadius) (ε : ℝ) (t : Icc (x - (h : ℝ)) (x + (h : ℝ))) :
    let margin := ‖(H : Reg n)‖ * (h : ℝ)
    (orbitCircuitCellMean H P x h + margin ≤ ε →
      HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) ∧
    (ε < orbitCircuitCellMean H P x h - margin →
      ¬ HasProjectiveCircuitApproximation n ε P (unitaryEvolution (H : Reg n) t)) := by
  have hh : 0 < (h : ℝ) := h.2
  have ht : |(t : ℝ) - x| ≤ (h : ℝ) := abs_le.mpr
    ⟨by linarith only [t.2.1], by linarith only [t.2.2]⟩
  have hb : ((t : ℝ) - x) ^ 2 ≤ (h : ℝ) ^ 2 := by
    rw [← sq_abs ((t : ℝ) - x)]
    exact (sq_le_sq₀ (abs_nonneg _) hh.le).mpr ht
  have he := (orbitCircuitCellMean_error H P x h t).trans (show
      ‖(H : Reg n)‖ * ((h : ℝ) ^ 2 + ((t : ℝ) - x) ^ 2) / (2 * (h : ℝ)) ≤
        ‖(H : Reg n)‖ * (h : ℝ) by
    apply (div_le_iff₀ (show 0 < 2 * (h : ℝ) by positivity)).mpr
    convert mul_le_mul_of_nonneg_left (add_le_add_left hb ((h : ℝ) ^ 2))
      (norm_nonneg (H : Reg n)) using 1 <;> ring)
  obtain ⟨hl, hu⟩ := abs_le.mp he
  dsimp only
  rw [hasProjectiveCircuitApproximation_iff_infDist, ← orbitCircuitDistance]
  constructor <;> intro hε <;> linarith only [hl, hu, hε]

#print axioms orbitCircuitCellMean_center_error
#print axioms orbitCircuitCellMean_certifies

end

end GaloisForLFunctions.HTGeometry
