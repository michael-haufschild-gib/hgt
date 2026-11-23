import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.GrowingHorizon.ExponentialTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.FixedHorizon.Concentration.UniformOverlap
import Mathlib.Data.Nat.Log

/-! # Uniform Choi overlap exclusion through a logarithmic time horizon -/
open MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section
local instance : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance

private theorem summable_mesh {c : ℝ} (hc : 0 < c) :
    Summable (fun n : ℕ => (n:ℝ)^4*Real.exp (-c*Real.sqrt n)) := by
  let F : ℝ := Nat.factorial 12
  have hF : 0 < F := Nat.cast_pos.mpr (Nat.factorial_pos _)
  have hp := Real.summable_one_div_nat_pow.mpr (by decide : 1 < 2)
  apply (hp.mul_left (F/c^12)).of_norm_bounded_eventually_nat
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have h := Real.pow_div_factorial_le_exp (c*Real.sqrt n) (mul_nonneg hc.le (Real.sqrt_nonneg _)) 12
  change (c*Real.sqrt n)^12/F ≤ Real.exp (c*Real.sqrt n) at h
  rw [mul_pow,show (Real.sqrt n)^12=((Real.sqrt n)^2)^6 by ring,
    Real.sq_sqrt hn'.le,div_le_iff₀ hF] at h
  rw [Real.norm_of_nonneg (by positivity),neg_mul,Real.exp_neg,←div_eq_mul_inv,
    div_le_iff₀ (Real.exp_pos _)]
  apply le_of_mul_le_mul_left _ (mul_pos (pow_pos hc 12) (sq_pos_of_pos hn'))
  calc (c^12*(n:ℝ)^2)*((n:ℝ)^4) = c^12*(n:ℝ)^6 := by ring
       _ ≤ Real.exp (c*Real.sqrt n)*F := h
       _ = _ := by field_simp [hc.ne',hn'.ne']

/-- One deterministic logarithmic horizon works simultaneously for every
circuit cut and every physical date on almost all sufficiently long prefixes. -/
theorem logarithmic_cut_window {a η κ : ℝ} (ha : 0 < a) (hη : 0 < η) (hκ : 0 < κ) :
    ∃ b : ℕ, 2 ≤ b ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      ∀ t ∈ Icc a (Nat.log b n:ℝ), ω ∉ cutOverlapEvent n t η κ := by
  obtain ⟨B,hB,c,hc,htail⟩ := geometric_cut_overlap_tail ha hη (half_pos hκ)
  let b := B^2
  have hb : 2 ≤ b := hB.trans (le_self_pow₀ (by omega) (by norm_num : 2 ≠ 0))
  let L := Nat.log b
  let E (n : ℕ) := gridOverlap a (L n:ℝ) η (κ/2) n
  obtain ⟨K,hK⟩ := exists_nat_gt a
  have hKpos : 0 < K := Nat.cast_pos.mp (ha.trans hK)
  have hs : Summable fun n => pathPauliDisorderLaw.real (E n) := by
    apply (summable_mesh hc).of_norm_bounded_eventually_nat
    filter_upwards [eventually_ge_atTop (b^K),eventually_gt_atTop 0] with n hn hn₀
    have hKL : K ≤ L n := (Nat.le_log_iff_pow_le hb hn₀.ne').mpr hn
    have hdate : a ≤ (L n:ℝ) := hK.le.trans (Nat.cast_le.mpr hKL)
    have hspace : B^(2*L n) ≤ n := by
      rw [pow_mul]
      exact Nat.pow_log_le_self b hn₀.ne'
    rw [Real.norm_of_nonneg measureReal_nonneg]
    exact (grid_overlap_le hdate (htail (L n) (hKpos.trans_le hKL) n hspace)).trans_eq (by ring)
  have hE : ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop, ω ∉ E n := by
    apply ae_eventually_notMem
    simpa only [ofReal_measureReal (measure_ne_top _ _)] using hs.tsum_ofReal_ne_top
  obtain ⟨C,hC,hH⟩ := gaussian_ae_pathHamiltonian_linear_norm_bound
  obtain ⟨M,hM⟩ := exists_nat_gt (4*C/κ)
  refine ⟨b,hb,?_⟩
  filter_upwards [hE,hH] with ω hw hω
  filter_upwards [hw,hω,eventually_ge_atTop M,eventually_ge_atTop 2] with n hn hnorm hM' hn₂
  have hlength : (L n:ℝ)-a < n := by
    have h : (L n:ℝ) ≤ n := Nat.cast_le.mpr (Nat.log_le_self b n)
    linarith only [h,ha]
  exact exclude_from_grid hC hκ hn₂ (max_lt hlength (hM.trans_le (Nat.cast_le.mpr hM'))) hnorm hn

#print axioms logarithmic_cut_window
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
