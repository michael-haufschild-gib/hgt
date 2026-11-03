import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheOverlapThatResolvesATwistIsAnExactThreshold
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.OverlapForcesNewRamanujanTerms
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# The growing shell correction is polar

The exact completed-energy identity separates a single linear term at
conductor one. At every other fixed conductor the shell grows only logarithmically.
-/

noncomputable section
open MeasureTheory Filter Topology

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
open SpacingScaleHarmonicAnalysis CompletedShell

/-- The overlap-independent part of the completed reference energy. -/
def shellReferenceConstant (φ : ℝ → ℝ) (m : ℕ) : ℝ :=
  completeWeilSelfFinitePart φ 1 + ramanujanAdjunctionEnergy m - Real.eulerMascheroniConstant

/-- The linear shell term occurs only in conductor one; the remaining energy is exact. -/
theorem shellCorrection_eq_polar_sub_log (φ : ℝ → ℝ) {c : ℝ} (hc : 0 < c)
    {m : ℕ} (hm : 0 < m) :
    shellCorrection φ c m =
      (if m = 1 then c * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) else 0) - Real.log c +
        shellReferenceConstant φ m - completedConductorEnergy φ c m := by
  rw [completedConductorEnergy_eq_sub_shellCorrection hc hm,
    completeWeilAdjunctionEnergy, completeWeilSelfFinitePart_eq_at_one_sub_log φ hc]
  unfold shellReferenceConstant completeWeilPoleShift
  split_ifs <;> ring

/-- Away from the single polar term, a fixed conductor costs at most a logarithm. -/
theorem abs_shellCorrection_sub_polar_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {c : ℝ} (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    |shellCorrection φ c m -
      (if m = 1 then c * ((∫ u, φ u) ^ 2 / ∫ u, φ u ^ 2) else 0)| ≤
      Real.log c + |shellReferenceConstant φ m| + completedConductorEnergy φ 1 m := by
  have hc0 := zero_lt_one.trans_le hc
  have hE := completedConductorEnergy_nonneg hφ hsupp hM hc0 hm
  have hE1 := completedConductorEnergy_anti hφ hsupp hM zero_lt_one hc hm
  have hlog := Real.log_nonneg hc
  rw [shellCorrection_eq_polar_sub_log φ hc0 hm]
  calc
    _ = |shellReferenceConstant φ m - Real.log c - completedConductorEnergy φ c m| := by
      congr 1
      ring
    _ ≤ |shellReferenceConstant φ m - Real.log c| + |completedConductorEnergy φ c m| :=
      by simpa only [sub_zero, zero_sub, abs_neg] using
        abs_sub_le (shellReferenceConstant φ m - Real.log c) 0 (completedConductorEnergy φ c m)
    _ ≤ (|shellReferenceConstant φ m| + |Real.log c|) + |completedConductorEnergy φ c m| := by
      have h := abs_sub_le (shellReferenceConstant φ m) 0 (Real.log c)
      simp only [sub_zero, zero_sub, abs_neg] at h
      linarith only [h]
    _ ≤ Real.log c + |shellReferenceConstant φ m| + completedConductorEnergy φ 1 m := by
      rw [abs_of_nonneg hlog, abs_of_nonneg hE]
      linarith only [hE1]

/-- The shell correction divided by overlap converges to the polar charge square. -/
theorem tendsto_shellCorrection_div_overlap {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hM : 0 < ∫ u, φ u ^ 2)
    {m : ℕ} (hm : 0 < m) :
    Tendsto (fun c : ℝ => shellCorrection φ c m / c) atTop
      (𝓝 (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0)) := by
  have hlog : Tendsto (fun c : ℝ => Real.log c / c) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hconst : Tendsto (fun c : ℝ => shellReferenceConstant φ m / c) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_inv_atTop_zero.const_mul (shellReferenceConstant φ m))
  have hE : Tendsto (fun c : ℝ => completedConductorEnergy φ c m / c) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using
      (tendsto_completedConductorEnergy_atTop hφ hsupp hM m).mul tendsto_inv_atTop_zero
  have hpolar : Tendsto
      (fun _c : ℝ => if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0) atTop
      (𝓝 (if m = 1 then (∫ u, φ u) ^ 2 / (∫ u, φ u ^ 2) else 0)) := tendsto_const_nhds
  have hlim := ((hpolar.sub hlog).add hconst).sub hE
  simp only [sub_zero, add_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with c hc
  rw [shellCorrection_eq_polar_sub_log φ hc hm]
  split_ifs <;> (field_simp [hc.ne']; ring)

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.shellCorrection_eq_polar_sub_log
#print axioms GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.tendsto_shellCorrection_div_overlap
