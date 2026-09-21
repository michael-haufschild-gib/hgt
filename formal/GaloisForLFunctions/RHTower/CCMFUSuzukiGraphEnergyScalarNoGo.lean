import GaloisForLFunctions.RHTower.CCMFUSuzukiCompletedRieszGraphEnergy
import GaloisForLFunctions.HTGeometry.HarmonicResidueTransfer
import GaloisForLFunctions.HTGeometry.ZetaVerticalAlmostPeriodic

/-!
# Graph energy does not coerce the CCM--FU scalar window

The completed CCM--FU/Suzuki source has a finite weighted graph energy.  This is not a scalar
coercivity estimate.  The explicit harmonic escape model below has square-summable weighted graph
slope while its normalized window tends to infinity.  Consequently no source-free passage from
the existing graph energy to a uniform unit-aperture/FU scalar bound is valid.

The surviving hard problem is therefore arithmetic: a new signed cumulative invariant must use
the literal prime--polar--Gamma source, rather than only its graph-energy norm.
-/

open Filter Topology

namespace RHTower

noncomputable section

/-- A universal escape model for weighted graph energy. -/
def ccmFUSuzukiGraphEnergyEscapeWitness (n : ℕ) : ℝ :=
  (n : ℝ) * (harmonic n : ℝ)

/-- The weighted edge slope in the escape model. -/
def ccmFUSuzukiGraphEnergyEscapeSlope (n : ℕ) : ℝ :=
  (ccmFUSuzukiGraphEnergyEscapeWitness (n + 1) -
    ccmFUSuzukiGraphEnergyEscapeWitness n) / (n + 1 : ℝ)

private theorem ccmFUSuzukiGraphEnergyEscapeSlope_eq (n : ℕ) :
    ccmFUSuzukiGraphEnergyEscapeSlope n = ((harmonic n : ℝ) + 1) / (n + 1 : ℝ) := by
  unfold ccmFUSuzukiGraphEnergyEscapeSlope ccmFUSuzukiGraphEnergyEscapeWitness
  rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  push_cast
  ring

private theorem ccmFUSuzukiGraphEnergyEscapeWitness_normalized_eq_harmonic (n : ℕ) :
    ccmFUSuzukiGraphEnergyEscapeWitness (n + 1) / (n + 1 : ℝ) =
      (harmonic (n + 1) : ℝ) := by
  unfold ccmFUSuzukiGraphEnergyEscapeWitness
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  field_simp [hn]
  push_cast
  ring

private theorem harmonic_add_one_le_two_add_log_succ (n : ℕ) :
    (harmonic n : ℝ) + 1 ≤ 2 + Real.log ((n + 1 : ℕ) : ℝ) := by
  have hsucc : (harmonic n : ℝ) ≤ (harmonic (n + 1) : ℝ) := by
    rw [harmonic_succ, Rat.cast_add, Rat.cast_inv, Rat.cast_natCast]
    exact le_add_of_nonneg_right (by positivity)
  have hupper : (harmonic (n + 1) : ℝ) ≤ 1 + Real.log ((n + 1 : ℕ) : ℝ) :=
    harmonic_le_one_add_log (n + 1)
  linarith

private theorem ccmFUSuzukiGraphEnergyEscapeSlope_sq_le_majorant (n : ℕ) :
    ccmFUSuzukiGraphEnergyEscapeSlope n ^ 2 ≤
      8 / ((n : ℝ) + 1) ^ 2 +
        2 * Real.log ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 1) ^ 2 := by
  have hden : 0 < (n : ℝ) + 1 := by positivity
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hlog : 0 ≤ Real.log ((n : ℝ) + 1) :=
    Real.log_nonneg (by linarith)
  have hhar : 0 ≤ (harmonic n : ℝ) := by
    norm_cast
    unfold harmonic
    exact Finset.sum_nonneg fun i _ => inv_nonneg.mpr (Nat.cast_nonneg i.succ)
  have hupper := harmonic_add_one_le_two_add_log_succ n
  push_cast at hupper
  have hnum : 0 ≤ (harmonic n : ℝ) + 1 := by linarith
  have hquot : ((harmonic n : ℝ) + 1) / ((n : ℝ) + 1) ≤
      (2 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1) := by
    exact (div_le_div_iff_of_pos_right hden).2 hupper
  rw [ccmFUSuzukiGraphEnergyEscapeSlope_eq]
  have hsq : (((harmonic n : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 ≤
      ((2 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)) ^ 2 :=
    (sq_le_sq₀ (div_nonneg hnum hden.le)
      (div_nonneg (by linarith) hden.le)).2 hquot
  calc
    (((harmonic n : ℝ) + 1) / ((n : ℝ) + 1)) ^ 2 ≤
        ((2 + Real.log ((n : ℝ) + 1)) / ((n : ℝ) + 1)) ^ 2 := hsq
    _ ≤ _ := by
      field_simp [hden.ne']
      nlinarith [sq_nonneg (2 - Real.log ((n : ℝ) + 1))]

private theorem summable_sq_ccmFUSuzukiGraphEnergyEscapeSlope :
    Summable (fun n : ℕ => ccmFUSuzukiGraphEnergyEscapeSlope n ^ 2) := by
  have hconstBase : Summable (fun n : ℕ => 8 / (n : ℝ) ^ 2) := by
    refine ((Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)).mul_left 8 |>.congr ?_
    intro n
    ring
  have hconst : Summable (fun n : ℕ => 8 / ((n : ℝ) + 1) ^ 2) := by
    refine (hconstBase.comp_injective Nat.succ_injective).congr ?_
    intro n
    simp only [Function.comp_apply]
    push_cast
    ring
  have hlogBase : Summable (fun n : ℕ =>
      Real.log (n : ℝ) ^ 2 / (n : ℝ) ^ (2 : ℝ)) :=
    HTGeometry.summable_log_pow_div_nat_rpow 2 (sigma := (2 : ℝ)) (by norm_num)
  have hlog : Summable (fun n : ℕ =>
      2 * Real.log ((n : ℝ) + 1) ^ 2 / ((n : ℝ) + 1) ^ 2) := by
    refine ((hlogBase.comp_injective Nat.succ_injective).mul_left 2).congr ?_
    intro n
    simp only [Function.comp_apply]
    push_cast
    rw [Real.rpow_two]
    ring
  refine Summable.of_nonneg_of_le
    (fun n => sq_nonneg (ccmFUSuzukiGraphEnergyEscapeSlope n))
    (fun n => ccmFUSuzukiGraphEnergyEscapeSlope_sq_le_majorant n) ?_
  exact hconst.add hlog

/-- **Sharp graph-energy no-go.** Square-summable weighted edge slopes permit an unbounded
normalized scalar window.  Thus the actual completed CCM--FU graph-energy theorem cannot imply
its RH-equivalent scalar bound without an additional source-sensitive cancellation law. -/
theorem exists_unbounded_normalizedWindow_with_summable_weightedGraphSlope :
    ∃ q : ℕ → ℝ,
      Summable (fun n : ℕ => ((q (n + 1) - q n) / (n + 1 : ℝ)) ^ 2) ∧
        Tendsto (fun n : ℕ => q (n + 1) / (n + 1 : ℝ)) atTop atTop := by
  refine ⟨ccmFUSuzukiGraphEnergyEscapeWitness, ?_, ?_⟩
  · exact summable_sq_ccmFUSuzukiGraphEnergyEscapeSlope
  · rw [show (fun n : ℕ =>
        ccmFUSuzukiGraphEnergyEscapeWitness (n + 1) / (n + 1 : ℝ)) =
        fun n : ℕ => (harmonic (n + 1) : ℝ) by
      funext n
      exact ccmFUSuzukiGraphEnergyEscapeWitness_normalized_eq_harmonic n]
    convert GaloisForLFunctions.tendsto_harmonic_cast_atTop.comp
      (tendsto_add_atTop_nat 1) using 1
    ext n
    rfl

end

end RHTower
