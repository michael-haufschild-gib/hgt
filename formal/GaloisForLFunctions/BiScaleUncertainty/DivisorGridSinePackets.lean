import GaloisForLFunctions.BiScaleUncertainty.DivisorGridTraceStability
import GaloisForLFunctions.BiScaleUncertainty.FinitePathSinePackets
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Sine producers for arbitrary divisor families

Masking finite sine packets constructs actual data for every requested length.
On an active run their exact energies give sharp modes and normalized near-null
producers, without an analytic admission premise.
-/

noncomputable section
open Filter
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorGridRunData (d : ℕ) (D : Set ℕ) (n : ℕ) (x : ℕ → ℝ) :
    DivisorGridData d D :=
  divisorGridData d D (intervalTraceData (divisorGridRunStart d D n) n x)

theorem divisorGridRunData_coe (d : ℕ) (D : Set ℕ) (n : ℕ) (x : ℕ → ℝ)
    (h : divisorGridHasRun d D n) :
    (divisorGridRunData d D n x).1 = intervalTraceData (divisorGridRunStart d D n) n x := by
  apply lp.ext
  funext k
  change (divisorGridData d D _).1 k = _
  rw [divisorGridData_apply]
  split_ifs with hk
  · rfl
  · symm
    apply intervalTraceData_off
    intro j hj he
    apply hk
    rw [he]
    exact divisorGridRunStart_active d D n h j hj

def divisorGridSinePacket (d : ℕ) (D : Set ℕ) (n : ℕ) : DivisorGridData d D :=
  divisorGridRunData d D n (pathSineValue n)

def divisorGridAlternatingPacket (d : ℕ) (D : Set ℕ) (n : ℕ) : DivisorGridData d D :=
  divisorGridRunData d D n (alternatingPathSineValue n)

theorem divisorGridSinePacket_ne_zero (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) (hn : 0 < n) : divisorGridSinePacket d D n ≠ 0 := by
  intro hz
  have he := congrArg (fun v : DivisorGridData d D => v.1 (divisorGridRunStart d D n)) hz
  change (divisorGridRunData d D n _).1 _ = 0 at he
  rw [divisorGridRunData_coe d D n _ h] at he
  have hv := intervalTraceData_at (divisorGridRunStart d D n) n 0 (pathSineValue n)
  simp only [Nat.add_zero, if_pos hn] at hv
  rw [hv] at he
  exact (ne_of_gt (pathSineValue_first_pos n hn)) he

theorem divisorGridPackets_norm_sq (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) :
    ‖divisorGridAlternatingPacket d D n‖^2 = ‖divisorGridSinePacket d D n‖^2 := by
  change ‖(divisorGridRunData d D n _).1‖^2 = ‖(divisorGridRunData d D n _).1‖^2
  simp only [divisorGridRunData_coe d D n _ h, intervalTraceData_norm_sq,
    alternatingPathSineValue_sq]

theorem divisorGridSinePacket_energy (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) :
    ‖divisorGridExtension d D (divisorGridSinePacket d D n)‖^2 =
      (2 - 2 * Real.cos (Real.pi / ((n : ℝ)+1))) * ‖divisorGridSinePacket d D n‖^2 := by
  rw [divisorGridExtension_energy]
  change 2 * ‖(divisorGridRunData d D n _).1‖^2 -
    2 * (∑' k, (divisorGridRunData d D n _).1 k * (divisorGridRunData d D n _).1 (k+1)) =
    _ * ‖(divisorGridRunData d D n _).1‖^2
  simp only [divisorGridRunData_coe d D n _ h]
  rw [intervalTraceData_adjacent _ _ _ (pathSineValue_end n),
    pathSineValue_adjacent, intervalTraceData_norm_sq]
  ring

theorem divisorGridAlternatingPacket_energy (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) :
    ‖divisorGridExtension d D (divisorGridAlternatingPacket d D n)‖^2 =
      (2 + 2 * Real.cos (Real.pi / ((n : ℝ)+1))) *
        ‖divisorGridAlternatingPacket d D n‖^2 := by
  rw [divisorGridExtension_energy]
  change 2 * ‖(divisorGridRunData d D n _).1‖^2 -
    2 * (∑' k, (divisorGridRunData d D n _).1 k * (divisorGridRunData d D n _).1 (k+1)) =
    _ * ‖(divisorGridRunData d D n _).1‖^2
  simp only [divisorGridRunData_coe d D n _ h]
  rw [intervalTraceData_adjacent _ _ _ (alternatingPathSineValue_end n),
    alternatingPathSineValue_adjacent, intervalTraceData_norm_sq]
  simp only [alternatingPathSineValue_sq]
  ring

theorem divisorGridExtension_sharp (d : ℕ) (D : Set ℕ)
    (h : divisorGridBoundedRuns d D) :
    ∃ lower upper : DivisorGridData d D, 0 < ‖lower‖^2 ∧ 0 < ‖upper‖^2 ∧
      ‖divisorGridExtension d D lower‖^2 = (2-2*divisorGridSineFactor d D)*‖lower‖^2 ∧
      ‖divisorGridExtension d D upper‖^2 = (2+2*divisorGridSineFactor d D)*‖upper‖^2 := by
  have hr := divisorGridRunLength_attained d D h
  have hp := sq_pos_of_pos (norm_pos_iff.mpr
    (divisorGridSinePacket_ne_zero d D _ hr (divisorGridRunLength_pos d D h)))
  refine ⟨divisorGridSinePacket d D _, divisorGridAlternatingPacket d D _, hp, ?_,
    divisorGridSinePacket_energy d D _ hr, divisorGridAlternatingPacket_energy d D _ hr⟩
  rwa [divisorGridPackets_norm_sq d D _ hr]

def divisorGridUnitPacket (d : ℕ) (D : Set ℕ) (n : ℕ) : DivisorGridData d D :=
  ‖divisorGridSinePacket d D n‖⁻¹ • divisorGridSinePacket d D n

theorem divisorGridUnitPacket_norm (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) (hn : 0 < n) : ‖divisorGridUnitPacket d D n‖ = 1 := by
  rw [divisorGridUnitPacket, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr (divisorGridSinePacket_ne_zero d D n h hn))

theorem divisorGridUnitPacket_energy (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) (hn : 0 < n) :
    ‖divisorGridExtension d D (divisorGridUnitPacket d D n)‖^2 =
      2 - 2 * Real.cos (Real.pi / ((n : ℝ)+1)) := by
  have hz := norm_ne_zero_iff.mpr (divisorGridSinePacket_ne_zero d D n h hn)
  rw [divisorGridUnitPacket, map_smul, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), mul_pow, divisorGridSinePacket_energy d D n h]
  field_simp

theorem pathSineGap_tendsto_zero :
    Tendsto (fun n : ℕ => 2 - 2 * Real.cos (Real.pi / ((n : ℝ)+1))) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => Real.pi / ((n : ℝ)+1)) atTop (𝓝 0) := by
    simpa only [mul_one_div, mul_zero] using
      (tendsto_const_nhds (x := Real.pi)).mul tendsto_one_div_add_atTop_nhds_zero_nat
  have hc := Real.continuous_cos.continuousAt.tendsto.comp h
  simpa using (tendsto_const_nhds (x := (2 : ℝ))).sub
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hc)

def divisorGridNearNull (d : ℕ) (D : Set ℕ) (n : ℕ) : DivisorGridData d D :=
  divisorGridUnitPacket d D (n+1)

theorem divisorGridNearNull_norm (d : ℕ) (D : Set ℕ)
    (h : ¬ divisorGridBoundedRuns d D) (n : ℕ) : ‖divisorGridNearNull d D n‖ = 1 :=
  divisorGridUnitPacket_norm d D (n+1) (divisorGrid_unbounded_runs d D h (n+1)) (by omega)

theorem divisorGridNearNull_energy_tendsto (d : ℕ) (D : Set ℕ)
    (h : ¬ divisorGridBoundedRuns d D) :
    Tendsto (fun n => ‖divisorGridExtension d D (divisorGridNearNull d D n)‖^2) atTop (𝓝 0) := by
  have he (n : ℕ) := divisorGridUnitPacket_energy d D (n+1)
    (divisorGrid_unbounded_runs d D h (n+1)) (by omega)
  simp only [divisorGridNearNull, he]
  exact (tendsto_add_atTop_iff_nat 1).2 pathSineGap_tendsto_zero

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
