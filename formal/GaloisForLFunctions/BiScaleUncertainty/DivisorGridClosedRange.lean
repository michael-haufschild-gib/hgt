import GaloisForLFunctions.BiScaleUncertainty.DivisorGridSinePackets
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Exact closed-range and energy-gap classification

Uniformly bounded active runs, positive interpolation coercivity and closed
physical range are equivalent. The exact unit-data energy infimum is the sharp
sine coefficient in the bounded case and unattained zero otherwise.
-/

noncomputable section
open Filter Set
open scoped Topology
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

/-- No analytic premise: this decides precisely when a positive coefficient exists. -/
theorem divisorGrid_coercivity_iff (d : ℕ) (D : Set ℕ) :
    (∃ c : ℝ, 0 < c ∧ ∀ v : DivisorGridData d D,
      c * ‖v‖^2 ≤ ‖divisorGridExtension d D v‖^2) ↔ divisorGridBoundedRuns d D := by
  constructor
  · rintro ⟨c, hc, hv⟩
    by_contra hb
    have he (n : ℕ) : c ≤ ‖divisorGridExtension d D (divisorGridNearNull d D n)‖^2 := by
      simpa only [divisorGridNearNull_norm d D hb n, one_pow, mul_one] using
        hv (divisorGridNearNull d D n)
    have hz := ge_of_tendsto' (divisorGridNearNull_energy_tendsto d D hb) he
    exact (not_le_of_gt hc) hz
  · intro hb
    refine ⟨2-2*divisorGridSineFactor d D, ?_, fun v => (divisorGridExtension_stability d D hb v).1⟩
    linarith only [divisorGridSineFactor_lt_one d D hb]

theorem divisorGrid_closed_range_iff (d : ℕ) (D : Set ℕ) :
    IsClosed (Set.range (divisorGridExtension d D)) ↔ divisorGridBoundedRuns d D := by
  constructor
  · intro hc
    obtain ⟨K, hK⟩ := (divisorGridExtension d D).antilipschitz_of_injective_of_isClosed_range
      (divisorGridExtension_injective d D) hc
    by_contra hb
    have he (n : ℕ) : 1 ≤ (K : ℝ)^2 *
        ‖divisorGridExtension d D (divisorGridNearNull d D n)‖^2 := by
      have hn := hK.le_mul_dist (divisorGridNearNull d D n) 0
      simp only [dist_zero_right, map_zero, divisorGridNearNull_norm d D hb n] at hn
      have hs := mul_self_le_mul_self (by norm_num : (0 : ℝ) ≤ 1) hn
      nlinarith only [hs]
    have ht := (tendsto_const_nhds (x := (K : ℝ)^2)).mul
      (divisorGridNearNull_energy_tendsto d D hb)
    have hz := ge_of_tendsto' ht he
    norm_num at hz
  · exact isClosed_range_divisorGridExtension d D

theorem divisorGrid_closed_range_iff_coercive (d : ℕ) (D : Set ℕ) :
    IsClosed (Set.range (divisorGridExtension d D)) ↔
      ∃ c : ℝ, 0 < c ∧ ∀ v : DivisorGridData d D,
        c * ‖v‖^2 ≤ ‖divisorGridExtension d D v‖^2 :=
  (divisorGrid_closed_range_iff d D).trans (divisorGrid_coercivity_iff d D).symm

def divisorGridUnitEnergies (d : ℕ) (D : Set ℕ) : Set ℝ :=
  {e | ∃ v : DivisorGridData d D, ‖v‖ = 1 ∧ e = ‖divisorGridExtension d D v‖^2}

theorem divisorGrid_unit_energy_pos (d : ℕ) (D : Set ℕ)
    (v : DivisorGridData d D) (hv : ‖v‖ = 1) : 0 < ‖divisorGridExtension d D v‖^2 := by
  apply sq_pos_of_pos
  apply norm_pos_iff.mpr
  intro hz
  have h0 : v = 0 := (divisorGridExtension_injective d D) (hz.trans (map_zero _).symm)
  simp only [h0, norm_zero] at hv
  exact zero_ne_one hv

theorem divisorGrid_zero_not_unit_energy (d : ℕ) (D : Set ℕ) :
    0 ∉ divisorGridUnitEnergies d D := by
  rintro ⟨v, hv, he⟩
  exact (ne_of_gt (divisorGrid_unit_energy_pos d D v hv)) he.symm

def divisorGridGap (d : ℕ) (D : Set ℕ) : ℝ :=
  if divisorGridBoundedRuns d D then 2-2*divisorGridSineFactor d D else 0

/-- The exact bottom energy, including the unstable infinite-family regime. -/
theorem divisorGridGap_isGLB (d : ℕ) (D : Set ℕ) :
    IsGLB (divisorGridUnitEnergies d D) (divisorGridGap d D) := by
  by_cases hb : divisorGridBoundedRuns d D
  · rw [divisorGridGap, if_pos hb]
    constructor
    · rintro e ⟨v, hv, rfl⟩
      simpa only [hv, one_pow, mul_one] using (divisorGridExtension_stability d D hb v).1
    · intro b hbnd
      have hr := divisorGridRunLength_attained d D hb
      have hp := divisorGridRunLength_pos d D hb
      apply hbnd
      exact ⟨divisorGridUnitPacket d D _, divisorGridUnitPacket_norm d D _ hr hp,
        (divisorGridUnitPacket_energy d D _ hr hp).symm⟩
  · rw [divisorGridGap, if_neg hb]
    constructor
    · rintro e ⟨v, _, rfl⟩
      exact sq_nonneg _
    · intro b hbnd
      apply ge_of_tendsto' (divisorGridNearNull_energy_tendsto d D hb)
      intro n
      exact hbnd ⟨divisorGridNearNull d D n, divisorGridNearNull_norm d D hb n, rfl⟩

theorem divisorGridGap_attained_iff (d : ℕ) (D : Set ℕ) :
    divisorGridGap d D ∈ divisorGridUnitEnergies d D ↔ divisorGridBoundedRuns d D := by
  constructor
  · intro hm
    by_contra hb
    rw [divisorGridGap, if_neg hb] at hm
    exact divisorGrid_zero_not_unit_energy d D hm
  · intro hb
    rw [divisorGridGap, if_pos hb]
    have hr := divisorGridRunLength_attained d D hb
    have hp := divisorGridRunLength_pos d D hb
    exact ⟨divisorGridUnitPacket d D _, divisorGridUnitPacket_norm d D _ hr hp,
      (divisorGridUnitPacket_energy d D _ hr hp).symm⟩

/-- A concrete infinite-family boundary: all spacings destroy closed range. -/
theorem divisorGrid_univ_not_closed (d : ℕ) :
    ¬ IsClosed (Set.range (divisorGridExtension d Set.univ)) :=
  fun h => divisorGrid_univ_unbounded d ((divisorGrid_closed_range_iff d Set.univ).mp h)

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
