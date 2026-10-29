import GaloisForLFunctions.HTGeometry.DiscreteValuationShells
import GaloisForLFunctions.HTGeometry.L1PeriodizationFourier
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# The spherical rank-one integral over a local field

The shell parameter `z` is the value `Q⁻ˢ`. On the radius-`n` shell the
spherical kernel is `(z/Q)ⁿ`. Exact shell measures and absolute convergence
give the local intertwining factor `(1-z/Q)/(1-z)` for `‖z‖ < 1`.
-/

namespace GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

open MeasureTheory MeasureTheory.Measure
open scoped WithZero WithZeroMulInt Pointwise ENNReal NNReal

noncomputable section

variable (K : Type*) [Field K] [Valued K ℤᵐ⁰]
  [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)]

local instance : (Valued.v : Valuation K ℤᵐ⁰).RankOne :=
  Valuation.IsRankOneDiscrete.rankOne _ (show (1 : NNReal) < 2 from one_lt_two)
local instance : NormedField K := Valued.toNormedField K ℤᵐ⁰
local instance : ProperSpace K :=
  Valued.integer.properSpace_iff_compactSpace_integer.mpr inferInstance
local instance : MeasurableSpace K := borel K
local instance : BorelSpace K := ⟨rfl⟩

variable (π : Integer K) (hπ : Irreducible π)

theorem residue_card_gt_one : 1 < Nat.card (Residue K) := Finite.one_lt_card

theorem measure_valuationShell_le (n : ℕ) :
    normalizedHaar K (valuationShell K π hπ n) ≤ (Nat.card (Residue K) : ℝ≥0∞) ^ n := by
  rw [← measure_integralDilate K π hπ n]
  exact measure_mono (disjointed_le _ _)

theorem measure_valuationShell_ne_top (n : ℕ) :
    normalizedHaar K (valuationShell K π hπ n) ≠ ∞ :=
  ne_top_of_le_ne_top (by finiteness) (measure_valuationShell_le K π hπ n)

theorem measureReal_valuationShell_le (n : ℕ) :
    (normalizedHaar K).real (valuationShell K π hπ n) ≤ (Nat.card (Residue K) : ℝ) ^ n := by
  simpa only [measureReal_def, ENNReal.toReal_pow, ENNReal.toReal_natCast] using
    ENNReal.toReal_mono (by finiteness) (measure_valuationShell_le K π hπ n)

@[simp] theorem measureReal_valuationShell_zero :
    (normalizedHaar K).real (valuationShell K π hπ 0) = 1 := by
  rw [measureReal_def, measure_valuationShell_zero, ENNReal.toReal_one]

theorem measureReal_valuationShell_succ (n : ℕ) :
    (normalizedHaar K).real (valuationShell K π hπ (n + 1)) =
      (Nat.card (Residue K) : ℝ) ^ (n + 1) - (Nat.card (Residue K) : ℝ) ^ n := by
  rw [measureReal_def, measure_valuationShell_succ,
    ENNReal.toReal_sub_of_le, ENNReal.toReal_pow, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  · exact_mod_cast pow_le_pow_right₀ (le_of_lt (residue_card_gt_one K)) (Nat.le_succ n)
  · finiteness

/-- The contribution supported on one actual valuation shell. -/
def sphericalShellTerm (z : ℂ) (n : ℕ) : K → ℂ :=
  (valuationShell K π hπ n).indicator
    (fun _ => ((Nat.card (Residue K) : ℂ)⁻¹ * z) ^ n)

/-- The radial spherical kernel, expressed in the proved shell partition. -/
def sphericalKernel (z : ℂ) (x : K) : ℂ := ∑' n : ℕ, sphericalShellTerm K π hπ z n x

omit [(Valued.v : Valuation K ℤᵐ⁰).IsNontrivial] [CompactSpace (Integer K)] in
theorem sphericalKernel_on_shell (z : ℂ) (n : ℕ) {x : K}
    (hx : x ∈ valuationShell K π hπ n) :
    sphericalKernel K π hπ z x = ((Nat.card (Residue K) : ℂ)⁻¹ * z) ^ n := by
  unfold sphericalKernel
  rw [tsum_eq_single n]
  · exact Set.indicator_of_mem hx _
  · intro m hmn
    have hx' : x ∉ valuationShell K π hπ m := fun hm =>
      Set.disjoint_left.mp (valuationShell_disjoint K π hπ hmn) hm hx
    exact Set.indicator_of_notMem hx' _

theorem sphericalShellTerm_integrable (z : ℂ) (n : ℕ) :
    Integrable (sphericalShellTerm K π hπ z n) (normalizedHaar K) := by
  apply (integrable_indicator_iff (valuationShell_measurable K π hπ n)).mpr
  exact integrableOn_const (measure_valuationShell_ne_top K π hπ n)

theorem integral_sphericalShellTerm_norm_le (z : ℂ) (n : ℕ) :
    (∫ x, ‖sphericalShellTerm K π hπ z n x‖ ∂normalizedHaar K) ≤ ‖z‖ ^ n := by
  have hq : (Nat.card (Residue K) : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt (residue_card_gt_one K)).ne'
  have he : (fun x => ‖sphericalShellTerm K π hπ z n x‖) =
      (valuationShell K π hπ n).indicator
        (fun _ => ‖((Nat.card (Residue K) : ℂ)⁻¹ * z) ^ n‖) := by
    funext x
    by_cases hx : x ∈ valuationShell K π hπ n <;> simp [sphericalShellTerm, hx]
  rw [he, integral_indicator_const _ (valuationShell_measurable K π hπ n), smul_eq_mul]
  calc
    _ ≤ (Nat.card (Residue K) : ℝ) ^ n *
        ‖((Nat.card (Residue K) : ℂ)⁻¹ * z) ^ n‖ :=
      mul_le_mul_of_nonneg_right (measureReal_valuationShell_le K π hπ n) (norm_nonneg _)
    _ = ‖z‖ ^ n := by
      rw [norm_pow, norm_mul, norm_inv, Complex.norm_natCast, ← mul_pow,
        ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

theorem sphericalShellTerm_norm_integrals_summable {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun n => ∫ x, ‖sphericalShellTerm K π hπ z n x‖ ∂normalizedHaar K) := by
  have hs := (summable_geometric_of_norm_lt_one hz).norm
  simp only [norm_pow] at hs
  exact Summable.of_nonneg_of_le (fun n => integral_nonneg (fun x => norm_nonneg _))
    (integral_sphericalShellTerm_norm_le K π hπ z) hs

/-- The spherical kernel is absolutely integrable in its convergence disk. -/
theorem sphericalKernel_integrable {z : ℂ} (hz : ‖z‖ < 1) :
    Integrable (sphericalKernel K π hπ z) (normalizedHaar K) :=
  HTGeometry.integrable_tsum_of_summable_integral_norm
    (sphericalShellTerm_integrable K π hπ z)
    (sphericalShellTerm_norm_integrals_summable K π hπ hz)

@[simp] theorem integral_sphericalShellTerm_zero (z : ℂ) :
    (∫ x, sphericalShellTerm K π hπ z 0 x ∂normalizedHaar K) = 1 := by
  rw [sphericalShellTerm, integral_indicator_const _ (valuationShell_measurable K π hπ 0),
    measureReal_valuationShell_zero, one_smul, pow_zero]

theorem integral_sphericalShellTerm_succ (z : ℂ) (n : ℕ) :
    (∫ x, sphericalShellTerm K π hπ z (n + 1) x ∂normalizedHaar K) =
      (1 - (Nat.card (Residue K) : ℂ)⁻¹) * z ^ (n + 1) := by
  have hq : (Nat.card (Residue K) : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.zero_lt_of_lt (residue_card_gt_one K)).ne'
  rw [sphericalShellTerm, integral_indicator_const _
    (valuationShell_measurable K π hπ (n + 1)), measureReal_valuationShell_succ,
    Complex.real_smul, Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_pow,
    Complex.ofReal_natCast, mul_pow, inv_pow, pow_succ]
  field_simp [hq]

/-- Exact local intertwining factor, derived from the actual Haar integral. -/
theorem integral_sphericalKernel {z : ℂ} (hz : ‖z‖ < 1) :
    (∫ x, sphericalKernel K π hπ z x ∂normalizedHaar K) =
      (1 - (Nat.card (Residue K) : ℂ)⁻¹ * z) / (1 - z) := by
  have hs := sphericalShellTerm_norm_integrals_summable K π hπ hz
  have hi := sphericalShellTerm_integrable K π hπ z
  have ht : Summable (fun n => ∫ x, sphericalShellTerm K π hπ z n x ∂normalizedHaar K) :=
    hs.of_norm_bounded (fun n => norm_integral_le_integral_norm _)
  change (∫ x, ∑' n, sphericalShellTerm K π hπ z n x ∂normalizedHaar K) = _
  rw [← integral_tsum_of_summable_integral_norm hi hs, ht.tsum_eq_zero_add,
    integral_sphericalShellTerm_zero]
  simp_rw [integral_sphericalShellTerm_succ, pow_succ', ← mul_assoc]
  rw [tsum_mul_left, tsum_geometric_of_norm_lt_one hz]
  have hz1 : 1 - z ≠ 0 := by
    intro h
    have he : z = 1 := (sub_eq_zero.mp h).symm
    simp only [he, norm_one, lt_self_iff_false] at hz
  field_simp [hz1]
  ring

end
end GaloisForLFunctions.HTGeometry.DiscreteValuationHaar

