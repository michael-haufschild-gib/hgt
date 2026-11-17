import GaloisForLFunctions.HTGeometry.PaperRecurrentDiagonal
import GaloisForLFunctions.HTGeometry.HardyDiskSpace
import GaloisForLFunctions.RHTower.RootOfUnityIntervalCompletion

/-!
# Compact cancellation for finite cyclic rotation compositions

The cancellation mechanism in arXiv:2610.35415 becomes exact for cyclic
rotations in the corpus's Hardy coefficient model. A finite linear
combination is compact precisely when all its distinct-rotation
coefficients vanish. Its full operator norm survives in the compact
quotient. Each diagonal operator is identified with actual composition
of its analytic function by the corresponding disk rotation.
-/

open Filter Topology
open scoped BigOperators
namespace GaloisForLFunctions.HilbertMetric.Dynamics
open HTGeometry RHTower.RootOfUnityCompletion
noncomputable section

private theorem phase_norm (N : ℕ) (a : ZMod (N + 1)) : ‖ZMod.stdAddChar a‖ = 1 := by
  rw [ZMod.stdAddChar_apply]
  exact Circle.norm_coe _

private theorem phase_order (N : ℕ) (a : ZMod (N + 1)) :
    ZMod.stdAddChar a ^ (N + 1) = 1 := by
  rw [← stdAddChar_mul_natCast_pow, ZMod.natCast_self, mul_zero, AddChar.map_zero_eq_one]

private theorem phase_power_bound (N : ℕ) (a : ZMod (N + 1)) (k : ℕ) :
    ‖ZMod.stdAddChar a ^ k‖ ≤ 1 := by
  rw [norm_pow, phase_norm, one_pow]

/-- Composition with one finite cyclic disk rotation in Taylor-coefficient coordinates. -/
def cyclicRotation (N : ℕ) (a : ZMod (N + 1)) : HardyDisk →L[ℂ] HardyDisk :=
  lpDiagonalCLM (fun k => ZMod.stdAddChar a ^ k) (by norm_num) (phase_power_bound N a)

@[simp] theorem cyclicRotation_apply (N : ℕ) (a : ZMod (N + 1)) (f : HardyDisk) (k : ℕ) :
    cyclicRotation N a f k = ZMod.stdAddChar a ^ k * f k := rfl

/-- The diagonal formula is literally the analytic rotation-composition action. -/
theorem cyclicRotation_hardyFun (N : ℕ) (a : ZMod (N + 1)) (f : HardyDisk) (z : ℂ) :
    hardyFun (cyclicRotation N a f) z = hardyFun f (ZMod.stdAddChar a * z) := by
  unfold hardyFun
  apply tsum_congr
  intro k
  rw [cyclicRotation_apply, mul_pow]
  ring

/-- Each rotation is a unitary operator on the actual Hardy Hilbert space. -/
theorem cyclicRotation_unitary (N : ℕ) (a : ZMod (N + 1)) :
    cyclicRotation N a ∈ unitary (HardyDisk →L[ℂ] HardyDisk) := by
  apply paperBoundedDiagonal_unitary _ (by norm_num) (phase_power_bound N a)
  intro k
  rw [norm_pow, phase_norm, one_pow]

/-- Periodic Fourier multiplier of a finite combination of distinct rotations. -/
def rotationSymbol (N : ℕ) (c : ZMod (N + 1) → ℂ) (k : ℕ) : ℂ :=
  ∑ a, c a * ZMod.stdAddChar a ^ k

private theorem rotationSymbol_bound (N : ℕ) (c : ZMod (N + 1) → ℂ) (k : ℕ) :
    ‖rotationSymbol N c k‖ ≤ ∑ a, ‖c a‖ := by
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro a _
  rw [norm_mul, norm_pow, phase_norm, one_pow, mul_one]

/-- The finite rotation sum as one bounded operator. -/
def rotationCombination (N : ℕ) (c : ZMod (N + 1) → ℂ) : HardyDisk →L[ℂ] HardyDisk :=
  lpDiagonalCLM (rotationSymbol N c) (Finset.sum_nonneg fun a _ => norm_nonneg (c a))
    (rotationSymbol_bound N c)

/-- Coefficient multiplication agrees with the finite sum of composition operators. -/
theorem rotationCombination_eq_sum (N : ℕ) (c : ZMod (N + 1) → ℂ) :
    rotationCombination N c = ∑ a, c a • cyclicRotation N a := by
  ext f k
  simp only [rotationCombination, lpDiagonalCLM_apply, rotationSymbol,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    lp.coeFn_sum, Finset.sum_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
    cyclicRotation_apply, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  ring

private theorem rotationSymbol_recurrent (N : ℕ) (c : ZMod (N + 1) → ℂ) :
    PaperDiagonalRecurrent (rotationSymbol N c) := by
  intro k
  refine ⟨fun r => k + (N + 1) * r, ?_, ?_⟩
  · apply tendsto_atTop_mono (fun r => ?_) tendsto_id
    change r ≤ k + (N + 1) * r
    rw [Nat.add_mul, one_mul]
    omega
  · intro r
    unfold rotationSymbol
    apply Finset.sum_congr rfl
    intro a _
    rw [pow_add, pow_mul, phase_order, one_pow, mul_one]

private theorem rotationSymbol_fourier (N : ℕ) (c : ZMod (N + 1) → ℂ)
    (h : ZMod (N + 1)) : rotationSymbol N c (-h).val = zmodCoeff c h := by
  unfold rotationSymbol zmodCoeff
  apply Finset.sum_congr rfl
  intro a _
  rw [← stdAddChar_mul_natCast_pow, ZMod.natCast_zmod_val]
  congr 2
  ring

/-- No nonzero cyclic rotation combination can be hidden by a compact correction. -/
theorem rotationCombination_essential_norm (N : ℕ) (c : ZMod (N + 1) → ℂ) :
    compactIdealDistance (rotationCombination N c) = ‖rotationCombination N c‖ :=
  paperRecurrentDiagonal_compactIdealDistance _ _ _ (rotationSymbol_recurrent N c)

/-- Fourier inversion gives the exact compactness classification. -/
theorem rotationCombination_compact_iff (N : ℕ) (c : ZMod (N + 1) → ℂ) :
    IsCompactOperator (rotationCombination N c) ↔ ∀ a, c a = 0 := by
  constructor
  · intro hc
    have hz : rotationCombination N c = 0 :=
      (paperRecurrentDiagonal_compact_iff_eq_zero _ _ _ (rotationSymbol_recurrent N c)).mp hc
    have hs (k : ℕ) : rotationSymbol N c k = 0 := by
      have h := congrArg (fun T : HardyDisk →L[ℂ] HardyDisk => (T (lp.single 2 k 1)) k) hz
      simpa [rotationCombination, lp.single_apply] using h
    have hf (h : ZMod (N + 1)) : zmodCoeff c h = 0 := by
      rw [← rotationSymbol_fourier]
      exact hs _
    intro a
    rw [fourier_inversion c a]
    simp only [hf, zero_mul, Finset.sum_const_zero, mul_zero]
  · intro hc
    have hz : rotationCombination N c = 0 := by
      ext f k
      simp [rotationCombination, rotationSymbol, hc]
    rw [hz]
    exact isCompactOperator_zero

/-- Compactness of the actual finite composition sum forces every coefficient to vanish. -/
theorem cyclicRotation_sum_compact_iff (N : ℕ) (c : ZMod (N + 1) → ℂ) :
    IsCompactOperator (∑ a, c a • cyclicRotation N a : HardyDisk →L[ℂ] HardyDisk) ↔
      ∀ a, c a = 0 := by
  rw [← rotationCombination_eq_sum, rotationCombination_compact_iff]

#print axioms cyclicRotation_hardyFun
#print axioms cyclicRotation_unitary
#print axioms rotationCombination_eq_sum
#print axioms rotationCombination_essential_norm
#print axioms cyclicRotation_sum_compact_iff
end
end GaloisForLFunctions.HilbertMetric.Dynamics
