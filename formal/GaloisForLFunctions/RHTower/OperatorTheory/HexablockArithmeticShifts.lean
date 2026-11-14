import GaloisForLFunctions.HTGeometry.OperatorTheory.HexablockAlgebra
import GaloisForLFunctions.RHTower.PaperPrimeCoShiftEscape

/-!
# Hexablock coordinates of multiplicative arithmetic shifts

Every four positive-integer shifts satisfy the energy and cross-coordinate
identities of the hexablock parametrization. The Brown–Halmos slice for each
shift is exactly invariance under multiplicative translation. A compact
operator invariant under all these slices vanishes, by escape through primes.
-/

noncomputable section
namespace RHTower.PrimeCoShift
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.Hexablock
open ContinuousLinearMap Filter Topology
open scoped InnerProductSpace

private theorem shift_isometry (p : ℕ+) : star (Vop p) * Vop p = 1 := by
  rw [star_Vop, coShift_mul_Vop]

/-- The hexablock energy and cross-coordinate identities for arbitrary arithmetic shifts. -/
theorem hexablock_arithmetic_relations (p q r s : ℕ+) :
    (star (a (Vop p) (Vop r)) * a (Vop p) (Vop r) +
      star (x₁ (Vop p) (Vop q)) * x₁ (Vop p) (Vop q) = 1) ∧
    (star (a (Vop p) (Vop r)) * a (Vop p) (Vop r) +
      star (x₂ (Vop p) (Vop r) (Vop s)) * x₂ (Vop p) (Vop r) (Vop s) = 1) ∧
    star (x₃ (Vop p) (Vop q) (Vop r) (Vop s)) *
      x₃ (Vop p) (Vop q) (Vop r) (Vop s) = 1 ∧
    star (x₁ (Vop p) (Vop q)) * x₃ (Vop p) (Vop q) (Vop r) (Vop s) =
      x₂ (Vop p) (Vop r) (Vop s) := by
  obtain ⟨h₁, h₂, h₃⟩ := energy _ _ _ _
    (shift_isometry p) (shift_isometry q) (shift_isometry r) (shift_isometry s)
  exact ⟨h₁, h₂, h₃, cross _ _ _ _ (shift_isometry p) (shift_isometry q)
    (Vop_commute p q) (Vop_commute p r) (Vop_commute p s)⟩

/-- Brown–Halmos equations on one arithmetic slice are multiplicative translation invariance. -/
theorem hexablock_arithmetic_brownHalmos_iff (p : ℕ+) (T : H →L[ℂ] H) :
    BrownHalmos (halfDiff (Vop p) 1) (halfSum (Vop p) 1)
      (halfSum (Vop p) 1) (Vop p) T ↔ primeCoShift p * T * Vop p = T := by
  rw [slice_brownHalmos_iff, star_Vop]

/-- Compact arithmetic Brown–Halmos operators vanish; no symbol representation is assumed. -/
theorem hexablock_arithmetic_compact_iff (T : H →L[ℂ] H) :
    ((∀ p : ℕ+, BrownHalmos (halfDiff (Vop p) 1) (halfSum (Vop p) 1)
      (halfSum (Vop p) 1) (Vop p) T) ∧ IsCompactOperator T) ↔ T = 0 := by
  constructor
  · rintro ⟨hfix, hc⟩
    apply ContinuousLinearMap.ext
    intro x
    rw [zero_apply]
    apply ext_inner_left ℂ
    intro y
    rw [inner_zero_right]
    have heq (n : ℕ) : ⟪y, T x⟫_ℂ =
        ⟪Vop (primePNat (paperCoShiftEscapePrime n)) y,
          T (Vop (primePNat (paperCoShiftEscapePrime n)) x)⟫_ℂ := by
      let p := primePNat (paperCoShiftEscapePrime n)
      have hp := (slice_brownHalmos_iff (Vop p) T).mp (hfix p)
      conv_lhs => rw [← hp]
      rw [mul_apply, mul_apply, _root_.ContinuousLinearMap.star_eq_adjoint, adjoint_inner_right]
    have ht : Tendsto (fun n =>
        ⟪Vop (primePNat (paperCoShiftEscapePrime n)) y,
          T (Vop (primePNat (paperCoShiftEscapePrime n)) x)⟫_ℂ) atTop (𝓝 0) := by
      have hb := (paperCoShiftEscape_compact_tendsto ⟨T, hc⟩ x).norm.const_mul ‖y‖
      rw [norm_zero, mul_zero] at hb
      refine squeeze_zero_norm (fun n => ?_) hb
      calc
        ‖⟪Vop (primePNat (paperCoShiftEscapePrime n)) y,
            T (Vop (primePNat (paperCoShiftEscapePrime n)) x)⟫_ℂ‖ ≤
            ‖Vop (primePNat (paperCoShiftEscapePrime n)) y‖ *
              ‖T (Vop (primePNat (paperCoShiftEscapePrime n)) x)‖ := norm_inner_le_norm _ _
        _ = ‖y‖ * ‖T (Vop (primePNat (paperCoShiftEscapePrime n)) x)‖ := by
          rw [show ‖Vop (primePNat (paperCoShiftEscapePrime n)) y‖ = ‖y‖ from
            (primeShift _).norm_map y]
    exact tendsto_nhds_unique (tendsto_const_nhds.congr heq) ht
  · rintro rfl
    refine ⟨fun p => (slice_brownHalmos_iff (Vop p) 0).mpr ?_, isCompactOperator_zero⟩
    simp only [mul_zero, zero_mul]

end RHTower.PrimeCoShift

#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_relations
#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_brownHalmos_iff
#print axioms RHTower.PrimeCoShift.hexablock_arithmetic_compact_iff
