import GaloisForLFunctions.BiarithmeticGeometry.CofactorGraphDomain
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# Isometric right shifts of complex shell coordinates

Normalized shell energy is ordinary complex `ell2`. A right shift inserts
zeros and preserves its complete norm exactly. These shifts provide the
bounded operators needed for infinite intrinsic Wiener convolution.
-/

noncomputable section
open Finset
namespace GaloisForLFunctions.BiarithmeticGeometry

/-- Right shift of normalized shell coordinates, with zero initial boundary. -/
def complexShellShiftFn (r : ℕ) (v : ℕ → ℂ) (M : ℕ) : ℂ :=
  if r ≤ M then v (M - r) else 0

theorem complexShellShiftFn_add_index (r M : ℕ) (v : ℕ → ℂ) :
    complexShellShiftFn r v (M + r) = v M := by
  rw [complexShellShiftFn, if_pos (by omega : r ≤ M + r), Nat.add_sub_cancel]

private theorem summable_complexShellShiftFn (r : ℕ) (v : PronicCoordinateSpace) :
    Summable (fun M => ‖complexShellShiftFn r v M‖ ^ 2) := by
  have hv := (lp.memℓp v).summable (by norm_num : 0 < (2 : ENNReal).toReal)
  apply (summable_nat_add_iff r).mp
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two, complexShellShiftFn_add_index] using hv

/-- The right shift as an element of the complete shell coordinate space. -/
def complexShellShiftVector (r : ℕ) (v : PronicCoordinateSpace) : PronicCoordinateSpace :=
  ⟨complexShellShiftFn r v, memℓp_gen
    ((summable_complexShellShiftFn r v).congr fun M => by
      rw [ENNReal.toReal_ofNat, Real.rpow_two])⟩

theorem complexShellShiftVector_apply (r : ℕ) (v : PronicCoordinateSpace) (M : ℕ) :
    complexShellShiftVector r v M = complexShellShiftFn r v M := rfl

/-- Inserting initial zero shells preserves the full Hilbert norm. -/
theorem norm_complexShellShiftVector (r : ℕ) (v : PronicCoordinateSpace) :
    ‖complexShellShiftVector r v‖ = ‖v‖ := by
  have hsum := (summable_complexShellShiftFn r v).sum_add_tsum_nat_add r
  have hhead : (∑ M ∈ range r, ‖complexShellShiftFn r v M‖ ^ 2) = 0 := by
    apply sum_eq_zero
    intro M hM
    rw [complexShellShiftFn, if_neg (not_le.mpr (mem_range.mp hM)), norm_zero,
      zero_pow (by omega : 2 ≠ 0)]
  rw [hhead, zero_add] at hsum
  simp only [complexShellShiftFn_add_index] at hsum
  have hnorm (w : PronicCoordinateSpace) : ‖w‖ ^ 2 = ∑' M : ℕ, ‖w M‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      lp.norm_rpow_eq_tsum (p := 2) (by norm_num) w
  have hs : ‖complexShellShiftVector r v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [hnorm, hnorm]
    exact hsum.symm
  nlinarith only [hs, norm_nonneg (complexShellShiftVector r v), norm_nonneg v]

/-- Bounded complex-linear right shift on the normalized shell space. -/
def complexShellShift (r : ℕ) : PronicCoordinateSpace →L[ℂ] PronicCoordinateSpace :=
  ({ toFun := complexShellShiftVector r
     map_add' := by
       intro v w
       apply lp.ext
       funext M
       by_cases hr : r ≤ M <;>
         simp only [complexShellShiftVector_apply, complexShellShiftFn, hr, if_true, if_false,
           lp.coeFn_add, Pi.add_apply, add_zero]
     map_smul' := by
       intro z v
       apply lp.ext
       funext M
       by_cases hr : r ≤ M <;>
         simp only [complexShellShiftVector_apply, complexShellShiftFn, hr, if_true, if_false,
           lp.coeFn_smul, Pi.smul_apply, RingHom.id_apply, smul_zero] } :
      PronicCoordinateSpace →ₗ[ℂ] PronicCoordinateSpace).mkContinuous 1 (by
        intro v
        change ‖complexShellShiftVector r v‖ ≤ 1 * ‖v‖
        rw [one_mul, norm_complexShellShiftVector])

theorem complexShellShift_apply (r : ℕ) (v : PronicCoordinateSpace) (M : ℕ) :
    complexShellShift r v M = if r ≤ M then v (M - r) else 0 := rfl

theorem norm_complexShellShift_apply (r : ℕ) (v : PronicCoordinateSpace) :
    ‖complexShellShift r v‖ = ‖v‖ := norm_complexShellShiftVector r v

theorem norm_complexShellShift_le (r : ℕ) : ‖complexShellShift r‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  rw [norm_complexShellShift_apply, one_mul]

/-- The shifts form the additive semigroup of the intrinsic norm lattice. -/
theorem complexShellShift_comp (r s : ℕ) :
    (complexShellShift r).comp (complexShellShift s) = complexShellShift (r + s) := by
  ext v M
  simp only [ContinuousLinearMap.comp_apply, complexShellShift_apply]
  by_cases hr : r ≤ M
  · rw [if_pos hr]
    by_cases hs : s ≤ M - r
    · rw [if_pos hs, if_pos (by omega : r + s ≤ M)]
      exact congrArg (fun n => v n) (by omega : M - r - s = M - (r + s))
    · rw [if_neg hs, if_neg (by omega : ¬r + s ≤ M)]
  · rw [if_neg hr, if_neg (by omega : ¬r + s ≤ M)]

theorem complexShellShift_zero : complexShellShift 0 = ContinuousLinearMap.id ℂ _ := by
  ext v M
  simp only [complexShellShift_apply, Nat.zero_le, if_true, Nat.sub_zero,
    ContinuousLinearMap.id_apply]

end GaloisForLFunctions.BiarithmeticGeometry

