import GaloisForLFunctions.BiScaleUncertainty.PhysicalAffineAction

/-!
# Exact finite alternating physical packets

Signed sums of actual orthonormal unit cells have explicit translation
energy. Their two boundary cells give the exact deficit two, at every length.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false

theorem ae_unitCell_indicator (k : ℕ) :
    unitCell k =ᵐ[volume] (Ioc (k : ℝ) (k+1)).indicator (fun _ => (1 : ℝ)) :=
  indicatorConstLp_coeFn

theorem physicalTranslation_neg_one_unitCell (k : ℕ) :
    physicalTranslation (-1) (unitCell k) = unitCell (k+1) := by
  apply Lp.ext
  filter_upwards [ae_physicalTranslation (-1) (unitCell k),
    ae_physicalTranslate_pullback (-1) (ae_unitCell_indicator k),
    ae_unitCell_indicator (k+1)] with t ht hm hr
  rw [ht, hm, hr]
  have he : t+(-1) ∈ Ioc (k : ℝ) (k+1) ↔
      t ∈ Ioc ((k+1 : ℕ) : ℝ) (((k+1 : ℕ) : ℝ)+1) := by
    simp only [mem_Ioc, Nat.cast_add, Nat.cast_one]
    constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith only [h1, h2]
  simp only [Set.indicator_apply, he]

def alternatingCellPacket (N : ℕ) : Velocity :=
  ∑ j ∈ Finset.range N, ((-1 : ℝ)^j) • unitCell j

theorem inner_unitCell_alternatingCellPacket (k N : ℕ) :
    ⟪unitCell k, alternatingCellPacket N⟫ = if k < N then (-1 : ℝ)^k else 0 := by
  classical
  simp only [alternatingCellPacket, inner_sum, real_inner_smul_right, inner_unitCell,
    mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  simp only [Finset.mem_range]

theorem alternatingCellPacket_energy (N : ℕ) : ‖alternatingCellPacket N‖^2 = (N : ℝ) := by
  calc
    _ = ∑ j ∈ Finset.range N, ((-1 : ℝ)^j)*⟪unitCell j, alternatingCellPacket N⟫ := by
      rw [← real_inner_self_eq_norm_sq]
      simp only [alternatingCellPacket, sum_inner, real_inner_smul_left]
    _ = ∑ _j ∈ Finset.range N, (1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [inner_unitCell_alternatingCellPacket, if_pos (Finset.mem_range.mp hj), ← mul_pow]
      norm_num
    _ = _ := by simp

theorem alternatingCellPacket_shift_inner (n : ℕ) :
    ⟪physicalTranslation (-1) (alternatingCellPacket (n+1)), alternatingCellPacket (n+1)⟫ =
      -(n : ℝ) := by
  have ht : physicalTranslation (-1) (alternatingCellPacket (n+1)) =
      ∑ j ∈ Finset.range (n+1), ((-1 : ℝ)^j) • unitCell (j+1) := by
    simp only [alternatingCellPacket, map_sum, map_smul, physicalTranslation_neg_one_unitCell]
  rw [ht, sum_inner]
  simp only [real_inner_smul_left, inner_unitCell_alternatingCellPacket]
  rw [Finset.sum_range_succ]
  simp only [lt_self_iff_false, if_false, mul_zero, add_zero]
  calc
    _ = ∑ _j ∈ Finset.range n, (-1 : ℝ) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [if_pos (Nat.succ_lt_succ (Finset.mem_range.mp hj)), pow_succ]
      calc
        _ = -(((-1 : ℝ)^j)*((-1 : ℝ)^j)) := by ring
        _ = -1 := by rw [← mul_pow]; norm_num
    _ = _ := by simp

theorem alternatingCellPacket_neg_shift_energy (n : ℕ) :
    ‖physicalTranslation (-1) (alternatingCellPacket (n+1))-alternatingCellPacket (n+1)‖^2 =
      4*((n : ℝ)+1)-2 := by
  rw [norm_sub_sq_real, physicalTranslation_norm, alternatingCellPacket_energy,
    alternatingCellPacket_shift_inner]
  push_cast
  ring

theorem alternatingCellPacket_shift_energy (n : ℕ) :
    ‖physicalTranslation 1 (alternatingCellPacket (n+1))-alternatingCellPacket (n+1)‖^2 =
      4*((n : ℝ)+1)-2 := by
  have h := (physicalTranslation 1).norm_map
    (physicalTranslation (-1) (alternatingCellPacket (n+1))-alternatingCellPacket (n+1))
  rw [map_sub, physicalTranslation_comp, add_neg_cancel, physicalTranslation_zero, norm_sub_rev] at h
  rw [h, alternatingCellPacket_neg_shift_energy]

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
