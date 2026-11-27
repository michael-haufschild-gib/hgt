import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.Physical.GaussianLoss
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.BlockMergers.BalancedMass
import Mathlib.Data.Nat.Log

/-! # Gaussian mass of exponentially separated physical spectra -/
open Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
noncomputable section

/-- A balanced binary split gives a register-wide gap of 1024⁻ᴷ at
probability cost exponential in K times its binary tree depth. -/
theorem hierarchical_gap_mass : ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
    let K := n+2
    exp (-C*(K:ℝ)*((Nat.clog 2 K:ℝ)+1)) ≤
      (standardLaw (PathLabel n)).real (gapEvent n (gapScale K)) := by
  obtain ⟨ρ,hρ,hrec⟩ := gaussian_merge_loss
  let base := min ρ (min (gapMass 0) (gapMass 1))
  have hbase_pos : 0 < base := lt_min hρ.1 (lt_min (seed_mass 0) (seed_mass 1))
  have hbase_le : base ≤ ρ := min_le_left ..
  have hbase_one := hbase_le.trans hρ.2
  let C := -log base
  have hC : 0 ≤ C := neg_nonneg.mpr (log_nonpos hbase_pos.le hbase_one)
  have hexp (m : ℕ) : exp (-C*(m:ℝ))=base^m := by
    rw [show -C=log base by exact neg_neg _,mul_comm,Real.exp_nat_mul,exp_log hbase_pos]
  let p (m : ℕ) := gapMass (m-2)
  have hp (m : ℕ) : 0 ≤ p m := measureReal_nonneg
  have hsmall (m : ℕ) (hm : 2 ≤ m) (hm' : m ≤ 3) : exp (-C*(m:ℝ)) ≤ p m := by
    rw [hexp]
    have h := (pow_le_pow_of_le_one hbase_pos.le hbase_one (by omega : 1 ≤ m)).trans_eq (pow_one _)
    have hbase : base ≤ min (gapMass 0) (gapMass 1) := min_le_right ..
    rcases (by omega : m=2 ∨ m=3) with rfl|rfl
    · exact h.trans (hbase.trans (min_le_left ..))
    · exact h.trans (hbase.trans (min_le_right ..))
  have hmerge (m : ℕ) (hm : 4 ≤ m) :
      exp (-C*(m:ℝ))*p (m/2)*p ((m+1)/2) ≤ p m := by
    let l := m/2-2
    let r := (m+1)/2-2
    have h := hrec l r (by dsimp only [l,r]; omega) (by dsimp only [l,r]; omega)
    rw [show l+r+4=m by dsimp only [l,r]; omega,
      show l+r+2=m-2 by dsimp only [l,r]; omega] at h
    rw [hexp]
    exact (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hbase_pos.le hbase_le m) (hp _)) (hp _)).trans h
  refine ⟨C,hC,fun n => ?_⟩
  exact balanced_mass p hp C hC hsmall hmerge (Nat.clog 2 (n+2)) (n+2) (by omega)
    (Nat.le_pow_clog (by decide) (n+2))

#print axioms hierarchical_gap_mass
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal.BlockMergers
