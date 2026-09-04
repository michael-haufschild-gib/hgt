import GaloisForLFunctions.RHTower.PrimeDepthAliasingModularEscape
import GaloisForLFunctions.RHTower.PrimeBurnolThetaModularHolonomy

open Complex Matrix

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

def primeBurnolThetaTwoThreeMismatch (a : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  (1 : Matrix (Fin 2) (Fin 2) ℂ) -
    _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
      _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩

theorem primeBurnolThetaTwoThreeMismatch_ne_zero
    {a : ℝ} (ha : a ≠ 0) : primeBurnolThetaTwoThreeMismatch a ≠ 0 := by
  intro hzero
  have hprod :
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩ = 1 := by
    rw [primeBurnolThetaTwoThreeMismatch] at hzero
    exact (sub_eq_zero.mp hzero).symm
  have hQeqP :
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ =
        _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
    calc
      _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ =
          _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ * 1 := by simp
      _ = _root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          (_root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩ *
            _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩) := by
          rw [_root_.RHTower.primeBurnolThetaBlock_neg_mul]
      _ = (_root_.RHTower.primeBurnolThetaBlock a ⟨3, Nat.prime_three⟩ *
          _root_.RHTower.primeBurnolThetaBlock (-a) ⟨2, Nat.prime_two⟩) *
            _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
              rw [Matrix.mul_assoc]
      _ = _root_.RHTower.primeBurnolThetaBlock a ⟨2, Nat.prime_two⟩ := by
        rw [hprod, Matrix.one_mul]
  have hentry := congrArg (fun M => M (1 : Fin 2) (0 : Fin 2)) hQeqP
  simp [_root_.RHTower.primeBurnolThetaBlock] at hentry
  have hpq : (⟨3, Nat.prime_three⟩ : Nat.Primes) ≠ ⟨2, Nat.prime_two⟩ := by
    intro h
    have hv := congrArg Subtype.val h
    norm_num at hv
  exact (_root_.RHTower.primeBurnolThetaContrast_ne_of_prime_ne ha hpq) hentry

theorem exists_primeBurnolThetaTwoThreeMismatch_entry_ne_zero
    {a : ℝ} (ha : a ≠ 0) :
    ∃ r s : Fin 2, primeBurnolThetaTwoThreeMismatch a r s ≠ 0 := by
  by_contra h
  push_neg at h
  apply primeBurnolThetaTwoThreeMismatch_ne_zero ha
  ext r s
  exact h r s

theorem exists_two_three_thetaModularEscapeCoefficient_gt
    {a M : ℝ} (ha : a ≠ 0) (hM : 0 ≤ M) :
    ∃ m n : ℕ, 0 < m ∧ 0 < n ∧
      ∃ r s : Fin 2,
        M < ‖(((64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3 /
          ((((m : ℝ) * Real.log 2) + ((n : ℝ) * Real.log 3)) ^ 6 -
            64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3) : ℝ) : ℂ) •
              primeBurnolThetaTwoThreeMismatch a) r s‖ := by
  obtain ⟨r, s, hrs⟩ := exists_primeBurnolThetaTwoThreeMismatch_entry_ne_zero ha
  have hnorm : 0 < ‖primeBurnolThetaTwoThreeMismatch a r s‖ := norm_pos_iff.mpr hrs
  let B := M / ‖primeBurnolThetaTwoThreeMismatch a r s‖
  have hB : 0 ≤ B := div_nonneg hM hnorm.le
  obtain ⟨m, n, hm, hn, hcap⟩ :=
    exists_two_three_primeDepth_cubicCauchyCapacity_gt hB
  let cap : ℝ :=
    64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3 /
      ((((m : ℝ) * Real.log 2) + ((n : ℝ) * Real.log 3)) ^ 6 -
        64 * ((m : ℝ) * Real.log 2) ^ 3 * ((n : ℝ) * Real.log 3) ^ 3)
  change B < cap at hcap
  have hcap0 : 0 < cap := lt_of_le_of_lt hB hcap
  have hmul : M < cap * ‖primeBurnolThetaTwoThreeMismatch a r s‖ := by
    apply (div_lt_iff₀ hnorm).mp
    exact hcap
  refine ⟨m, n, hm, hn, r, s, ?_⟩
  change M < ‖(cap : ℂ) * primeBurnolThetaTwoThreeMismatch a r s‖
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcap0]
  exact hmul

end

end GaloisForLFunctions.RHTower
