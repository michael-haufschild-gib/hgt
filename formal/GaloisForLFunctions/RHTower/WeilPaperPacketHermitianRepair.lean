import GaloisForLFunctions.RHTower.WeilPaperPacketRepair

/-!
# Hermitian covariance halves integer-repair costs

Integer logarithmic constraints read only strict multiplicative lower diagonals.
The selected covariance entries and their transposes are disjoint. Hermitian
symmetry therefore pays for their squared norm twice in the Crouzeix gap.
-/

open Matrix Complex GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Keep exactly the matrix entries observed by the selected integer constraints. -/
def packetMaskProjection {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    Matrix (PacketIndex N) (PacketIndex N) ℂ := fun m k =>
  if ∃ j ∈ s, (j : ℕ) * (k : ℕ) = (m : ℕ) then C m k else 0

private theorem packetMask_selected_lt {N : ℕ} (s : Finset LogIndex)
    (m k : PacketIndex N) (h : ∃ j ∈ s, (j : ℕ) * (k : ℕ) = (m : ℕ)) :
    (k : ℕ) < (m : ℕ) := by
  obtain ⟨j, _, h⟩ := h
  have hk := (Finset.mem_Icc.mp k.property).1
  have hm : 2 * (k : ℕ) ≤ (m : ℕ) := by
    rw [← h]
    exact Nat.mul_le_mul_right _ j.property
  omega

/-- Every selected integer constraint sees exactly the original matrix. -/
theorem divisibilityTrace_packetMaskProjection {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (j : LogIndex) (hj : j ∈ s) :
    divisibilityTrace (packetMaskProjection s C) j = divisibilityTrace C j := by
  classical
  unfold divisibilityTrace
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : (j : ℕ) * (k : ℕ) = (m : ℕ)
  · have hs : ∃ j ∈ s, (j : ℕ) * (k : ℕ) = (m : ℕ) := ⟨j, hj, h⟩
    simp only [if_pos h, packetMaskProjection, if_pos hs]
  · simp only [if_neg h]

/-- Integer masks vanish on and above the main diagonal. -/
theorem packetMaskProjection_eq_zero_of_le {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (m k : PacketIndex N)
    (hmk : (m : ℕ) ≤ (k : ℕ)) : packetMaskProjection s C m k = 0 := by
  classical
  unfold packetMaskProjection
  apply if_neg
  intro h
  have hlt := packetMask_selected_lt s m k h
  omega

private theorem packetMaskProjection_entry_sq_le {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (m k : PacketIndex N) :
    ‖packetMaskProjection s C m k‖ ^ 2 ≤ ‖C m k‖ ^ 2 := by
  classical
  unfold packetMaskProjection
  split_ifs
  · exact le_rfl
  · simp

/-- Projection to observed integer entries never increases covariance energy. -/
theorem packetMaskProjection_energy_le {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) :
    finiteMatrixHilbertSchmidtSq (packetMaskProjection s C) ≤ finiteMatrixHilbertSchmidtSq C := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  exact Finset.sum_le_sum fun m _ =>
    Finset.sum_le_sum fun k _ => packetMaskProjection_entry_sq_le s C m k

/-- A Hermitian matrix spends at least twice the energy visible to integer constraints. -/
theorem packetMaskProjection_twice_energy_le {N : ℕ} (s : Finset LogIndex)
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (hC : C.IsHermitian) :
    2 * finiteMatrixHilbertSchmidtSq (packetMaskProjection s C) ≤
      finiteMatrixHilbertSchmidtSq C := by
  have hentry (m k : PacketIndex N) :
      ‖packetMaskProjection s C m k‖ ^ 2 + ‖packetMaskProjection s C k m‖ ^ 2 ≤
        ‖C m k‖ ^ 2 := by
    have hnorm : ‖C k m‖ = ‖C m k‖ := by
      simpa using congrArg norm (hC.apply m k)
    by_cases hmk : (m : ℕ) ≤ (k : ℕ)
    · rw [packetMaskProjection_eq_zero_of_le s C m k hmk]
      simpa only [norm_zero, zero_pow (Nat.succ_ne_zero 1), zero_add, hnorm] using
        packetMaskProjection_entry_sq_le s C k m
    · have hkm : (k : ℕ) ≤ (m : ℕ) := by omega
      rw [packetMaskProjection_eq_zero_of_le s C k m hkm]
      simpa only [norm_zero, zero_pow (Nat.succ_ne_zero 1), add_zero] using
        packetMaskProjection_entry_sq_le s C m k
  have hsum : (∑ m : PacketIndex N, ∑ k : PacketIndex N,
      (‖packetMaskProjection s C m k‖ ^ 2 + ‖packetMaskProjection s C k m‖ ^ 2)) ≤
        ∑ m : PacketIndex N, ∑ k : PacketIndex N, ‖C m k‖ ^ 2 :=
    Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun k _ => hentry m k
  have hswap : (∑ m : PacketIndex N, ∑ k : PacketIndex N, ‖packetMaskProjection s C k m‖ ^ 2) =
      ∑ m : PacketIndex N, ∑ k : PacketIndex N, ‖packetMaskProjection s C m k‖ ^ 2 :=
    Finset.sum_comm
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  simpa only [Finset.sum_add_distrib, hswap, two_mul] using hsum

/-- Hermitian symmetry halves the simultaneous absolute observation bound. -/
theorem divisibilityTrace_weighted_abs_sum_twice_sq_le {N : ℕ}
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (hC : C.IsHermitian)
    (s : Finset LogIndex) (w : LogIndex → ℝ) :
    2 * (∑ j ∈ s, |w j| * ‖divisibilityTrace C j‖) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq C * ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by
  have h := divisibilityTrace_weighted_abs_sum_sq_le (packetMaskProjection s C) s w
  have heq : (∑ j ∈ s, |w j| * ‖divisibilityTrace (packetMaskProjection s C) j‖) =
      ∑ j ∈ s, |w j| * ‖divisibilityTrace C j‖ := by
    exact Finset.sum_congr rfl fun j hj => by rw [divisibilityTrace_packetMaskProjection s C j hj]
  rw [heq] at h
  have hS : 0 ≤ ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (sq_nonneg _) (packetDivisibilityMass_nonneg N j)
  calc
    _ ≤ 2 * (finiteMatrixHilbertSchmidtSq (packetMaskProjection s C) *
        ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j) := mul_le_mul_of_nonneg_left h (by positivity)
    _ = (2 * finiteMatrixHilbertSchmidtSq (packetMaskProjection s C)) *
        ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (packetMaskProjection_twice_energy_le s C hC) hS

/-- The actual Crouzeix covariance gap pays for integer observations with the improved factor. -/
theorem divisibilityTrace_weighted_abs_sub_sum_twice_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (s : Finset LogIndex) (w : LogIndex → ℝ) :
    2 * (∑ j ∈ s, |w j| * ‖divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j‖) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by
  simp_rw [← divisibilityTrace_sub, crouzeix_gram_energy_identity]
  exact divisibilityTrace_weighted_abs_sum_twice_sq_le _
    ((Matrix.isHermitian_mul_conjTranspose_self A).sub (Matrix.isHermitian_mul_conjTranspose_self B)) s w

/-- Positive repair pays at most half the general squared covariance budget. -/
theorem packetRepairBudget_twice_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    2 * repairBudget (defect (packetColumnMixture L B) - defect (packetColumnMixture L A)) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) * packetRepairSensitivity N L := by
  classical
  have hb0 : 0 ≤ repairBudget
      (defect (packetColumnMixture L B) - defect (packetColumnMixture L A)) := by
    exact Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (atomCost_nonneg j)
  have hsq := pow_le_pow_left₀ hb0 (packetRepairBudget_le_weighted_trace L A B) 2
  have hw (j : LogIndex) : |packetRepairWeight N L j| = packetRepairWeight N L j :=
    abs_of_nonneg (packetRepairWeight_nonneg N L j)
  calc
    _ ≤ 2 * (∑ j ∈ packetLogIndices N, packetRepairWeight N L j *
        ‖divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j‖) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ ≤ _ := by
      simpa only [hw, packetRepairSensitivity] using
        divisibilityTrace_weighted_abs_sub_sum_twice_sq_le_crouzeix A B
          (packetLogIndices N) (packetRepairWeight N L)

/-- Exact integer-defect transport inherits the halved squared energy cost. -/
theorem packetTransferRepair_energy_sub_twice_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    2 * (energy (packetTransferRepair L A B) - packetArchEnergy (L + 1) A) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) * packetRepairSensitivity N L := by
  have hsq := pow_le_pow_left₀ (abs_nonneg _) (abs_energy_repair_le
    (defect (packetColumnMixture L B) - defect (packetColumnMixture L A))) 2
  rw [sq_abs] at hsq
  rw [packetTransferRepair, map_add, energy_packetColumnMixture, add_sub_cancel_left]
  exact (mul_le_mul_of_nonneg_left hsq (by positivity)).trans
    (packetRepairBudget_twice_sq_le_crouzeix L A B)

/-- The target comparison pays the improved arithmetic cost alongside the analytic cost. -/
theorem packetTransferRepair_target_energy_sq_le_hermitian_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) :
    (energy (packetTransferRepair L A B) - packetArchEnergy (L + 1) B) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          (packetRepairSensitivity N L +
            2 * finiteMatrixHilbertSchmidtSq (packetArchKernel N (L + 1))) := by
  have h1 := packetTransferRepair_energy_sub_twice_sq_le_crouzeix L A B
  have h2 := packetArchEnergy_sub_sq_le_crouzeix (L + 1) A B
  have hs := sq_nonneg (energy (packetTransferRepair L A B) -
    2 * packetArchEnergy (L + 1) A + packetArchEnergy (L + 1) B)
  nlinarith

/-- The actual nonnegative integer-null repair satisfies the improved unconditional bound. -/
theorem nullRepair_packetColumnMixture_energy_sub_twice_sq_le {N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    2 * (energy (nullRepair (packetColumnMixture L A)) - packetArchEnergy (L + 1) A) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq (Aᴴ * A) * packetRepairSensitivity N L := by
  have hd0 : defect (packetColumnMixture L (0 : Matrix (PacketIndex N) ι ℂ)) = 0 := by
    ext j
    simp [defect_packetColumnMixture, divisibilityTrace]
  have hz : finiteMatrixHilbertSchmidtSq (0 : Matrix ι ι ℂ) = 0 := by
    simp [finiteMatrixHilbertSchmidtSq]
  have hb := packetRepairBudget_twice_sq_le_crouzeix L A (0 : Matrix (PacketIndex N) ι ℂ)
  simp only [hd0, zero_sub, Matrix.conjTranspose_zero, Matrix.mul_zero,
    hz, add_zero, mul_zero, sub_zero] at hb
  have h := pow_le_pow_left₀ (abs_nonneg _)
    (abs_energy_nullRepair_sub_le (packetColumnMixture L A)) 2
  rw [sq_abs, energy_packetColumnMixture] at h
  exact (mul_le_mul_of_nonneg_left h (by positivity)).trans hb

/-- Every packet family has a nonnegative, all-integer-null mixture with the smaller budget. -/
theorem exists_packet_integer_null_mixture_with_hermitian_energy_bound {N : ℕ} {ι : Type*}
    [Fintype ι] [DecidableEq ι] (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → c.sum (fun f t => t * logValue f.1 n) = 0) ∧
      2 * (energy c - packetArchEnergy (L + 1) A) ^ 2 ≤
        finiteMatrixHilbertSchmidtSq (Aᴴ * A) * packetRepairSensitivity N L := by
  exact ⟨nullRepair (packetColumnMixture L A),
    nullRepair_nonneg (packetColumnMixture_nonneg L A),
    logValue_nullRepair (packetColumnMixture L A),
    nullRepair_packetColumnMixture_energy_sub_twice_sq_le L A⟩

end RHTower.WeilWorkPBAP
