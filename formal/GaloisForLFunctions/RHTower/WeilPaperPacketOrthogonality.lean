import GaloisForLFunctions.RHTower.WeilPaperPacketDivisibility

/-!
# Disjoint integer masks sharpen positive packet correction costs

An entry on one integer multiplicative diagonal cannot belong to another.
Weighted absolute sums of all observed traces therefore cost one weighted mask
energy, without an extra factor counting the observations.
-/

open Matrix GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Absolute observation weights placed on their disjoint multiplicative diagonals. -/
def packetMaskWeight {N : ℕ} (s : Finset LogIndex) (w : LogIndex → ℝ)
    (m k : PacketIndex N) : ℝ :=
  ∑ j ∈ s, if (j : ℕ) * (k : ℕ) = (m : ℕ) then |w j| else 0

/-- Integer multiplicative masks have disjoint support. -/
theorem packetMaskWeight_sq {N : ℕ} (s : Finset LogIndex) (w : LogIndex → ℝ)
    (m k : PacketIndex N) :
    packetMaskWeight s w m k ^ 2 =
      ∑ j ∈ s, if (j : ℕ) * (k : ℕ) = (m : ℕ) then w j ^ 2 else 0 := by
  classical
  have hk : 0 < (k : ℕ) := (Finset.mem_Icc.mp k.property).1
  by_cases h : ∃ j ∈ s, (j : ℕ) * (k : ℕ) = (m : ℕ)
  · obtain ⟨j, hj, he⟩ := h
    have heq (i : LogIndex) : (i : ℕ) * (k : ℕ) = (m : ℕ) ↔ i = j := by
      constructor
      · intro hi
        exact Subtype.ext (Nat.mul_right_cancel hk (hi.trans he.symm))
      · rintro rfl
        exact he
    simp only [packetMaskWeight, heq]
    simp [hj]
  · have hz (j : LogIndex) (hj : j ∈ s) : (j : ℕ) * (k : ℕ) ≠ (m : ℕ) :=
      fun he => h ⟨j, hj, he⟩
    have hsum : packetMaskWeight s w m k = 0 :=
      Finset.sum_eq_zero fun j hj => if_neg (hz j hj)
    rw [hsum, zero_pow (Nat.succ_ne_zero 1)]
    exact (Finset.sum_eq_zero fun j hj => if_neg (hz j hj)).symm

/-- Exact energy of the combined mask; no cross terms survive. -/
theorem packetMaskWeight_energy {N : ℕ} (s : Finset LogIndex) (w : LogIndex → ℝ) :
    (∑ m : PacketIndex N, ∑ k : PacketIndex N, packetMaskWeight s w m k ^ 2) =
      ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by
  simp_rw [packetMaskWeight_sq]
  calc
    _ = ∑ m : PacketIndex N, ∑ j ∈ s, ∑ k : PacketIndex N,
        if (j : ℕ) * (k : ℕ) = (m : ℕ) then w j ^ 2 else 0 :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ j ∈ s, ∑ m : PacketIndex N, ∑ k : PacketIndex N,
        if (j : ℕ) * (k : ℕ) = (m : ℕ) then w j ^ 2 else 0 := Finset.sum_comm
    _ = _ := by simp only [packetDivisibilityMass, Finset.mul_sum, mul_ite, mul_one, mul_zero]

private theorem divisibilityTrace_norm_le {N : ℕ}
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (j : LogIndex) :
    ‖divisibilityTrace C j‖ ≤ ∑ m : PacketIndex N, ∑ k : PacketIndex N,
      if (j : ℕ) * (k : ℕ) = (m : ℕ) then ‖C m k‖ else 0 := by
  unfold divisibilityTrace
  calc
    _ ≤ ∑ m : PacketIndex N,
        ‖∑ k : PacketIndex N, if (j : ℕ) * (k : ℕ) = (m : ℕ) then C m k else 0‖ :=
      norm_sum_le _ _
    _ ≤ ∑ m : PacketIndex N, ∑ k : PacketIndex N,
        ‖if (j : ℕ) * (k : ℕ) = (m : ℕ) then C m k else 0‖ :=
      Finset.sum_le_sum fun _ _ => norm_sum_le _ _
    _ = _ := by simp only [apply_ite, norm_zero]

/-- Simultaneous absolute trace control uses disjoint mask energy, not the number of masks. -/
theorem divisibilityTrace_weighted_abs_sum_sq_le {N : ℕ}
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ)
    (s : Finset LogIndex) (w : LogIndex → ℝ) :
    (∑ j ∈ s, |w j| * ‖divisibilityTrace C j‖) ^ 2 ≤
      finiteMatrixHilbertSchmidtSq C * ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by
  have hbound : (∑ j ∈ s, |w j| * ‖divisibilityTrace C j‖) ≤
      ∑ m : PacketIndex N, ∑ k : PacketIndex N, ‖C m k‖ * packetMaskWeight s w m k := by
    calc
      _ ≤ ∑ j ∈ s, |w j| * ∑ m : PacketIndex N, ∑ k : PacketIndex N,
          if (j : ℕ) * (k : ℕ) = (m : ℕ) then ‖C m k‖ else 0 :=
        Finset.sum_le_sum fun j _ =>
          mul_le_mul_of_nonneg_left (divisibilityTrace_norm_le C j) (abs_nonneg _)
      _ = ∑ m : PacketIndex N, ∑ j ∈ s, ∑ k : PacketIndex N,
          if (j : ℕ) * (k : ℕ) = (m : ℕ) then |w j| * ‖C m k‖ else 0 := by
        simp only [Finset.mul_sum, mul_ite, mul_zero]
        exact Finset.sum_comm
      _ = ∑ m : PacketIndex N, ∑ k : PacketIndex N, ∑ j ∈ s,
          if (j : ℕ) * (k : ℕ) = (m : ℕ) then |w j| * ‖C m k‖ else 0 :=
        Finset.sum_congr rfl fun _ _ => Finset.sum_comm
      _ = _ := by simp only [packetMaskWeight, Finset.mul_sum, mul_ite, mul_zero, mul_comm]
  have h0 : 0 ≤ ∑ j ∈ s, |w j| * ‖divisibilityTrace C j‖ :=
    Finset.sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (norm_nonneg _)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product (Finset.univ : Finset (PacketIndex N)))
    (fun p => ‖C p.1 p.2‖) (fun p => packetMaskWeight s w p.1 p.2)
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, ← packetMaskWeight_energy s w]
  exact (pow_le_pow_left₀ h0 hbound 2).trans
    (by simpa only [Finset.product_eq_sprod, Finset.sum_product] using hcs)

/-- A single Crouzeix covariance gap controls the weighted absolute total of all chosen defects. -/
theorem divisibilityTrace_weighted_abs_sub_sum_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (s : Finset LogIndex) (w : LogIndex → ℝ) :
    (∑ j ∈ s, |w j| * ‖divisibilityTrace (A * Aᴴ) j - divisibilityTrace (B * Bᴴ) j‖) ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          ∑ j ∈ s, w j ^ 2 * packetDivisibilityMass N j := by
  simp_rw [← divisibilityTrace_sub, crouzeix_gram_energy_identity]
  exact divisibilityTrace_weighted_abs_sum_sq_le _ s w

end RHTower.WeilWorkPBAP
