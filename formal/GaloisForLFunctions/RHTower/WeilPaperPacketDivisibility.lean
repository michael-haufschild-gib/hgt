import GaloisForLFunctions.RHTower.WeilPaperPacketArchEnergy

/-!
# One covariance gap controls Weil packet energy and integer constraints

The positive-block identity used in the Crouzeix proof controls every multiplicative
matrix diagonal of the actual PBAP packet construction. The same gap simultaneously
bounds the full pole-plus-archimedean energy change and any finite weighted family of
integer-null defects. No rank, positivity, or nonzero-gap assumption is required.
-/

open Matrix GaloisForLFunctions.HTGeometry
open scoped BigOperators ComplexConjugate Matrix

noncomputable section

namespace RHTower.WeilWorkPBAP

/-- The matrix mask selecting the exact integer logarithm constraint. -/
def packetDivisibilityKernel (N n : ℕ) : Matrix (PacketIndex N) (PacketIndex N) ℂ :=
  fun m k => if n * (k : ℕ) = (m : ℕ) then 1 else 0

/-- Number of entries participating in one multiplicative diagonal, as a real number. -/
def packetDivisibilityMass (N n : ℕ) : ℝ :=
  ∑ m : PacketIndex N, ∑ k : PacketIndex N,
    if n * (k : ℕ) = (m : ℕ) then 1 else 0

theorem packetDivisibilityMass_nonneg (N n : ℕ) : 0 ≤ packetDivisibilityMass N n := by
  unfold packetDivisibilityMass
  positivity

theorem packetDivisibilityKernel_energy (N n : ℕ) :
    finiteMatrixHilbertSchmidtSq (packetDivisibilityKernel N n) =
      packetDivisibilityMass N n := by
  rw [finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, packetDivisibilityMass]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  simp only [packetDivisibilityKernel]
  split_ifs <;> simp


private theorem packetDivisibilityMass_column (N n : ℕ) (k : PacketIndex N) :
    (∑ m : PacketIndex N, if n * (k : ℕ) = (m : ℕ) then (1 : ℝ) else 0) =
      if n * (k : ℕ) ∈ Finset.Icc 1 N then 1 else 0 := by
  by_cases hk : n * (k : ℕ) ∈ Finset.Icc 1 N
  · rw [if_pos hk]
    let j : PacketIndex N := ⟨n * (k : ℕ), hk⟩
    have heq (m : PacketIndex N) : n * (k : ℕ) = (m : ℕ) ↔ m = j := by
      constructor
      · intro h
        exact Subtype.ext h.symm
      · intro h
        exact congrArg Subtype.val h.symm
    simp_rw [heq]
    simp
  · rw [if_neg hk]
    apply Finset.sum_eq_zero
    intro m _
    apply if_neg
    intro h
    apply hk
    simpa only [h] using m.property

/-- One column contributes at most one entry to an integer multiplicative diagonal. -/
theorem packetDivisibilityMass_le (N n : ℕ) : packetDivisibilityMass N n ≤ N := by
  rw [packetDivisibilityMass, Finset.sum_comm]
  simp_rw [packetDivisibilityMass_column]
  calc
    _ ≤ ∑ _k : PacketIndex N, (1 : ℝ) := Finset.sum_le_sum fun k _ => by
      split_ifs <;> norm_num
    _ = N := by simp [PacketIndex]

/-- No arithmetic perturbation is hidden above the packet label cutoff. -/
theorem packetDivisibilityMass_eq_zero_above {N n : ℕ} (hn : N < n) :
    packetDivisibilityMass N n = 0 := by
  unfold packetDivisibilityMass
  apply Finset.sum_eq_zero
  intro m _
  apply Finset.sum_eq_zero
  intro k _
  have hmN := (Finset.mem_Icc.mp m.property).2
  have hk1 := (Finset.mem_Icc.mp k.property).1
  apply if_neg
  intro h
  nlinarith

theorem divisibilityTrace_sub {N : ℕ}
    (C D : Matrix (PacketIndex N) (PacketIndex N) ℂ) (n : ℕ) :
    divisibilityTrace (C - D) n = divisibilityTrace C n - divisibilityTrace D n := by
  simp only [divisibilityTrace, Matrix.sub_apply, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> simp

private theorem divisibilityTrace_eq_pairing {N : ℕ}
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (n : ℕ) :
    divisibilityTrace C n = ∑ m, ∑ k, C m k * packetDivisibilityKernel N n m k := by
  simp [divisibilityTrace, packetDivisibilityKernel, mul_ite]

/-- The precise size of the multiplicative diagonal pays for its trace. -/
theorem divisibilityTrace_norm_sq_le {N : ℕ}
    (C : Matrix (PacketIndex N) (PacketIndex N) ℂ) (n : ℕ) :
    ‖divisibilityTrace C n‖ ^ 2 ≤
      finiteMatrixHilbertSchmidtSq C * packetDivisibilityMass N n := by
  have hn : ‖divisibilityTrace C n‖ ≤
      ∑ m, ∑ k, ‖C m k‖ * ‖packetDivisibilityKernel N n m k‖ := by
    rw [divisibilityTrace_eq_pairing]
    calc
      _ ≤ ∑ m, ‖∑ k, C m k * packetDivisibilityKernel N n m k‖ := norm_sum_le _ _
      _ ≤ _ := Finset.sum_le_sum fun m _ => by simpa only [norm_mul] using
        (norm_sum_le (s := Finset.univ) (fun k => C m k * packetDivisibilityKernel N n m k))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product (Finset.univ : Finset (PacketIndex N)))
    (fun p => ‖C p.1 p.2‖) (fun p => ‖packetDivisibilityKernel N n p.1 p.2‖)
  rw [← packetDivisibilityKernel_energy,
    finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq, finiteMatrixHilbertSchmidtSq_eq_sum_norm_sq]
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans
    (by simpa only [Finset.product_eq_sprod, Finset.sum_product] using hcs)

/-- Integer constraints inherit the source Crouzeix covariance bound. -/
theorem divisibilityTrace_sub_norm_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ) (n : ℕ) :
    ‖divisibilityTrace (A * Aᴴ) n - divisibilityTrace (B * Bᴴ) n‖ ^ 2 ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) * packetDivisibilityMass N n := by
  rw [← divisibilityTrace_sub, crouzeix_gram_energy_identity]
  exact divisibilityTrace_norm_sq_le _ n

/-- Any finite weighted set of integer constraints is controlled without a rank assumption. -/
theorem divisibilityTrace_weighted_sub_sq_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (s : Finset ℕ) (w : ℕ → ℝ) :
    (∑ n ∈ s, w n ^ 2 *
      ‖divisibilityTrace (A * Aᴴ) n - divisibilityTrace (B * Bᴴ) n‖ ^ 2) ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          ∑ n ∈ s, w n ^ 2 * packetDivisibilityMass N n := by
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n _
  convert mul_le_mul_of_nonneg_left
    (divisibilityTrace_sub_norm_sq_le_crouzeix A B n) (sq_nonneg (w n)) using 1
  ring

/-- One covariance gap controls both the full archimedean energy and the arithmetic defects. -/
theorem packet_energy_and_integer_defects_le_crouzeix {N : ℕ} {ι κ : Type*}
    [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (L : ℕ) (A : Matrix (PacketIndex N) ι ℂ) (B : Matrix (PacketIndex N) κ ℂ)
    (s : Finset ℕ) (w : ℕ → ℝ) :
    (packetArchEnergy L A - packetArchEnergy L B) ^ 2 +
      (∑ n ∈ s, w n ^ 2 *
        ‖divisibilityTrace (A * Aᴴ) n - divisibilityTrace (B * Bᴴ) n‖ ^ 2) ≤
      (finiteMatrixHilbertSchmidtSq (Aᴴ * A) + finiteMatrixHilbertSchmidtSq (Bᴴ * B) -
        2 * finiteMatrixHilbertSchmidtSq (Aᴴ * B)) *
          (finiteMatrixHilbertSchmidtSq (packetArchKernel N L) +
            ∑ n ∈ s, w n ^ 2 * packetDivisibilityMass N n) := by
  rw [mul_add]
  exact add_le_add (packetArchEnergy_sub_sq_le_crouzeix L A B)
    (divisibilityTrace_weighted_sub_sq_le_crouzeix A B s w)

end RHTower.WeilWorkPBAP
