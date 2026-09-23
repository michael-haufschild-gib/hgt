import GaloisForLFunctions.RHTower.MobiusRenewalPacketEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

/-!
# Möbius packet block correlations

A dyadic block of literal packets is a signed arithmetic pair sum against an
explicit geometric kernel. The kernel identity identifies the off-diagonal
correlation that must be controlled to bound the full packet energy.
-/

open Finset
open scoped BigOperators

/-- Rearrange a finite square sum into its pair-correlation matrix. -/
private theorem packet_square_swap {R : Type*} [CommSemiring R]
    (B S : Finset ℕ) (f : ℕ → ℕ → R) :
    (∑ k ∈ B, (∑ n ∈ S, f n k) ^ (2 : ℕ)) =
      ∑ m ∈ S, ∑ n ∈ S, ∑ k ∈ B, f m k * f n k := by
  calc
    (∑ k ∈ B, (∑ n ∈ S, f n k) ^ (2 : ℕ)) =
      ∑ k ∈ B, ∑ m ∈ S, ∑ n ∈ S, f m k * f n k := by
        apply Finset.sum_congr rfl
        intro k _
        rw [pow_two, Finset.sum_mul_sum]
    _ = ∑ m ∈ S, ∑ n ∈ S, ∑ k ∈ B, f m k * f n k := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro m _
        rw [Finset.sum_comm]

namespace RHTower.MobiusRenewalPacketCorrelation

noncomputable section

/-- Geometric window kernel for packet indices `K ≤ k < 2K`. -/
def blockKernel (r : ℝ) (K m n : ℕ) : ℝ :=
  MobiusPacketDifference.weight r m * MobiusPacketDifference.weight r n *
    ∑ k ∈ Ico K (2 * K),
      (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ k

/-- Exact quadratic-form identity for a finite arithmetic source. -/
theorem packetBlockEnergy_eq_pairCorrelation
    (a : ℕ → ℝ) (N K : ℕ) (r : ℝ) :
    (∑ k ∈ Ico K (2 * K),
      (MobiusRenewalPacketEnergy.sourcePacket a N r k) ^ (2 : ℕ)) =
    ∑ m ∈ range N, ∑ n ∈ range N,
      a m * a n * blockKernel r K m n := by
  let B : Finset ℕ := Ico K (2 * K)
  let S : Finset ℕ := range N
  let f : ℕ → ℕ → ℝ := fun n k =>
    a n * MobiusPacketDifference.weight r n * MobiusPacketDifference.node n ^ k
  change (∑ k ∈ B, (∑ n ∈ S, f n k) ^ (2 : ℕ)) =
    ∑ m ∈ S, ∑ n ∈ S, a m * a n * blockKernel r K m n
  rw [packet_square_swap B S f]
  apply Finset.sum_congr rfl
  intro m _
  apply Finset.sum_congr rfl
  intro n _
  rw [blockKernel, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  dsimp [f]
  rw [mul_pow]
  ring

end
end RHTower.MobiusRenewalPacketCorrelation

namespace RHTower.MobiusRenewalPacketCorrelation

private theorem node_nonneg (n : ℕ) :
    0 ≤ MobiusPacketDifference.node n := by
  unfold MobiusPacketDifference.node
  positivity

private theorem node_lt_one (n : ℕ) :
    MobiusPacketDifference.node n < 1 := by
  unfold MobiusPacketDifference.node
  apply (div_lt_one (by positivity : (0 : ℝ) < (n : ℝ) + 2)).2
  linarith

private theorem node_mul_lt_one (m n : ℕ) :
    MobiusPacketDifference.node m * MobiusPacketDifference.node n < 1 := by
  calc
    MobiusPacketDifference.node m * MobiusPacketDifference.node n ≤
      1 * MobiusPacketDifference.node n :=
        mul_le_mul_of_nonneg_right (node_lt_one m).le (node_nonneg n)
    _ = MobiusPacketDifference.node n := one_mul _
    _ < 1 := node_lt_one n

/-- The packet window is a finite geometric series at each pair of source atoms. -/
theorem blockKernel_eq_geometric (r : ℝ) (K m n : ℕ) :
    blockKernel r K m n =
      MobiusPacketDifference.weight r m * MobiusPacketDifference.weight r n *
        ((MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ K *
          (1 - (MobiusPacketDifference.node m * MobiusPacketDifference.node n) ^ K) /
          (1 - MobiusPacketDifference.node m * MobiusPacketDifference.node n)) := by
  let q := MobiusPacketDifference.node m * MobiusPacketDifference.node n
  have hq : q ≠ 1 := (node_mul_lt_one m n).ne
  unfold blockKernel
  rw [Finset.sum_Ico_eq_sum_range]
  have hK : 2 * K - K = K := by omega
  rw [hK]
  have hsum : (∑ j ∈ Finset.range K, q ^ (K + j)) = q ^ K * ∑ j ∈ Finset.range K, q ^ j := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [pow_add]
  change _ * (∑ j ∈ Finset.range K, q ^ (K + j)) = _
  rw [hsum, geom_sum_eq hq]
  have hfrac : (q ^ K - 1) / (q - 1) = (1 - q ^ K) / (1 - q) := by
    have hq' : q - 1 ≠ 0 := sub_ne_zero.mpr hq
    field_simp
    ring
  rw [hfrac]
  ring

end RHTower.MobiusRenewalPacketCorrelation

namespace RHTower.MobiusRenewalPacketCorrelation

/-- The actual finite Möbius packet energy is this kernel applied to the literal coefficients. -/
theorem finiteMobiusPacketBlockEnergy_eq_pairCorrelation (N K : ℕ) (r : ℝ) :
    (∑ k ∈ Finset.Ico K (2 * K),
      (MobiusPacketDifference.packet N r k) ^ (2 : ℕ)) =
    ∑ m ∈ Finset.range N, ∑ n ∈ Finset.range N,
      shiftedMobiusRealCoefficient m * shiftedMobiusRealCoefficient n *
        blockKernel r K m n := by
  simpa only [MobiusRenewalPacketEnergy.sourcePacket_eq_mobiusPacket] using
    packetBlockEnergy_eq_pairCorrelation shiftedMobiusRealCoefficient N K r

end RHTower.MobiusRenewalPacketCorrelation

namespace RHTower.MobiusRenewalPacketCorrelation

/-- A symmetric finite pair sum splits into its diagonal and twice one strict triangle. -/
private theorem sum_symmetric_pair_eq_diagonal_add_two_mul_offDiagonal
    (S : Finset ℕ) (f : ℕ × ℕ → ℝ)
    (hsymm : ∀ a ∈ S, ∀ b ∈ S, f (a, b) = f (b, a)) :
    (∑ a ∈ S, ∑ b ∈ S, f (a, b)) =
      (∑ ab ∈ (S.product S).filter (fun ab => ab.1 = ab.2), f ab) +
        2 * ∑ ab ∈ (S.product S).filter (fun ab => ab.1 < ab.2), f ab := by
  rw [← Finset.sum_product]
  let A := S.product S
  have hfirst := Finset.sum_filter_add_sum_filter_not A (fun ab => ab.1 < ab.2) f
  have hsecond := Finset.sum_filter_add_sum_filter_not
    (A.filter fun ab => ¬ ab.1 < ab.2) (fun ab => ab.1 = ab.2) f
  have hEq :
      (A.filter fun ab => ¬ ab.1 < ab.2).filter (fun ab => ab.1 = ab.2) =
        A.filter (fun ab => ab.1 = ab.2) := by
    ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, _⟩, heq⟩
      exact ⟨hA, heq⟩
    · rintro ⟨hA, heq⟩
      exact ⟨⟨hA, by omega⟩, heq⟩
  have hGt :
      (A.filter fun ab => ¬ ab.1 < ab.2).filter (fun ab => ¬ ab.1 = ab.2) =
        A.filter (fun ab => ab.2 < ab.1) := by
    ext ab
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hA, hnotLt⟩, hne⟩
      exact ⟨hA, by omega⟩
    · rintro ⟨hA, hgt⟩
      exact ⟨⟨hA, by omega⟩, by omega⟩
  rw [hEq, hGt] at hsecond
  have hpartition :
      ∑ ab ∈ A, f ab =
        (∑ ab ∈ A.filter (fun ab => ab.1 < ab.2), f ab) +
        (∑ ab ∈ A.filter (fun ab => ab.1 = ab.2), f ab) +
        (∑ ab ∈ A.filter (fun ab => ab.2 < ab.1), f ab) := by
    rw [← hfirst, ← hsecond]
    ring
  have hswap :
      (∑ ab ∈ A.filter (fun ab => ab.2 < ab.1), f ab) =
        ∑ ab ∈ A.filter (fun ab => ab.1 < ab.2), f ab := by
    apply Finset.sum_equiv (Equiv.prodComm ℕ ℕ)
    · rintro ⟨a, b⟩
      simp [A, and_comm]
    · rintro ⟨a, b⟩ hab
      have hab' : (a ∈ S ∧ b ∈ S) ∧ b < a := by
        simpa [A] using hab
      exact hsymm b hab'.1.2 a hab'.1.1 |>.symm
  change (∑ ab ∈ A, f ab) =
    (∑ ab ∈ A.filter (fun ab => ab.1 = ab.2), f ab) +
      2 * ∑ ab ∈ A.filter (fun ab => ab.1 < ab.2), f ab
  rw [hpartition, hswap]
  ring

/-- The geometric packet kernel is symmetric in its source atoms. -/
theorem blockKernel_symm (r : ℝ) (K m n : ℕ) :
    blockKernel r K m n = blockKernel r K n m := by
  unfold blockKernel
  rw [mul_comm (MobiusPacketDifference.node m) (MobiusPacketDifference.node n)]
  ring

/-- Diagonal squarefree mass in a finite Möbius packet block. -/
noncomputable def finiteDiagonal (N K : ℕ) (r : ℝ) : ℝ :=
  ∑ ab ∈ ((Finset.range N).product (Finset.range N)).filter (fun ab => ab.1 = ab.2),
    shiftedMobiusRealCoefficient ab.1 * shiftedMobiusRealCoefficient ab.2 *
      blockKernel r K ab.1 ab.2

/-- One strict half of the signed Möbius pair correlation. -/
noncomputable def finiteOffDiagonal (N K : ℕ) (r : ℝ) : ℝ :=
  ∑ ab ∈ ((Finset.range N).product (Finset.range N)).filter (fun ab => ab.1 < ab.2),
    shiftedMobiusRealCoefficient ab.1 * shiftedMobiusRealCoefficient ab.2 *
      blockKernel r K ab.1 ab.2

/-- Exact finite source identity: the unresolved energy lies in positive off-diagonal excursions. -/
theorem finiteMobiusPacketBlockEnergy_eq_diagonal_add_two_mul_offDiagonal
    (N K : ℕ) (r : ℝ) :
    (∑ k ∈ Finset.Ico K (2 * K),
      (MobiusPacketDifference.packet N r k) ^ (2 : ℕ)) =
    finiteDiagonal N K r + 2 * finiteOffDiagonal N K r := by
  rw [finiteMobiusPacketBlockEnergy_eq_pairCorrelation]
  unfold finiteDiagonal finiteOffDiagonal
  refine sum_symmetric_pair_eq_diagonal_add_two_mul_offDiagonal
    (Finset.range N)
    (fun ab => shiftedMobiusRealCoefficient ab.1 * shiftedMobiusRealCoefficient ab.2 *
      blockKernel r K ab.1 ab.2) ?_
  intro a _ b _
  rw [blockKernel_symm]
  ring

end RHTower.MobiusRenewalPacketCorrelation
