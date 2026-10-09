import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriSpectral
import GaloisForLFunctions.RHTower.HorizontalIsolationBlockPacket

/-!
# The pair-field count for sampled Weil matrices

For Zeta23's block data the normalised zero-side matrix is the kernel of the horizontal packet
`blockPacket` (`blockP_add_blockQ_eq_kernel`).  The spectral horizontal Lamzouri inequality
(`HorizontalPacket.four_mass_sub_energy_le_of_pairField`) then removes from Zeta23's count every
simple critical zero `x` whose pair field

`G(f_x) = Σ_p 2m_p (⟪Re u_p, f_x⟫² − ⟪Im u_p, f_x⟫²)/c`,

taken over the off-line pair representatives `p` of the block, is at least `‖f_x‖² − 1/2`:
`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M)` (`pairField_block_count`).  No overlap or displacement condition
on the own pair of `x` enters; only the field of all pairs at `f_x` does.
-/

open scoped RealInnerProductSpace

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

section Block

set_option linter.unusedSectionVars false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (M : Finset ι)

/-- **Pair-field count at the block level.**  If every simple critical zero in `M ⊆ S₁` has pair
field at least `‖f_x‖² − 1/2`, then `4 tr − ‖·‖² − 2N ≤ #(S₁ \ M)` for the normalised block matrix. -/
theorem pairField_block_count (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (hG : ∀ x : {z // z ∈ M}, ‖blockReVec D c x‖ ^ 2 - 1 / 2 ≤
      (blockPacket D Pr c M).pairField (blockReVec D c x)) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) := by
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have h := Pk.four_mass_sub_energy_le_of_pairField
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    hG
  rw [Fintype.card_coe] at h
  exact h

end Block

end

end RHTower
