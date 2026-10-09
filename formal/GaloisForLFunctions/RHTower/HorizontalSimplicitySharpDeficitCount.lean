import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriMixedRangeSharp
import GaloisForLFunctions.RHTower.HorizontalSimplicityDeficitCount

/-!
# Absorbed block counts with the quadratic mixed gain

For the sampled Weil matrix of a zero block, a set `M ⊆ S₁` of simple on-line points with
absorbers `σ x` (a multiple on-line point or an off-line pair) and deficits `d_x` satisfying
`−d_x ≤ 1 + 2⟪f_x, g_{σ x}⟫²/‖g_{σ x}‖² − 2‖f_x‖²` gives, for every `b ≥ 0`,

`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + Σ_{x∈M} ((1 + b)d_x − b + b²)`

(`absorbed_block_count_add_sharp_deficit`). At `b = 0` this is `absorbed_block_count_add_deficit`.
For `b > 0` it spends the quadratic gain of the mixed range
(`HorizontalPacket.four_mass_sub_energy_le_sharp`). A mixed point with `d_x ≤ (b − b²)/(1 + b)`
then costs nothing; for `b = √2 − 1` this threshold is `d_x ≤ 3 − 2√2`.
-/

open scoped RealInnerProductSpace
open Finset

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (M : Finset ι)

/-- **Absorbed count with sharp deficits at the block level.** -/
theorem absorbed_block_count_add_sharp_deficit (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (σ : {z // z ∈ M} → ι) (hσ : ∀ x, σ x ∈ D.S₂ ∨ σ x ∈ Pr.R) (dfc : {z // z ∈ M} → ℝ)
    (hcost : ∀ x : {z // z ∈ M}, -dfc x ≤ 1 + 2 * ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2
        / ‖blockReVec D c (σ x)‖ ^ 2 - 2 * ‖blockReVec D c x‖ ^ 2) {b : ℝ} (hb : 0 ≤ b) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) + ∑ x, ((1 + b) * dfc x - b + b ^ 2) := by
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have hmem : ∀ x, blockReVec D c (σ x) ∈ Pk.absorbing := fun x => by
    rcases hσ x with h | h
    · exact Pk.f₂_mem_absorbing ⟨σ x, h⟩
    · exact Pk.g_mem_absorbing ⟨σ x, h⟩
  have hproj : ∀ x : {z // z ∈ M}, ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2
      / ‖blockReVec D c (σ x)‖ ^ 2 ≤ ‖Pk.absorbing.starProjection (Pk.fM x)‖ ^ 2 := by
    intro x
    have h := inner_sq_le_norm_sq_starProjection_mul (hmem x) (Pk.fM x)
    rcases (sq_nonneg ‖blockReVec D c (σ x)‖).lt_or_eq with hpos | hzero
    · rw [div_le_iff₀ hpos]; exact h
    · rw [← hzero, div_zero]; exact sq_nonneg _
  have h := HorizontalPacket.four_mass_sub_energy_le_add_sharp_deficit Pk
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    (fun x => norm_blockReVec_le_one D c hc (hPois x (hS1on x (hM x.2))))
    dfc (fun x => by
      have h1 := hcost x
      have h2 : ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2 / ‖blockReVec D c (σ x)‖ ^ 2
          ≤ ‖Pk.absorbing.starProjection (blockReVec D c x)‖ ^ 2 := hproj x
      show -dfc x ≤ 1 + 2 * ‖Pk.absorbing.starProjection (blockReVec D c x)‖ ^ 2
        - 2 * ‖blockReVec D c x‖ ^ 2
      rw [mul_div_assoc] at h1
      linarith) hb
  rw [Fintype.card_coe] at h
  exact h

end Block

end

end RHTower
