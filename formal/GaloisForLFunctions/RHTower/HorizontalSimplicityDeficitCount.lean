import GaloisForLFunctions.RHTower.HorizontalIsolationBlockPacket

/-!
# Horizontal counts with deficits for unabsorbed mixed points

The unnormalised horizontal Lamzouri inequality
`4·mass − E − 2N + 2 Σ_H (1 − ‖f‖²) + Σ_M (1 + 2‖P_A f‖² − 2‖f‖²) ≤ #H`
(`HorizontalPacket.four_mass_sub_energy_le`) keeps every mixed point. When a mixed point `x` is
only partly absorbed, its term is bounded below by `−d_x` for an explicit deficit `d_x ≥ 0`, and

`4·mass − E − 2N ≤ #H + Σ_{x ∈ M} d_x`   (`four_mass_sub_energy_le_add_deficit`).

At the block level of the sampled Weil matrix this reads
`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + Σ_{x ∈ M} d_x` (`absorbed_block_count_add_deficit`), for any set
`M ⊆ S₁` of simple on-line points with absorbers `σ x` (a multiple on-line point or an off-line
pair) satisfying `−d_x ≤ 1 + 2⟨f_x, g⟩²/‖g‖² − 2‖f_x‖²`.
-/

open scoped RealInnerProductSpace
open Finset

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- **The abstract count with deficits.** -/
theorem HorizontalPacket.four_mass_sub_energy_le_add_deficit {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM]
    [Fintype ιP] (P : HorizontalPacket V ι₂ ιH ιM ιP) (hm₂ : ∀ i, 2 ≤ P.m₂ i)
    (hmP : ∀ p, 1 ≤ P.mP p) (hH : ∀ i, ‖P.fH i‖ ≤ 1) (dfc : ιM → ℝ)
    (hcost : ∀ i, -dfc i ≤ 1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) :
    4 * P.mass - P.energy - 2 * P.count ≤ Fintype.card ιH + ∑ i, dfc i := by
  have h := P.four_mass_sub_energy_le hm₂ hmP
  have h1 : 0 ≤ ∑ i, (1 - ‖P.fH i‖ ^ 2) := Finset.sum_nonneg fun i _ => by
    have := hH i
    have := norm_nonneg (P.fH i)
    nlinarith
  have h2 : -∑ i, dfc i ≤
      ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hcost i
  linarith

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (M : Finset ι)

/-- **Absorbed count with deficits at the block level.** -/
theorem absorbed_block_count_add_deficit (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (σ : {z // z ∈ M} → ι) (hσ : ∀ x, σ x ∈ D.S₂ ∨ σ x ∈ Pr.R) (dfc : {z // z ∈ M} → ℝ)
    (hcost : ∀ x : {z // z ∈ M}, -dfc x ≤ 1 + 2 * ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2
        / ‖blockReVec D c (σ x)‖ ^ 2 - 2 * ‖blockReVec D c x‖ ^ 2) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) + ∑ x, dfc x := by
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
  have h := HorizontalPacket.four_mass_sub_energy_le_add_deficit Pk
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    dfc (fun x => by
      have h1 := hcost x
      have h2 : ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2 / ‖blockReVec D c (σ x)‖ ^ 2
          ≤ ‖Pk.absorbing.starProjection (blockReVec D c x)‖ ^ 2 := hproj x
      show -dfc x ≤ 1 + 2 * ‖Pk.absorbing.starProjection (blockReVec D c x)‖ ^ 2
        - 2 * ‖blockReVec D c x‖ ^ 2
      rw [mul_div_assoc] at h1
      linarith)
  rw [Fintype.card_coe] at h
  exact h

end Block

end

end RHTower
