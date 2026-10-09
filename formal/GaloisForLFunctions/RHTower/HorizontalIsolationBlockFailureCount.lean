import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriRouteToMultiple
import GaloisForLFunctions.HilbertMetric.SpanAngleFromGramFrame
import GaloisForLFunctions.RHTower.HorizontalIsolationBlockPairField

/-!
# The odd-angle failure count for sampled Weil matrices

For Zeta23's block data, the normalised zero-side matrix is the kernel of the horizontal packet
`blockPacket`. The failure-tolerant odd-angle count
(`HorizontalPacket.four_mass_sub_energy_le_add_card_fail`) therefore gives Zeta23's count with
the mixed points removed, plus one unit per uncertified mixed point:
`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + #{x ∈ M uncertified}` (`oddAngle_block_count`).

A mixed point `x` is certified when the owner form of its pair `own x` (the even vector of the
owner against the odd vectors of all pairs) has `r(‖f_x‖² − ½) ≤ ⟪Φ⁺ f_x, f_x⟫`, where `r` is
the number of owners. With owner weights `w` (`oddAngle_block_hybrid_count`), the hybrid
certificate supplies `‖f_x‖² − ½ ≤ w_{own x}⟪Φ⁺ f_x, f_x⟫` from the large-family angle `κ` and the
small-family overlaps `σ²`. The number of uncertified mixed points is at most `Σ_x (K_x/θ_x)²`.
The angle `κ` is bounded by the pairwise angles `⟪ĥ_q, g_p⟫` through
`abs_inner_le_of_rowSum`. The overlaps `⟪h_q, g_p⟫` are bounded by
`abs_inner_blockImVec_blockReVec_sub_le` and `abs_integral_cross_window_le`, which give the
full-grid window integral (decaying like `1/|γ_q − γ_p|`) plus the leakages.
-/

open scoped RealInnerProductSpace

noncomputable section

namespace RHTower

open GaloisForLFunctions.HilbertMetric

section Block

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (M : Finset ι)

/-- **Odd-angle failure count for the block.** -/
theorem oddAngle_block_count (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (own : {z // z ∈ M} → {z // z ∈ Pr.R}) (O : Finset {z // z ∈ Pr.R})
    (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty) (good : Finset {z // z ∈ M})
    (hgood : ∀ x ∈ good, (blockPacket D Pr c M).Certified own O.card x) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) + (Finset.univ \ good).card := by
  classical
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have h := Pk.four_mass_sub_energy_le_add_card_fail
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    (fun x => norm_blockReVec_le_one D c hc (hPois x (hS1on x (hM x.2))))
    own O hO hOne good hgood
  rw [Fintype.card_coe] at h
  exact h

/-- **Hybrid failure count for the block.** With owner weights `w ≥ 0` on `O`, `Σ_O w = 1`, and
per-mixed-point hybrid data `(L_x, κ_x, σ²_x, λ₀_x, θ_x)`,
`4 tr − ‖·‖² − 2N ≤ #(S₁ \ M) + Σ_x (K_x/θ_x)²`, `K_x = κ_x + √(σ²_x/(4λ₀_x))`. -/
theorem oddAngle_block_hybrid_count (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (own : {z // z ∈ M} → {z // z ∈ Pr.R}) (O : Finset {z // z ∈ Pr.R})
    (hO : ∀ x, own x ∈ O) (w : {z // z ∈ Pr.R} → ℝ) (hw0 : ∀ q ∈ O, 0 ≤ w q)
    (hw1 : ∑ q ∈ O, w q = 1) (Lset : {z // z ∈ M} → Finset {z // z ∈ Pr.R}) (κ σ2 lam0 θ : {z // z ∈ M} → ℝ)
    (hκ0 : ∀ x, 0 ≤ κ x)
    (hκ : ∀ x, ∀ d ∈ Submodule.span ℝ
        (Set.range fun q : {q // q ∈ Lset x} => blockImVec D c (q : {z // z ∈ Pr.R})),
      |⟪d, blockReVec D c (own x)⟫| ≤ κ x * ‖d‖)
    (hσ : ∀ x, ∑ q : {q // q ∉ Lset x},
      2 * (D.m (q : {z // z ∈ Pr.R}) : ℝ) *
        (|⟪blockImVec D c (q : {z // z ∈ Pr.R}), blockReVec D c (own x)⟫| +
          ‖blockImVec D c (q : {z // z ∈ Pr.R})‖ * κ x) ^ 2 ≤ σ2 x)
    (hgap : ∀ x, κ x ^ 2 < ‖blockReVec D c (own x)‖ ^ 2) (hlam0 : ∀ x, 0 < lam0 x)
    (hlam0le : ∀ x, lam0 x ≤ 2 * (D.m (own x) : ℝ) *
        (‖blockReVec D c (own x)‖ ^ 2 - κ x ^ 2) -
      σ2 x / (‖blockReVec D c (own x)‖ ^ 2 - κ x ^ 2))
    (hθ : ∀ x, 0 < θ x)
    (hθdef : ∀ x : {z // z ∈ M}, ‖blockReVec D c x‖ ^ 2 - 1 / 2 ≤ w (own x) *
      (2 * (D.m (own x) : ℝ) *
        max (|⟪blockReVec D c (own x), blockReVec D c x⟫| - θ x * ‖blockReVec D c x‖) 0 ^ 2)) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) +
        ∑ x, ((κ x + Real.sqrt (σ2 x / (4 * lam0 x))) / θ x) ^ 2 := by
  classical
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have h := Pk.four_mass_sub_energy_le_add_hybrid_count
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    (fun x => norm_blockReVec_le_one D c hc (hPois x (hS1on x (hM x.2))))
    own O hO w hw0 hw1 Lset κ σ2 lam0 θ hκ0 hκ hσ hgap hlam0 hlam0le hθ hθdef
  rw [Fintype.card_coe] at h
  exact h

/-- **Routed failure count for the block.** The pairs of `S` are counted as multiple real points
with vector `g_q` and multiplicity `2m_q`; each costs `4m_q(D′(h_q) − 2‖h_q‖²)`, where `D′` is the
diagonal form of the routed packet. -/
theorem oddAngle_block_route_count (hc : 0 < c) (hM : M ⊆ D.S₁)
    (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c) (S : Finset {z // z ∈ Pr.R})
    (own : {z // z ∈ M} → {q // q ∉ S}) (O : Finset {q // q ∉ S})
    (hO : ∀ x, own x ∈ O) (hOne : O.Nonempty) (β : {q // q ∉ S} → ℝ)
    (hβ0 : ∀ q ∈ O, 0 ≤ β q) (hβ1 : ∑ q ∈ O, β q ≤ 1) (good : Finset {z // z ∈ M})
    (hgood : ∀ x ∈ good, ((blockPacket D Pr c M).routeToMultiple S).CertifiedWith own β x) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) ≤ ((D.S₁ \ M).card : ℝ) + (Finset.univ \ good).card +
        ∑ q : {q // q ∈ S}, 4 * (D.m (q : {z // z ∈ Pr.R}) : ℝ) *
          (((blockPacket D Pr c M).routeToMultiple S).diagForm
              (blockImVec D c (q : {z // z ∈ Pr.R})) -
            2 * ‖blockImVec D c (q : {z // z ∈ Pr.R})‖ ^ 2) := by
  classical
  set Pk := blockPacket D Pr c M
  rw [blockP_add_blockQ_eq_kernel D Pr c M hc hM, frobSq_ofReal_matrix, rtrace_ofReal_matrix,
    ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacket_count D Pr c M hM]
  have hS1on : ∀ z ∈ D.S₁, z ∈ D.onLine := fun z hz => by
    rw [D.onLine_eq_S₁_union_S₂]; exact Finset.mem_union_left _ hz
  have h := Pk.four_mass_sub_energy_le_route_add_card_fail S
    (fun i => by
      have := (Finset.mem_filter.mp i.2).2.2
      show (2 : ℝ) ≤ (D.m i : ℝ); exact_mod_cast this)
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
    (fun i => norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1))))
    (fun x => norm_blockReVec_le_one D c hc (hPois x (hS1on x (hM x.2))))
    own O hO hOne β hβ0 hβ1 good hgood
  rw [Fintype.card_coe] at h
  exact h

end Block

end RHTower
