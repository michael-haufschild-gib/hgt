import GaloisForLFunctions.RHTower.HorizontalIsolationBlockPacket

/-!
# Block packets with simple representatives in the absorbing range

Split the simple on-line points `S₁` of Zeta23's block data into a set `Q` of representatives, a set
`M` of absorbed points and the rest.  Placing `Q` next to the multiple points `S₂` in the absorbing
range gives a horizontal packet whose kernel is still the normalised sampled Weil matrix
(`blockP_add_blockQ_eq_kernelQ`).  The trace form of the unnormalised Lamzouri inequality then gives

`4 tr − ‖·‖² − 2N + 2 Σ_{x∈M} κ_x ≤ #(S₁ ∖ (M ∪ Q)) + 2 #Q`

whenever every `x ∈ M` has an absorber `σ x ∈ S₂ ∪ Q ∪ R` with `κ_x ≤ 1 + 2⟨f_x,g⟩²/‖g‖² − 2‖f_x‖²`
(`clustered_block_count`).  A representative costs `2`; an absorbed point whose vector nearly
coincides with its absorber earns almost `2`.

Representatives are supplied by a half-size dominating set: in a finite graph without isolated
vertices, some dominating set has at most half of the vertices (`exists_dominating_half`).
-/

open scoped RealInnerProductSpace
open Finset Matrix

namespace RHTower

noncomputable section

open GaloisForLFunctions.HilbertMetric

/-- **Half-size dominating sets.**  In a finite set of vertices with a symmetric irreflexive
adjacency in which every vertex has a neighbour, some subset `Q` with `2|Q| ≤ |V|` dominates:
every vertex outside `Q` has a neighbour in `Q`. -/
theorem exists_dominating_half {α : Type*} [DecidableEq α] (V : Finset α) (adj : α → α → Prop)
    [DecidableRel adj] (hsymm : ∀ a b, adj a b → adj b a) (hirr : ∀ a, ¬ adj a a)
    (hnb : ∀ v ∈ V, ∃ u ∈ V, adj v u) :
    ∃ Q ⊆ V, 2 * Q.card ≤ V.card ∧ ∀ v ∈ V \ Q, ∃ q ∈ Q, adj v q := by
  set 𝒟 := V.powerset.filter fun D => ∀ v ∈ V \ D, ∃ d ∈ D, adj v d
  have hV : V ∈ 𝒟 := Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr subset_rfl, fun v hv =>
    absurd (Finset.mem_sdiff.mp hv).1 (Finset.mem_sdiff.mp hv).2⟩
  obtain ⟨D, hD, hmin⟩ := 𝒟.exists_min_image Finset.card ⟨V, hV⟩
  have hDsub : D ⊆ V := Finset.mem_powerset.mp (Finset.mem_filter.mp hD).1
  have hDdom : ∀ v ∈ V \ D, ∃ d ∈ D, adj v d := (Finset.mem_filter.mp hD).2
  -- the complement of a minimum dominating set dominates
  have hcomp : ∀ v ∈ V \ (V \ D), ∃ u ∈ V \ D, adj v u := by
    intro v hv
    have hvD : v ∈ D := by
      rw [Finset.mem_sdiff] at hv
      by_contra h
      exact hv.2 (Finset.mem_sdiff.mpr ⟨hv.1, h⟩)
    by_contra hno
    push Not at hno
    set D' := D.erase v
    have hD' : D' ∈ 𝒟 := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr ((Finset.erase_subset _ _).trans hDsub),
        fun w hw => ?_⟩
      rw [Finset.mem_sdiff] at hw
      by_cases hwv : w = v
      · subst hwv
        obtain ⟨u, huV, hwu⟩ := hnb w hw.1
        have huD : u ∈ D := by
          by_contra huD
          exact hno u (Finset.mem_sdiff.mpr ⟨huV, huD⟩) hwu
        refine ⟨u, Finset.mem_erase.mpr ⟨fun h => hirr w (h ▸ hwu), huD⟩, hwu⟩
      · have hwD : w ∉ D := fun h => hw.2 (Finset.mem_erase.mpr ⟨hwv, h⟩)
        obtain ⟨d, hdD, hwd⟩ := hDdom w (Finset.mem_sdiff.mpr ⟨hw.1, hwD⟩)
        by_cases hdv : d = v
        · subst hdv
          exact absurd (hsymm _ _ hwd) (hno w (Finset.mem_sdiff.mpr ⟨hw.1, hwD⟩))
        · exact ⟨d, Finset.mem_erase.mpr ⟨hdv, hdD⟩, hwd⟩
    have := hmin D' hD'
    have hlt : D'.card < D.card := Finset.card_erase_lt_of_mem hvD
    omega
  by_cases hsmall : 2 * D.card ≤ V.card
  · exact ⟨D, hDsub, hsmall, hDdom⟩
  · refine ⟨V \ D, Finset.sdiff_subset, ?_, hcomp⟩
    rw [Finset.card_sdiff_of_subset hDsub]
    omega

section Block

set_option linter.unusedSectionVars false

variable {ι d : Type*} [Fintype ι] [DecidableEq ι] [Fintype d] [DecidableEq d]
variable (D : Zeta23.ZeroSide.ZeroBlockData ι d) (Pr : D.PairReps) (c : ℝ) (Q M : Finset ι)

/-- The horizontal packet with the representatives `Q ⊆ S₁` moved into the absorbing range:
absorbing on-line points `S₂ ∪ Q`, horizontally simple points `S₁ ∖ (M ∪ Q)`, absorbed points `M`,
and the off-line pairs `R`. -/
def blockPacketQ : HorizontalPacket (EuclideanSpace ℝ d) {z // z ∈ D.S₂ ∪ Q}
    {z // z ∈ D.S₁ \ (M ∪ Q)} {z // z ∈ M} {z // z ∈ Pr.R} where
  f₂ z := blockReVec D c z
  m₂ z := D.m z
  fH z := blockReVec D c z
  fM z := blockReVec D c z
  g p := blockReVec D c p
  h p := blockImVec D c p
  mP p := D.m p

theorem sum_S₁_split (hQ : Q ⊆ D.S₁) (hM : M ⊆ D.S₁) (hMQ : Disjoint M Q) (F : ι → ℝ) :
    ∑ z ∈ D.S₁, F z = ∑ z ∈ D.S₁ \ (M ∪ Q), F z + ∑ z ∈ M, F z + ∑ z ∈ Q, F z := by
  have hsub : M ∪ Q ⊆ D.S₁ := Finset.union_subset hM hQ
  conv_lhs => rw [← Finset.sdiff_union_of_subset hsub]
  rw [Finset.sum_union Finset.sdiff_disjoint, Finset.sum_union hMQ, add_assoc]

theorem m_eq_one_of_mem_S₁ {z : ι} (hz : z ∈ D.S₁) : (D.m z : ℝ) = 1 := by
  have := (Finset.mem_filter.mp hz).2.2
  exact_mod_cast this

/-- **The sampled matrix is the kernel of the packet with representatives.** -/
theorem blockP_add_blockQ_apply_Q (hc : 0 < c) (hQ : Q ⊆ D.S₁) (hM : M ⊆ D.S₁)
    (hMQ : Disjoint M Q) (k l : d) :
    (D.blockP c + D.blockQ c) k l = ((packetKernel (blockPacketQ D Pr c Q M) k l : ℝ) : ℂ) := by
  rw [D.blockP_add_blockQ, Matrix.smul_apply, blockA_apply_split D Pr, smul_eq_mul,
    ← Complex.ofReal_mul]
  congr 1
  have hprod : ∀ x y : ℝ, x / Real.sqrt c * (y / Real.sqrt c) = c⁻¹ * (x * y) := fun x y => by
    field_simp; rw [Real.sq_sqrt hc.le]; ring
  unfold packetKernel
  rw [(blockPacketQ D Pr c Q M).sum_wt_mul (fun v => v k * v l)]
  simp only [blockPacketQ, blockReVec_apply, blockImVec_apply, hprod]
  simp only [Finset.sum_coe_sort (s := D.S₂ ∪ Q)
      (f := fun z => (D.m z : ℝ) * (c⁻¹ * ((D.v z k).re * (D.v z l).re))),
    Finset.sum_coe_sort (s := D.S₁ \ (M ∪ Q)) (f := fun z => c⁻¹ * ((D.v z k).re * (D.v z l).re)),
    Finset.sum_coe_sort (s := M) (f := fun z => c⁻¹ * ((D.v z k).re * (D.v z l).re)),
    Finset.sum_coe_sort (s := Pr.R)
      (f := fun z => 2 * (D.m z : ℝ) * (c⁻¹ * ((D.v z k).re * (D.v z l).re))),
    Finset.sum_coe_sort (s := Pr.R)
      (f := fun z => 2 * (D.m z : ℝ) * (c⁻¹ * ((D.v z k).im * (D.v z l).im)))]
  have hQS₂ : Disjoint D.S₂ Q := Finset.disjoint_of_subset_right hQ D.disjoint_S₁_S₂.symm
  have hon : ∑ z ∈ D.onLine, (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re)
      = ∑ z ∈ D.S₂ ∪ Q, (D.m z : ℝ) * ((D.v z k).re * (D.v z l).re)
        + ∑ z ∈ D.S₁ \ (M ∪ Q), (D.v z k).re * (D.v z l).re
        + ∑ z ∈ M, (D.v z k).re * (D.v z l).re := by
    rw [D.onLine_eq_S₁_union_S₂, Finset.sum_union D.disjoint_S₁_S₂, Finset.sum_union hQS₂,
      Finset.sum_congr rfl fun z hz => by rw [m_eq_one_of_mem_S₁ D hz, one_mul],
      Finset.sum_congr (rfl : Q = Q) fun z hz => by rw [m_eq_one_of_mem_S₁ D (hQ hz), one_mul],
      sum_S₁_split D Q M hQ hM hMQ]
    ring
  rw [hon, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum,
    Finset.mul_sum, add_sub_assoc, ← Finset.sum_sub_distrib]
  refine congrArg₂ (· + ·) (congrArg₂ (· + ·) (congrArg₂ (· + ·) ?_ ?_) ?_) ?_ <;>
    exact Finset.sum_congr rfl fun z _ => by ring

theorem blockP_add_blockQ_eq_kernelQ (hc : 0 < c) (hQ : Q ⊆ D.S₁) (hM : M ⊆ D.S₁)
    (hMQ : Disjoint M Q) :
    D.blockP c + D.blockQ c
      = (fun k l => ((packetKernel (blockPacketQ D Pr c Q M) k l : ℝ) : ℂ) : Matrix d d ℂ) := by
  ext k l
  exact blockP_add_blockQ_apply_Q D Pr c Q M hc hQ hM hMQ k l

theorem blockPacketQ_count (hQ : Q ⊆ D.S₁) (hM : M ⊆ D.S₁) (hMQ : Disjoint M Q) :
    (blockPacketQ D Pr c Q M).count = (D.Ncount : ℝ) := by
  simp only [HorizontalPacket.count, blockPacketQ, Fintype.card_coe]
  rw [Finset.sum_coe_sort (s := D.S₂ ∪ Q) (f := fun z => (D.m z : ℝ)),
    Finset.sum_coe_sort (s := Pr.R) (f := fun z => (D.m z : ℝ))]
  have hN : (D.Ncount : ℝ) = ∑ z ∈ D.onLine, (D.m z : ℝ)
      + ∑ z ∈ Pr.R, ((D.m z : ℝ) + D.m (D.σ z)) := by
    unfold Zeta23.ZeroSide.ZeroBlockData.Ncount
    push_cast
    exact D.sum_split Pr (fun z => (D.m z : ℝ))
  rw [hN]
  simp only [D.m_σ]
  have hQS₂ : Disjoint D.S₂ Q := Finset.disjoint_of_subset_right hQ D.disjoint_S₁_S₂.symm
  rw [D.onLine_eq_S₁_union_S₂, Finset.sum_union D.disjoint_S₁_S₂, Finset.sum_union hQS₂,
    Finset.sum_congr rfl fun z hz => m_eq_one_of_mem_S₁ D hz,
    Finset.sum_congr (rfl : Q = Q) fun z hz => m_eq_one_of_mem_S₁ D (hQ hz),
    sum_S₁_split D Q M hQ hM hMQ]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum, ← two_mul]
  ring

/-- **Clustered count at the block level.**  Let `Q, M ⊆ S₁` be disjoint.  If every `x ∈ M` has an
absorber `σ x ∈ S₂ ∪ Q ∪ R` and `κ_x ≤ 1 + 2⟨f_x, g⟩²/‖g‖² − 2‖f_x‖²` for the normalised real
vectors, then `4 tr − ‖·‖² − 2N + 2 Σ_M κ ≤ #(S₁ ∖ (M ∪ Q)) + 2 #Q`. -/
theorem clustered_block_count (hc : 0 < c) (hQ : Q ⊆ D.S₁) (hM : M ⊆ D.S₁)
    (hMQ : Disjoint M Q) (hPois : ∀ z ∈ D.onLine, ∑ k, ‖D.v z k‖ ^ 2 ≤ c)
    (σ : {z // z ∈ M} → ι) (hσ : ∀ x, σ x ∈ D.S₂ ∪ Q ∨ σ x ∈ Pr.R)
    (κ : {z // z ∈ M} → ℝ)
    (hcost : ∀ x : {z // z ∈ M}, κ x ≤ 1 + 2 * ⟪blockReVec D c x, blockReVec D c (σ x)⟫ ^ 2
        / ‖blockReVec D c (σ x)‖ ^ 2 - 2 * ‖blockReVec D c x‖ ^ 2) :
    4 * RHLinalg.rtrace (D.blockP c + D.blockQ c) - RHLinalg.frobSq (D.blockP c + D.blockQ c)
      - 2 * (D.Ncount : ℝ) + 2 * ∑ x, κ x
      ≤ ((D.S₁ \ (M ∪ Q)).card : ℝ) + 2 * (Q.card : ℝ) := by
  set Pk := blockPacketQ D Pr c Q M
  rw [blockP_add_blockQ_eq_kernelQ D Pr c Q M hc hQ hM hMQ, frobSq_ofReal_matrix,
    rtrace_ofReal_matrix, ← energy_eq_sum_packetKernel_sq, ← mass_eq_sum_packetKernel_diag,
    ← blockPacketQ_count D Pr c Q M hQ hM hMQ]
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
  have h := Pk.four_mass_sub_energy_le_trace
    (fun p => by show (1 : ℝ) ≤ (D.m p : ℝ); exact_mod_cast D.one_le_m p)
  have hH : 0 ≤ ∑ i, (1 - ‖Pk.fH i‖ ^ 2) := Finset.sum_nonneg fun i _ => by
    have := norm_blockReVec_le_one D c hc
      (hPois i (hS1on i ((Finset.mem_sdiff.mp i.2).1)))
    have h0 := norm_nonneg (blockReVec D c i)
    show 0 ≤ 1 - ‖blockReVec D c i‖ ^ 2
    nlinarith
  have hMs : 2 * ∑ x, κ x
      ≤ ∑ i, (2 + 4 * ‖Pk.absorbing.starProjection (Pk.fM i)‖ ^ 2 - 4 * ‖Pk.fM i‖ ^ 2) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    have h1 := hcost x
    have h2 := hproj x
    rw [mul_div_assoc] at h1
    show 2 * κ x ≤ 2 + 4 * ‖Pk.absorbing.starProjection (Pk.fM x)‖ ^ 2
      - 4 * ‖blockReVec D c x‖ ^ 2
    linarith
  have hm₂ : ∑ i, (2 - Pk.m₂ i) ≤ (Q.card : ℝ) := by
    show ∑ i : {z // z ∈ D.S₂ ∪ Q}, (2 - (D.m i : ℝ)) ≤ (Q.card : ℝ)
    rw [Finset.sum_coe_sort (s := D.S₂ ∪ Q) (f := fun z => 2 - (D.m z : ℝ))]
    have hQS₂ : Disjoint D.S₂ Q := Finset.disjoint_of_subset_right hQ D.disjoint_S₁_S₂.symm
    rw [Finset.sum_union hQS₂]
    have h1 : ∑ z ∈ D.S₂, (2 - (D.m z : ℝ)) ≤ 0 := Finset.sum_nonpos fun z hz => by
      have := (Finset.mem_filter.mp hz).2.2
      have : (2 : ℝ) ≤ D.m z := by exact_mod_cast this
      linarith
    have h2 : ∑ z ∈ Q, (2 - (D.m z : ℝ)) = Q.card := by
      rw [Finset.sum_congr rfl fun z hz => by rw [m_eq_one_of_mem_S₁ D (hQ hz)]]
      simp
      ring
    linarith
  rw [Fintype.card_coe] at h
  linarith

end Block

end

end RHTower
