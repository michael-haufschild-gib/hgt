import GaloisForLFunctions.HeckeKreinToeplitz.GrowthReadsTheDepthOfTheDeepestPair

/-!
# The index is the number of exceptional waves

A **count** along a tower `⟨u⟩` is a bound on the kernel values `k(u^n)`. Index zero is a bounded
count (self-upgrade, HKT). This module proves the finite-stratum form of that law as a ceiling: a
count that becomes bounded after subtracting finitely many **waves** `Σ_i a_i v_i^n` bounds the
index by the number of waves, and the minimum is attained by the outer nodes.

**Wave ceiling** (`card_le_of_bounded_sub_waves`). For a positive-definite kernel plus `κ` pairs
separated at `u`, if `‖k(u^n) − Σ_{i<m} a_i v_i^n‖ ≤ M` for all `n ≥ 0`, then `κ ≤ m`. Merging equal
frequencies, the difference is an exponential sum plus the bounded positive part; non-cancellation at
the top modulus (`coeff_eq_zero_of_norm_le`) kills every merged coefficient of modulus `> 1`, so
each outer node of a pair must be one of the waves, and distinct pairs use distinct waves.

**Attainment** (`exists_waves_bounded`). Subtracting the `κ` outer nodes with their weights leaves
the positive part and the decaying inner nodes: bounded.

**Rigidity of minimal counts** (`nodeCoeff_outer_eq_sum_waves`, `minimal_waves_eq_outerNodes`). The
weight of each outer node is the total wave coefficient at it; a count bounded after exactly `κ`
waves uses the outer nodes, one each, with the pair weights as coefficients. A minimal count
determines the hyperbolic spectrum and its weights.

**The index formula** (`negIndex_eq_card_waves`). Hence `κ(k)` is the least number of exceptional
waves of a bounded count along a separating tower. For the Weil kernel of `ζ` on the finite stratum
this is the subtracted-lag law: `ψ(x) − x` minus finitely many waves `x^ρ/ρ` is bounded by `√x log²x`
exactly when off-line support is finite, and the number of waves is the index. Every finite count
ceiling for `ζ` therefore proves the Lindelöf hypothesis.
-/

open Complex Finset Filter
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz

noncomputable section

namespace GaloisForLFunctions.ArithmeticKreinLangerTheory

variable {G : Type*} [Group G] {κ : ℕ}

/-- **Merging frequencies.** A finite exponential sum bounded along `n ≥ 0` has, at every
frequency of modulus `> 1`, total coefficient zero. -/
theorem sum_coeff_eq_zero_of_norm_le {ι : Type*} [Fintype ι] (ν : ι → ℂ) (c : ι → ℂ) {M : ℝ}
    (h : ∀ n : ℕ, ‖∑ i, c i * ν i ^ n‖ ≤ M) {w : ℂ} (hw : 1 < ‖w‖) :
    ∑ i ∈ univ.filter (fun i => ν i = w), c i = 0 := by
  classical
  set V := univ.image ν
  set b : V → ℂ := fun v => ∑ i ∈ univ.filter (fun i => ν i = v), c i
  have hmerge : ∀ n : ℕ, ∑ i, c i * ν i ^ n = ∑ v : V, b v * (v : ℂ) ^ n := fun n => by
    rw [← sum_fiberwise_of_maps_to (s := univ) (t := V) (g := ν)
      (fun i _ => mem_image_of_mem ν (mem_univ i)), ← V.sum_coe_sort]
    refine sum_congr rfl fun v _ => ?_
    rw [sum_mul]
    exact sum_congr rfl fun i hi => by rw [(mem_filter.mp hi).2]
  by_cases hwV : w ∈ V
  · have := coeff_eq_zero_of_norm_le (ν := fun v : V => (v : ℂ)) Subtype.val_injective b one_pos
      (M := M) (fun n => by rw [← hmerge, one_pow, mul_one]; exact h n) (i := ⟨w, hwV⟩) hw
    exact this
  · refine sum_eq_zero fun i hi => absurd ?_ hwV
    rw [← (mem_filter.mp hi).2]; exact mem_image_of_mem ν (mem_univ i)

/-- The outer node of pair `j` at `u`. -/
def outerNode (χ : Fin κ → G →* ℂ) (u : G) (j : Fin κ) : Fin κ ⊕ Fin κ :=
  if 1 < ‖χ j u‖ then Sum.inl j else Sum.inr j

theorem one_lt_norm_outerNode {χ : Fin κ → G →* ℂ} {u : G} (hne : ∀ j, ‖χ j u‖ ≠ 1) (j : Fin κ) :
    1 < ‖nodes χ u (outerNode χ u j)‖ := by
  unfold outerNode; split_ifs with h
  · exact h
  · simp only [nodes, Sum.elim_inr, norm_reflectChar]
    exact one_lt_inv_iff₀.mpr ⟨norm_pos_iff.mpr (map_ne_zero _ _),
      lt_of_le_of_ne (not_lt.mp h) (hne j)⟩

theorem outerNode_injective (χ : Fin κ → G →* ℂ) (u : G) : Function.Injective (outerNode χ u) := by
  intro j j' h
  unfold outerNode at h
  split_ifs at h <;> simpa using h

/-- **The wave ceiling.** A count along a separating tower that is bounded after subtracting `m`
waves bounds the number of pairs by `m`. -/
theorem card_le_of_bounded_sub_waves {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u)) {m : ℕ} (v a : Fin m → ℂ)
    (hb : ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
      ∑ i, a i * v i ^ n‖ ≤ M) : κ ≤ m := by
  classical
  obtain ⟨M, hM⟩ := hb
  -- the combined exponential sum of nodes and subtracted waves
  set ν : (Fin κ ⊕ Fin κ) ⊕ Fin m → ℂ := Sum.elim (nodes χ u) v
  set c : (Fin κ ⊕ Fin κ) ⊕ Fin m → ℂ := Sum.elim (nodeCoeff ω) fun i => -a i
  have hbound : ∀ n : ℕ, ‖∑ i, c i * ν i ^ n‖ ≤ M + (p 1).re := fun n => by
    have hs : ∑ i, c i * ν i ^ n = (p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
        ∑ i, a i * v i ^ n) - p (u ^ n) := by
      rw [Fintype.sum_sum_type, sum_pairKernel_pow]
      simp only [ν, c, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
      ring
    rw [hs]
    exact (norm_sub_le _ _).trans (add_le_add (hM n) (hp.norm_le _))
  -- each outer node is one of the waves
  have hwave : ∀ j, ∃ i, v i = nodes χ u (outerNode χ u j) := fun j => by
    have h0 := sum_coeff_eq_zero_of_norm_le ν c hbound (one_lt_norm_outerNode hne j)
    rw [← sum_filter_add_sum_filter_not (univ.filter fun i => ν i = nodes χ u (outerNode χ u j))
      (fun i : (Fin κ ⊕ Fin κ) ⊕ Fin m => i.isLeft)] at h0
    by_contra hnone
    push Not at hnone
    have hright : ∑ i ∈ (univ.filter fun i => ν i = nodes χ u (outerNode χ u j)).filter
        (fun i : (Fin κ ⊕ Fin κ) ⊕ Fin m => ¬ i.isLeft), c i = 0 :=
      sum_eq_zero fun i hi => by
        obtain ⟨hi1, hi2⟩ := mem_filter.mp hi
        rcases i with i | i
        · simp at hi2
        · exact absurd (mem_filter.mp hi1).2 (hnone i)
    have hleft : ∑ i ∈ (univ.filter fun i => ν i = nodes χ u (outerNode χ u j)).filter
        (fun i : (Fin κ ⊕ Fin κ) ⊕ Fin m => i.isLeft), c i = nodeCoeff ω (outerNode χ u j) := by
      rw [sum_eq_single (Sum.inl (outerNode χ u j))]
      · rfl
      · intro i hi hne'
        obtain ⟨hi1, hi2⟩ := mem_filter.mp hi
        rcases i with i | i
        · exact absurd (congrArg Sum.inl (hsep (mem_filter.mp hi1).2)) hne'
        · simp at hi2
      · intro h
        exact (h (mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, by simp [ν]⟩, by simp⟩)).elim
    rw [hleft, hright, add_zero] at h0
    have hc : nodeCoeff ω (outerNode χ u j) ≠ 0 := by
      unfold outerNode; split_ifs
      · exact hω j
      · exact (star_ne_zero).mpr (hω j)
    exact hc h0
  choose f hf using hwave
  have hinj : Function.Injective f := fun j j' h =>
    outerNode_injective χ u (hsep ((hf j).symm.trans (h ▸ hf j')))
  simpa using Fintype.card_le_of_injective f hinj

/-- **Merged coefficients vanish at the outer nodes.** For a count bounded after subtracting the
waves `(v, a)`, the weight of each outer node equals the total wave coefficient at that node. -/
theorem nodeCoeff_outer_eq_sum_waves {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1) (hsep : Function.Injective (nodes χ u))
    {m : ℕ} (v a : Fin m → ℂ)
    (hb : ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
      ∑ i, a i * v i ^ n‖ ≤ M) (j : Fin κ) :
    nodeCoeff ω (outerNode χ u j) =
      ∑ i ∈ univ.filter (fun i => v i = nodes χ u (outerNode χ u j)), a i := by
  classical
  obtain ⟨M, hM⟩ := hb
  set ν : (Fin κ ⊕ Fin κ) ⊕ Fin m → ℂ := Sum.elim (nodes χ u) v
  set c : (Fin κ ⊕ Fin κ) ⊕ Fin m → ℂ := Sum.elim (nodeCoeff ω) fun i => -a i
  have hbound : ∀ n : ℕ, ‖∑ i, c i * ν i ^ n‖ ≤ M + (p 1).re := fun n => by
    have hs : ∑ i, c i * ν i ^ n = (p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
        ∑ i, a i * v i ^ n) - p (u ^ n) := by
      rw [Fintype.sum_sum_type, sum_pairKernel_pow]
      simp only [ν, c, Sum.elim_inl, Sum.elim_inr, neg_mul, sum_neg_distrib]
      ring
    rw [hs]
    exact (norm_sub_le _ _).trans (add_le_add (hM n) (hp.norm_le _))
  set w := nodes χ u (outerNode χ u j) with hw
  have h0 := sum_coeff_eq_zero_of_norm_le ν c hbound (one_lt_norm_outerNode hne j)
  rw [sum_filter, Fintype.sum_sum_type] at h0
  have hleft : ∑ x : Fin κ ⊕ Fin κ, (if ν (Sum.inl x) = w then c (Sum.inl x) else 0) =
      nodeCoeff ω (outerNode χ u j) := by
    exact (Fintype.sum_eq_single (outerNode χ u j) fun x hx => if_neg fun h => hx (hsep h)).trans
      (if_pos rfl)
  have hright : ∑ i : Fin m, (if ν (Sum.inr i) = w then c (Sum.inr i) else 0) =
      -∑ i ∈ univ.filter (fun i => v i = w), a i := by
    rw [sum_filter, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    simp only [ν, c, Sum.elim_inr]
    split_ifs <;> simp
  rw [hleft, hright, add_neg_eq_zero] at h0
  exact h0

/-- **The waves of a minimal count are the outer nodes with their weights.** If a count along a
separating tower is bounded after subtracting exactly `κ` waves, the waves are the outer nodes, one
each, and their coefficients are the pair weights: the minimal count determines the hyperbolic
spectrum and its weights. -/
theorem minimal_waves_eq_outerNodes {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u)) (v a : Fin κ → ℂ)
    (hb : ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
      ∑ i, a i * v i ^ n‖ ≤ M) :
    ∃ σ : Fin κ ≃ Fin κ, ∀ j, v (σ j) = nodes χ u (outerNode χ u j) ∧
      a (σ j) = nodeCoeff ω (outerNode χ u j) := by
  classical
  have hc : ∀ j, nodeCoeff ω (outerNode χ u j) ≠ 0 := fun j => by
    unfold outerNode; split_ifs
    · exact hω j
    · exact (star_ne_zero).mpr (hω j)
  have hex : ∀ j, ∃ i, v i = nodes χ u (outerNode χ u j) := fun j => by
    by_contra hnone
    push Not at hnone
    have := nodeCoeff_outer_eq_sum_waves hp χ ω u hne hsep v a hb j
    rw [sum_eq_zero fun i hi => absurd (mem_filter.mp hi).2 (hnone i)] at this
    exact hc j this
  choose f hf using hex
  have hinj : Function.Injective f := fun j j' h =>
    outerNode_injective χ u (hsep ((hf j).symm.trans (h ▸ hf j')))
  have hbij : Function.Bijective f := (Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, rfl⟩
  refine ⟨Equiv.ofBijective f hbij, fun j => ⟨hf j, ?_⟩⟩
  have hsum := nodeCoeff_outer_eq_sum_waves hp χ ω u hne hsep v a hb j
  rw [hsum, sum_eq_single (f j)]
  · rfl
  · intro i hi hij
    obtain ⟨j', rfl⟩ := hbij.2 i
    have := (mem_filter.mp hi).2
    rw [hf j'] at this
    exact absurd (congrArg f (outerNode_injective χ u (hsep this))) hij
  · intro h; exact (h (mem_filter.mpr ⟨mem_univ _, hf j⟩)).elim

/-- **Attainment.** Subtracting the outer nodes with their weights leaves a bounded count. -/
theorem exists_waves_bounded {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (u : G) :
    ∃ v a : Fin κ → ℂ, ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
      ∑ i, a i * v i ^ n‖ ≤ M := by
  classical
  -- the inner node of pair `j` and its coefficient
  set inner : Fin κ → Fin κ ⊕ Fin κ := fun j => if 1 < ‖χ j u‖ then Sum.inr j else Sum.inl j
  have hinner : ∀ j, ‖nodes χ u (inner j)‖ ≤ 1 := fun j => by
    simp only [inner]; split_ifs with h
    · simp only [nodes, Sum.elim_inr, norm_reflectChar]
      exact inv_le_one_of_one_le₀ h.le
    · exact (not_lt.mp h)
  refine ⟨fun j => nodes χ u (outerNode χ u j), fun j => nodeCoeff ω (outerNode χ u j),
    (p 1).re + ∑ j, ‖nodeCoeff ω (inner j)‖, fun n => ?_⟩
  have hsplit : ∑ j, pairKernel (χ j) (ω j) (u ^ n) =
      ∑ j, nodeCoeff ω (outerNode χ u j) * nodes χ u (outerNode χ u j) ^ n +
        ∑ j, nodeCoeff ω (inner j) * nodes χ u (inner j) ^ n := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    by_cases h : 1 < ‖χ j u‖
    · simp only [pairKernel, map_pow, outerNode, inner, h, if_true, nodeCoeff, nodes,
        Sum.elim_inl, Sum.elim_inr]
    · simp only [pairKernel, map_pow, outerNode, inner, h, if_false, nodeCoeff, nodes,
        Sum.elim_inl, Sum.elim_inr]
      ring
  rw [hsplit]
  beta_reduce
  rw [show ∀ x y z : ℂ, x + (y + z) - y = x + z from fun x y z => by ring]
  refine (norm_add_le _ _).trans (add_le_add (hp.norm_le _) ((norm_sum_le _ _).trans
    (sum_le_sum fun j _ => ?_)))
  rw [norm_mul, norm_pow]
  exact mul_le_of_le_one_right (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) (hinner j))

/-- **The index is the number of exceptional waves.** For a positive-definite kernel plus `κ` pairs
separated at `u`, `κ(k) = κ`, every count along `⟨u⟩` bounded after subtracting `m` waves has
`κ ≤ m`, and `κ` waves suffice. -/
theorem negIndex_eq_card_waves {p : G → ℂ} (hp : IsPosDefKernel p) (χ : Fin κ → G →* ℂ)
    (ω : Fin κ → ℂ) (hω : ∀ j, ω j ≠ 0) (u : G) (hne : ∀ j, ‖χ j u‖ ≠ 1)
    (hsep : Function.Injective (nodes χ u)) :
    negIndex (fun g => p g + ∑ j, pairKernel (χ j) (ω j) g) = κ ∧
      (∀ (m : ℕ) (v a : Fin m → ℂ), (∃ M, ∀ n : ℕ, ‖p (u ^ n) +
        ∑ j, pairKernel (χ j) (ω j) (u ^ n) - ∑ i, a i * v i ^ n‖ ≤ M) → κ ≤ m) ∧
      ∃ v a : Fin κ → ℂ, ∃ M, ∀ n : ℕ, ‖p (u ^ n) + ∑ j, pairKernel (χ j) (ω j) (u ^ n) -
        ∑ i, a i * v i ^ n‖ ≤ M :=
  ⟨negIndex_add_sum_pairKernel_eq hp χ ω hω u hne hsep,
    fun _ v a hb => card_le_of_bounded_sub_waves hp χ ω hω u hne hsep v a hb,
    exists_waves_bounded hp χ ω u⟩

end GaloisForLFunctions.ArithmeticKreinLangerTheory

#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.minimal_waves_eq_outerNodes
#print axioms GaloisForLFunctions.ArithmeticKreinLangerTheory.negIndex_eq_card_waves
