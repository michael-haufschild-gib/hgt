import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Constructions

/-!
# An invariant metric on a product with countably many finite blocks

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 7.6 (`t86`),
in the form of its general topological content.

Let `ι` be covered by finite blocks `blk k` indexed by a countable set `κ`, and let `C` be a metric
space.  Weighting the bounded distances `d / (1 + d)` blockwise,

`blockDist (P, Q) = ∑_k c_k ∑_{i ∈ blk k} d (P i, Q i) / (1 + d (P i, Q i))` ,

gives a metric on `ι → C` inducing the product topology, provided the weights are positive and
`∑_k c_k · #(blk k) < ∞`.  Such weights always exist when `κ` is countable.  A permutation of `ι`
preserving every block acts by isometries, which is what makes the metric invariant under a group
whose orbits are exactly the blocks.
-/

namespace HTGeometry

noncomputable def boundedDist (x : ℝ) : ℝ := x / (1 + x)

theorem boundedDist_nonneg {x : ℝ} (hx : 0 ≤ x) : 0 ≤ boundedDist x :=
  div_nonneg hx (by linarith)

theorem boundedDist_le_self {x : ℝ} (hx : 0 ≤ x) : boundedDist x ≤ x := by
  rw [boundedDist, div_le_iff₀ (by linarith)]
  nlinarith

theorem boundedDist_lt_one {x : ℝ} (hx : 0 ≤ x) : boundedDist x < 1 := by
  rw [boundedDist, div_lt_one (by linarith)]
  linarith

theorem boundedDist_le_one {x : ℝ} (hx : 0 ≤ x) : boundedDist x ≤ 1 :=
  (boundedDist_lt_one hx).le

theorem boundedDist_mono {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    boundedDist x ≤ boundedDist y := by
  rw [boundedDist, boundedDist, div_le_div_iff₀ (by linarith) (by linarith)]
  nlinarith

theorem boundedDist_zero : boundedDist 0 = 0 := by simp [boundedDist]

theorem boundedDist_pos {x : ℝ} (hx : 0 < x) : 0 < boundedDist x :=
  div_pos hx (by linarith)

theorem lt_of_boundedDist_lt {x y : ℝ} (hy : 0 ≤ y) (h : boundedDist x < boundedDist y) :
    x < y := by
  by_contra hc
  rw [not_lt] at hc
  exact absurd (boundedDist_mono hy hc) (not_le.2 h)

theorem boundedDist_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    boundedDist (x + y) ≤ boundedDist x + boundedDist y := by
  have h1 : x / (1 + (x + y)) ≤ x / (1 + x) := by gcongr; linarith
  have h2 : y / (1 + (x + y)) ≤ y / (1 + y) := by gcongr; linarith
  have h3 : boundedDist (x + y) = x / (1 + (x + y)) + y / (1 + (x + y)) := by
    rw [boundedDist]; ring
  rw [h3, boundedDist, boundedDist]
  linarith

/-! ### The block-weighted distance on a product -/

section Block

variable {ι κ C : Type*} [MetricSpace C]

/-- The block-weighted distance on `ι → C`: for a family of finite blocks `blk k ⊆ ι` covering
`ι` and positive weights `c k`, the weighted sum of the bounded distances over each block. -/
noncomputable def blockDist (blk : κ → Finset ι) (c : κ → ℝ) (P Q : ι → C) : ℝ :=
  ∑' k : κ, c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i))

variable {blk : κ → Finset ι} {c : κ → ℝ}

theorem blockDist_term_nonneg (hc : ∀ k, 0 ≤ c k) (P Q : ι → C) (k : κ) :
    0 ≤ c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) :=
  mul_nonneg (hc k) (Finset.sum_nonneg fun _ _ => boundedDist_nonneg dist_nonneg)

theorem blockDist_term_le (hc : ∀ k, 0 ≤ c k) (P Q : ι → C) (k : κ) :
    c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) ≤ c k * ((blk k).card : ℝ) := by
  refine mul_le_mul_of_nonneg_left ?_ (hc k)
  calc ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) ≤ ∑ _i ∈ blk k, (1 : ℝ) :=
        Finset.sum_le_sum fun _ _ => boundedDist_le_one dist_nonneg
    _ = ((blk k).card : ℝ) := by simp

theorem blockDist_summable (hc : ∀ k, 0 ≤ c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (P Q : ι → C) :
    Summable fun k => c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) :=
  Summable.of_nonneg_of_le (blockDist_term_nonneg hc P Q) (blockDist_term_le hc P Q) hsum

theorem blockDist_self (P : ι → C) : blockDist blk c P P = 0 := by
  simp [blockDist, boundedDist_zero]

theorem blockDist_comm (P Q : ι → C) : blockDist blk c P Q = blockDist blk c Q P := by
  simp only [blockDist, dist_comm]

theorem blockDist_nonneg (hc : ∀ k, 0 ≤ c k) (P Q : ι → C) : 0 ≤ blockDist blk c P Q :=
  tsum_nonneg (blockDist_term_nonneg hc P Q)

theorem blockDist_triangle (hc : ∀ k, 0 ≤ c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (P Q R : ι → C) :
    blockDist blk c P R ≤ blockDist blk c P Q + blockDist blk c Q R := by
  rw [blockDist, blockDist, blockDist,
    ← Summable.tsum_add (blockDist_summable hc hsum P Q) (blockDist_summable hc hsum Q R)]
  refine Summable.tsum_le_tsum ?_ (blockDist_summable hc hsum P R)
    ((blockDist_summable hc hsum P Q).add (blockDist_summable hc hsum Q R))
  intro k
  rw [← mul_add]
  refine mul_le_mul_of_nonneg_left ?_ (hc k)
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  calc boundedDist (dist (P i) (R i))
      ≤ boundedDist (dist (P i) (Q i) + dist (Q i) (R i)) :=
        boundedDist_mono dist_nonneg (dist_triangle _ _ _)
    _ ≤ _ := boundedDist_add_le dist_nonneg dist_nonneg

theorem blockDist_term_le_blockDist (hc : ∀ k, 0 ≤ c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (P Q : ι → C) (k : κ) :
    c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) ≤ blockDist blk c P Q :=
  Summable.le_tsum (blockDist_summable hc hsum P Q) k
    (fun j _ => blockDist_term_nonneg hc P Q j)

theorem dist_lt_of_blockDist_lt (hc : ∀ k, 0 < c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) {P Q : ι → C} {k : κ} {i : ι}
    (hi : i ∈ blk k) {ε : ℝ} (hε : 0 < ε)
    (h : blockDist blk c P Q < c k * boundedDist ε) : dist (P i) (Q i) < ε := by
  have h1 := blockDist_term_le_blockDist (fun k => (hc k).le) hsum P Q k
  have h3 : ∑ j ∈ blk k, boundedDist (dist (P j) (Q j)) < boundedDist ε :=
    lt_of_mul_lt_mul_left (lt_of_le_of_lt h1 h) (hc k).le
  have h4 : boundedDist (dist (P i) (Q i)) ≤ ∑ j ∈ blk k, boundedDist (dist (P j) (Q j)) :=
    Finset.single_le_sum (fun _ _ => boundedDist_nonneg dist_nonneg) hi
  exact lt_of_boundedDist_lt hε.le (lt_of_le_of_lt h4 h3)

theorem eq_of_blockDist_eq_zero (hc : ∀ k, 0 < c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (hcov : ∀ i, ∃ k, i ∈ blk k)
    {P Q : ι → C} (h : blockDist blk c P Q = 0) : P = Q := by
  funext i
  obtain ⟨k, hk⟩ := hcov i
  by_contra hne
  have hpos : 0 < dist (P i) (Q i) := dist_pos.2 hne
  have := dist_lt_of_blockDist_lt hc hsum hk hpos
    (by rw [h]; exact mul_pos (hc k) (boundedDist_pos hpos))
  exact absurd this (lt_irrefl _)

/-- The block-weighted distance induces the product topology. -/
theorem blockDist_isOpen_iff (hc : ∀ k, 0 < c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (hcov : ∀ i, ∃ k, i ∈ blk k)
    (s : Set (ι → C)) :
    IsOpen s ↔ ∀ P ∈ s, ∃ ε > 0, ∀ Q, blockDist blk c P Q < ε → Q ∈ s := by
  classical
  constructor
  · intro hs P hP
    obtain ⟨I, u, hu, hIu⟩ := isOpen_pi_iff.1 hs P hP
    have hrad : ∀ a : ι, ∃ δ : ℝ, 0 < δ ∧ (a ∈ I → Metric.ball (P a) δ ⊆ u a) := by
      intro a
      by_cases ha : a ∈ I
      · obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (hu a ha).1 (P a) (hu a ha).2
        exact ⟨δ, hδ, fun _ => hball⟩
      · exact ⟨1, one_pos, fun h => absurd h ha⟩
    choose δ hδ hball using hrad
    choose kk hkk using hcov
    refine ⟨(insert (1 : ℝ) (I.image (fun a => c (kk a) * boundedDist (δ a)))).min'
      ⟨1, by simp⟩, ?_, ?_⟩
    · refine (Finset.lt_min'_iff _ _).2 fun y hy => ?_
      rcases Finset.mem_insert.1 hy with rfl | hy
      · norm_num
      · obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 hy
        exact mul_pos (hc _) (boundedDist_pos (hδ a))
    · intro Q hQ
      refine hIu ?_
      intro a ha
      refine hball a ha ?_
      rw [Metric.mem_ball, dist_comm]
      refine dist_lt_of_blockDist_lt hc hsum (hkk a) (hδ a) (lt_of_lt_of_le hQ ?_)
      exact Finset.min'_le _ _ (Finset.mem_insert_of_mem
        (Finset.mem_image_of_mem _ (by exact_mod_cast ha)))
  · intro h
    rw [isOpen_iff_mem_nhds]
    intro P hP
    obtain ⟨ε, hε, hεs⟩ := h P hP
    have htend := tendsto_tsum_compl_atTop_zero (fun k => c k * ((blk k).card : ℝ))
    obtain ⟨T, hT⟩ := (htend.eventually_lt_const (by positivity : (0:ℝ) < ε / 2)).exists
    set M : ℝ := ∑ k ∈ T, c k * ((blk k).card : ℝ) with hM
    have hM0 : 0 ≤ M := Finset.sum_nonneg fun k _ =>
      mul_nonneg (hc k).le (by positivity)
    set δ : ℝ := ε / (2 * (M + 1)) with hδdef
    have hδ : 0 < δ := by positivity
    refine mem_nhds_iff.2 ⟨(↑(T.biUnion blk) : Set ι).pi (fun i => Metric.ball (P i) δ), ?_, ?_, ?_⟩
    · intro Q hQ
      refine hεs Q ?_
      have hhead : ∑ k ∈ T, c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i))
          ≤ boundedDist δ * M := by
        rw [hM, Finset.mul_sum]
        refine Finset.sum_le_sum fun k hk => ?_
        have hin : ∀ i ∈ blk k, boundedDist (dist (P i) (Q i)) ≤ boundedDist δ := by
          intro i hi
          have hmem : i ∈ T.biUnion blk := Finset.mem_biUnion.2 ⟨k, hk, hi⟩
          have := hQ i (Finset.mem_coe.2 hmem)
          rw [Metric.mem_ball, dist_comm] at this
          exact boundedDist_mono dist_nonneg this.le
        calc c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i))
            ≤ c k * ∑ _i ∈ blk k, boundedDist δ :=
              mul_le_mul_of_nonneg_left (Finset.sum_le_sum hin) (hc k).le
          _ = boundedDist δ * (c k * ((blk k).card : ℝ)) := by
              rw [Finset.sum_const, nsmul_eq_mul]; ring
      have htail : ∑' k : { x // x ∉ T }, c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i))
          ≤ ∑' k : { x // x ∉ T }, c k * ((blk k).card : ℝ) := by
        refine Summable.tsum_le_tsum (fun k => ?_) ?_ ?_
        · exact blockDist_term_le (fun k => (hc k).le) P Q k
        · exact (blockDist_summable (fun k => (hc k).le) hsum P Q).subtype _
        · exact hsum.subtype _
      have hsplit : blockDist blk c P Q
          = (∑ k ∈ T, c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)))
            + ∑' k : { x // x ∉ T }, c k * ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) := by
        rw [blockDist]
        exact ((blockDist_summable (fun k => (hc k).le) hsum P Q).sum_add_tsum_compl).symm
      have hbd : boundedDist δ * M < ε / 2 := by
        have h1 : boundedDist δ ≤ δ := boundedDist_le_self hδ.le
        have h2 : boundedDist δ * M ≤ δ * M := by nlinarith
        have h3 : δ * M < ε / 2 := by
          rw [hδdef]
          rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by norm_num)]
          nlinarith
        linarith
      rw [hsplit]
      linarith [hT]
    · exact isOpen_set_pi (Finset.finite_toSet _) fun i _ => Metric.isOpen_ball
    · intro i _
      simp [hδ]


/-- A permutation of the index set preserving every block acts by isometries. -/
theorem blockDist_congr_equiv (σ : ι ≃ ι) (hσ : ∀ k, (blk k).map σ.toEmbedding = blk k)
    (P Q : ι → C) : blockDist blk c (P ∘ σ) (Q ∘ σ) = blockDist blk c P Q := by
  refine tsum_congr fun k => ?_
  congr 1
  calc ∑ i ∈ blk k, boundedDist (dist ((P ∘ σ) i) ((Q ∘ σ) i))
      = ∑ i ∈ (blk k).map σ.toEmbedding, boundedDist (dist (P i) (Q i)) :=
        (Finset.sum_map (blk k) σ.toEmbedding
          (fun x => boundedDist (dist (P x) (Q x)))).symm
    _ = ∑ i ∈ blk k, boundedDist (dist (P i) (Q i)) := by rw [hσ k]

/-- **Deninger, Proposition 7.6 (`t86`), the metric.**  The block-weighted distance is a metric
whose topology is the product topology. -/
@[implicit_reducible]
noncomputable def blockMetricSpace (hc : ∀ k, 0 < c k)
    (hsum : Summable fun k => c k * ((blk k).card : ℝ)) (hcov : ∀ i, ∃ k, i ∈ blk k) :
    MetricSpace (ι → C) :=
  MetricSpace.ofDistTopology (blockDist blk c) blockDist_self blockDist_comm
    (blockDist_triangle (fun k => (hc k).le) hsum)
    (blockDist_isOpen_iff hc hsum hcov)
    (fun _ _ h => eq_of_blockDist_eq_zero hc hsum hcov h)

end Block

section Weights

variable {ι κ : Type*} [Countable κ]

/-- Positive weights making the block sum finite always exist for a countable index set. -/
theorem exists_blockWeights (blk : κ → Finset ι) :
    ∃ c : κ → ℝ, (∀ k, 0 < c k) ∧ Summable fun k => c k * ((blk k).card : ℝ) := by
  obtain ⟨j, hj⟩ := Countable.exists_injective_nat κ
  refine ⟨fun k => (1 / 2 : ℝ) ^ (j k) / (((blk k).card : ℝ) + 1), fun k => ?_, ?_⟩
  · positivity
  · have hgeom : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
      summable_geometric_of_lt_one (by norm_num) (by norm_num)
    have hcomp : Summable fun k : κ => (1 / 2 : ℝ) ^ (j k) := hgeom.comp_injective hj
    refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_) hcomp
    · positivity
    · rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      have h1 : ((blk k).card : ℝ) ≤ ((blk k).card : ℝ) + 1 := by linarith
      have h2 : (0 : ℝ) < (1 / 2 : ℝ) ^ (j k) := by positivity
      nlinarith

end Weights

/-! ### Transport along an inducing map -/

section Induced

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- A distance on `Y` inducing its topology induces, along an inducing map `f : X → Y`, the
topology of `X`. -/
theorem isOpen_iff_of_isInducing {f : X → Y} (hf : Topology.IsInducing f) (dY : Y → Y → ℝ)
    (htri : ∀ a b c, dY a c ≤ dY a b + dY b c)
    (hself : ∀ y, dY y y = 0)
    (hY : ∀ t : Set Y, IsOpen t ↔ ∀ y ∈ t, ∃ ε > 0, ∀ z, dY y z < ε → z ∈ t)
    (s : Set X) :
    IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, ∀ z, dY (f x) (f z) < ε → z ∈ s := by
  have hball : ∀ (y₀ : Y) (r : ℝ), IsOpen {y | dY y₀ y < r} := by
    intro y₀ r
    refine (hY _).2 fun y hy => ⟨r - dY y₀ y, by simpa using hy, fun z hz => ?_⟩
    have := htri y₀ y z
    simp only [Set.mem_setOf_eq] at hy ⊢
    linarith
  constructor
  · intro hs x hx
    obtain ⟨t, ht, rfl⟩ := hf.isOpen_iff.1 hs
    obtain ⟨ε, hε, hεt⟩ := (hY t).1 ht (f x) hx
    exact ⟨ε, hε, fun z hz => hεt _ hz⟩
  · intro h
    have h' : ∀ x : (s : Set X), ∃ ε : ℝ, 0 < ε ∧ ∀ z, dY (f x.1) (f z) < ε → z ∈ s :=
      fun x => h x.1 x.2
    choose ε hε hεs using h'
    refine hf.isOpen_iff.2 ⟨⋃ x : (s : Set X), {y | dY (f x.1) y < ε x}, ?_, ?_⟩
    · exact isOpen_iUnion fun x => hball _ _
    · ext z
      simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_setOf_eq]
      constructor
      · rintro ⟨x, hz⟩
        exact hεs x z hz
      · intro hz
        exact ⟨⟨z, hz⟩, by rw [hself]; exact hε ⟨z, hz⟩⟩

end Induced

end HTGeometry
