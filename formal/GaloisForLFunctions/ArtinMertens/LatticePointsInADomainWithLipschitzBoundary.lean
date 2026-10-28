import Mathlib

/-!
# Lattice points in a domain with a Lipschitz boundary

For a lattice `Λ` in a finite-dimensional real normed space `E` and a bounded measurable set `Y`,
`|#(Y ∩ Λ)·covol(Λ) − vol Y| ≤ vol((∂Y)_d)`, where `(∂Y)_d` is the closed `d`-thickening of the
frontier and `d` bounds the norms in a fundamental cell (`abs_ncard_mul_covolume_sub_le`). If `∂Y`
is covered by finitely many `M`-Lipschitz images of faces of the unit cube `[0,1]^ι` with
`card ι = dim E = n`, then `|#(tY ∩ Λ)·covol(Λ) − tⁿ vol Y| ≤ C tⁿ⁻¹` for `t ≥ 1`
(`exists_abs_ncard_smul_sub_le`).

* **Crossing** (`isPreconnected_inter_frontier_nonempty`, `exists_frontier_near`): a segment from a
  point of `Y` to a point outside meets `∂Y`. So the cell of a lattice point of `Y` lies in
  `Y ∪ (∂Y)_d`, and a point of `Y` farther than `d` from `∂Y` lies in the cell of a lattice point
  of `Y`; the cells are disjoint translates of volume `covol(Λ)`.
* **Thin boundary** (`measureReal_cthickening_iUnion_image_cubeFace_le`): the `ε`-thickening of the
  image of a cube face under an `M`-Lipschitz map is covered by `(⌈M/ε⌉ + 2)^{n−1}` balls of radius
  `3ε`, centred at the images of a grid of spacing `≤ ε/M`; its volume is `O(ε)`.
-/

noncomputable section

open MeasureTheory Metric Set Bornology Module
open scoped Pointwise NNReal

namespace GaloisForLFunctions.ArtinMertens

/-- **Crossing**: a preconnected set meeting `t` and its complement meets the frontier of `t`. -/
theorem isPreconnected_inter_frontier_nonempty {α : Type*} [TopologicalSpace α] {s t : Set α}
    (hs : IsPreconnected s) (h₁ : (s ∩ t).Nonempty) (h₂ : (s \ t).Nonempty) :
    (s ∩ frontier t).Nonempty := by
  by_contra h
  rw [not_nonempty_iff_eq_empty] at h
  have hnf : ∀ x ∈ s, x ∉ frontier t := fun x hx hf => by
    have : x ∈ s ∩ frontier t := ⟨hx, hf⟩
    rw [h] at this
    exact this
  have hsub : s ⊆ interior t ∪ (closure t)ᶜ := by
    intro x hx
    by_cases hxi : x ∈ interior t
    · exact Or.inl hxi
    · exact Or.inr fun hcl => hnf x hx ⟨hcl, hxi⟩
  obtain ⟨a, has, hat⟩ := h₁
  obtain ⟨b, hbs, hbt⟩ := h₂
  have ha : a ∈ interior t := by
    by_contra hai
    exact hnf a has ⟨subset_closure hat, hai⟩
  have hb : b ∈ (closure t)ᶜ := by
    rcases hsub hbs with hbi | hbc
    · exact absurd (interior_subset hbi) hbt
    · exact hbc
  obtain ⟨x, -, hx₁, hx₂⟩ := hs _ _ isOpen_interior isClosed_closure.isOpen_compl hsub
    ⟨a, has, ha⟩ ⟨b, hbs, hb⟩
  exact hx₂ (subset_closure (interior_subset hx₁))

/-- The segment from `a ∈ Y` to `b ∉ Y` meets `∂Y` within `dist a b` of both ends. -/
theorem exists_frontier_near {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {Y : Set E}
    {a b : E} (ha : a ∈ Y) (hb : b ∉ Y) :
    ∃ z ∈ frontier Y, dist a z ≤ dist a b ∧ dist b z ≤ dist a b := by
  obtain ⟨z, hzs, hzf⟩ := isPreconnected_inter_frontier_nonempty (convex_segment a b).isPreconnected
    ⟨a, left_mem_segment ℝ a b, ha⟩ ⟨b, right_mem_segment ℝ a b, hb⟩
  refine ⟨z, hzf, ?_, ?_⟩
  · have h := (convex_closedBall a (dist a b)).segment_subset (mem_closedBall_self dist_nonneg)
      (mem_closedBall.mpr (dist_comm b a).le) hzs
    rw [dist_comm]
    exact mem_closedBall.mp h
  · have h := (convex_closedBall b (dist a b)).segment_subset (mem_closedBall.mpr le_rfl)
      (mem_closedBall_self dist_nonneg) hzs
    rw [dist_comm]
    exact mem_closedBall.mp h

section Counting

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- The fundamental cell `{Σ aᵢbᵢ : aᵢ ∈ [0,1)}` of a chosen basis of `L`. -/
def latticeCell : Set E :=
  ZSpan.fundamentalDomain ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)

omit [MeasurableSpace E] [BorelSpace E] in
theorem isBounded_latticeCell : IsBounded (latticeCell L) := ZSpan.fundamentalDomain_isBounded _

theorem measurableSet_latticeCell : MeasurableSet (latticeCell L) :=
  ZSpan.fundamentalDomain_measurableSet _

theorem covolume_eq_measureReal_latticeCell :
    ZLattice.covolume L μ = μ.real (latticeCell L) :=
  ZLattice.covolume_eq_measure_fundamentalDomain L μ (ZLattice.isAddFundamentalDomain _ μ)

omit [MeasurableSpace E] [BorelSpace E] in
theorem span_latticeBasis :
    Submodule.span ℤ (range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) = L := by
  rw [Module.Basis.ofZLatticeBasis_span]

omit [MeasurableSpace E] [BorelSpace E] in
/-- Every point lies in the cell of some lattice point. -/
theorem exists_sub_mem_latticeCell (x : E) : ∃ v ∈ L, x - v ∈ latticeCell L := by
  obtain ⟨v, hv, -⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) x
  have hvL : (v : E) ∈ L := (span_latticeBasis L).le v.2
  refine ⟨-(v : E), L.neg_mem hvL, ?_⟩
  rw [sub_neg_eq_add, add_comm]
  exact hv

omit [MeasurableSpace E] [BorelSpace E] in
/-- The cells of distinct lattice points are disjoint. -/
theorem eq_of_sub_mem_latticeCell {x v w : E} (hv : v ∈ L) (hw : w ∈ L)
    (hxv : x - v ∈ latticeCell L) (hxw : x - w ∈ latticeCell L) : v = w := by
  have hv' : -v ∈ Submodule.span ℤ (range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [span_latticeBasis]
    exact L.neg_mem hv
  have hw' : -w ∈ Submodule.span ℤ (range ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L)) := by
    rw [span_latticeBasis]
    exact L.neg_mem hw
  obtain ⟨u, -, hu⟩ := ZSpan.exist_unique_vadd_mem_fundamentalDomain
    ((Module.Free.chooseBasis ℤ L).ofZLatticeBasis ℝ L) x
  have h₁ := hu ⟨-v, hv'⟩ (by
    change -v + x ∈ latticeCell L
    rwa [neg_add_eq_sub])
  have h₂ := hu ⟨-w, hw'⟩ (by
    change -w + x ∈ latticeCell L
    rwa [neg_add_eq_sub])
  have := congrArg Subtype.val (h₁.trans h₂.symm)
  simpa using this

omit [MeasurableSpace E] [BorelSpace E] [IsZLattice ℝ L] in
theorem finite_inter_lattice {Y : Set E} (hY : IsBounded Y) : (Y ∩ (L : Set E)).Finite :=
  Metric.finite_isBounded_inter_isClosed
    (isDiscrete_iff_discreteTopology.mpr ‹DiscreteTopology L›) hY
    (AddSubgroup.isClosed_of_discrete (H := L.toAddSubgroup))

/-- **Lattice points versus volume**: if the cell of `L` lies in `closedBall 0 d`, then for every
bounded measurable `Y`, `|#(Y ∩ L)·covol(L) − vol Y| ≤ vol((∂Y)_d)`. -/
theorem abs_ncard_mul_covolume_sub_le {d : ℝ} (hd : latticeCell L ⊆ closedBall 0 d) {Y : Set E}
    (hY : IsBounded Y) :
    |((Y ∩ (L : Set E)).ncard : ℝ) * ZLattice.covolume L μ - μ.real Y| ≤
      μ.real (cthickening d (frontier Y)) := by
  rw [ncard_eq_toFinset_card _ (finite_inter_lattice L hY)]
  set A := (finite_inter_lattice L hY).toFinset with hA
  set F := latticeCell L with hFdef
  have hF : MeasurableSet F := measurableSet_latticeCell L
  have hFfin : μ F ≠ ⊤ := (isBounded_latticeCell L).measure_lt_top.ne
  have hT : IsBounded (cthickening d (frontier Y)) :=
    (hY.closure.subset frontier_subset_closure).cthickening
  have hTfin : μ (cthickening d (frontier Y)) ≠ ⊤ := hT.measure_lt_top.ne
  have hmemA : ∀ v, v ∈ A ↔ v ∈ Y ∧ v ∈ L := fun v => by simp [hA]
  have hnorm : ∀ {x v : E}, x - v ∈ F → dist x v ≤ d := fun h => by
    rw [dist_eq_norm]
    exact mem_closedBall_zero_iff.mp (hd h)
  have hmem : ∀ {v x : E}, x ∈ v +ᵥ F ↔ x - v ∈ F := fun {v x} => by
    rw [mem_vadd_set_iff_neg_vadd_mem, vadd_eq_add, neg_add_eq_sub]
  have hsum : ∑ v ∈ A, μ.real (v +ᵥ F) = A.card * μ.real F := by
    rw [Finset.sum_congr rfl fun v _ => by rw [measureReal_def, measure_vadd, ← measureReal_def],
      Finset.sum_const, nsmul_eq_mul]
  -- the cells of the lattice points of `Y` lie in `Y ∪ (∂Y)_d`
  have hsub : (⋃ v ∈ A, v +ᵥ F) ⊆ Y ∪ cthickening d (frontier Y) := by
    intro x hx
    simp only [mem_iUnion] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    by_cases hxY : x ∈ Y
    · exact Or.inl hxY
    · right
      obtain ⟨z, hz, -, hxz⟩ := exists_frontier_near ((hmemA v).mp hv).1 hxY
      exact mem_cthickening_of_dist_le x z d _ hz
        (hxz.trans ((dist_comm v x).le.trans (hnorm (hmem.mp hxv))))
  have hUfin : μ (Y ∪ cthickening d (frontier Y)) ≠ ⊤ :=
    (measure_union_lt_top hY.measure_lt_top hT.measure_lt_top).ne
  rw [abs_sub_le_iff, covolume_eq_measureReal_latticeCell, ← hFdef, ← hsum]
  constructor
  · -- the cells are disjoint
    have hdisj : (A : Set E).PairwiseDisjoint fun v => v +ᵥ F := by
      intro v hv w hw hvw
      rw [Function.onFun, Set.disjoint_left]
      intro x hxv hxw
      exact hvw (eq_of_sub_mem_latticeCell L ((hmemA v).mp hv).2 ((hmemA w).mp hw).2
        (hmem.mp hxv) (hmem.mp hxw))
    have h₁ : ∑ v ∈ A, μ.real (v +ᵥ F) ≤ μ.real Y + μ.real (cthickening d (frontier Y)) := by
      rw [← measureReal_biUnion_finset hdisj (fun v _ => hF.const_vadd v)
        (fun v _ => by rw [measure_vadd]; exact hFfin)]
      exact (measureReal_mono hsub hUfin).trans (measureReal_union_le _ _)
    linarith
  · -- a point of `Y` farther than `d` from `∂Y` lies in the cell of a lattice point of `Y`
    have hsub₂ : Y \ cthickening d (frontier Y) ⊆ ⋃ v ∈ A, v +ᵥ F := by
      rintro y ⟨hyY, hyT⟩
      obtain ⟨v, hvL, hyv⟩ := exists_sub_mem_latticeCell L y
      have hvY : v ∈ Y := by
        by_contra hvY
        obtain ⟨z, hz, hyz, -⟩ := exists_frontier_near hyY hvY
        exact hyT (mem_cthickening_of_dist_le y z d _ hz (hyz.trans (hnorm hyv)))
      simp only [mem_iUnion]
      exact ⟨v, (hmemA v).mpr ⟨hvY, hvL⟩, hmem.mpr hyv⟩
    have h₂ := le_measureReal_sdiff (μ := μ) (s₁ := Y) hTfin
    have h₃ := measureReal_mono hsub₂ (ne_top_of_le_ne_top hUfin (measure_mono hsub))
    have h₄ := measureReal_biUnion_finset_le (μ := μ) A fun v => v +ᵥ F
    linarith

end Counting

section ThinBoundary

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]

/-- The face `{y ∈ [0,1]^ι : y i₀ = c}` of the unit cube. -/
def cubeFace {ι : Type*} (i₀ : ι) (c : ℝ) : Set (ι → ℝ) := Icc 0 1 ∩ {y | y i₀ = c}

/-- The grid of spacing `1/N` on a cube face. -/
def faceGrid {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (c : ℝ) (N : ℕ) :
    Finset (ι → ℝ) :=
  (Fintype.piFinset fun i => if i = i₀ then ({0} : Finset ℕ) else Finset.range (N + 1)).image
    fun k i => if i = i₀ then c else (k i : ℝ) / N

theorem card_faceGrid_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (c : ℝ) (N : ℕ) :
    (faceGrid i₀ c N).card ≤ (N + 1) ^ (Fintype.card ι - 1) := by
  refine Finset.card_image_le.trans (le_of_eq ?_)
  rw [Fintype.card_piFinset, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i₀)]
  simp only [↓reduceIte, Finset.card_singleton, one_mul]
  rw [Finset.prod_congr rfl fun i hi => by rw [if_neg (Finset.ne_of_mem_erase hi),
    Finset.card_range], Finset.prod_const, Finset.card_erase_of_mem (Finset.mem_univ _),
    Finset.card_univ]

/-- Every point of a face is within `1/N` of a grid point of the face. -/
theorem exists_faceGrid_near {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι} {c : ℝ}
    (hc : c ∈ Icc (0 : ℝ) 1) {N : ℕ} (hN : 0 < N) {y : ι → ℝ} (hy : y ∈ cubeFace i₀ c) :
    ∃ g ∈ faceGrid i₀ c N, g ∈ Icc 0 1 ∧ dist y g ≤ 1 / N := by
  obtain ⟨⟨hy0, hy1⟩, hyc⟩ := hy
  have hy0' : ∀ i, 0 ≤ y i := fun i => hy0 i
  have hy1' : ∀ i, y i ≤ 1 := fun i => hy1 i
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : ∀ i, ⌊(N : ℝ) * y i⌋₊ ≤ N := fun i =>
    Nat.floor_le_of_le (by nlinarith [hy0' i, hy1' i])
  refine ⟨fun i => if i = i₀ then c else (⌊(N : ℝ) * y i⌋₊ : ℝ) / N, ?_, ⟨fun i => ?_, fun i => ?_⟩,
    ?_⟩
  · refine Finset.mem_image.mpr ⟨fun i => if i = i₀ then 0 else ⌊(N : ℝ) * y i⌋₊,
      Fintype.mem_piFinset.mpr fun i => ?_, ?_⟩
    · by_cases hi : i = i₀
      · simp [hi]
      · simp only [if_neg hi, Finset.mem_range]
        exact Nat.lt_succ_of_le (hk i)
    · funext i
      by_cases hi : i = i₀ <;> simp [hi]
  · by_cases hi : i = i₀
    · simp only [Pi.zero_apply, if_pos hi]
      exact hc.1
    · simp only [Pi.zero_apply, if_neg hi]
      positivity
  · by_cases hi : i = i₀
    · simp only [Pi.one_apply, if_pos hi]
      exact hc.2
    · simp only [Pi.one_apply, if_neg hi]
      rw [div_le_one hN']
      exact_mod_cast hk i
  · rw [dist_pi_le_iff (by positivity)]
    intro i
    by_cases hi : i = i₀
    · simp only [if_pos hi]
      rw [hi, hyc, dist_self]
      positivity
    · simp only [if_neg hi, Real.dist_eq]
      have h₁ := Nat.floor_le (mul_nonneg hN'.le (hy0' i))
      have h₂ := Nat.lt_floor_add_one ((N : ℝ) * y i)
      have hlo : (⌊(N : ℝ) * y i⌋₊ : ℝ) / N ≤ y i := by
        rw [div_le_iff₀ hN']
        linarith
      have hhi : y i - (⌊(N : ℝ) * y i⌋₊ : ℝ) / N ≤ 1 / N := by
        rw [sub_le_iff_le_add, ← add_div, le_div_iff₀ hN']
        linarith
      rw [abs_sub_le_iff]
      exact ⟨hhi, by linarith [one_div_nonneg.mpr hN'.le]⟩

/-- **Thin boundary**: the `ε`-thickening of finitely many `M`-Lipschitz images of cube faces has
volume at most `#J (⌈M/ε⌉ + 2)^{card ι − 1} vol(B(0, 3ε))`. -/
theorem measureReal_cthickening_iUnion_image_cubeFace_le {ι J : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype J] {φ : J → (ι → ℝ) → E} {M : ℝ≥0} (hφ : ∀ j, LipschitzOnWith M (φ j) (Icc 0 1))
    (i₀ : J → ι) {c : J → ℝ} (hc : ∀ j, c j ∈ Icc (0 : ℝ) 1) {ε : ℝ} (hε : 0 < ε) :
    μ.real (cthickening ε (⋃ j, φ j '' cubeFace (i₀ j) (c j))) ≤
      Fintype.card J * ((⌈(M : ℝ) / ε⌉₊ + 2 : ℕ) : ℝ) ^ (Fintype.card ι - 1) *
        μ.real (closedBall (0 : E) (3 * ε)) := by
  classical
  set N := ⌈(M : ℝ) / ε⌉₊ + 1 with hNdef
  have hN : 0 < N := Nat.succ_pos _
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hMN : (M : ℝ) / N ≤ ε := by
    rw [div_le_iff₀ hN']
    have h := Nat.le_ceil ((M : ℝ) / ε)
    rw [div_le_iff₀ hε] at h
    have : (⌈(M : ℝ) / ε⌉₊ : ℝ) ≤ N := by
      rw [hNdef]
      push_cast
      linarith
    nlinarith
  -- the centres: images of the face grids
  set T : Finset E := Finset.univ.biUnion fun j => (faceGrid (i₀ j) (c j) N).image (φ j)
  have hTcard : (T.card : ℝ) ≤ Fintype.card J * ((N + 1 : ℕ) : ℝ) ^ (Fintype.card ι - 1) := by
    have h : T.card ≤ Fintype.card J * (N + 1) ^ (Fintype.card ι - 1) := by
      refine Finset.card_biUnion_le.trans ?_
      calc ∑ j, ((faceGrid (i₀ j) (c j) N).image (φ j)).card
          ≤ ∑ _j : J, (N + 1) ^ (Fintype.card ι - 1) :=
            Finset.sum_le_sum fun j _ => Finset.card_image_le.trans (card_faceGrid_le _ _ _)
        _ = Fintype.card J * (N + 1) ^ (Fintype.card ι - 1) := by
            rw [Finset.sum_const, Finset.card_univ, smul_eq_mul]
    exact_mod_cast h
  have hcover : cthickening ε (⋃ j, φ j '' cubeFace (i₀ j) (c j)) ⊆
      ⋃ e ∈ T, closedBall e (3 * ε) := by
    intro x hx
    have hx' := cthickening_subset_iUnion_closedBall_of_lt _ (by positivity : 0 < 2 * ε)
      (by linarith) hx
    simp only [mem_iUnion] at hx' ⊢
    obtain ⟨z, ⟨j, y, hy, rfl⟩, hxz⟩ := hx'
    obtain ⟨g, hgG, hgI, hyg⟩ := exists_faceGrid_near (hc j) hN hy
    refine ⟨φ j g, Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, Finset.mem_image_of_mem _ hgG⟩, ?_⟩
    have hlip := (hφ j).dist_le_mul y hy.1 g hgI
    rw [mem_closedBall] at hxz ⊢
    calc dist x (φ j g) ≤ dist x (φ j y) + dist (φ j y) (φ j g) := dist_triangle _ _ _
      _ ≤ 2 * ε + M * (1 / N) := add_le_add hxz (hlip.trans
          (mul_le_mul_of_nonneg_left hyg M.2))
      _ ≤ 3 * ε := by rw [mul_one_div]; linarith
  have hballs : μ (⋃ e ∈ T, closedBall e (3 * ε)) ≠ ⊤ :=
    ((measure_biUnion_finset_le T _).trans_lt
      (ENNReal.sum_lt_top.mpr fun e _ => measure_closedBall_lt_top)).ne
  calc μ.real (cthickening ε (⋃ j, φ j '' cubeFace (i₀ j) (c j)))
      ≤ μ.real (⋃ e ∈ T, closedBall e (3 * ε)) := measureReal_mono hcover hballs
    _ ≤ ∑ e ∈ T, μ.real (closedBall e (3 * ε)) := measureReal_biUnion_finset_le _ _
    _ = T.card * μ.real (closedBall (0 : E) (3 * ε)) := by
        rw [Finset.sum_congr rfl fun e _ => by
          rw [measureReal_def, Measure.addHaar_closedBall_center, ← measureReal_def],
          Finset.sum_const, nsmul_eq_mul]
    _ ≤ Fintype.card J * ((N + 1 : ℕ) : ℝ) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * ε)) :=
        mul_le_mul_of_nonneg_right hTcard measureReal_nonneg
    _ = Fintype.card J * ((⌈(M : ℝ) / ε⌉₊ + 2 : ℕ) : ℝ) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * ε)) := by
        rw [hNdef]

end ThinBoundary

section Dilates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  (L : Submodule ℤ E) [DiscreteTopology L] [IsZLattice ℝ L]

/-- **Lattice points in dilates of a domain with Lipschitz boundary**: if `∂Y` is covered by
finitely many `M`-Lipschitz images of faces of `[0,1]^ι`, `card ι = n = dim E`, then
`|#(tY ∩ L)·covol(L) − tⁿ vol Y| ≤ C tⁿ⁻¹` for all `t ≥ 1`. -/
theorem exists_abs_ncard_smul_sub_le {ι J : Type*} [Fintype ι] [DecidableEq ι] [Fintype J]
    (hι : Fintype.card ι = finrank ℝ E) {φ : J → (ι → ℝ) → E} {M : ℝ≥0}
    (hφ : ∀ j, LipschitzOnWith M (φ j) (Icc 0 1)) (i₀ : J → ι) {c : J → ℝ}
    (hc : ∀ j, c j ∈ Icc (0 : ℝ) 1) {Y : Set E} (hY : IsBounded Y)
    (hfr : frontier Y ⊆ ⋃ j, φ j '' cubeFace (i₀ j) (c j)) :
    ∃ C : ℝ, ∀ t : ℝ, 1 ≤ t →
      |(((t • Y) ∩ (L : Set E)).ncard : ℝ) * ZLattice.covolume L μ -
          t ^ finrank ℝ E * μ.real Y| ≤ C * t ^ (finrank ℝ E - 1) := by
  obtain ⟨d₀, hd₀⟩ := (isBounded_latticeCell L).subset_closedBall 0
  set d := max d₀ 1 with hd
  have hd1 : 1 ≤ d := le_max_right _ _
  have hdpos : 0 < d := by linarith
  have hcell : latticeCell L ⊆ closedBall 0 d := hd₀.trans (closedBall_subset_closedBall
    (le_max_left _ _))
  refine ⟨Fintype.card J * ((M : ℝ) / d + 3) ^ (Fintype.card ι - 1) *
    μ.real (closedBall (0 : E) (3 * d)), fun t ht => ?_⟩
  have ht0 : 0 < t := by linarith
  -- scaling `Y`: volume `tⁿ vol Y`, frontier `t • ∂Y`
  have hvol : μ.real (t • Y) = t ^ finrank ℝ E * μ.real Y := by
    rw [measureReal_def, Measure.addHaar_smul, ENNReal.toReal_mul, ENNReal.toReal_ofReal
      (abs_nonneg _), abs_of_nonneg (pow_nonneg ht0.le _), ← measureReal_def]
  have hfrt : frontier (t • Y) ⊆ ⋃ j, (fun y => t • φ j y) '' cubeFace (i₀ j) (c j) := by
    have h := (Homeomorph.smulOfNeZero t ht0.ne').image_frontier Y
    rw [show ((Homeomorph.smulOfNeZero t ht0.ne') : E → E) '' Y = t • Y from rfl] at h
    rw [← h]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨j, y, hy, rfl⟩ := mem_iUnion.mp (hfr hz)
    exact mem_iUnion.mpr ⟨j, y, hy, rfl⟩
  have hlipt : ∀ j, LipschitzOnWith (⟨t, ht0.le⟩ * M) (fun y => t • φ j y) (Icc 0 1) := by
    intro j
    refine LipschitzOnWith.of_dist_le_mul fun a ha b hb => ?_
    rw [dist_smul₀, Real.norm_eq_abs, abs_of_pos ht0, NNReal.coe_mul]
    calc t * dist (φ j a) (φ j b) ≤ t * (M * dist a b) :=
          mul_le_mul_of_nonneg_left ((hφ j).dist_le_mul a ha b hb) ht0.le
      _ = _ := (mul_assoc t (M : ℝ) (dist a b)).symm
  have hthick := measureReal_cthickening_iUnion_image_cubeFace_le μ hlipt i₀ hc hdpos
  have hbdd : IsBounded (⋃ j, (fun y => t • φ j y) '' cubeFace (i₀ j) (c j)) := by
    refine isBounded_iUnion.mpr fun j => ?_
    exact ((isCompact_Icc.inter_right (isClosed_eq (continuous_apply (i₀ j))
      continuous_const)).image_of_continuousOn
      ((hlipt j).continuousOn.mono inter_subset_left)).isBounded
  have hTfin : μ (cthickening d (⋃ j, (fun y => t • φ j y) '' cubeFace (i₀ j) (c j))) ≠ ⊤ :=
    hbdd.cthickening.measure_lt_top.ne
  have hA := abs_ncard_mul_covolume_sub_le μ L hcell (hY.smul₀ t)
  rw [hvol] at hA
  -- `⌈tM/d⌉ + 2 ≤ t (M/d + 3)` for `t ≥ 1`
  have hceil : ((⌈((⟨t, ht0.le⟩ * M : ℝ≥0) : ℝ) / d⌉₊ + 2 : ℕ) : ℝ) ≤ t * ((M : ℝ) / d + 3) := by
    have h := Nat.ceil_lt_add_one (div_nonneg (NNReal.coe_nonneg (⟨t, ht0.le⟩ * M)) hdpos.le)
    have hMd : 0 ≤ (M : ℝ) / d := div_nonneg M.2 hdpos.le
    have hmul : ((⟨t, ht0.le⟩ * M : ℝ≥0) : ℝ) / d = t * ((M : ℝ) / d) := by
      rw [NNReal.coe_mul]
      exact mul_div_assoc t (M : ℝ) d
    rw [hmul] at h
    rw [Nat.cast_add, Nat.cast_ofNat, hmul]
    nlinarith
  calc |(((t • Y) ∩ (L : Set E)).ncard : ℝ) * ZLattice.covolume L μ -
          t ^ finrank ℝ E * μ.real Y|
      ≤ μ.real (cthickening d (frontier (t • Y))) := hA
    _ ≤ μ.real (cthickening d (⋃ j, (fun y => t • φ j y) '' cubeFace (i₀ j) (c j))) :=
        measureReal_mono (cthickening_subset_of_subset d hfrt) hTfin
    _ ≤ _ := hthick
    _ ≤ Fintype.card J * (t * ((M : ℝ) / d + 3)) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * d)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (Nat.cast_nonneg _) hceil _) (Nat.cast_nonneg _)) measureReal_nonneg
    _ = Fintype.card J * ((M : ℝ) / d + 3) ^ (Fintype.card ι - 1) *
          μ.real (closedBall (0 : E) (3 * d)) * t ^ (finrank ℝ E - 1) := by
        rw [mul_pow, hι]
        ring

end Dilates

end GaloisForLFunctions.ArtinMertens
