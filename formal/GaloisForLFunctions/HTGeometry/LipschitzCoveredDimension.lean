import GaloisForLFunctions.HTGeometry.PolynomialZeroSetDimension

/-!
# Sets covered by countably many Lipschitz images of a `k`-dimensional cube

A set covered by countably many Lipschitz images of subsets of `ℝ^k` has Hausdorff dimension at most
`k`.  Unlike Hausdorff dimension itself, this property behaves well under products, which is what a
parametric codimension count needs: a bad set of dimension `d` crossed with a parameter set of
dimension `e` still has dimension at most `d + e`, so a projection to a space of dimension larger
than `d + e` has dense complement.

The zero set of a nonzero polynomial is covered in this sense in dimension `card ι - 1`: on a region
where one partial derivative is bounded away from zero, forgetting the corresponding coordinate is
injective with Lipschitz inverse on the zero set.
-/

open MvPolynomial Set Filter Topology
open scoped ENNReal NNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A set covered by countably many Lipschitz images of subsets of `ℝ^k`. -/
def IsLipschitzCovered (k : ℕ) {X : Type*} [MetricSpace X] (s : Set X) : Prop :=
  ∃ (f : ℕ → (Fin k → ℝ) → X) (A : ℕ → Set (Fin k → ℝ)) (C : ℕ → NNReal),
    (∀ n, LipschitzOnWith (C n) (f n) (A n)) ∧ s ⊆ ⋃ n, f n '' A n

theorem IsLipschitzCovered.mono {k : ℕ} {X : Type*} [MetricSpace X] {s t : Set X}
    (hst : s ⊆ t) (ht : IsLipschitzCovered k t) : IsLipschitzCovered k s := by
  obtain ⟨f, A, C, hlip, hcov⟩ := ht
  exact ⟨f, A, C, hlip, hst.trans hcov⟩

theorem IsLipschitzCovered.dimH_le {k : ℕ} {X : Type*} [MetricSpace X] {s : Set X}
    (hs : IsLipschitzCovered k s) : dimH s ≤ (k : ENNReal) := by
  obtain ⟨f, A, C, hlip, hcov⟩ := hs
  refine le_trans (dimH_mono hcov) ?_
  rw [dimH_iUnion]
  refine iSup_le fun n => ?_
  refine le_trans ((hlip n).dimH_image_le) ?_
  refine le_trans (dimH_mono (Set.subset_univ _)) ?_
  rw [Real.dimH_univ_pi_fin]

theorem IsLipschitzCovered.iUnion {k : ℕ} {X : Type*} [MetricSpace X] {s : ℕ → Set X}
    (hs : ∀ n, IsLipschitzCovered k (s n)) : IsLipschitzCovered k (⋃ n, s n) := by
  classical
  choose f A C hlip hcov using hs
  set e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm.trans (Equiv.refl _) with he
  refine ⟨fun n => f (e n).1 (e n).2, fun n => A (e n).1 (e n).2, fun n => C (e n).1 (e n).2,
    fun n => hlip _ _, ?_⟩
  refine Set.iUnion_subset fun n => (hcov n).trans (Set.iUnion_subset fun m => ?_)
  refine Set.subset_iUnion_of_subset (e.symm (n, m)) ?_
  simp only [Equiv.apply_symm_apply]
  exact le_rfl

theorem IsLipschitzCovered.union {k : ℕ} {X : Type*} [MetricSpace X] {s t : Set X}
    (hs : IsLipschitzCovered k s) (ht : IsLipschitzCovered k t) :
    IsLipschitzCovered k (s ∪ t) := by
  have hall : ∀ n : ℕ, IsLipschitzCovered k (if n = 0 then s else t) := by
    intro n
    by_cases h : n = 0
    · rw [if_pos h]; exact hs
    · rw [if_neg h]; exact ht
  refine IsLipschitzCovered.mono ?_ (IsLipschitzCovered.iUnion hall)
  intro x hx
  rcases hx with hx | hx
  · exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
  · exact Set.mem_iUnion.mpr ⟨1, by simpa using hx⟩

theorem IsLipschitzCovered.image {k : ℕ} {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s : Set X} {g : X → Y} {D : NNReal} (hg : LipschitzOnWith D g s)
    (hs : IsLipschitzCovered k s) : IsLipschitzCovered k (g '' s) := by
  obtain ⟨f, A, C, hlip, hcov⟩ := hs
  refine ⟨fun n => g ∘ f n, fun n => A n ∩ (f n) ⁻¹' s, fun n => D * C n, fun n => ?_, ?_⟩
  · refine LipschitzOnWith.comp (t := s) ?_ ?_ ?_
    · exact hg
    · exact (hlip n).mono Set.inter_subset_left
    · intro u hu
      exact hu.2
  · rintro y ⟨x, hx, rfl⟩
    obtain ⟨-, ⟨n, rfl⟩, hxn⟩ := hcov hx
    obtain ⟨u, hu, rfl⟩ := hxn
    exact Set.mem_iUnion.mpr ⟨n, ⟨u, ⟨hu, hx⟩, rfl⟩⟩

/-- Any subset of a coordinate space of dimension at most `k` is covered in dimension `k`. -/
theorem isLipschitzCovered_pi {ι : Type} [Fintype ι] {k : ℕ} (hk : Fintype.card ι ≤ k)
    (s : Set (ι → ℝ)) : IsLipschitzCovered k s := by
  classical
  obtain ⟨e⟩ : Nonempty (ι ↪ Fin k) := by
    refine Function.Embedding.nonempty_of_card_le ?_
    simpa using hk
  refine ⟨fun _ => fun u => fun j => u (e j), fun _ => (fun u => fun j : ι => u (e j)) ⁻¹' s,
    fun _ => 1, fun _ => ?_, ?_⟩
  · refine LipschitzWith.lipschitzOnWith ?_
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [NNReal.coe_one, one_mul]
    refine (dist_pi_le_iff dist_nonneg).mpr fun j => ?_
    exact dist_le_pi_dist u v (e j)
  · intro x hx
    refine Set.mem_iUnion.mpr ⟨0, ?_⟩
    refine ⟨fun i => if h : ∃ j, e j = i then x h.choose else 0, ?_, ?_⟩
    · show (fun j : ι => _) ∈ s
      have hfun : (fun j : ι => dite (∃ j', e j' = e j) (fun h => x h.choose) fun _ => 0) = x := by
        funext j
        rw [dif_pos ⟨j, rfl⟩]
        congr 1
        exact e.injective (Exists.choose_spec (⟨j, rfl⟩ : ∃ j', e j' = e j))
      rw [hfun]
      exact hx
    · funext j
      show dite (∃ j', e j' = e j) (fun h => x h.choose) (fun _ => 0) = x j
      rw [dif_pos ⟨j, rfl⟩]
      congr 1
      exact e.injective (Exists.choose_spec (⟨j, rfl⟩ : ∃ j', e j' = e j))

theorem isLipschitzCovered_empty {k : ℕ} {X : Type*} [MetricSpace X] [Nonempty X] :
    IsLipschitzCovered k (∅ : Set X) :=
  ⟨fun _ _ => Classical.arbitrary X, fun _ => ∅, fun _ => 0,
    fun _ => LipschitzOnWith.of_dist_le_mul fun u hu => absurd hu (Set.notMem_empty u),
    Set.empty_subset _⟩

theorem IsLipschitzCovered.iUnion_countable {k : ℕ} {X : Type*} [MetricSpace X] [Nonempty X]
    {ι : Type*} [Countable ι] {s : ι → Set X} (hs : ∀ i, IsLipschitzCovered k (s i)) :
    IsLipschitzCovered k (⋃ i, s i) := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine IsLipschitzCovered.mono ?_ (isLipschitzCovered_empty (k := k) (X := X))
    simp
  · obtain ⟨g, hg⟩ := exists_surjective_nat ι
    refine IsLipschitzCovered.mono ?_ (IsLipschitzCovered.iUnion (s := fun n => s (g n))
      fun n => hs (g n))
    refine Set.iUnion_subset fun i => ?_
    obtain ⟨n, rfl⟩ := hg i
    exact Set.subset_iUnion (fun n => s (g n)) n

/-! ### Products -/

theorem IsLipschitzCovered.prod {k l : ℕ} {X Y : Type*} [MetricSpace X] [MetricSpace Y]
    {s : Set X} {t : Set Y} (hs : IsLipschitzCovered k s) (ht : IsLipschitzCovered l t) :
    IsLipschitzCovered (k + l) (s ×ˢ t) := by
  classical
  obtain ⟨f, A, C, hlipf, hcovf⟩ := hs
  obtain ⟨g, B, D, hlipg, hcovg⟩ := ht
  set Ξ : (Fin (k + l) → ℝ) → (Fin k → ℝ) × (Fin l → ℝ) :=
    fun u => (fun i => u (Fin.castAdd l i), fun j => u (Fin.natAdd k j)) with hΞ
  have hΞlip : LipschitzWith 1 Ξ := by
    refine LipschitzWith.of_dist_le_mul fun u v => ?_
    rw [NNReal.coe_one, one_mul, Prod.dist_eq]
    refine max_le ?_ ?_
    · exact (dist_pi_le_iff dist_nonneg).mpr fun i => dist_le_pi_dist u v _
    · exact (dist_pi_le_iff dist_nonneg).mpr fun j => dist_le_pi_dist u v _
  set e : ℕ ≃ ℕ × ℕ := (Denumerable.eqv (ℕ × ℕ)).symm.trans (Equiv.refl _) with he
  refine ⟨fun n => (Prod.map (f (e n).1) (g (e n).2)) ∘ Ξ,
    fun n => Ξ ⁻¹' (A (e n).1 ×ˢ B (e n).2),
    fun n => max (C (e n).1) (D (e n).2), fun n => ?_, ?_⟩
  · refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
    have hΞd : dist (Ξ u) (Ξ v) ≤ dist u v := by
      have h1 := hΞlip.dist_le_mul u v
      rw [NNReal.coe_one, one_mul] at h1
      exact h1
    have hfst : dist (Ξ u).1 (Ξ v).1 ≤ dist u v :=
      le_trans (by rw [Prod.dist_eq]; exact le_max_left _ _) hΞd
    have hsnd : dist (Ξ u).2 (Ξ v).2 ≤ dist u v :=
      le_trans (by rw [Prod.dist_eq]; exact le_max_right _ _) hΞd
    have hmax : ((max (C (e n).1) (D (e n).2) : NNReal) : ℝ)
        = max ((C (e n).1 : ℝ)) ((D (e n).2 : ℝ)) := by
      push_cast
      rfl
    show dist (Prod.map (f (e n).1) (g (e n).2) (Ξ u))
      (Prod.map (f (e n).1) (g (e n).2) (Ξ v)) ≤ _
    rw [Prod.dist_eq, hmax]
    refine max_le ?_ ?_
    · calc dist (f (e n).1 (Ξ u).1) (f (e n).1 (Ξ v).1)
          ≤ (C (e n).1 : ℝ) * dist (Ξ u).1 (Ξ v).1 :=
            (hlipf (e n).1).dist_le_mul _ hu.1 _ hv.1
        _ ≤ (C (e n).1 : ℝ) * dist u v := mul_le_mul_of_nonneg_left hfst (by positivity)
        _ ≤ max ((C (e n).1 : ℝ)) ((D (e n).2 : ℝ)) * dist u v :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
    · calc dist (g (e n).2 (Ξ u).2) (g (e n).2 (Ξ v).2)
          ≤ (D (e n).2 : ℝ) * dist (Ξ u).2 (Ξ v).2 :=
            (hlipg (e n).2).dist_le_mul _ hu.2 _ hv.2
        _ ≤ (D (e n).2 : ℝ) * dist u v := mul_le_mul_of_nonneg_left hsnd (by positivity)
        _ ≤ max ((C (e n).1 : ℝ)) ((D (e n).2 : ℝ)) * dist u v :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  · rintro ⟨x, y⟩ ⟨hx, hy⟩
    obtain ⟨-, ⟨n, rfl⟩, a, ha, rfl⟩ := hcovf hx
    obtain ⟨-, ⟨m, rfl⟩, b, hb, rfl⟩ := hcovg hy
    refine Set.mem_iUnion.mpr ⟨e.symm (n, m), ?_⟩
    refine ⟨Fin.addCases a b, ?_, ?_⟩
    · simp only [Equiv.apply_symm_apply, Set.mem_preimage]
      constructor
      · show (fun i => Fin.addCases a b (Fin.castAdd l i)) ∈ A n
        have : (fun i => (Fin.addCases a b : Fin (k+l) → ℝ) (Fin.castAdd l i)) = a := by
          funext i
          exact Fin.addCases_left (motive := fun _ => ℝ) i
        rw [this]
        exact ha
      · show (fun j => Fin.addCases a b (Fin.natAdd k j)) ∈ B m
        have : (fun j => (Fin.addCases a b : Fin (k+l) → ℝ) (Fin.natAdd k j)) = b := by
          funext j
          exact Fin.addCases_right (motive := fun _ => ℝ) j
        rw [this]
        exact hb
    · simp only [Equiv.apply_symm_apply, Function.comp_apply, Prod.map]
      have ha' : (fun i => (Fin.addCases a b : Fin (k+l) → ℝ) (Fin.castAdd l i)) = a := by
        funext i
        exact Fin.addCases_left (motive := fun _ => ℝ) i
      have hb' : (fun j => (Fin.addCases a b : Fin (k+l) → ℝ) (Fin.natAdd k j)) = b := by
        funext j
        exact Fin.addCases_right (motive := fun _ => ℝ) j
      rw [hΞ]
      simp only [ha', hb']

/-! ### An antilipschitz projection gives a Lipschitz parametrization -/

theorem lipschitzOnWith_invFunOn {α β : Type*} [MetricSpace α] [MetricSpace β] [Nonempty α]
    {f : α → β} {s : Set α} {K : NNReal}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ K * dist (f x) (f y)) :
    LipschitzOnWith K (Function.invFunOn f s) (f '' s) := by
  refine LipschitzOnWith.of_dist_le_mul fun u hu v hv => ?_
  have humem : Function.invFunOn f s u ∈ s := Function.invFunOn_mem hu
  have hueq : f (Function.invFunOn f s u) = u := Function.invFunOn_eq hu
  have hvmem : Function.invFunOn f s v ∈ s := Function.invFunOn_mem hv
  have hveq : f (Function.invFunOn f s v) = v := Function.invFunOn_eq hv
  have := h _ humem _ hvmem
  rwa [hueq, hveq] at this

theorem subset_image_invFunOn {α β : Type*} [MetricSpace α] [MetricSpace β] [Nonempty α]
    {f : α → β} {s : Set α} {K : NNReal}
    (h : ∀ x ∈ s, ∀ y ∈ s, dist x y ≤ K * dist (f x) (f y)) :
    s ⊆ (Function.invFunOn f s) '' (f '' s) := by
  intro x hx
  refine ⟨f x, ⟨x, hx, rfl⟩, ?_⟩
  have hmem : Function.invFunOn f s (f x) ∈ s := Function.invFunOn_mem ⟨x, hx, rfl⟩
  have heq : f (Function.invFunOn f s (f x)) = f x := Function.invFunOn_eq ⟨x, hx, rfl⟩
  have hd := h _ hmem _ hx
  rw [heq, dist_self, mul_zero] at hd
  exact dist_le_zero.mp hd

/-! ### The zero set of a polynomial is covered in codimension one -/

set_option maxHeartbeats 1000000 in
theorem isLipschitzCovered_regular_zeroSet {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hk : Fintype.card ι - 1 ≤ k) (P : MvPolynomial ι ℝ) (i : ι) (x₀ : ι → ℝ)
    (hx₀ : MvPolynomial.eval x₀ (MvPolynomial.pderiv i P) ≠ 0) :
    ∃ ρ > 0, IsLipschitzCovered k
      ({x : ι → ℝ | MvPolynomial.eval x P = 0} ∩ Metric.ball x₀ ρ) := by
  classical
  set ε := |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| / 2 with hε
  have hεpos : 0 < ε := by
    have habs : 0 < |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| := abs_pos.mpr hx₀
    positivity
  have hcont : Continuous fun z : ι → ℝ =>
      |MvPolynomial.eval z (MvPolynomial.pderiv i P)| :=
    (contDiff_mvPolynomial_eval_pi _).continuous.abs
  have hopen : IsOpen {z : ι → ℝ | ε < |MvPolynomial.eval z (MvPolynomial.pderiv i P)|} :=
    isOpen_lt continuous_const hcont
  have hx₀mem : x₀ ∈ {z : ι → ℝ | ε < |MvPolynomial.eval z (MvPolynomial.pderiv i P)|} := by
    show ε < _
    rw [hε]
    have habs : 0 < |MvPolynomial.eval x₀ (MvPolynomial.pderiv i P)| := abs_pos.mpr hx₀
    linarith
  obtain ⟨σ, hσ, hsub⟩ := Metric.isOpen_iff.mp hopen x₀ hx₀mem
  obtain ⟨M, hMbound⟩ := (isCompact_closedBall x₀ (σ/2)).exists_bound_of_continuousOn
    (f := fun z : ι → ℝ => ∑ j, |MvPolynomial.eval z (MvPolynomial.pderiv j P)|)
    (Continuous.continuousOn (continuous_finsetSum _ fun j _ =>
      (contDiff_mvPolynomial_eval_pi _).continuous.abs))
  have hM0 : 0 ≤ M := by
    have hx : x₀ ∈ Metric.closedBall x₀ (σ/2) := Metric.mem_closedBall_self (by linarith)
    have hb := hMbound x₀ hx
    refine le_trans ?_ hb
    positivity
  refine ⟨σ/2, by linarith, ?_⟩
  set Z := {x : ι → ℝ | MvPolynomial.eval x P = 0} with hZ
  set B := Metric.ball x₀ (σ/2) with hB
  have hBsub : B ⊆ Metric.closedBall x₀ (σ/2) := Metric.ball_subset_closedBall
  have hBsub2 : B ⊆ Metric.ball x₀ σ := Metric.ball_subset_ball (by linarith)
  have hlow : ∀ z ∈ B, ε ≤ |MvPolynomial.eval z (MvPolynomial.pderiv i P)| :=
    fun z hz => le_of_lt (hsub (hBsub2 hz))
  have hhigh : ∀ z ∈ B, ∀ j, |MvPolynomial.eval z (MvPolynomial.pderiv j P)| ≤ M := by
    intro z hz j
    refine le_trans ?_ (hMbound z (hBsub hz))
    refine le_trans (Finset.single_le_sum (f := fun j =>
      |MvPolynomial.eval z (MvPolynomial.pderiv j P)|) (fun l _ => abs_nonneg _)
      (Finset.mem_univ j)) ?_
    exact le_abs_self _
  set K : NNReal := Real.toNNReal (1 + M * Fintype.card ι / ε) with hK
  have hKval : (K : ℝ) = 1 + M * Fintype.card ι / ε := by
    rw [hK, Real.coe_toNNReal]
    positivity
  have hanti : ∀ x ∈ Z ∩ B, ∀ y ∈ Z ∩ B,
      dist x y ≤ K * dist (dropCoord i x) (dropCoord i y) := by
    intro x hx y hy
    rw [hKval]
    exact dist_le_of_zero_of_pderiv_bounds P i (convex_ball x₀ (σ/2)) hεpos hM0
      (fun u hu => hlow u hu) (fun u hu j => hhigh u hu j) hx.2 hy.2 hx.1 hy.1
  have hcov : IsLipschitzCovered k (dropCoord i '' (Z ∩ B)) := by
    refine isLipschitzCovered_pi ?_ _
    have hc : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
      have h1 : Fintype.card {j : ι // ¬ (j = i)} = Fintype.card ι
          - Fintype.card {j : ι // j = i} := Fintype.card_subtype_compl _
      simp only [Fintype.card_subtype_eq] at h1
      exact h1
    rw [hc]
    exact hk
  refine IsLipschitzCovered.mono (subset_image_invFunOn hanti) ?_
  exact IsLipschitzCovered.image (lipschitzOnWith_invFunOn hanti) hcov

set_option maxHeartbeats 1000000 in
theorem isLipschitzCovered_zeroSet {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hk : Fintype.card ι - 1 ≤ k) :
    ∀ (m : ℕ) (P : MvPolynomial ι ℝ), P.totalDegree ≤ m → P ≠ 0 →
      IsLipschitzCovered k {x : ι → ℝ | MvPolynomial.eval x P = 0} := by
  classical
  intro m
  induction m with
  | zero =>
      intro P hdeg hP
      set a := P.coeff 0 with ha0
      have hC : P = MvPolynomial.C a :=
        MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp (Nat.le_zero.mp hdeg)
      have ha : a ≠ 0 := fun h => hP (by rw [hC, h, map_zero])
      have hempty : {x : ι → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hC, MvPolynomial.eval_C]
        exact ha
      rw [hempty]
      exact isLipschitzCovered_empty
  | succ m ih =>
      intro P hdeg hP
      by_cases hzero : P.totalDegree = 0
      · set a := P.coeff 0 with ha0
        have hC : P = MvPolynomial.C a :=
          MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp hzero
        have ha : a ≠ 0 := fun h => hP (by rw [hC, h, map_zero])
        have hempty : {x : ι → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
          ext x
          simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, hC, MvPolynomial.eval_C]
          exact ha
        rw [hempty]
        exact isLipschitzCovered_empty
      · have hpos : 0 < P.totalDegree := Nat.pos_of_ne_zero hzero
        obtain ⟨i, hi⟩ := exists_pderiv_ne_zero hpos
        set Z := {x : ι → ℝ | MvPolynomial.eval x P = 0} with hZ
        set R := {x : ι → ℝ | MvPolynomial.eval x P = 0 ∧
          MvPolynomial.eval x (MvPolynomial.pderiv i P) ≠ 0} with hR
        have hsing : IsLipschitzCovered k
            {x : ι → ℝ | MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0} :=
          ih (MvPolynomial.pderiv i P) (by have := totalDegree_pderiv_lt i hpos; omega) hi
        have hloc : ∀ x₀ : ↥R, ∃ ρ > 0, IsLipschitzCovered k (Z ∩ Metric.ball (x₀ : ι → ℝ) ρ) :=
          fun x₀ => isLipschitzCovered_regular_zeroSet hk P i (x₀ : ι → ℝ) x₀.2.2
        choose ρ hρpos hρcov using hloc
        obtain ⟨T, hTcount, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
          (fun x₀ : ↥R => Metric.ball (x₀ : ι → ℝ) (ρ x₀))
          (fun x₀ => Metric.isOpen_ball)
        haveI : Countable ↥T := hTcount.to_subtype
        have hRcov : R ⊆ ⋃ x₀ : ↥T, (Z ∩ Metric.ball ((x₀ : ↥R) : ι → ℝ) (ρ (x₀ : ↥R))) := by
          intro x hx
          have hx' : x ∈ ⋃ x₀ : ↥R, Metric.ball (x₀ : ι → ℝ) (ρ x₀) :=
            Set.mem_iUnion.mpr ⟨⟨x, hx⟩, Metric.mem_ball_self (hρpos ⟨x, hx⟩)⟩
          rw [← hTeq] at hx'
          obtain ⟨-, ⟨x₀, rfl⟩, hball⟩ := hx'
          obtain ⟨-, ⟨hx₀T, rfl⟩, hball⟩ := hball
          exact Set.mem_iUnion.mpr ⟨⟨x₀, hx₀T⟩, ⟨hx.1, hball⟩⟩
        have hRc : IsLipschitzCovered k R :=
          IsLipschitzCovered.mono hRcov
            (IsLipschitzCovered.iUnion_countable fun x₀ => hρcov (x₀ : ↥R))
        have hsplit : Z ⊆ R ∪ {x : ι → ℝ | MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0} := by
          intro x hx
          by_cases hd : MvPolynomial.eval x (MvPolynomial.pderiv i P) = 0
          · exact Or.inr hd
          · exact Or.inl ⟨hx, hd⟩
        exact IsLipschitzCovered.mono hsplit (hRc.union hsing)

/-- **The zero set of a nonzero real polynomial is covered by countably many Lipschitz images of
subsets of `ℝ^(card ι - 1)`.** -/
theorem isLipschitzCovered_setOf_eval_eq_zero {ι : Type} [Fintype ι] [DecidableEq ι] {k : ℕ}
    (hk : Fintype.card ι - 1 ≤ k) (P : MvPolynomial ι ℝ) (hP : P ≠ 0) :
    IsLipschitzCovered k {x : ι → ℝ | MvPolynomial.eval x P = 0} :=
  isLipschitzCovered_zeroSet hk P.totalDegree P le_rfl hP

/-! ### Finite products -/

theorem IsLipschitzCovered.cons {n k l : ℕ} {X : Type*} [MetricSpace X] [Nonempty X]
    {s : Set X} {t : Set (Fin n → X)} (hs : IsLipschitzCovered k s)
    (ht : IsLipschitzCovered l t) :
    IsLipschitzCovered (k + l)
      ((fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) '' (s ×ˢ t)) := by
  refine IsLipschitzCovered.image (D := 1) ?_ (hs.prod ht)
  refine LipschitzOnWith.of_dist_le_mul fun p _ q _ => ?_
  rw [NNReal.coe_one, one_mul, Prod.dist_eq]
  refine (dist_pi_le_iff (le_max_of_le_left dist_nonneg)).mpr fun a => ?_
  refine Fin.cases ?_ ?_ a
  · simp only [Fin.cons_zero]
    exact le_max_left (dist p.1 q.1) (dist p.2 q.2)
  · intro j
    simp only [Fin.cons_succ]
    exact le_trans (dist_le_pi_dist p.2 q.2 j) (le_max_right _ _)

theorem isLipschitzCovered_univ_fin_zero {X : Type*} [MetricSpace X] [Nonempty X] :
    IsLipschitzCovered 0 (Set.univ : Set (Fin 0 → X)) := by
  refine ⟨fun _ _ => (fun _ => Classical.arbitrary X), fun _ => Set.univ, fun _ => 0,
    fun _ => LipschitzOnWith.of_dist_le_mul fun u _ v _ => ?_, ?_⟩
  · rw [NNReal.coe_zero, zero_mul]
    refine le_of_eq ?_
    refine dist_eq_zero.mpr ?_
    funext a
    exact absurd a.2 (by omega)
  · intro x _
    refine Set.mem_iUnion.mpr ⟨0, ⟨fun _ => 0, Set.mem_univ _, ?_⟩⟩
    funext a
    exact absurd a.2 (by omega)

theorem IsLipschitzCovered.piFin {X : Type*} [MetricSpace X] [Nonempty X] :
    ∀ (n : ℕ) (S : Fin n → Set X) (k : Fin n → ℕ), (∀ a, IsLipschitzCovered (k a) (S a)) →
      IsLipschitzCovered (∑ a, k a) (Set.pi Set.univ S) := by
  intro n
  induction n with
  | zero =>
      intro S k h
      have hpi : Set.pi Set.univ S = (Set.univ : Set (Fin 0 → X)) := by
        ext x
        simp only [Set.mem_pi, Set.mem_univ, iff_true]
        intro a _
        exact absurd a.2 (by omega)
      have hsum : (∑ a : Fin 0, k a) = 0 := by simp
      rw [hpi, hsum]
      exact isLipschitzCovered_univ_fin_zero
  | succ n ih =>
      intro S k h
      have hpi : Set.pi Set.univ S
          = (fun p : X × (Fin n → X) => (Fin.cons p.1 p.2 : Fin (n + 1) → X)) ''
            (S 0 ×ˢ Set.pi Set.univ (fun a : Fin n => S a.succ)) := by
        ext x
        constructor
        · intro hx
          refine ⟨(x 0, Fin.tail x), ⟨hx 0 (Set.mem_univ _), fun a _ => hx a.succ
            (Set.mem_univ _)⟩, ?_⟩
          exact Fin.cons_self_tail x
        · rintro ⟨⟨a, y⟩, ⟨ha, hy⟩, rfl⟩
          intro j _
          refine Fin.cases ?_ ?_ j
          · simpa using ha
          · intro l
            simpa using hy l (Set.mem_univ _)
      rw [hpi, Fin.sum_univ_succ]
      exact IsLipschitzCovered.cons (h 0) (ih (fun a => S a.succ) (fun a => k a.succ)
        fun a => h a.succ)

/-! ### Generic avoidance -/

/-- **A bad set covered in dimension smaller than the ambient dimension has dense complement.**
This is the codimension replacement for parametric transversality: a bad parameter set that is a
countable union of Lipschitz images of a lower-dimensional cube cannot contain a ball. -/
theorem dense_compl_of_isLipschitzCovered {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {k : ℕ} {T : Set V} (hT : IsLipschitzCovered k T)
    (hk : k < Module.finrank ℝ V) : Dense Tᶜ := by
  refine dense_compl_of_dimH_lt_finrank (lt_of_le_of_lt hT.dimH_le ?_)
  exact_mod_cast hk

/-! ### A decoupled system of row equations -/

theorem nat_row_count (n j c : ℕ) (hj : j ≤ n) (hc : 1 ≤ c) :
    j * (c - 1) + (n - j) * c = n * c - j := by
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
  simp only [Nat.add_sub_cancel, Nat.add_sub_cancel_left]
  refine (Nat.sub_eq_of_eq_add ?_).symm
  ring

set_option maxHeartbeats 1000000 in
/-- **Independent row equations cut the dimension by their number.**  If on `J` of the `N`
independent copies of the row space a nonzero polynomial equation is imposed, the solution set is
covered in dimension `N · card ι - card J`. -/
theorem isLipschitzCovered_pi_zeroSets {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    {N : ℕ} (Q : Fin N → MvPolynomial ι ℝ) (J : Finset (Fin N)) (hJ : ∀ a ∈ J, Q a ≠ 0) :
    IsLipschitzCovered (N * Fintype.card ι - J.card)
      {x : Fin N → (ι → ℝ) | ∀ a ∈ J, MvPolynomial.eval (x a) (Q a) = 0} := by
  classical
  have hcard : 1 ≤ Fintype.card ι := Fintype.card_pos
  set k : Fin N → ℕ := fun a => if a ∈ J then Fintype.card ι - 1 else Fintype.card ι with hk
  have hcov : ∀ a : Fin N, IsLipschitzCovered (k a)
      (if a ∈ J then {x : ι → ℝ | MvPolynomial.eval x (Q a) = 0} else Set.univ) := by
    intro a
    by_cases ha : a ∈ J
    · rw [if_pos ha, hk]
      simp only [if_pos ha]
      exact isLipschitzCovered_setOf_eval_eq_zero le_rfl (Q a) (hJ a ha)
    · rw [if_neg ha, hk]
      simp only [if_neg ha]
      exact isLipschitzCovered_pi le_rfl _
  have hpi : {x : Fin N → (ι → ℝ) | ∀ a ∈ J, MvPolynomial.eval (x a) (Q a) = 0}
      = Set.pi Set.univ (fun a => if a ∈ J then
        {x : ι → ℝ | MvPolynomial.eval x (Q a) = 0} else Set.univ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx a
      by_cases ha : a ∈ J
      · rw [if_pos ha]
        exact hx a ha
      · rw [if_neg ha]
        exact Set.mem_univ _
    · intro hx a ha
      have h := hx a
      rwa [if_pos ha] at h
  have hsum : (∑ a, k a) = N * Fintype.card ι - J.card := by
    have hjN : J.card ≤ N := by
      have h := Finset.card_le_card (Finset.subset_univ J)
      simpa using h
    have hstep : (∑ a : Fin N, k a)
        = J.card * (Fintype.card ι - 1) + (N - J.card) * Fintype.card ι := by
      rw [hk, Finset.sum_ite]
      have h1 : (Finset.univ.filter fun a : Fin N => a ∈ J) = J := by ext a; simp
      have h2 : (Finset.univ.filter fun a : Fin N => a ∉ J) = Finset.univ \ J := by ext a; simp
      rw [h1, h2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        Finset.card_univ_sdiff]
      simp
    rw [hstep]
    exact nat_row_count N J.card (Fintype.card ι) hjN hcard
  rw [hpi, ← hsum]
  exact IsLipschitzCovered.piFin N _ k hcov

/-! ### Complex coordinates -/

variable {κ : Type} [Fintype κ] [DecidableEq κ]

omit [DecidableEq κ] in
theorem isLipschitzCovered_univ_complex {k : ℕ} (hk : 2 * Fintype.card κ ≤ k)
    (s : Set (κ → ℂ)) : IsLipschitzCovered k s := by
  classical
  have hbase : IsLipschitzCovered k (Set.univ : Set ((κ ⊕ κ) → ℝ)) := by
    refine isLipschitzCovered_pi ?_ _
    rw [Fintype.card_sum]
    omega
  have himg : IsLipschitzCovered k (realifyPoint '' (Set.univ : Set ((κ ⊕ κ) → ℝ))) :=
    IsLipschitzCovered.image
      (LipschitzWith.lipschitzOnWith (K := 2) (f := realifyPoint (κ := κ))
        lipschitzWith_realifyPoint (s := (Set.univ : Set ((κ ⊕ κ) → ℝ)))) hbase
  refine IsLipschitzCovered.mono (fun z _ => ?_) himg
  refine ⟨Sum.elim (fun j => (z j).re) (fun j => (z j).im), Set.mem_univ _, ?_⟩
  funext j
  exact Complex.ext rfl rfl

theorem isLipschitzCovered_setOf_complex_eval_eq_zero {k : ℕ}
    (hk : 2 * Fintype.card κ - 1 ≤ k) (Q : MvPolynomial κ ℂ) (hQ : Q ≠ 0) :
    IsLipschitzCovered k {z : κ → ℂ | MvPolynomial.eval z Q = 0} := by
  classical
  set Q' := complexSplitSubst Q with hQ'
  have hQ'ne : Q' ≠ 0 := complexSplitSubst_ne_zero hQ
  have hcard : Fintype.card (κ ⊕ κ) - 1 ≤ k := by
    rw [Fintype.card_sum]
    omega
  obtain hP | hP := rePoly_ne_zero_or_imPoly_ne_zero hQ'ne
  · refine IsLipschitzCovered.mono
      (?_ : {z : κ → ℂ | MvPolynomial.eval z Q = 0}
        ⊆ realifyPoint '' {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (rePoly Q') = 0})
      (IsLipschitzCovered.image
        (LipschitzWith.lipschitzOnWith (K := 2) (f := realifyPoint (κ := κ))
          lipschitzWith_realifyPoint
          (s := {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (rePoly Q') = 0}))
        (isLipschitzCovered_setOf_eval_eq_zero hcard (rePoly Q') hP))
    intro z hz
    refine ⟨Sum.elim (fun j => (z j).re) (fun j => (z j).im), ?_, ?_⟩
    · show MvPolynomial.eval _ (rePoly Q') = 0
      rw [eval_rePoly]
      have hpt : realifyPoint (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) = z := by
        funext j
        exact Complex.ext rfl rfl
      rw [eval_complexSplitSubst, hpt, hz, Complex.zero_re]
    · funext j
      exact Complex.ext rfl rfl
  · refine IsLipschitzCovered.mono
      (?_ : {z : κ → ℂ | MvPolynomial.eval z Q = 0}
        ⊆ realifyPoint '' {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (imPoly Q') = 0})
      (IsLipschitzCovered.image
        (LipschitzWith.lipschitzOnWith (K := 2) (f := realifyPoint (κ := κ))
          lipschitzWith_realifyPoint
          (s := {u : (κ ⊕ κ) → ℝ | MvPolynomial.eval u (imPoly Q') = 0}))
        (isLipschitzCovered_setOf_eval_eq_zero hcard (imPoly Q') hP))
    intro z hz
    refine ⟨Sum.elim (fun j => (z j).re) (fun j => (z j).im), ?_, ?_⟩
    · show MvPolynomial.eval _ (imPoly Q') = 0
      rw [eval_imPoly]
      have hpt : realifyPoint (Sum.elim (fun j => (z j).re) (fun j => (z j).im)) = z := by
        funext j
        exact Complex.ext rfl rfl
      rw [eval_complexSplitSubst, hpt, hz, Complex.zero_im]
    · funext j
      exact Complex.ext rfl rfl

set_option maxHeartbeats 1000000 in
/-- **Independent complex row equations cut the real dimension by their number.** -/
theorem isLipschitzCovered_pi_complex_zeroSets [Nonempty κ]
    {N : ℕ} (Q : Fin N → MvPolynomial κ ℂ) (J : Finset (Fin N)) (hJ : ∀ a ∈ J, Q a ≠ 0) :
    IsLipschitzCovered (N * (2 * Fintype.card κ) - J.card)
      {x : Fin N → (κ → ℂ) | ∀ a ∈ J, MvPolynomial.eval (x a) (Q a) = 0} := by
  classical
  have hcard : 1 ≤ 2 * Fintype.card κ := by
    have := Fintype.card_pos (α := κ)
    omega
  set k : Fin N → ℕ := fun a => if a ∈ J then 2 * Fintype.card κ - 1 else 2 * Fintype.card κ
    with hk
  have hcov : ∀ a : Fin N, IsLipschitzCovered (k a)
      (if a ∈ J then {z : κ → ℂ | MvPolynomial.eval z (Q a) = 0} else Set.univ) := by
    intro a
    by_cases ha : a ∈ J
    · rw [if_pos ha, hk]
      simp only [if_pos ha]
      exact isLipschitzCovered_setOf_complex_eval_eq_zero le_rfl (Q a) (hJ a ha)
    · rw [if_neg ha, hk]
      simp only [if_neg ha]
      exact isLipschitzCovered_univ_complex le_rfl _
  have hpi : {x : Fin N → (κ → ℂ) | ∀ a ∈ J, MvPolynomial.eval (x a) (Q a) = 0}
      = Set.pi Set.univ (fun a => if a ∈ J then
        {z : κ → ℂ | MvPolynomial.eval z (Q a) = 0} else Set.univ) := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
    constructor
    · intro hx a
      by_cases ha : a ∈ J
      · rw [if_pos ha]
        exact hx a ha
      · rw [if_neg ha]
        exact Set.mem_univ _
    · intro hx a ha
      have h := hx a
      rwa [if_pos ha] at h
  have hsum : (∑ a, k a) = N * (2 * Fintype.card κ) - J.card := by
    have hjN : J.card ≤ N := by
      have h := Finset.card_le_card (Finset.subset_univ J)
      simpa using h
    have hstep : (∑ a : Fin N, k a)
        = J.card * (2 * Fintype.card κ - 1) + (N - J.card) * (2 * Fintype.card κ) := by
      rw [hk, Finset.sum_ite]
      have h1 : (Finset.univ.filter fun a : Fin N => a ∈ J) = J := by ext a; simp
      have h2 : (Finset.univ.filter fun a : Fin N => a ∉ J) = Finset.univ \ J := by ext a; simp
      rw [h1, h2, Finset.sum_const, Finset.sum_const, smul_eq_mul, smul_eq_mul,
        Finset.card_univ_sdiff]
      simp
    rw [hstep]
    exact nat_row_count N J.card (2 * Fintype.card κ) hjN hcard
  rw [hpi, ← hsum]
  exact IsLipschitzCovered.piFin N _ k hcov

/-! ### Transport along a map with locally Lipschitz local inverses -/

/-- **Preimages under a locally invertible map stay covered.**  If every point of `V` has a
neighbourhood on which `Φ` admits a Lipschitz left inverse, then the preimage of a covered set is
covered in the same dimension.  Together with the inverse function theorem this is the transport
from jet coordinates to parameter coordinates. -/
theorem IsLipschitzCovered.preimage {V W : Type*} [MetricSpace V] [SecondCountableTopology V]
    [Nonempty V] [MetricSpace W] {Φ : V → W}
    (hΦ : ∀ x : V, ∃ (u : Set V), u ∈ nhds x ∧ ∃ (ψ : W → V) (C : NNReal),
        LipschitzOnWith C ψ (Φ '' u) ∧ ∀ y ∈ u, ψ (Φ y) = y)
    {k : ℕ} {S : Set W} (hS : IsLipschitzCovered k S) :
    IsLipschitzCovered k (Φ ⁻¹' S) := by
  classical
  choose u hu ψ C hψlip hψinv using hΦ
  obtain ⟨T, hTcount, hTeq⟩ := TopologicalSpace.isOpen_iUnion_countable
    (fun x : V => interior (u x)) (fun x => isOpen_interior)
  haveI : Countable ↥T := hTcount.to_subtype
  have hcover : Φ ⁻¹' S ⊆ ⋃ x : ↥T, ψ (x : V) '' (S ∩ Φ '' u (x : V)) := by
    intro y hy
    have hy' : y ∈ ⋃ x : V, interior (u x) :=
      Set.mem_iUnion.mpr ⟨y, mem_interior_iff_mem_nhds.mpr (hu y)⟩
    rw [← hTeq] at hy'
    obtain ⟨-, ⟨x, rfl⟩, hmem⟩ := hy'
    obtain ⟨-, ⟨hxT, rfl⟩, hmem⟩ := hmem
    refine Set.mem_iUnion.mpr ⟨⟨x, hxT⟩, ?_⟩
    refine ⟨Φ y, ⟨hy, ⟨y, interior_subset hmem, rfl⟩⟩, ?_⟩
    exact hψinv x y (interior_subset hmem)
  refine IsLipschitzCovered.mono hcover ?_
  refine IsLipschitzCovered.iUnion_countable fun x => ?_
  exact IsLipschitzCovered.image
    ((hψlip (x : V)).mono Set.inter_subset_right)
    (hS.mono Set.inter_subset_left)

end

end GaloisForLFunctions.HTGeometry
