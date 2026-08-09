import Mathlib
import GaloisForLFunctions.HTGeometry.FiniteMonotonicityVariation

/-!
# A cell with no interior critical point is monotone

Darboux's theorem gives the derivative the intermediate value property, so on a cell where the
derivative never vanishes it has constant sign, and the function is monotone there in one direction
or the other.

This is the step that turns "finitely many critical points" into the monotone partition the
finite-variation law consumes: the partition cells are the gaps between critical points, and this
lemma is what certifies each gap.
-/

noncomputable section

open Set

namespace HTGeometry

/-- **A cell free of interior critical points is monotone.**  The derivative has the intermediate
value property, so not vanishing on the open cell forces a constant sign there. -/
theorem monotoneOn_or_antitoneOn_of_hasDerivAt_ne_zero {f f' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hne : ∀ x ∈ Ioo a b, f' x ≠ 0) :
    MonotoneOn f (Icc a b) ∨ AntitoneOn f (Icc a b) := by
  have hsub : Ioo a b ⊆ Icc a b := Ioo_subset_Icc_self
  have hcont : ContinuousOn f (Icc a b) :=
    fun x hx => ((hf x hx).continuousAt).continuousWithinAt
  have hderivEq : ∀ x ∈ Ioo a b, deriv f x = f' x := fun x hx => (hf x (hsub hx)).deriv
  have hwithin : ∀ x ∈ Ioo a b, HasDerivWithinAt f (f' x) (Ioo a b) x :=
    fun x hx => (hf x (hsub hx)).hasDerivWithinAt
  rcases hasDerivWithinAt_forall_lt_or_forall_gt_of_forall_ne (convex_Ioo a b) hwithin hne with
    hneg | hpos
  · right
    refine (strictAntiOn_of_deriv_neg (convex_Icc a b) hcont ?_).antitoneOn
    intro x hx
    rw [interior_Icc] at hx
    rw [hderivEq x hx]
    exact hneg x hx
  · left
    refine (strictMonoOn_of_deriv_pos (convex_Icc a b) hcont ?_).monotoneOn
    intro x hx
    rw [interior_Icc] at hx
    rw [hderivEq x hx]
    exact hpos x hx

/-- The same, phrased for a monotone partition index: if the derivative avoids zero on the interior
of every cell, every cell is monotone in one direction. -/
theorem partition_monotone_of_deriv_ne_zero {f f' : ℝ → ℝ} {I : ℕ → ℝ} {n : ℕ}
    (hI : Monotone I)
    (hf : ∀ x ∈ Icc (I 0) (I n), HasDerivAt f (f' x) x)
    (hne : ∀ i < n, ∀ x ∈ Ioo (I i) (I (i + 1)), f' x ≠ 0) :
    ∀ i < n, MonotoneOn f (Icc (I i) (I (i + 1))) ∨ AntitoneOn f (Icc (I i) (I (i + 1))) := by
  intro i hi
  have hcell : Icc (I i) (I (i + 1)) ⊆ Icc (I 0) (I n) := by
    refine Icc_subset_Icc (hI (Nat.zero_le i)) (hI (Nat.succ_le_iff.mpr hi))
  exact monotoneOn_or_antitoneOn_of_hasDerivAt_ne_zero (fun x hx => hf x (hcell hx)) (hne i hi)

/-- **The finite-critical-point variation law.**  A function whose derivative avoids zero on the
interior of every cell of a monotone partition has total variation at most `2 n B`. -/
theorem eVariationOn_le_of_deriv_ne_zero_on_cells {f f' : ℝ → ℝ} {I : ℕ → ℝ} {n : ℕ} {B : ℝ}
    (hI : Monotone I)
    (hf : ∀ x ∈ Icc (I 0) (I n), HasDerivAt f (f' x) x)
    (hne : ∀ i < n, ∀ x ∈ Ioo (I i) (I (i + 1)), f' x ≠ 0)
    (hbound : ∀ x ∈ Icc (I 0) (I n), |f x| ≤ B) :
    eVariationOn f (Icc (I 0) (I n)) ≤ ENNReal.ofReal (2 * n * B) :=
  eVariationOn_le_of_piecewise_monotone f I n hI
    (partition_monotone_of_deriv_ne_zero hI hf hne) B hbound

/-- **The ordered partition assembly.**  A finite set of critical points inside `[a, b]` can be
enumerated in order into a monotone partition index whose cells have interiors free of that set.
This is the missing link between "finitely many critical points" and the finite-variation law,
whose hypothesis is a monotone index. -/
theorem exists_monotone_partition_of_finset {a b : ℝ} (hab : a ≤ b) (S : Finset ℝ) :
    ∃ (n : ℕ) (I : ℕ → ℝ), Monotone I ∧ I 0 = a ∧ I n = b ∧ n ≤ S.card + 1 ∧
      (∀ i : ℕ, n ≤ i → I i = b) ∧ ∀ i < n, ∀ x ∈ Ioo (I i) (I (i + 1)), x ∉ S := by
  classical
  set T : Finset ℝ := insert a (insert b (S.filter (fun x => a ≤ x ∧ x ≤ b))) with hTdef
  have haT : a ∈ T := by rw [hTdef]; exact Finset.mem_insert_self a _
  have hbT : b ∈ T := by
    rw [hTdef]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_self b _)
  have hrange : ∀ y ∈ T, a ≤ y ∧ y ≤ b := by
    intro y hy
    rw [hTdef] at hy
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨le_rfl, hab⟩
    rcases Finset.mem_insert.mp hy with rfl | hy
    · exact ⟨hab, le_rfl⟩
    · exact (Finset.mem_filter.mp hy).2
  set L : ℕ := T.card with hLdef
  have hL1 : 1 ≤ L := Finset.card_pos.mpr ⟨a, haT⟩
  set e : Fin L ↪o ℝ := T.orderEmbOfFin rfl with hedef
  have hmemT : ∀ i : Fin L, e i ∈ T := by
    intro i
    have : e i ∈ Set.range (T.orderEmbOfFin (rfl : T.card = L)) := ⟨i, rfl⟩
    rw [Finset.range_orderEmbOfFin] at this
    exact this
  have hsurj : ∀ y ∈ T, ∃ i : Fin L, e i = y := by
    intro y hy
    have : y ∈ Set.range (T.orderEmbOfFin (rfl : T.card = L)) := by
      rw [Finset.range_orderEmbOfFin]; exact hy
    exact this
  set I : ℕ → ℝ := fun i => if h : i < L then e ⟨i, h⟩ else b with hIdef
  have hIle : ∀ i : ℕ, I i ≤ b := by
    intro i
    rw [hIdef]
    by_cases h : i < L
    · simp only [dif_pos h]
      exact (hrange _ (hmemT ⟨i, h⟩)).2
    · simp only [dif_neg h]
      exact le_rfl
  have hIge : ∀ i : ℕ, a ≤ I i := by
    intro i
    rw [hIdef]
    by_cases h : i < L
    · simp only [dif_pos h]
      exact (hrange _ (hmemT ⟨i, h⟩)).1
    · simp only [dif_neg h]
      exact hab
  have hImono : Monotone I := by
    intro i j hij
    rw [hIdef]
    by_cases hj : j < L
    · have hi : i < L := lt_of_le_of_lt hij hj
      simp only [dif_pos hi, dif_pos hj]
      exact (OrderEmbedding.le_iff_le e).mpr (by exact hij)
    · simp only [dif_neg hj]
      exact hIle i
  have hI0 : I 0 = a := by
    obtain ⟨k, hk⟩ := hsurj a haT
    have h0 : (0 : ℕ) < L := hL1
    have hle : e ⟨0, h0⟩ ≤ e k := (OrderEmbedding.le_iff_le e).mpr (by exact Nat.zero_le _)
    have hge : a ≤ e ⟨0, h0⟩ := (hrange _ (hmemT ⟨0, h0⟩)).1
    rw [hIdef]
    simp only [dif_pos h0]
    rw [hk] at hle
    linarith
  have hIlast : I (L - 1) = b := by
    obtain ⟨k, hk⟩ := hsurj b hbT
    have hlt : L - 1 < L := Nat.sub_lt hL1 Nat.one_pos
    have hkle : (k : ℕ) ≤ L - 1 := Nat.le_sub_one_of_lt k.isLt
    have hle : e k ≤ e ⟨L - 1, hlt⟩ := (OrderEmbedding.le_iff_le e).mpr (by exact hkle)
    have hub : e ⟨L - 1, hlt⟩ ≤ b := (hrange _ (hmemT ⟨L - 1, hlt⟩)).2
    rw [hIdef]
    simp only [dif_pos hlt]
    rw [hk] at hle
    linarith
  have hcard : L ≤ S.card + 2 := by
    have h1 : T.card ≤ (insert b (S.filter (fun x => a ≤ x ∧ x ≤ b))).card + 1 := by
      rw [hTdef]
      exact Finset.card_insert_le _ _
    have h2 : (insert b (S.filter (fun x => a ≤ x ∧ x ≤ b))).card
        ≤ (S.filter (fun x => a ≤ x ∧ x ≤ b)).card + 1 := Finset.card_insert_le _ _
    have h3 : (S.filter (fun x => a ≤ x ∧ x ≤ b)).card ≤ S.card := Finset.card_filter_le _ _
    omega
  have htail : ∀ i : ℕ, L - 1 ≤ i → I i = b := by
    intro i hi
    rcases eq_or_lt_of_le hi with heq | hlt
    · rw [← heq]; exact hIlast
    · have hiL : L ≤ i := by omega
      rw [hIdef]
      simp only [dif_neg (Nat.not_lt.mpr hiL)]
  refine ⟨L - 1, I, hImono, hI0, hIlast, by omega, htail, ?_⟩
  intro i hi x hx hxS
  have hi1 : i + 1 < L := by omega
  have hi0 : i < L := by omega
  have hxab : a ≤ x ∧ x ≤ b := ⟨le_trans (hIge i) (le_of_lt hx.1),
    le_trans (le_of_lt hx.2) (hIle (i + 1))⟩
  have hxT : x ∈ T := by
    rw [hTdef]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
      (Finset.mem_filter.mpr ⟨hxS, hxab⟩))
  obtain ⟨k, hk⟩ := hsurj x hxT
  have hlt1 : e ⟨i, hi0⟩ < e k := by
    rw [hk]
    have : I i = e ⟨i, hi0⟩ := by rw [hIdef]; simp only [dif_pos hi0]
    rw [← this]
    exact hx.1
  have hlt2 : e k < e ⟨i + 1, hi1⟩ := by
    rw [hk]
    have : I (i + 1) = e ⟨i + 1, hi1⟩ := by rw [hIdef]; simp only [dif_pos hi1]
    rw [← this]
    exact hx.2
  have h1 : i < (k : ℕ) := by
    have := (OrderEmbedding.lt_iff_lt e).mp hlt1
    exact this
  have h2 : (k : ℕ) < i + 1 := by
    have := (OrderEmbedding.lt_iff_lt e).mp hlt2
    exact this
  omega


/-- **From a finite critical set to a variation bound.**  If the derivative vanishes only on a
finite set inside `(a, b)`, the total variation is at most `2 (|S| + 1) B`. -/
theorem eVariationOn_le_of_finite_critical_set {f f' : ℝ → ℝ} {a b B : ℝ} (hab : a ≤ b)
    (S : Finset ℝ)
    (hf : ∀ x ∈ Icc a b, HasDerivAt f (f' x) x)
    (hcrit : ∀ x ∈ Ioo a b, f' x = 0 → x ∈ S)
    (hbound : ∀ x ∈ Icc a b, |f x| ≤ B) :
    eVariationOn f (Icc a b) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  obtain ⟨n, I, hImono, hI0, hIn, hncard, _, hcell⟩ := exists_monotone_partition_of_finset hab S
  have hB : 0 ≤ B := le_trans (abs_nonneg (f a)) (hbound a ⟨le_rfl, hab⟩)
  have hIcc : Icc (I 0) (I n) = Icc a b := by rw [hI0, hIn]
  have hne : ∀ i < n, ∀ x ∈ Ioo (I i) (I (i + 1)), f' x ≠ 0 := by
    intro i hi x hx hzero
    have hxab : x ∈ Ioo a b := by
      constructor
      · exact lt_of_le_of_lt (hI0 ▸ hImono (Nat.zero_le i)) hx.1
      · exact lt_of_lt_of_le hx.2 (hIn ▸ hImono (Nat.succ_le_iff.mpr hi))
    exact hcell i hi x hx (hcrit x hxab hzero)
  have hmain := eVariationOn_le_of_deriv_ne_zero_on_cells (f := f) (f' := f') (I := I) (n := n)
    (B := B) hImono (by rw [hIcc]; exact hf) hne (by rw [hIcc]; exact hbound)
  rw [hIcc] at hmain
  refine le_trans hmain (ENNReal.ofReal_le_ofReal ?_)
  have hn : (n : ℝ) ≤ (S.card : ℝ) + 1 := by exact_mod_cast hncard
  nlinarith [hB, hn]


/-- **Cellwise uniqueness gives global finiteness.**  If each cell of a monotone partition contains
at most one critical point, the whole range contains finitely many.  This is the Sturm count: on a
cell where the flux is strictly monotone the derivative vanishes at most once. -/
theorem finite_critical_of_cellwise_subsingleton {y' : ℝ → ℝ} {J : ℕ → ℝ}
    (hsub : ∀ i : ℕ, {x : ℝ | x ∈ Ioo (J i) (J (i + 1)) ∧ y' x = 0}.Subsingleton) (m : ℕ) :
    {x : ℝ | x ∈ Ioo (J 0) (J m) ∧ y' x = 0}.Finite := by
  induction m with
  | zero =>
      have hempty : {x : ℝ | x ∈ Ioo (J 0) (J 0) ∧ y' x = 0} = ∅ := by
        ext x
        simp
      rw [hempty]
      exact Set.finite_empty
  | succ m ih =>
      refine Set.Finite.subset (ih.union ((Set.finite_singleton (J m)).union
        (hsub m).finite)) ?_
      rintro x ⟨⟨hx1, hx2⟩, hx0⟩
      rcases lt_trichotomy x (J m) with h | h | h
      · exact Or.inl ⟨⟨hx1, h⟩, hx0⟩
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨⟨h, hx2⟩, hx0⟩)

/-- **The Sturm variation law.**  A function whose derivative vanishes at most once per cell of a
monotone partition has finite total variation, bounded by twice the critical count. -/
theorem eVariationOn_le_of_cellwise_subsingleton {f f' : ℝ → ℝ} {J : ℕ → ℝ} {m : ℕ} {B : ℝ}
    (hJ : Monotone J)
    (hsub : ∀ i : ℕ, {x : ℝ | x ∈ Ioo (J i) (J (i + 1)) ∧ f' x = 0}.Subsingleton)
    (hf : ∀ x ∈ Icc (J 0) (J m), HasDerivAt f (f' x) x)
    (hbound : ∀ x ∈ Icc (J 0) (J m), |f x| ≤ B) :
    ∃ S : Finset ℝ, eVariationOn f (Icc (J 0) (J m)) ≤ ENNReal.ofReal (2 * (S.card + 1) * B) := by
  classical
  have hfin := finite_critical_of_cellwise_subsingleton hsub m
  refine ⟨hfin.toFinset, ?_⟩
  refine eVariationOn_le_of_finite_critical_set (hJ (Nat.zero_le m)) _ hf ?_ hbound
  intro x hx hzero
  exact hfin.mem_toFinset.mpr ⟨hx, hzero⟩


/-- **A continuous function with no zero on an open cell has fixed sign there.**  Immediate from
the intermediate value theorem. -/
theorem sign_fixed_of_no_zero {g : ℝ → ℝ} {a b : ℝ}
    (hg : ContinuousOn g (Icc a b)) (hne : ∀ x ∈ Ioo a b, g x ≠ 0) :
    (∀ x ∈ Ioo a b, 0 < g x) ∨ ∀ x ∈ Ioo a b, g x < 0 := by
  by_cases hex : ∃ x ∈ Ioo a b, 0 < g x
  · obtain ⟨x, hx, hxpos⟩ := hex
    left
    intro y hy
    rcases lt_trichotomy (g y) 0 with hneg | hzero | hpos
    · exfalso
      have hsub : uIcc y x ⊆ Ioo a b :=
        Set.OrdConnected.uIcc_subset Set.ordConnected_Ioo hy hx
      have hcont : ContinuousOn g (uIcc y x) :=
        hg.mono (hsub.trans Ioo_subset_Icc_self)
      have h0 : (0 : ℝ) ∈ uIcc (g y) (g x) := by
        rw [Set.mem_uIcc]
        exact Or.inl ⟨le_of_lt hneg, le_of_lt hxpos⟩
      obtain ⟨z, hz, hgz⟩ := intermediate_value_uIcc hcont h0
      exact hne z (hsub hz) hgz
    · exact absurd hzero (hne y hy)
    · exact hpos
  · right
    push Not at hex
    intro x hx
    rcases lt_trichotomy (g x) 0 with hneg | hzero | hpos
    · exact hneg
    · exact absurd hzero (hne x hx)
    · exact absurd hpos (not_lt.mpr (hex x hx))


end HTGeometry
