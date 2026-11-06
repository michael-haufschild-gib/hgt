import GaloisForLFunctions.ZeroConfigurationGeometry.HeatStepsNeverShrinkTheMesh

/-!
# The Dyson flow keeps the mesh

The zeros of a real-rooted polynomial under `∂_t p = −p″` follow the Dyson flow `ẋ_j = 2 Σ_{k ≠ j} 1/(x_j − x_k)`, and the
squared gap of a pair moves by `d(g²)/dt = 8 − 4g² Σ_k 1/((x' − x_k)(x − x_k))` (`rate_eq_of_dyson`).

* **Compression at the mesh pair** (`sum_inv_mul_le_of_sep`). If the other `R + L` points lie at least `g`-separated on the
  two sides of a pair of gap `g`, their compression is below that of a lattice,
  `g² Σ_k 1/((x' − x_k)(x − x_k)) ≤ 2 − 1/(R + 1) − 1/(L + 1)`, by telescoping over the worst case.
* **Away from the mesh** (`sum_inv_mul_le_of_mesh`). If the other points are `μ`-separated and `μ` away from a pair, then `g²S ≤ 4(g/μ)²`, so a pair much closer than its surroundings opens at nearly full rate.
* **The mesh grows** (`mesh_sq_growth`). So `d(g²)/dt ≥ 4/(R + 1) + 4/(L + 1) ≥ 16/n` at the mesh pair, and a first-touch argument
  gives `μ²(t) ≥ μ²(a) + 16(t − a)/n`. The bound is exact for `n = 2` (`g² = 8t`) and `n = 3` (`g² = 6t` from a triple point). An infinite
  lattice is stationary, in accordance with the rate `16/n → 0`.

The statements are about the flow alone. They hold along every Dyson trajectory, including those that start at a collision.
-/

open Filter Topology Set
open GaloisForLFunctions.ZeroConfigurationGeometry

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-! ## Compression at the mesh pair -/

/-- The telescoping sum of the lattice. -/
theorem sum_range_inv_mul_eq {g : ℝ} (hg : 0 < g) (n : ℕ) :
    ∑ m ∈ Finset.range n, 1 / ((((m : ℝ) + 1) * g) * (((m : ℝ) + 1) * g + g)) =
      (1 - 1 / ((n : ℝ) + 1)) / g ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    have h1 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1 + 1) ≠ 0 := by positivity
    have h3 : ((n : ℝ) + 1) * g + g = ((n : ℝ) + 1 + 1) * g := by ring
    rw [h3]
    field_simp
    ring

/-- One side of the compression: points at least `g`-separated, at distance at least `g` from one end of the pair. -/
theorem sum_side_le {α : Type*} [DecidableEq α] (pos : α → ℝ) {g : ℝ} (hg : 0 < g) (A : Finset α) (c : ℝ)
    (hsep : ∀ x ∈ A, ∀ x' ∈ A, x ≠ x' → g ≤ |pos x - pos x'|) (hle : ∀ x ∈ A, g ≤ c - pos x) :
    ∑ x ∈ A, 1 / ((c - pos x) * (c - pos x + g)) ≤ (1 - 1 / ((A.card : ℝ) + 1)) / g ^ 2 := by
  have h := sum_le_sum_range_of_sep pos hg.le A.card A c (fun D => 1 / (D * (D + g))) rfl
    (fun D hD => by
      have : 0 < D := hg.trans_le hD
      positivity)
    (fun D D' hD hDD' => by
      have hD0 : 0 < D := hg.trans_le hD
      have hD'0 : 0 < D' := hD0.trans_le hDD'
      apply one_div_le_one_div_of_le (by positivity)
      gcongr) hsep hle
  rwa [sum_range_inv_mul_eq hg] at h

/-- **The compression at a separated pair.** With the other points on the right in `R`, on the left in `Le`, all at least
`g`-separated from each other and from the pair, the compression is below that of a lattice. -/
theorem sum_inv_mul_le_of_sep {x x' g : ℝ} (hg : 0 < g) (hgap : x' - x = g) {R Le : Finset ℝ}
    (hRsep : ∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → g ≤ |y - y'|) (hLsep : ∀ y ∈ Le, ∀ y' ∈ Le, y ≠ y' → g ≤ |y - y'|)
    (hR : ∀ y ∈ R, g ≤ y - x') (hL : ∀ y ∈ Le, g ≤ x - y) :
    ∑ y ∈ R, 1 / ((x' - y) * (x - y)) + ∑ y ∈ Le, 1 / ((x' - y) * (x - y)) ≤
      (2 - 1 / ((R.card : ℝ) + 1) - 1 / ((Le.card : ℝ) + 1)) / g ^ 2 := by
  have hright := sum_side_le (fun y : ℝ => -y) hg R (-x')
    (fun y hy y' hy' hne => by
      have := hRsep y hy y' hy' hne
      rwa [show -y - -y' = -(y - y') by ring, abs_neg])
    (fun y hy => by linarith only [hR y hy])
  have hleft := sum_side_le (fun y : ℝ => y) hg Le x hLsep hL
  have hR' : ∑ y ∈ R, 1 / ((x' - y) * (x - y)) =
      ∑ y ∈ R, 1 / ((-x' - -y) * (-x' - -y + g)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    rw [← hgap]
    ring
  have hL' : ∑ y ∈ Le, 1 / ((x' - y) * (x - y)) = ∑ y ∈ Le, 1 / ((x - y) * (x - y + g)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    congr 1
    rw [← hgap]
    ring
  rw [hR', hL']
  have hsplit : (2 - 1 / ((R.card : ℝ) + 1) - 1 / ((Le.card : ℝ) + 1)) / g ^ 2 =
      (1 - 1 / ((R.card : ℝ) + 1)) / g ^ 2 + (1 - 1 / ((Le.card : ℝ) + 1)) / g ^ 2 := by
    ring
  rw [hsplit]
  exact add_le_add hright hleft

/-- `4/(R + 1) + 4/(L + 1) ≥ 16/(R + L + 2)`. -/
theorem sixteen_div_le (R L : ℝ) (hR : 0 ≤ R) (hL : 0 ≤ L) :
    16 / (R + L + 2) ≤ 4 / (R + 1) + 4 / (L + 1) := by
  have h1 : 0 < R + 1 := by linarith only [hR]
  have h2 : 0 < L + 1 := by linarith only [hL]
  have h3 : 0 < R + L + 2 := by linarith only [hR, hL]
  rw [div_add_div _ _ h1.ne' h2.ne', div_le_div_iff₀ h3 (by positivity)]
  nlinarith only [sq_nonneg (R - L)]

/-! ## The first touch -/

/-- **First touch for a finite family.** If a function of the family can reach `0` while all others are nonnegative only with
positive right derivative, then no member becomes negative. -/
theorem nonneg_of_first_touch {ι : Type*} [Finite ι] {f : ι → ℝ → ℝ} {a b : ℝ}
    (hc : ∀ i, ContinuousOn (f i) (Icc a b)) (h0 : ∀ i, 0 ≤ f i a)
    (hd : ∀ s ∈ Ico a b, ∀ i, f i s = 0 → (∀ j, 0 ≤ f j s) →
      ∃ D > 0, HasDerivWithinAt (f i) D (Ici s) s) :
    ∀ s ∈ Icc a b, ∀ i, 0 ≤ f i s := by
  by_contra hcon
  push Not at hcon
  obtain ⟨s₁, hs₁, i₁, hneg⟩ := hcon
  set T := {s | s ∈ Icc a b ∧ ∃ i, f i s < 0} with hT
  have hs₁T : s₁ ∈ T := ⟨hs₁, i₁, hneg⟩
  have hTne : T.Nonempty := ⟨s₁, hs₁T⟩
  have hTbdd : BddBelow T := ⟨a, fun s hs => hs.1.1⟩
  set c := sInf T with hcdef
  have hac : a ≤ c := le_csInf hTne fun s hs => hs.1.1
  have hcs₁ : c ≤ s₁ := csInf_le hTbdd hs₁T
  have hcb : c ≤ b := hcs₁.trans hs₁.2
  have hcI : c ∈ Icc a b := ⟨hac, hcb⟩
  -- all members are nonnegative at `c`
  have hall : ∀ j, 0 ≤ f j c := by
    intro j
    rcases hac.eq_or_lt with heq | hlt
    · rw [← heq]
      exact h0 j
    · have hcw : ContinuousWithinAt (f j) (Ico a c) c :=
        (hc j c hcI).mono fun s hs => ⟨hs.1, hs.2.le.trans hcb⟩
      haveI : (𝓝[Ico a c] c).NeBot := right_nhdsWithin_Ico_neBot hlt
      refine ge_of_tendsto hcw.tendsto ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      by_contra hn
      have hsT : s ∈ T := ⟨⟨hs.1, hs.2.le.trans hcb⟩, j, not_le.mp hn⟩
      exact absurd (csInf_le hTbdd hsT) (not_le.mpr hs.2)
  have hcT : c ∉ T := fun h => by
    obtain ⟨-, i, hi⟩ := h
    exact absurd (hall i) (not_le.mpr hi)
  have hcltb : c < s₁ := lt_of_le_of_ne hcs₁ fun h => hcT (by rw [h]; exact hs₁T)
  -- along a sequence decreasing to `c` some fixed member stays negative
  have hfreq : ∃ᶠ s in 𝓝[>] c, s ∈ T := by
    rw [Filter.frequently_iff]
    intro U hU
    obtain ⟨d, hd', hsub⟩ := (mem_nhdsGT_iff_exists_Ioo_subset).mp hU
    obtain ⟨s, hsT, hsd⟩ := exists_lt_of_csInf_lt hTne (show c < d from hd')
    have hsc : c < s := lt_of_le_of_ne (csInf_le hTbdd hsT) fun h => hcT (by rw [h]; exact hsT)
    exact ⟨s, hsub ⟨hsc, hsd⟩, hsT⟩
  have hexists : ∃ i, ∃ᶠ s in 𝓝[>] c, s ∈ Icc a b ∧ f i s < 0 := by
    by_contra hno
    push Not at hno
    have hev : ∀ᶠ s in 𝓝[>] c, ∀ i, s ∈ Icc a b → 0 ≤ f i s := Filter.eventually_all.mpr hno
    obtain ⟨s, hsT, hsev⟩ := (hfreq.and_eventually hev).exists
    obtain ⟨hsI, i, hi⟩ := hsT
    exact absurd (hsev i hsI) (not_le.mpr hi)
  obtain ⟨i, hi⟩ := hexists
  have hicb : c ∈ Ico a b := ⟨hac, hcltb.trans_le hs₁.2⟩
  -- the member vanishes at `c`
  have hzero : f i c = 0 := by
    refine le_antisymm ?_ (hall i)
    by_contra hpos
    have hev := (hc i c hcI).eventually (lt_mem_nhds (not_le.mp hpos))
    rw [eventually_nhdsWithin_iff] at hev
    obtain ⟨s, ⟨hsI, hsneg⟩, hspos⟩ := (hi.and_eventually (hev.filter_mono nhdsWithin_le_nhds)).exists
    exact absurd (hspos hsI) (not_lt.mpr hsneg.le)
  -- but it has positive right derivative there
  obtain ⟨D, hDpos, hD⟩ := hd c hicb i hzero hall
  have hslope := (hasDerivWithinAt_iff_tendsto_slope' (notMem_Ioi.mpr le_rfl)).mp hD.Ioi_of_Ici
  have hevs : ∀ᶠ s in 𝓝[>] c, 0 < slope (f i) c s := hslope.eventually (lt_mem_nhds hDpos)
  obtain ⟨s, ⟨-, hsneg⟩, hs1, hs2⟩ :=
    (hi.and_eventually (hevs.and self_mem_nhdsWithin)).exists
  rw [slope_def_field, hzero, sub_zero] at hs1
  have hsc : 0 < s - c := sub_pos.mpr hs2
  have := (div_pos_iff_of_pos_right hsc).mp hs1
  exact absurd this (not_lt.mpr hsneg.le)

/-! ## The mesh under the Dyson flow -/

/-- The Dyson velocity of the `j`-th point. -/
def dysonVelocity {n : ℕ} (y : Fin n → ℝ) (j : Fin n) : ℝ :=
  2 * ∑ k ∈ Finset.univ.erase j, 1 / (y j - y k)

/-- **The gap rate under the Dyson flow.** -/
theorem rate_eq_of_dyson {n : ℕ} {y : Fin n → ℝ} {i j : Fin n} (hij : i ≠ j) (hinj : Function.Injective y) :
    2 * (y j - y i) * (dysonVelocity y j - dysonVelocity y i) =
      8 - 4 * (y j - y i) ^ 2 * ∑ k ∈ (Finset.univ.erase i).erase j,
        1 / ((y j - y k) * (y i - y k)) := by
  classical
  have hgne : y j - y i ≠ 0 := sub_ne_zero.mpr fun h => hij (hinj h).symm
  have hgne' : y i - y j ≠ 0 := sub_ne_zero.mpr fun h => hij (hinj h)
  have hie : i ∈ Finset.univ.erase j := Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
  have hje : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ _⟩
  have hswap : (Finset.univ.erase j).erase i = (Finset.univ.erase i).erase j :=
    Finset.erase_right_comm
  set T := (Finset.univ.erase i).erase j with hT
  have h1 : ∑ k ∈ Finset.univ.erase j, 1 / (y j - y k) =
      1 / (y j - y i) + ∑ k ∈ T, 1 / (y j - y k) := by
    rw [← Finset.add_sum_erase _ _ hie, hswap]
  have h2 : ∑ k ∈ Finset.univ.erase i, 1 / (y i - y k) =
      1 / (y i - y j) + ∑ k ∈ T, 1 / (y i - y k) := by
    rw [← Finset.add_sum_erase _ _ hje]
  have h3 : ∑ k ∈ T, 1 / (y j - y k) - ∑ k ∈ T, 1 / (y i - y k) =
      -(y j - y i) * ∑ k ∈ T, 1 / ((y j - y k) * (y i - y k)) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    have hki : k ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have h4 : y j - y k ≠ 0 := sub_ne_zero.mpr fun h => hkj (hinj h).symm
    have h5 : y i - y k ≠ 0 := sub_ne_zero.mpr fun h => hki (hinj h).symm
    field_simp
    ring
  have h6 : 1 / (y i - y j) = -(1 / (y j - y i)) := by
    rw [show y i - y j = -(y j - y i) by ring, one_div, one_div, inv_neg]
  have h7 : (y j - y i) * (1 / (y j - y i)) = 1 := by field_simp
  simp only [dysonVelocity]
  rw [h1, h2, h6]
  linear_combination (8 : ℝ) * h7 + 4 * (y j - y i) * h3

/-- **The rate at a mesh pair of `n` points.** If `y_j − y_i` is the least gap of an ordered configuration, then its square opens under the Dyson flow at rate at least `16/n`. -/
theorem rate_ge_of_mesh_pair {n : ℕ} {y : Fin n → ℝ} (hstrict : StrictMono y) {i j : Fin n} (hij : i < j)
    (hsep : ∀ k l : Fin n, k < l → y j - y i ≤ y l - y k) :
    16 / (n : ℝ) ≤ 2 * (y j - y i) * (dysonVelocity y j - dysonVelocity y i) := by
  classical
  set g := y j - y i with hg
  have hgpos : 0 < g := sub_pos.mpr (hstrict hij)
  -- so the other points lie outside the pair
  have hout (k : Fin n) (hki : k ≠ i) (hkj : k ≠ j) : k < i ∨ j < k := by
    by_contra hcon
    push Not at hcon
    have hik : i < k := lt_of_le_of_ne hcon.1 hki.symm
    have hkj' : k < j := lt_of_le_of_ne hcon.2 hkj
    have h1 := hsep i k hik
    have h2 := hsep k j hkj'
    have h3 : y j - y i = (y j - y k) + (y k - y i) := by ring
    linarith only [h1, h2, h3, hg, hgpos]
  set Rk := (Finset.univ : Finset (Fin n)).filter (fun k => j < k) with hRk
  set Lk := (Finset.univ : Finset (Fin n)).filter (fun k => k < i) with hLk
  have hinj : Function.Injective y := hstrict.injective
  set R := Rk.image y with hR
  set Le := Lk.image y with hLe
  have hRcard : R.card = Rk.card := Finset.card_image_of_injective _ hinj
  have hLcard : Le.card = Lk.card := Finset.card_image_of_injective _ hinj
  have hcomp := sum_inv_mul_le_of_sep (x := y i) (x' := y j) hgpos rfl (R := R) (Le := Le)
    (by
      intro a₁ ha₁ a₂ ha₂ hne
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha₁
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ha₂
      rcases lt_or_gt_of_ne (fun h => hne (congrArg y h) : k ≠ l) with h | h
      · rw [abs_sub_comm]
        exact (hsep k l h).trans (le_abs_self _)
      · exact (hsep l k h).trans (le_abs_self _))
    (by
      intro a₁ ha₁ a₂ ha₂ hne
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha₁
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ha₂
      rcases lt_or_gt_of_ne (fun h => hne (congrArg y h) : k ≠ l) with h | h
      · rw [abs_sub_comm]
        exact (hsep k l h).trans (le_abs_self _)
      · exact (hsep l k h).trans (le_abs_self _))
    (by
      intro a₁ ha₁
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha₁
      exact hsep j k (Finset.mem_filter.mp hk).2)
    (by
      intro a₁ ha₁
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha₁
      exact hsep k i (Finset.mem_filter.mp hk).2)
  -- the rest of the points is the disjoint union of the two sides
  have hrest : (Finset.univ.erase i).erase j = Rk ∪ Lk := by
    ext k
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_union, hRk, hLk,
      Finset.mem_filter, true_and]
    constructor
    · rintro ⟨hkj, hki⟩
      exact (hout k hki hkj).symm
    · rintro (h | h)
      · exact ⟨h.ne', (hij.trans h).ne'⟩
      · exact ⟨(h.trans hij).ne, h.ne⟩
  have hdisj : Disjoint Rk Lk := Finset.disjoint_left.mpr fun k h1 h2 => by
    have h3 := (Finset.mem_filter.mp h1).2
    have h4 := (Finset.mem_filter.mp h2).2
    exact absurd (h4.trans (hij.trans h3)) (lt_irrefl _)
  have hsumsplit : ∑ k ∈ (Finset.univ.erase i).erase j, 1 / ((y j - y k) * (y i - y k)) =
      ∑ w ∈ R, 1 / ((y j - w) * (y i - w)) + ∑ w ∈ Le, 1 / ((y j - w) * (y i - w)) := by
    rw [hrest, Finset.sum_union hdisj, hR, hLe, Finset.sum_image fun _ _ _ _ h => hinj h,
      Finset.sum_image fun _ _ _ _ h => hinj h]
  -- the rate
  have hid := rate_eq_of_dyson (y := y) (i := i) (j := j) hij.ne hinj
  rw [hsumsplit, ← hg] at hid
  have hg2 : 0 < g ^ 2 := by positivity
  have hbound : g ^ 2 * (∑ w ∈ R, 1 / ((y j - w) * (y i - w)) + ∑ w ∈ Le, 1 / ((y j - w) * (y i - w))) ≤
      2 - 1 / ((R.card : ℝ) + 1) - 1 / ((Le.card : ℝ) + 1) := by
    have := mul_le_mul_of_nonneg_left hcomp hg2.le
    rwa [mul_div_cancel₀ _ hg2.ne'] at this
  have hcardsum : (R.card : ℝ) + (Le.card : ℝ) + 2 ≤ n := by
    have hdisj2 : Disjoint (Rk ∪ Lk) ({i, j} : Finset (Fin n)) := by
      rw [Finset.disjoint_left]
      intro k hk hk'
      rcases Finset.mem_union.mp hk with h | h
      · have h3 := (Finset.mem_filter.mp h).2
        rcases Finset.mem_insert.mp hk' with rfl | h4
        · exact absurd (hij.trans h3) (lt_irrefl _)
        · rw [Finset.mem_singleton.mp h4] at h3
          exact absurd h3 (lt_irrefl _)
      · have h3 := (Finset.mem_filter.mp h).2
        rcases Finset.mem_insert.mp hk' with rfl | h4
        · exact absurd h3 (lt_irrefl _)
        · rw [Finset.mem_singleton.mp h4] at h3
          exact absurd (h3.trans hij) (lt_irrefl _)
    have hle := Finset.card_le_univ ((Rk ∪ Lk) ∪ ({i, j} : Finset (Fin n)))
    rw [Finset.card_union_of_disjoint hdisj2, Finset.card_union_of_disjoint hdisj,
      Finset.card_pair hij.ne, Fintype.card_fin] at hle
    rw [hRcard, hLcard]
    exact_mod_cast hle
  have hRn : (0 : ℝ) ≤ R.card := Nat.cast_nonneg _
  have hLn : (0 : ℝ) ≤ Le.card := Nat.cast_nonneg _
  have h16 := sixteen_div_le _ _ hRn hLn
  have hmono16 : 16 / (n : ℝ) ≤ 16 / ((R.card : ℝ) + (Le.card : ℝ) + 2) :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcardsum
  have hr1 : 4 / ((R.card : ℝ) + 1) = 4 * (1 / ((R.card : ℝ) + 1)) := by ring
  have hr2 : 4 / ((Le.card : ℝ) + 1) = 4 * (1 / ((Le.card : ℝ) + 1)) := by ring
  have hrategt : 16 / (n : ℝ) ≤ 2 * g * (dysonVelocity y j - dysonVelocity y i) := by
    rw [hid]
    nlinarith only [hbound, h16, hmono16, hr1, hr2]
  exact hrategt

/-- **The mesh grows under the Dyson flow.** If `x` follows the Dyson flow in strict order on `[a, b]`, the least squared gap
increases at rate at least `16/n`: `μ²(s) ≥ μ²(a) + 16(s − a)/n`. -/
theorem mesh_sq_growth {n : ℕ} (hn : 2 ≤ n) {x : Fin n → ℝ → ℝ} {a b m₀ : ℝ}
    (hmono : ∀ s ∈ Icc a b, StrictMono fun j => x j s)
    (hcont : ∀ j, ContinuousOn (x j) (Icc a b))
    (hflow : ∀ j, ∀ s ∈ Ico a b, HasDerivWithinAt (x j) (dysonVelocity (fun k => x k s) j) (Ici s) s)
    (hstart : ∀ i j : Fin n, i < j → m₀ ≤ (x j a - x i a) ^ 2) :
    ∀ s ∈ Icc a b, ∀ i j : Fin n, i < j → m₀ + 16 / (n : ℝ) * (s - a) ≤ (x j s - x i s) ^ 2 := by
  classical
  have hnpos : (0 : ℝ) < n := by
    have : (2 : ℝ) ≤ n := by exact_mod_cast hn
    linarith only [this]
  -- first touch for every rate below `16/n`
  have hrate : ∀ r : ℝ, r < 16 / (n : ℝ) → ∀ s ∈ Icc a b, ∀ i j : Fin n, i < j →
      m₀ + r * (s - a) ≤ (x j s - x i s) ^ 2 := by
    intro r hr s hs i j hij
    set ι := {p : Fin n × Fin n // p.1 < p.2}
    set f : ι → ℝ → ℝ := fun p u => (x p.1.2 u - x p.1.1 u) ^ 2 - m₀ - r * (u - a) with hf
    have hfc (p : ι) : ContinuousOn (f p) (Icc a b) := by
      simp only [hf]
      exact ((((hcont p.1.2).sub (hcont p.1.1)).pow 2).sub continuousOn_const).sub
        (continuousOn_const.mul (continuousOn_id.sub continuousOn_const))
    have hf0 (p : ι) : 0 ≤ f p a := by
      simp only [hf, sub_self, mul_zero, sub_zero]
      linarith only [hstart _ _ p.2]
    have hmain := nonneg_of_first_touch hfc hf0 (by
      intro u hu p hp hall
      obtain ⟨⟨i, j⟩, hij⟩ := p
      simp only [hf] at hp hall
      have huI : u ∈ Icc a b := Ico_subset_Icc_self hu
      set y : Fin n → ℝ := fun k => x k u with hy
      have hstrict : StrictMono y := hmono u huI
      set g := y j - y i with hg
      have hgpos : 0 < g := sub_pos.mpr (hstrict hij)
      have hgsq : g ^ 2 = m₀ + r * (u - a) := by
        have : (x j u - x i u) ^ 2 - m₀ - r * (u - a) = 0 := hp
        rw [hg]
        linarith only [this]
      -- every gap is at least `g`
      have hsep (k l : Fin n) (hkl : k < l) : g ≤ y l - y k := by
        have h1 := hall ⟨(k, l), hkl⟩
        have h2 : g ^ 2 ≤ (y l - y k) ^ 2 := by
          rw [hgsq]
          linarith only [h1]
        exact abs_le_of_sq_le_sq' h2 (sub_pos.mpr (hstrict hkl)).le |>.2
      have hrategt := rate_ge_of_mesh_pair hstrict hij hsep
      -- the derivative of the family member
      have hdj := hflow j u hu
      have hdi := hflow i u hu
      have hfd : HasDerivWithinAt
          (fun w => (x j w - x i w) ^ 2 - m₀ - r * (w - a))
          (2 * (x j u - x i u) * (dysonVelocity y j - dysonVelocity y i) - r) (Ici u) u := by
        have h1 := ((hdj.sub hdi).pow 2)
        have h2 : HasDerivWithinAt (fun w : ℝ => r * (w - a)) r (Ici u) u := by
          simpa using (((hasDerivAt_id u).sub_const a).const_mul r).hasDerivWithinAt
        have h3 := (h1.sub_const m₀).sub h2
        refine h3.congr_deriv ?_
        simp only [Pi.sub_apply]
        norm_num
        exact Or.inl rfl
      refine ⟨_, ?_, hfd⟩
      have : 2 * (x j u - x i u) * (dysonVelocity y j - dysonVelocity y i) = 2 * g * (dysonVelocity y j - dysonVelocity y i) := rfl
      rw [this]
      linarith only [hrategt, hr]) s hs ⟨(i, j), hij⟩
    simp only [hf] at hmain
    linarith only [hmain]
  -- letting the rate tend to `16/n`
  intro s hs i j hij
  have hsa : 0 ≤ s - a := by linarith only [hs.1]
  refine le_of_forall_pos_le_add fun ε hε => ?_
  rcases hsa.eq_or_lt with h0 | hpos
  · have := hrate (16 / (n : ℝ) - 1) (by linarith only) s hs i j hij
    rw [← h0, mul_zero] at this ⊢
    linarith only [this, hε]
  · have := hrate (16 / (n : ℝ) - ε / (s - a)) (by
      have : 0 < ε / (s - a) := by positivity
      linarith only [this]) s hs i j hij
    have heq : (16 / (n : ℝ) - ε / (s - a)) * (s - a) = 16 / (n : ℝ) * (s - a) - ε := by
      field_simp
    rw [heq] at this
    linarith only [this]

/-- The elementary sum `Σ_{k ≤ n} 1/k² ≤ 2`. -/
theorem sum_range_inv_sq_le (n : ℕ) : ∑ m ∈ Finset.range n, 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 := by
  have h (n : ℕ) : ∑ m ∈ Finset.range (n + 1), 1 / ((m : ℝ) + 1) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
      rw [Finset.sum_range_succ]
      push_cast
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h2 : (0 : ℝ) < (n : ℝ) + 1 + 1 := by positivity
      have h3 : 1 / ((n : ℝ) + 1 + 1) ^ 2 ≤ 1 / ((n : ℝ) + 1) - 1 / ((n : ℝ) + 1 + 1) := by
        rw [div_sub_div _ _ h1.ne' h2.ne', div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [h1, h2]
      linarith only [ih, h3]
  cases n with
  | zero => simp
  | succ n =>
    have h1 := h n
    have h2 : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith only [h1, h2]

/-- **Compression away from the mesh.** If the other points are `μ`-separated, and at distance at least `μ` from a pair of gap `g`, each side of the pair compresses it by at most `2/μ²`, whatever the ratio `g/μ`. So `g²S ≤ 4(g/μ)²`: a pair much closer than its surroundings opens at nearly full rate. -/
theorem sum_inv_mul_le_of_mesh {x x' μ : ℝ} (hμ : 0 < μ) (hxx' : x ≤ x') {R Le : Finset ℝ}
    (hRsep : ∀ y ∈ R, ∀ y' ∈ R, y ≠ y' → μ ≤ |y - y'|) (hLsep : ∀ y ∈ Le, ∀ y' ∈ Le, y ≠ y' → μ ≤ |y - y'|)
    (hR : ∀ y ∈ R, μ ≤ y - x') (hL : ∀ y ∈ Le, μ ≤ x - y) :
    ∑ y ∈ R, 1 / ((x' - y) * (x - y)) + ∑ y ∈ Le, 1 / ((x' - y) * (x - y)) ≤ 4 / μ ^ 2 := by
  have hside {A : Finset ℝ} (pos : ℝ → ℝ) (c : ℝ) (hsep : ∀ y ∈ A, ∀ y' ∈ A, y ≠ y' → μ ≤ |pos y - pos y'|)
      (hle : ∀ y ∈ A, μ ≤ c - pos y) :
      ∑ y ∈ A, 1 / (c - pos y) ^ 2 ≤ 2 / μ ^ 2 := by
    have h := sum_le_sum_range_of_sep pos hμ.le A.card A c (fun D => 1 / D ^ 2) rfl
      (fun D hD => by positivity)
      (fun D D' hD hDD' => by
        have hD0 : 0 < D := hμ.trans_le hD
        exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ hD0.le hDD' 2)) hsep hle
    refine h.trans ?_
    have h2 : ∑ m ∈ Finset.range A.card, 1 / (((m : ℝ) + 1) * μ) ^ 2 =
        (∑ m ∈ Finset.range A.card, 1 / ((m : ℝ) + 1) ^ 2) / μ ^ 2 := by
      rw [Finset.sum_div]
      refine Finset.sum_congr rfl fun m _ => ?_
      have : (0 : ℝ) < (m : ℝ) + 1 := by positivity
      field_simp
    rw [h2]
    exact div_le_div_of_nonneg_right (sum_range_inv_sq_le _) (by positivity)
  have hright := hside (A := R) (fun y => -y) (-x')
    (fun y hy y' hy' hne => by
      have := hRsep y hy y' hy' hne
      rwa [show -y - -y' = -(y - y') by ring, abs_neg])
    (fun y hy => by linarith only [hR y hy])
  have hleft := hside (A := Le) (fun y => y) x hLsep hL
  have h1 : ∑ y ∈ R, 1 / ((x' - y) * (x - y)) ≤ ∑ y ∈ R, 1 / (-x' - -y) ^ 2 := by
    refine Finset.sum_le_sum fun y hy => ?_
    have h2 := hR y hy
    have h3 : 0 < -x' - -y := by linarith only [h2, hμ]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h4 : (x' - y) * (x - y) = (-x' - -y) * (-x' - -y + (x' - x)) := by ring
    rw [h4]
    nlinarith only [h3, mul_nonneg h3.le (sub_nonneg.mpr hxx')]
  have h2 : ∑ y ∈ Le, 1 / ((x' - y) * (x - y)) ≤ ∑ y ∈ Le, 1 / (x - y) ^ 2 := by
    refine Finset.sum_le_sum fun y hy => ?_
    have h2 := hL y hy
    have h3 : 0 < x - y := by linarith only [h2, hμ]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have h4 : (x' - y) * (x - y) = (x - y) * (x - y + (x' - x)) := by ring
    rw [h4]
    nlinarith only [h3, mul_nonneg h3.le (sub_nonneg.mpr hxx')]
  have h5 : 4 / μ ^ 2 = 2 / μ ^ 2 + 2 / μ ^ 2 := by ring
  rw [h5]
  exact add_le_add (h1.trans hright) (h2.trans hleft)

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
