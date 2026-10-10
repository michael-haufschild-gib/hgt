import GaloisForLFunctions.HTGeometry.ToeplitzGeometricBranching
import GaloisForLFunctions.HTGeometry.ToeplitzGeometricTotalPositivity
import GaloisForLFunctions.HTGeometry.ToeplitzTotalPositivityTwoTerm
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The corner ratio of Toeplitz minors of geometric products

Let `a` be the coefficient sequence of `∏_{s ≤ N} 1/(1 − x_s u)` with `x₁ ≥ x₂ ≥ … ≥ x_N ≥ 0`, and
let `M(j) = det (a_{j_c − i_r})` be a Toeplitz minor with strictly increasing rows `i` and columns
`j` (`m` columns).  For every `r`,

`x_r · Σ_{c ≥ m − r, j_c ≥ 1} M(j − e_c) ≤ r · M(j)`

(`cornerRatio_geomProdSeq`), with `x_r = 0` for `r > N`.  In Schur-function language,
`r · s_{λ/μ}(x) ≥ x_r · Σ_{i ≤ r} s_{(λ − e_i)/μ}(x)`: column `c` is row `m − c` of the shape.  In
particular, lowering one of the last `r` columns by one costs at most the factor `r/x_r`.

The proof is a double induction on the number of variables, using the branching rule
`M_{x,y}(j) = Σ_{l interlacing j} y^{|j| − |l|} M_x(l)` (`toeplitzMinor_cauchyConv_geometric`).
The terms on the left are pairs `(c, κ)` with `κ` interlacing `j − e_c`.  A pair is *good* when
`κ + e_c` interlaces `j`.  Otherwise it is *bad*, which forces `κ_{c+1} = j_c`, and then
`κ + e_{c+1}` interlaces `j`.  Good pairs go to the slot `(κ + e_c, c)` and bad pairs to
`(κ + e_{c+1}, c + 1)`.  No good pair and bad pair share a slot, so pairs map injectively into the
terms of the same inequality for `l = κ + e_label` with one variable fewer.

* `N > r`: peel the smallest variable; the `r`-th largest variable is unchanged.
* `N = r`: peel the largest variable `x₁`.  Labels `≥ m − r + 1` are covered by the statement for
  `r − 1`, whose `(r−1)`-th variable is `x_r`.  Good pairs at column `m − r` are charged to the
  term `l = κ` itself, at cost `x_r/x₁ ≤ 1`, at most once each.
-/

open Finset Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Geometric products -/

/-- The power series `1/(1 − x u) = Σ xⁿ uⁿ`. -/
def geomPowerSeries (x : ℝ) : PowerSeries ℝ := PowerSeries.mk fun n => x ^ n

/-- The coefficient sequence of `∏_{x ∈ xs} 1/(1 − x u)`. -/
def geomProdSeq (xs : List ℝ) (n : ℕ) : ℝ := PowerSeries.coeff n (xs.map geomPowerSeries).prod

theorem cauchyConv_coeff (P Q : PowerSeries ℝ) :
    cauchyConv (fun n => PowerSeries.coeff n P) (fun n => PowerSeries.coeff n Q) =
      fun n => PowerSeries.coeff n (P * Q) := by
  funext n
  rw [PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun p q => PowerSeries.coeff p P *
      PowerSeries.coeff q Q)]
  rfl

theorem coeff_geomPowerSeries (x : ℝ) (n : ℕ) :
    PowerSeries.coeff n (geomPowerSeries x) = x ^ n := by
  simp [geomPowerSeries]

theorem geomProdSeq_cons (x : ℝ) (xs : List ℝ) :
    geomProdSeq (x :: xs) = cauchyConv (geomProdSeq xs) fun n => x ^ n := by
  have hx : (fun n : ℕ => x ^ n) = fun n => PowerSeries.coeff n (geomPowerSeries x) :=
    funext fun n => (coeff_geomPowerSeries x n).symm
  rw [hx]
  unfold geomProdSeq
  rw [cauchyConv_coeff]
  funext n
  rw [List.map_cons, List.prod_cons, mul_comm]

theorem geomProdSeq_append_singleton (xs : List ℝ) (y : ℝ) :
    geomProdSeq (xs ++ [y]) = cauchyConv (geomProdSeq xs) fun n => y ^ n := by
  have hy : (fun n : ℕ => y ^ n) = fun n => PowerSeries.coeff n (geomPowerSeries y) :=
    funext fun n => (coeff_geomPowerSeries y n).symm
  rw [hy]
  unfold geomProdSeq
  rw [cauchyConv_coeff]
  funext n
  rw [List.map_append, List.prod_append, List.map_singleton, List.prod_singleton]

theorem geomProdSeq_nil : geomProdSeq [] = twoTermSeq 1 0 := by
  funext n
  simp only [geomProdSeq, List.map_nil, List.prod_nil, twoTermSeq]
  rw [PowerSeries.coeff_one]
  split_ifs <;> simp_all

/-- Geometric products of nonnegative ratios are `PF_k` for every `k`. -/
theorem pfSeq_geomProdSeq {xs : List ℝ} (hxs : ∀ x ∈ xs, 0 ≤ x) (k : ℕ) :
    PFSeq k (geomProdSeq xs) := by
  induction xs with
  | nil =>
    rw [geomProdSeq_nil]
    exact PFSeq.twoTerm zero_le_one le_rfl k
  | cons x xs ih =>
    rw [geomProdSeq_cons]
    exact (ih fun y hy => hxs y (List.mem_cons_of_mem x hy)).conv
      (PFSeq.geometric (hxs x List.mem_cons_self) k)

/-! ## Raising and lowering one column -/

/-- Lower column `c` by one. -/
def colDecr {m : ℕ} (j : Fin m → ℕ) (c : Fin m) : Fin m → ℕ := Function.update j c (j c - 1)

/-- Raise column `c` by one. -/
def colIncr {m : ℕ} (j : Fin m → ℕ) (c : Fin m) : Fin m → ℕ := Function.update j c (j c + 1)

theorem colDecr_colIncr {m : ℕ} (κ : Fin m → ℕ) (c : Fin m) : colDecr (colIncr κ c) c = κ := by
  funext c'
  by_cases h : c' = c
  · subst h; simp [colDecr, colIncr]
  · simp [colDecr, colIncr, Function.update_of_ne h]

/-- A Toeplitz minor with two equal column indices vanishes. -/
theorem toeplitzMinor_eq_zero_of_eq {a : ℕ → ℝ} {m : ℕ} {i j : Fin m → ℕ} {c₁ c₂ : Fin m}
    (hne : c₁ ≠ c₂) (heq : j c₁ = j c₂) : toeplitzMinor a m i j = 0 := by
  unfold toeplitzMinor
  exact det_zero_of_column_eq hne fun r => by simp [heq]

/-- Lowering one column of a strictly increasing index keeps a `PF` minor nonnegative: either the
columns stay strictly increasing, or two of them coincide. -/
theorem toeplitzMinor_colDecr_nonneg {a : ℕ → ℝ} {m : ℕ} (ha : PFSeq m a) {i j : Fin m → ℕ}
    (hi : StrictMono i) (hj : StrictMono j) (c : Fin m) :
    0 ≤ toeplitzMinor a m i (colDecr j c) := by
  by_cases hmono : StrictMono (colDecr j c)
  · exact ha m le_rfl i _ hi hmono
  · rw [StrictMono] at hmono
    push Not at hmono
    obtain ⟨c₁, c₂, h12, hle⟩ := hmono
    by_cases h1 : c₁ = c
    · subst h1
      have : j c₁ < j c₂ := hj h12
      simp only [colDecr, Function.update_self, Function.update_of_ne (ne_of_gt h12)] at hle
      omega
    · by_cases h2 : c₂ = c
      · subst h2
        have hlt : j c₁ < j c₂ := hj h12
        simp only [colDecr, Function.update_self, Function.update_of_ne h1] at hle
        have heq : colDecr j c₂ c₁ = colDecr j c₂ c₂ := by
          simp only [colDecr, Function.update_self, Function.update_of_ne h1]
          omega
        exact (toeplitzMinor_eq_zero_of_eq h1 heq).ge
      · simp only [colDecr, Function.update_of_ne h1, Function.update_of_ne h2] at hle
        exact absurd (hj h12) (not_lt.mpr hle)

/-! ## Good and bad pairs -/

/-- The bad case: the column after `c` sits at `j_c`. -/
def IsBadPair {m : ℕ} (j : Fin m → ℕ) (c : Fin m) (κ : Fin m → ℕ) : Prop :=
  ∃ c₁ : Fin m, c₁.val = c.val + 1 ∧ κ c₁ = j c

/-- A good pair raises column `c` back to an interlacing column set of `j`. -/
theorem colIncr_mem_interlaceSet_of_good {m : ℕ} {j κ : Fin m → ℕ} {c : Fin m} (hc : 0 < j c)
    (hκ : κ ∈ interlaceSet (colDecr j c)) (hgood : ¬ IsBadPair j c κ) :
    colIncr κ c ∈ interlaceSet j := by
  rw [mem_interlaceSet] at hκ ⊢
  obtain ⟨h1, h2⟩ := hκ
  refine ⟨fun c' => ?_, fun c₂ c₁ h => ?_⟩
  · by_cases h : c' = c
    · subst h
      have := h1 c'
      simp only [colDecr, Function.update_self] at this
      simp only [colIncr, Function.update_self]
      omega
    · have := h1 c'
      simp only [colDecr, Function.update_of_ne h] at this
      simp only [colIncr, Function.update_of_ne h]
      exact this
  · have hc₁ : c₁ ≠ c₂ := by intro e; rw [e] at h; omega
    by_cases hc2 : c₂ = c
    · subst hc2
      have := h2 c₂ c₁ h
      simp only [colDecr, Function.update_of_ne hc₁] at this
      simp only [colIncr, Function.update_self]
      omega
    · by_cases hc1 : c₁ = c
      · subst hc1
        have := h2 c₂ c₁ h
        simp only [colDecr, Function.update_self] at this
        simp only [colIncr, Function.update_of_ne hc2]
        have hne : κ c₂ ≠ j c₁ := fun e => hgood ⟨c₂, by omega, e⟩
        omega
      · have := h2 c₂ c₁ h
        simp only [colDecr, Function.update_of_ne hc1] at this
        simp only [colIncr, Function.update_of_ne hc2]
        exact this

/-- A bad pair raises the next column to an interlacing column set of `j`. -/
theorem colIncr_mem_interlaceSet_of_bad {m : ℕ} {j κ : Fin m → ℕ} (hj : StrictMono j) {c c₁ : Fin m}
    (hκ : κ ∈ interlaceSet (colDecr j c)) (hc₁ : c₁.val = c.val + 1) (hbad : κ c₁ = j c) :
    colIncr κ c₁ ∈ interlaceSet j := by
  rw [mem_interlaceSet] at hκ ⊢
  obtain ⟨h1, h2⟩ := hκ
  have hcc₁ : c ≠ c₁ := by intro e; rw [e] at hc₁; omega
  have hlt : j c < j c₁ := hj (Fin.lt_def.mpr (by omega))
  refine ⟨fun c' => ?_, fun c₂ c₃ h => ?_⟩
  · by_cases h : c' = c₁
    · subst h
      simp only [colIncr, Function.update_self]
      omega
    · have := h1 c'
      simp only [colIncr, Function.update_of_ne h]
      by_cases h' : c' = c
      · subst h'
        simp only [colDecr, Function.update_self] at this
        omega
      · simp only [colDecr, Function.update_of_ne h'] at this
        exact this
  · by_cases hc2 : c₂ = c₁
    · subst hc2
      have hc3 : c₃ = c := Fin.ext (by omega)
      subst hc3
      simp only [colIncr, Function.update_self]
      omega
    · have := h2 c₂ c₃ h
      simp only [colIncr, Function.update_of_ne hc2]
      have hc3 : c₃ ≠ c := by
        intro e; subst e; exact hc2 (Fin.ext (by omega))
      simp only [colDecr, Function.update_of_ne hc3] at this
      exact this

/-! ## Labels, weights and the charging of pairs to slots -/

/-- Elements of the interlacing set of a strictly increasing `j` are strictly increasing. -/
theorem strictMono_of_mem_interlaceSet {m : ℕ} {j l : Fin m → ℕ} (hj : StrictMono j)
    (hl : l ∈ interlaceSet j) : StrictMono l := by
  rw [mem_interlaceSet] at hl
  obtain ⟨h1, h2⟩ := hl
  intro c₁ c₂ h12
  rcases Nat.lt_or_ge (c₁.val + 1) c₂.val with h | h
  · have hle : j c₁ ≤ j ⟨c₂.val - 1, by omega⟩ := hj.monotone (Fin.le_def.mpr (by simp; omega))
    have := h2 c₂ ⟨c₂.val - 1, by omega⟩ (by simp; omega)
    have := h1 c₁
    omega
  · have := h2 c₂ c₁ (by have := Fin.lt_def.mp h12; omega)
    have := h1 c₁
    omega

/-- The label of a pair `(c, κ)`: the next column in the bad case, `c` otherwise. -/
def interlacePairLabel {m : ℕ} (j : Fin m → ℕ) (c : Fin m) (κ : Fin m → ℕ) : Fin m :=
  open Classical in if h : IsBadPair j c κ then h.choose else c

theorem interlacePairLabel_of_bad {m : ℕ} {j : Fin m → ℕ} {c : Fin m} {κ : Fin m → ℕ}
    (h : IsBadPair j c κ) :
    (interlacePairLabel j c κ).val = c.val + 1 ∧ κ (interlacePairLabel j c κ) = j c := by
  unfold interlacePairLabel
  rw [dif_pos h]
  exact h.choose_spec

theorem interlacePairLabel_of_good {m : ℕ} {j : Fin m → ℕ} {c : Fin m} {κ : Fin m → ℕ}
    (h : ¬ IsBadPair j c κ) : interlacePairLabel j c κ = c := by
  unfold interlacePairLabel
  rw [dif_neg h]

/-- Raising the label column of a pair gives an interlacing column set of `j`. -/
theorem colIncr_interlacePairLabel_mem {m : ℕ} {j κ : Fin m → ℕ} (hj : StrictMono j) {c : Fin m}
    (hc : 0 < j c) (hκ : κ ∈ interlaceSet (colDecr j c)) :
    colIncr κ (interlacePairLabel j c κ) ∈ interlaceSet j := by
  by_cases hbad : IsBadPair j c κ
  · obtain ⟨h1, h2⟩ := interlacePairLabel_of_bad hbad
    exact colIncr_mem_interlaceSet_of_bad hj hκ h1 h2
  · rw [interlacePairLabel_of_good hbad]
    exact colIncr_mem_interlaceSet_of_good hc hκ hbad

/-- The exponent of a pair equals the exponent of its slot. -/
theorem sum_colDecr_sub_eq {m : ℕ} {j κ : Fin m → ℕ} {c d : Fin m} (hc : 0 < j c)
    (hκ : ∀ c', κ c' ≤ colDecr j c c') (hν : ∀ c', colIncr κ d c' ≤ j c') :
    ∑ c', (colDecr j c c' - κ c') = ∑ c', (j c' - colIncr κ d c') := by
  classical
  rw [Finset.sum_tsub_distrib _ fun x _ => hκ x, Finset.sum_tsub_distrib _ fun x _ => hν x]
  have h1 : ∑ c', colDecr j c c' + 1 = ∑ c', j c' := by
    unfold colDecr
    rw [Finset.sum_update_of_mem (Finset.mem_univ c),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ c), Finset.sdiff_singleton_eq_erase]
    omega
  have h2 : ∑ c', colIncr κ d c' = ∑ c', κ c' + 1 := by
    unfold colIncr
    rw [Finset.sum_update_of_mem (Finset.mem_univ d),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ d), Finset.sdiff_singleton_eq_erase]
    omega
  omega

/-- **Charging pairs to slots.**  The pair terms `y^{w} M'(κ)`, `κ` interlacing `j − e_c`, are
bounded by the slot terms `y^{|j| − |ν|} M'(ν − e_{c'})` over `ν` interlacing `j` and labels
`c' ∈ D'`, provided every pair's label lies in `D'`. -/
theorem sum_pairs_le_sum_slots {m : ℕ} {a' : ℕ → ℝ} (ha' : PFSeq m a') {i j : Fin m → ℕ}
    (hi : StrictMono i) (hj : StrictMono j) {y : ℝ} (hy : 0 ≤ y)
    (P : Finset (Σ _ : Fin m, Fin m → ℕ))
    (hP : ∀ p ∈ P, 0 < j p.1 ∧ p.2 ∈ interlaceSet (colDecr j p.1))
    (D' : Finset (Fin m)) (hD' : ∀ p ∈ P, interlacePairLabel j p.1 p.2 ∈ D') :
    ∑ p ∈ P, y ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * toeplitzMinor a' m i p.2 ≤
      ∑ ν ∈ interlaceSet j, ∑ c' ∈ D'.filter (fun c' => 0 < ν c'),
        y ^ (∑ c'', (j c'' - ν c'')) * toeplitzMinor a' m i (colDecr ν c') := by
  classical
  set g : (Σ _ : Fin m → ℕ, Fin m) → ℝ := fun q =>
    y ^ (∑ c'', (j c'' - q.1 c'')) * toeplitzMinor a' m i (colDecr q.1 q.2) with hg
  set φ : (Σ _ : Fin m, Fin m → ℕ) → (Σ _ : Fin m → ℕ, Fin m) := fun p =>
    ⟨colIncr p.2 (interlacePairLabel j p.1 p.2), interlacePairLabel j p.1 p.2⟩ with hφ
  set Q : Finset (Σ _ : Fin m → ℕ, Fin m) :=
    (interlaceSet j).sigma fun ν => D'.filter fun c' => 0 < ν c' with hQ
  have hRHS : ∑ ν ∈ interlaceSet j, ∑ c' ∈ D'.filter (fun c' => 0 < ν c'),
      y ^ (∑ c'', (j c'' - ν c'')) * toeplitzMinor a' m i (colDecr ν c') = ∑ q ∈ Q, g q := by
    rw [hQ, Finset.sum_sigma]
  rw [hRHS]
  -- each pair term is the slot term of its image
  have hterm : ∀ p ∈ P, y ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * toeplitzMinor a' m i p.2 =
      g (φ p) := by
    intro p hp
    obtain ⟨hc, hκ⟩ := hP p hp
    have hmem := colIncr_interlacePairLabel_mem hj hc hκ
    rw [mem_interlaceSet] at hκ hmem
    simp only [hg, hφ, colDecr_colIncr]
    rw [sum_colDecr_sub_eq hc hκ.1 hmem.1]
  rw [Finset.sum_congr rfl hterm]
  -- injectivity of the labelling
  have hinj : Set.InjOn φ P := by
    rintro ⟨c₁, κ₁⟩ h₁ ⟨c₂, κ₂⟩ h₂ he
    simp only [hφ, Sigma.mk.injEq] at he
    obtain ⟨hν, hlab⟩ := he
    have hlab' : interlacePairLabel j c₁ κ₁ = interlacePairLabel j c₂ κ₂ := eq_of_heq hlab
    have hκ : κ₁ = κ₂ := by
      have e₁ := colDecr_colIncr κ₁ (interlacePairLabel j c₁ κ₁)
      have e₂ := colDecr_colIncr κ₂ (interlacePairLabel j c₂ κ₂)
      rw [← e₁, ← e₂, hν, hlab']
    subst hκ
    have hP₁ := (hP _ h₁).2
    have hP₂ := (hP _ h₂).2
    simp only at hP₁ hP₂
    -- a good pair at `L` and a bad pair at `L − 1` cannot share `κ`
    have key : ∀ {c c' : Fin m}, κ₁ ∈ interlaceSet (colDecr j c) → ¬ IsBadPair j c κ₁ →
        IsBadPair j c' κ₁ → interlacePairLabel j c κ₁ = interlacePairLabel j c' κ₁ → False := by
      intro c c' hc hgood hbad hL
      rw [interlacePairLabel_of_good hgood] at hL
      obtain ⟨hv, hval⟩ := interlacePairLabel_of_bad hbad
      rw [← hL] at hv hval
      rw [mem_interlaceSet] at hc
      have hcc' : c' ≠ c := by intro e; rw [e] at hv; omega
      have := hc.2 c c' (by omega)
      simp only [colDecr, Function.update_of_ne hcc'] at this
      omega
    by_cases hb₁ : IsBadPair j c₁ κ₁ <;> by_cases hb₂ : IsBadPair j c₂ κ₁
    · have e₁ := (interlacePairLabel_of_bad hb₁).1
      have e₂ := (interlacePairLabel_of_bad hb₂).1
      have : c₁ = c₂ := Fin.ext (by rw [hlab'] at e₁; omega)
      subst this; rfl
    · exact (key hP₂ hb₂ hb₁ hlab'.symm).elim
    · exact (key hP₁ hb₁ hb₂ hlab').elim
    · rw [interlacePairLabel_of_good hb₁, interlacePairLabel_of_good hb₂] at hlab'
      subst hlab'; rfl
  rw [← Finset.sum_image hinj]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun q hq _ => ?_
  · intro q hq
    rw [Finset.mem_image] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    obtain ⟨hc, hκ⟩ := hP p hp
    rw [hQ, Finset.mem_sigma, Finset.mem_filter]
    refine ⟨colIncr_interlacePairLabel_mem hj hc hκ, hD' p hp, ?_⟩
    simp [hφ, colIncr]
  · rw [hQ, Finset.mem_sigma] at hq
    have hν := strictMono_of_mem_interlaceSet hj hq.1
    exact mul_nonneg (pow_nonneg hy _) (toeplitzMinor_colDecr_nonneg ha' hi hν q.2)

/-! ## Expanding the lowered minors into pairs -/

/-- If lowering column `c` breaks strict monotonicity, the previous column sits just below. -/
theorem exists_pred_of_not_strictMono_colDecr {m : ℕ} {j : Fin m → ℕ} (hj : StrictMono j)
    {c : Fin m} (h : ¬ StrictMono (colDecr j c)) :
    ∃ c' : Fin m, c'.val + 1 = c.val ∧ j c' + 1 = j c := by
  rw [StrictMono] at h
  push Not at h
  obtain ⟨c₁, c₂, h12, hle⟩ := h
  by_cases h1 : c₁ = c
  · subst h1
    have : j c₁ < j c₂ := hj h12
    simp only [colDecr, Function.update_self, Function.update_of_ne (ne_of_gt h12)] at hle
    omega
  · by_cases h2 : c₂ = c
    · subst h2
      have hlt : j c₁ < j c₂ := hj h12
      simp only [colDecr, Function.update_self, Function.update_of_ne h1] at hle
      have hc : 1 ≤ c₂.val := by have := Fin.lt_def.mp h12; omega
      refine ⟨⟨c₂.val - 1, by omega⟩, by simp; omega, ?_⟩
      have hle1 : j c₁ ≤ j ⟨c₂.val - 1, by omega⟩ :=
        hj.monotone (Fin.le_def.mpr (by simp; have := Fin.lt_def.mp h12; omega))
      have hlt1 : j ⟨c₂.val - 1, by omega⟩ < j c₂ := hj (Fin.lt_def.mpr (by simp; omega))
      omega
    · simp only [colDecr, Function.update_of_ne h1, Function.update_of_ne h2] at hle
      exact absurd (hj h12) (not_lt.mpr hle)

/-- **Pair expansion.**  For `a = a' ∗ (yⁿ)`, the lowered minors of `a` over a set `D` of columns
are the pair terms `y^{w} M_{a'}(κ)`, `κ` interlacing `j − e_c`. -/
theorem sum_colDecr_eq_sum_pairs (a' : ℕ → ℝ) (y : ℝ) {m : ℕ} (i j : Fin m → ℕ)
    (hj : StrictMono j) (D : Finset (Fin m)) :
    ∑ c ∈ D.filter (fun c => 0 < j c),
        toeplitzMinor (cauchyConv a' fun n => y ^ n) m i (colDecr j c) =
      ∑ p ∈ (D.filter fun c => 0 < j c).sigma (fun c => interlaceSet (colDecr j c)),
        y ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * toeplitzMinor a' m i p.2 := by
  rw [Finset.sum_sigma]
  refine Finset.sum_congr rfl fun c _ => ?_
  by_cases hmono : StrictMono (colDecr j c)
  · exact toeplitzMinor_cauchyConv_geometric a' y i _ hmono
  · obtain ⟨c', hc', hjc'⟩ := exists_pred_of_not_strictMono_colDecr hj hmono
    have hne : c' ≠ c := by intro e; rw [e] at hc'; omega
    have heq : colDecr j c c' = colDecr j c c := by
      simp only [colDecr, Function.update_self, Function.update_of_ne hne]
      omega
    rw [toeplitzMinor_eq_zero_of_eq hne heq]
    have hempty : interlaceSet (colDecr j c) = ∅ := by
      ext l
      simp only [Finset.notMem_empty, iff_false]
      intro hl
      rw [mem_interlaceSet] at hl
      have h1 := hl.1 c
      have h2 := hl.2 c c' hc'
      rw [heq] at h2
      omega
    rw [hempty, Finset.sum_empty]

/-- A good pair's `κ` already interlaces `j`. -/
theorem mem_interlaceSet_of_good {m : ℕ} {j κ : Fin m → ℕ} {c : Fin m}
    (hκ : κ ∈ interlaceSet (colDecr j c)) (hgood : ¬ IsBadPair j c κ) : κ ∈ interlaceSet j := by
  rw [mem_interlaceSet] at hκ ⊢
  obtain ⟨h1, h2⟩ := hκ
  refine ⟨fun c' => ?_, fun c₂ c₁ h => ?_⟩
  · have := h1 c'
    by_cases h' : c' = c
    · subst h'; simp only [colDecr, Function.update_self] at this; omega
    · simp only [colDecr, Function.update_of_ne h'] at this; exact this
  · have := h2 c₂ c₁ h
    by_cases hc1 : c₁ = c
    · subst hc1
      simp only [colDecr, Function.update_self] at this
      have hne : κ c₂ ≠ j c₁ := fun e => hgood ⟨c₂, by omega, e⟩
      have hc₂ : c₂ ≠ c₁ := by intro e; rw [e] at h; omega
      omega
    · simp only [colDecr, Function.update_of_ne hc1] at this; exact this

/-- The total lowering of a pair `κ ≤ j − e_c` is one more than its pair weight. -/
theorem sum_sub_eq_sum_colDecr_sub_add_one {m : ℕ} {j κ : Fin m → ℕ} {c : Fin m} (hc : 0 < j c)
    (hκ : ∀ c', κ c' ≤ colDecr j c c') :
    ∑ c', (j c' - κ c') = ∑ c', (colDecr j c c' - κ c') + 1 := by
  classical
  have hκj : ∀ c', κ c' ≤ j c' := fun c' => by
    have := hκ c'
    by_cases h : c' = c
    · subst h; simp only [colDecr, Function.update_self] at this; omega
    · simp only [colDecr, Function.update_of_ne h] at this; exact this
  rw [Finset.sum_tsub_distrib _ fun x _ => hκj x, Finset.sum_tsub_distrib _ fun x _ => hκ x]
  have h1 : ∑ c', colDecr j c c' + 1 = ∑ c', j c' := by
    unfold colDecr
    rw [Finset.sum_update_of_mem (Finset.mem_univ c),
      ← Finset.add_sum_erase _ _ (Finset.mem_univ c), Finset.sdiff_singleton_eq_erase]
    omega
  have h2 : ∑ c', κ c' ≤ ∑ c', colDecr j c c' := Finset.sum_le_sum fun x _ => hκ x
  omega

/-! ## The corner ratio -/

/-- The last `r` columns, `c ≥ m − r` (the first `r` rows of the shape). -/
def topCols (m r : ℕ) : Finset (Fin m) := univ.filter fun c => m ≤ c.val + r

theorem getD_le_head {x : ℝ} {xs : List ℝ} (hs : (x :: xs).Pairwise (· ≥ ·))
    (hx : ∀ z ∈ x :: xs, 0 ≤ z) (n : ℕ) : (x :: xs).getD n 0 ≤ x := by
  cases n with
  | zero => simp
  | succ n =>
    rw [List.getD_cons_succ]
    rcases Nat.lt_or_ge n xs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]
      exact (List.pairwise_cons.mp hs).1 _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
      exact hx x List.mem_cons_self

/-- **Corner ratio for Toeplitz minors of geometric products.**  For ratios
`x₁ ≥ … ≥ x_N ≥ 0`, strictly increasing `i, j` and every `r`,
`x_r · Σ_{c ≥ m − r, j_c ≥ 1} M(j − e_c) ≤ r · M(j)`, where `M(j) = det (a_{j_c − i_r})` for the
coefficients `a` of `∏ 1/(1 − x_s u)` and `x_r = 0` for `r > N`. -/
theorem cornerRatio_geomProdSeq : ∀ (N : ℕ) (xs : List ℝ), xs.length = N →
    xs.Pairwise (· ≥ ·) → (∀ x ∈ xs, 0 ≤ x) →
    ∀ (m : ℕ) (i j : Fin m → ℕ), StrictMono i → StrictMono j → ∀ r : ℕ,
      xs.getD (r - 1) 0 * ∑ c ∈ (topCols m r).filter (fun c => 0 < j c),
          toeplitzMinor (geomProdSeq xs) m i (colDecr j c) ≤
        r * toeplitzMinor (geomProdSeq xs) m i j := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro xs hlen hsort hnn m i j hi hj r
  have hPF : ∀ ys : List ℝ, (∀ x ∈ ys, 0 ≤ x) → PFSeq m (geomProdSeq ys) :=
    fun ys h => pfSeq_geomProdSeq h m
  have hM0 : 0 ≤ toeplitzMinor (geomProdSeq xs) m i j := hPF xs hnn m le_rfl i j hi hj
  -- `r = 0`: no columns
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0
    have : (topCols m 0).filter (fun c => 0 < j c) = ∅ := by
      ext c; simp [topCols]
    rw [this, Finset.sum_empty, mul_zero]
    simp
  -- `r > N`: `x_r = 0`
  rcases Nat.lt_or_ge N r with hNr | hNr
  · rw [List.getD_eq_default _ _ (by omega), zero_mul]
    exact mul_nonneg (Nat.cast_nonneg _) hM0
  rcases Nat.eq_or_lt_of_le hNr with hNr | hNr
  · -- `N = r`: peel the largest ratio
    rw [hNr]
    have hN0 : 0 < N := hNr ▸ hr0
    obtain ⟨x, xs'', rfl⟩ : ∃ x xs'', xs = x :: xs'' := by
      cases xs with
      | nil => simp at hlen; omega
      | cons x xs'' => exact ⟨x, xs'', rfl⟩
    have hx : 0 ≤ x := hnn x List.mem_cons_self
    have hnn'' : ∀ z ∈ xs'', 0 ≤ z := fun z hz => hnn z (List.mem_cons_of_mem x hz)
    have hsort'' : xs''.Pairwise (· ≥ ·) := (List.pairwise_cons.mp hsort).2
    have hlen'' : xs''.length = N - 1 := by simp at hlen; omega
    set xr := (x :: xs'').getD (N - 1) 0 with hxr
    have hxr0 : 0 ≤ xr := by
      rw [hxr]
      rcases Nat.lt_or_ge (N - 1) (x :: xs'').length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact hnn _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]
    have hxrx : xr ≤ x := getD_le_head hsort hnn _
    rw [geomProdSeq_cons, sum_colDecr_eq_sum_pairs _ x i j hj,
      toeplitzMinor_cauchyConv_geometric _ x i j hj]
    set P := ((topCols m N).filter fun c => 0 < j c).sigma fun c => interlaceSet (colDecr j c)
      with hP
    have hPmem : ∀ p ∈ P, 0 < j p.1 ∧ p.2 ∈ interlaceSet (colDecr j p.1) ∧ m ≤ p.1.val + N := by
      intro p hp
      rw [hP, Finset.mem_sigma, Finset.mem_filter, topCols, Finset.mem_filter] at hp
      exact ⟨hp.1.2, hp.2, hp.1.1.2⟩
    set spec : (Σ _ : Fin m, Fin m → ℕ) → Prop := fun p =>
      p.1.val + N = m ∧ ¬ IsBadPair j p.1 p.2 with hspec
    rw [← Finset.sum_filter_add_sum_filter_not P spec, mul_add]
    set a'' := geomProdSeq xs'' with ha''
    have hPF'' := hPF xs'' hnn''
    -- the special good pairs
    have hspecle : xr * ∑ p ∈ P.filter spec, x ^ (∑ c', (colDecr j p.1 c' - p.2 c')) *
        toeplitzMinor a'' m i p.2 ≤
        ∑ l ∈ interlaceSet j, x ^ (∑ c, (j c - l c)) * toeplitzMinor a'' m i l := by
      rw [Finset.mul_sum]
      have hinj : Set.InjOn (fun p : (Σ _ : Fin m, Fin m → ℕ) => p.2) (P.filter spec) := by
        rintro ⟨c₁, κ₁⟩ h₁ ⟨c₂, κ₂⟩ h₂ he
        simp only at he
        subst he
        have e₁ := (Finset.mem_filter.mp h₁).2.1
        have e₂ := (Finset.mem_filter.mp h₂).2.1
        have : c₁ = c₂ := Fin.ext (by simp only at e₁ e₂; omega)
        subst this; rfl
      calc ∑ p ∈ P.filter spec, xr * (x ^ (∑ c', (colDecr j p.1 c' - p.2 c')) *
            toeplitzMinor a'' m i p.2)
          ≤ ∑ p ∈ P.filter spec, x ^ (∑ c, (j c - p.2 c)) * toeplitzMinor a'' m i p.2 := by
            refine Finset.sum_le_sum fun p hp => ?_
            obtain ⟨hc, hκ, -⟩ := hPmem p (Finset.mem_filter.mp hp).1
            have hκ' := hκ
            rw [mem_interlaceSet] at hκ'
            rw [sum_sub_eq_sum_colDecr_sub_add_one hc hκ'.1, pow_succ]
            have hgood := (Finset.mem_filter.mp hp).2.2
            have hmem := mem_interlaceSet_of_good hκ hgood
            have hM := hPF'' m le_rfl i _ hi (strictMono_of_mem_interlaceSet hj hmem)
            have hpow := pow_nonneg hx (∑ c', (colDecr j p.1 c' - p.2 c'))
            calc xr * (x ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * toeplitzMinor a'' m i p.2)
                = (xr * x ^ (∑ c', (colDecr j p.1 c' - p.2 c'))) * toeplitzMinor a'' m i p.2 := by
                  ring
              _ ≤ (x ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * x) * toeplitzMinor a'' m i p.2 := by
                  refine mul_le_mul_of_nonneg_right ?_ hM
                  rw [mul_comm]
                  exact mul_le_mul_of_nonneg_left hxrx hpow
        _ = ∑ l ∈ (P.filter spec).image (fun p => p.2),
              x ^ (∑ c, (j c - l c)) * toeplitzMinor a'' m i l :=
            (Finset.sum_image (f := fun l => x ^ (∑ c, (j c - l c)) * toeplitzMinor a'' m i l)
              hinj).symm
        _ ≤ ∑ l ∈ interlaceSet j, x ^ (∑ c, (j c - l c)) * toeplitzMinor a'' m i l := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun l hl _ => ?_
            · intro l hl
              rw [Finset.mem_image] at hl
              obtain ⟨p, hp, rfl⟩ := hl
              obtain ⟨-, hκ, -⟩ := hPmem p (Finset.mem_filter.mp hp).1
              exact mem_interlaceSet_of_good hκ (Finset.mem_filter.mp hp).2.2
            · exact mul_nonneg (pow_nonneg hx _)
                (hPF'' m le_rfl i _ hi (strictMono_of_mem_interlaceSet hj hl))
    -- the remaining pairs, charged to the statement for `r − 1`
    have hrestle : xr * ∑ p ∈ P.filter (fun p => ¬ spec p),
        x ^ (∑ c', (colDecr j p.1 c' - p.2 c')) * toeplitzMinor a'' m i p.2 ≤
        ((N - 1 : ℕ) : ℝ) * ∑ l ∈ interlaceSet j, x ^ (∑ c, (j c - l c)) *
          toeplitzMinor a'' m i l := by
      have hcharge := sum_pairs_le_sum_slots (hPF xs'' hnn'') hi hj hx (P.filter fun p => ¬ spec p)
        (fun p hp => ⟨(hPmem p (Finset.mem_filter.mp hp).1).1,
          (hPmem p (Finset.mem_filter.mp hp).1).2.1⟩) (topCols m (N - 1)) (fun p hp => by
          obtain ⟨hc, hκ, htop⟩ := hPmem p (Finset.mem_filter.mp hp).1
          have hns := (Finset.mem_filter.mp hp).2
          rw [topCols, Finset.mem_filter]
          refine ⟨Finset.mem_univ _, ?_⟩
          by_cases hbad : IsBadPair j p.1 p.2
          · have := (interlacePairLabel_of_bad hbad).1
            omega
          · rw [interlacePairLabel_of_good hbad]
            have : p.1.val + N ≠ m := fun e => hns ⟨e, hbad⟩
            omega)
      refine (mul_le_mul_of_nonneg_left hcharge hxr0).trans ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_le_sum fun l hl => ?_
      have hl' := strictMono_of_mem_interlaceSet hj hl
      have hIH := ih (N - 1) (by omega) xs'' hlen'' hsort'' hnn'' m i l hi hl' (N - 1)
      have hxr' : xs''.getD (N - 1 - 1) 0 = xr ∨ (topCols m (N - 1)).filter
          (fun c => 0 < l c) = ∅ := by
        rcases Nat.lt_or_ge 1 N with h | h
        · left
          obtain ⟨k, hk⟩ : ∃ k, N - 1 = k + 1 := ⟨N - 2, by omega⟩
          rw [hxr, hk, List.getD_cons_succ, Nat.add_sub_cancel]
        · right
          ext c
          simp only [topCols, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
            iff_false, not_and]
          intro h'
          have := c.isLt
          omega
      rw [← Finset.mul_sum, ← mul_assoc, mul_comm xr, mul_assoc]
      have hpow := pow_nonneg hx (∑ c, (j c - l c))
      rw [show ((N - 1 : ℕ) : ℝ) * (x ^ (∑ c, (j c - l c)) * toeplitzMinor a'' m i l) =
        x ^ (∑ c, (j c - l c)) * (((N - 1 : ℕ) : ℝ) * toeplitzMinor a'' m i l) by ring]
      refine mul_le_mul_of_nonneg_left ?_ hpow
      rcases hxr' with h | h
      · rw [h] at hIH; exact hIH
      · rw [h, Finset.sum_empty, mul_zero]
        exact mul_nonneg (Nat.cast_nonneg _) (hPF'' m le_rfl i l hi hl')
    have hN1 : ((N - 1 : ℕ) : ℝ) + 1 = N := by
      rw [Nat.cast_sub (by omega : 1 ≤ N)]; push_cast; ring
    rw [← hN1, add_mul, one_mul]
    linarith
  · -- `N > r`: peel the smallest ratio
    have hne : xs ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
    set xs' := xs.dropLast with hxs'
    set y := xs.getLast hne with hy
    have hsplit : xs = xs' ++ [y] := (List.dropLast_append_getLast hne).symm
    have hyy : 0 ≤ y := hnn y (List.getLast_mem hne)
    have hnn' : ∀ z ∈ xs', 0 ≤ z := fun z hz => hnn z (List.mem_of_mem_dropLast hz)
    have hsort' : xs'.Pairwise (· ≥ ·) := hsort.sublist (List.dropLast_sublist xs)
    have hlen' : xs'.length = N - 1 := by simp [hxs', hlen]
    have hxr : xs.getD (r - 1) 0 = xs'.getD (r - 1) 0 := by
      conv_lhs => rw [hsplit]
      exact List.getD_append _ _ _ _ (by omega)
    rw [hxr]
    conv_lhs => rw [hsplit]
    conv_rhs => rw [hsplit]
    rw [geomProdSeq_append_singleton, sum_colDecr_eq_sum_pairs _ y i j hj,
      toeplitzMinor_cauchyConv_geometric _ y i j hj]
    set P := ((topCols m r).filter fun c => 0 < j c).sigma fun c => interlaceSet (colDecr j c)
      with hP
    have hPF' := hPF xs' hnn'
    have hcharge := sum_pairs_le_sum_slots hPF' hi hj hyy P
      (fun p hp => by
        rw [hP, Finset.mem_sigma, Finset.mem_filter] at hp
        exact ⟨hp.1.2, hp.2⟩) (topCols m r) (fun p hp => by
        rw [hP, Finset.mem_sigma, Finset.mem_filter, topCols, Finset.mem_filter] at hp
        rw [topCols, Finset.mem_filter]
        refine ⟨Finset.mem_univ _, ?_⟩
        by_cases hbad : IsBadPair j p.1 p.2
        · have := (interlacePairLabel_of_bad hbad).1; omega
        · rw [interlacePairLabel_of_good hbad]; exact hp.1.1.2)
    have hxr0 : 0 ≤ xs'.getD (r - 1) 0 := by
      rcases Nat.lt_or_ge (r - 1) xs'.length with h | h
      · rw [List.getD_eq_getElem _ _ h]; exact hnn' _ (List.getElem_mem h)
      · rw [List.getD_eq_default _ _ h]
    refine (mul_le_mul_of_nonneg_left hcharge hxr0).trans ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun l hl => ?_
    have hl' := strictMono_of_mem_interlaceSet hj hl
    have hIH := ih (N - 1) (by omega) xs' hlen' hsort' hnn' m i l hi hl' r
    rw [← Finset.mul_sum]
    have hpow := pow_nonneg hyy (∑ c, (j c - l c))
    calc xs'.getD (r - 1) 0 * (y ^ (∑ c, (j c - l c)) *
          ∑ c' ∈ (topCols m r).filter (fun c' => 0 < l c'),
            toeplitzMinor (geomProdSeq xs') m i (colDecr l c'))
        = y ^ (∑ c, (j c - l c)) * (xs'.getD (r - 1) 0 *
          ∑ c' ∈ (topCols m r).filter (fun c' => 0 < l c'),
            toeplitzMinor (geomProdSeq xs') m i (colDecr l c')) := by ring
      _ ≤ y ^ (∑ c, (j c - l c)) * (r * toeplitzMinor (geomProdSeq xs') m i l) :=
          mul_le_mul_of_nonneg_left hIH hpow
      _ = r * (y ^ (∑ c, (j c - l c)) * toeplitzMinor (geomProdSeq xs') m i l) := by ring

/-- **Single corner ratio.**  Lowering one of the last `r` columns costs at most `r/x_r`:
`x_r · M(j − e_c) ≤ r · M(j)` for `c ≥ m − r` with `j_c ≥ 1`. -/
theorem cornerRatio_single {xs : List ℝ} (hsort : xs.Pairwise (· ≥ ·)) (hnn : ∀ x ∈ xs, 0 ≤ x)
    {m : ℕ} {i j : Fin m → ℕ} (hi : StrictMono i) (hj : StrictMono j) {r : ℕ} {c : Fin m}
    (hc : m ≤ c.val + r) (hjc : 0 < j c) :
    xs.getD (r - 1) 0 * toeplitzMinor (geomProdSeq xs) m i (colDecr j c) ≤
      r * toeplitzMinor (geomProdSeq xs) m i j := by
  have hxr0 : 0 ≤ xs.getD (r - 1) 0 := by
    rcases Nat.lt_or_ge (r - 1) xs.length with h | h
    · rw [List.getD_eq_getElem _ _ h]; exact hnn _ (List.getElem_mem h)
    · rw [List.getD_eq_default _ _ h]
  refine le_trans ?_ (cornerRatio_geomProdSeq _ xs rfl hsort hnn m i j hi hj r)
  refine mul_le_mul_of_nonneg_left ?_ hxr0
  have hmem : c ∈ (topCols m r).filter (fun c => 0 < j c) := by
    simp [topCols, hc, hjc]
  exact Finset.single_le_sum (f := fun c => toeplitzMinor (geomProdSeq xs) m i (colDecr j c))
    (fun c' _ => toeplitzMinor_colDecr_nonneg (pfSeq_geomProdSeq hnn m) hi hj c') hmem

end

end GaloisForLFunctions.HTGeometry
