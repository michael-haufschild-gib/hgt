import GaloisForLFunctions.PrimeTorusTheory.TheOrbitOfAPhaseSystem

/-!
# Large-value heights form an approximate group

Group closure turns the sets of heights where a column sum is large into approximate groups.

* **Bohr sets** `B(r) = {t : D(t) ≤ r²}` are symmetric, contain `0`, and satisfy `B(r) + B(s) ⊆ B(r + s)`
  and `n B(r) ⊆ B(nr)`. So two heights of defect `≤ r²` differ by a height of defect `≤ 4r²`
  (`sub_mem_bohr`), and a return yields a whole progression of returns.
* **Clusters** (`card_le_of_gap`). If `B(2r)` has a gap `δ < |u| < τ`, the set `B(r)` splits into clusters of
  diameter `δ` separated by `τ`, so an interval of length `L` carries at most `L/τ + 1` of them.
* **All levels** (`exists_pair_column_ge`, `card_pairs_ge`). Below the corner there is no triangle
  inequality, but Halász–Montgomery still acts: `N` heights at level `θ` have differences of average
  level `≥ θ²`, and a proportion `θ²/2` of the pairs has level `≥ θ²/2`.
* **Descent** (`exists_low_return_of_many_large_values`, `card_le_of_no_low_return`). Pigeonholing a large-value
  set into short intervals gives a large value at a *low* height. Rare heights are controlled by the first
  return: `N` separated large values in a window of length `L` need a return below `L/J`, for every
  `J < N/(m−1)`.
-/

open Finset Real

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- The Bohr set of radius `r`: the heights of defect at most `r²`. -/
def bohr (r : ℝ) : Set ℝ := {t | S.defect t ≤ r ^ 2}

/-- The heights where the column is at least the proportion `θ` of its size. -/
def largeValue (θ : ℝ) : Set ℝ := {t | θ * S.size ≤ S.column t}

theorem mem_bohr {r t : ℝ} : t ∈ S.bohr r ↔ S.defect t ≤ r ^ 2 := Iff.rfl

theorem mem_largeValue {θ t : ℝ} : t ∈ S.largeValue θ ↔ θ * S.size ≤ S.column t := Iff.rfl

theorem zero_mem_bohr (r : ℝ) : (0 : ℝ) ∈ S.bohr r := by
  simp only [mem_bohr, defect_zero]
  positivity

theorem neg_mem_bohr {r t : ℝ} (ht : t ∈ S.bohr r) : -t ∈ S.bohr r := by
  rw [mem_bohr, defect_neg]
  exact ht

/-- A Bohr set is a level set of the column. -/
theorem mem_bohr_iff_mem_largeValue {r t : ℝ} (hS : 0 < S.size) :
    t ∈ S.bohr r ↔ t ∈ S.largeValue (1 - r ^ 2 / S.size) := by
  rw [mem_bohr, mem_largeValue, sub_mul, div_mul_cancel₀ _ hS.ne', one_mul]
  unfold defect
  constructor <;> intro h <;> linarith

theorem sqrt_defect_le_of_mem_bohr {r t : ℝ} (hr : 0 ≤ r) (ht : t ∈ S.bohr r) :
    √(S.defect t) ≤ r := by
  rw [mem_bohr] at ht
  calc
    √(S.defect t) ≤ √(r ^ 2) := Real.sqrt_le_sqrt ht
    _ = r := Real.sqrt_sq hr

theorem mem_bohr_of_sqrt_defect_le {r t : ℝ} (ht : √(S.defect t) ≤ r) : t ∈ S.bohr r := by
  rw [mem_bohr]
  have h0 := Real.sqrt_nonneg (S.defect t)
  have := pow_le_pow_left₀ h0 ht 2
  rwa [Real.sq_sqrt (S.defect_nonneg t)] at this

/-- `B(r) + B(s) ⊆ B(r + s)`. -/
theorem add_mem_bohr {r s t u : ℝ} (hr : 0 ≤ r) (hs : 0 ≤ s) (ht : t ∈ S.bohr r)
    (hu : u ∈ S.bohr s) : t + u ∈ S.bohr (r + s) := by
  refine S.mem_bohr_of_sqrt_defect_le ((S.sqrt_defect_add_le t u).trans ?_)
  exact add_le_add (S.sqrt_defect_le_of_mem_bohr hr ht) (S.sqrt_defect_le_of_mem_bohr hs hu)

/-- Two heights of defect `≤ r²` differ by a height of defect `≤ 4r²`. -/
theorem sub_mem_bohr {r t u : ℝ} (hr : 0 ≤ r) (ht : t ∈ S.bohr r) (hu : u ∈ S.bohr r) :
    t - u ∈ S.bohr (2 * r) := by
  have := S.add_mem_bohr hr hr ht (S.neg_mem_bohr hu)
  rwa [← sub_eq_add_neg, ← two_mul] at this

/-- `n B(r) ⊆ B(nr)`: a return yields a progression of returns. -/
theorem nat_mul_mem_bohr {r t : ℝ} (hr : 0 ≤ r) (n : ℕ) (ht : t ∈ S.bohr r) :
    (n : ℝ) * t ∈ S.bohr (n * r) := by
  refine S.mem_bohr_of_sqrt_defect_le ((S.sqrt_defect_nat_mul_le n t).trans ?_)
  exact mul_le_mul_of_nonneg_left (S.sqrt_defect_le_of_mem_bohr hr ht) (Nat.cast_nonneg n)

/-- A return transports every value of the column by at most `√(2S) r`. -/
theorem abs_column_add_sub_le {r u : ℝ} (hr : 0 ≤ r) (hu : u ∈ S.bohr r) (t : ℝ) :
    |S.column (t + u) - S.column t| ≤ √(2 * S.size) * r := by
  have h := S.column_sub_sq_le (t + u) t
  rw [add_sub_cancel_left] at h
  have hS : 0 ≤ 2 * S.size := by have := S.size_nonneg; positivity
  have h2 : (S.column (t + u) - S.column t) ^ 2 ≤ 2 * S.size * r ^ 2 :=
    h.trans (mul_le_mul_of_nonneg_left (S.mem_bohr.mp hu) hS)
  rw [← Real.sqrt_sq_eq_abs]
  calc
    √((S.column (t + u) - S.column t) ^ 2) ≤ √(2 * S.size * r ^ 2) := Real.sqrt_le_sqrt h2
    _ = √(2 * S.size) * r := by rw [Real.sqrt_mul hS, Real.sqrt_sq hr]

/-! ### Clusters -/

/-- A family of reals in an interval of length `L`, pairwise `τ`-separated, has at most `L/τ + 1` members. -/
theorem card_le_of_separated {A : Finset ℝ} {T L τ : ℝ} (hL : 0 ≤ L) (hτ : 0 < τ)
    (hA : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hsep : ∀ t ∈ A, ∀ u ∈ A, t ≠ u → τ ≤ |t - u|) :
    (A.card : ℝ) ≤ L / τ + 1 := by
  by_cases hne : A.Nonempty
  · have hmaps : ∀ t ∈ A, ⌊(t - T) / τ⌋₊ ∈ Finset.range (⌊L / τ⌋₊ + 1) := by
      intro t ht
      rw [Finset.mem_range, Nat.lt_succ_iff]
      refine Nat.floor_le_floor (div_le_div_of_nonneg_right ?_ hτ.le)
      linarith [(hA t ht).2]
    have hinj : Set.InjOn (fun t : ℝ => ⌊(t - T) / τ⌋₊) (A : Set ℝ) := by
      intro t ht u hu hfl
      by_contra hne'
      have hs := hsep t ht u hu hne'
      have ht0 : 0 ≤ (t - T) / τ := div_nonneg (by linarith [(hA t ht).1]) hτ.le
      have hu0 : 0 ≤ (u - T) / τ := div_nonneg (by linarith [(hA u hu).1]) hτ.le
      have h1 := Nat.floor_le ht0
      have h2 := Nat.lt_floor_add_one ((t - T) / τ)
      have h3 := Nat.floor_le hu0
      have h4 := Nat.lt_floor_add_one ((u - T) / τ)
      simp only at hfl
      rw [hfl] at h1 h2
      have h5 : |(t - T) / τ - (u - T) / τ| < 1 := by
        rw [abs_lt]
        constructor <;> linarith
      have h6 : |(t - T) / τ - (u - T) / τ| = |t - u| / τ := by
        rw [← sub_div, abs_div, abs_of_pos hτ]
        congr 2
        ring
      rw [h6, div_lt_one hτ] at h5
      linarith
    have hcard := Finset.card_le_card_of_injOn _ hmaps hinj
    rw [Finset.card_range] at hcard
    have h7 : (A.card : ℝ) ≤ ((⌊L / τ⌋₊ + 1 : ℕ) : ℝ) := by exact_mod_cast hcard
    have h8 := Nat.floor_le (div_nonneg hL hτ.le)
    push_cast at h7
    linarith
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    subst hne
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity

/-- **Clusters.** If `B(2r)` has a gap `δ < |u| < τ`, a `δ`-separated part of `B(r)` is `τ`-separated. -/
theorem le_abs_sub_of_gap {r δ τ t u : ℝ} (hr : 0 ≤ r)
    (hgap : ∀ v, δ < |v| → |v| < τ → v ∉ S.bohr (2 * r)) (ht : t ∈ S.bohr r) (hu : u ∈ S.bohr r)
    (hsep : δ < |t - u|) : τ ≤ |t - u| := by
  by_contra h
  exact hgap (t - u) hsep (not_le.mp h) (S.sub_mem_bohr hr ht hu)

/-- A window of length `L` carries at most `L/τ + 1` clusters of `B(r)`. -/
theorem card_le_of_gap {r δ τ T L : ℝ} {A : Finset ℝ} (hr : 0 ≤ r) (hL : 0 ≤ L) (hτ : 0 < τ)
    (hgap : ∀ v, δ < |v| → |v| < τ → v ∉ S.bohr (2 * r)) (hAB : ∀ t ∈ A, t ∈ S.bohr r)
    (hAI : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hsep : ∀ t ∈ A, ∀ u ∈ A, t ≠ u → δ < |t - u|) :
    (A.card : ℝ) ≤ L / τ + 1 :=
  card_le_of_separated hL hτ hAI fun t ht u hu htu =>
    S.le_abs_sub_of_gap hr hgap (hAB t ht) (hAB u hu) (hsep t ht u hu htu)

/-! ### All levels: Halász–Montgomery -/

/-- `N` heights at level `θ` force the column on the differences to have mean at least `θ² S`. -/
theorem sum_sum_column_ge {A : Finset ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hS : 0 < S.size)
    (hA : ∀ t ∈ A, t ∈ S.largeValue θ) :
    θ ^ 2 * (A.card : ℝ) ^ 2 * S.size ≤ ∑ t ∈ A, ∑ u ∈ A, S.column (t - u) := by
  have h1 : (A.card : ℝ) * (θ * S.size) ≤ ∑ t ∈ A, S.column t := by
    have := Finset.card_nsmul_le_sum A S.column (θ * S.size) hA
    simpa [nsmul_eq_mul] using this
  have h0 : 0 ≤ (A.card : ℝ) * (θ * S.size) := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have h3 := S.sq_sum_column_le A
  have h4 : S.size * (θ ^ 2 * (A.card : ℝ) ^ 2 * S.size) ≤
      S.size * ∑ t ∈ A, ∑ u ∈ A, S.column (t - u) := by
    calc
      S.size * (θ ^ 2 * (A.card : ℝ) ^ 2 * S.size) = ((A.card : ℝ) * (θ * S.size)) ^ 2 := by ring
      _ ≤ _ := h2.trans h3
  exact le_of_mul_le_mul_left h4 hS

/-- The double sum over a set splits into the diagonal and the differences. -/
theorem sum_sum_column_eq (A : Finset ℝ) :
    ∑ t ∈ A, ∑ u ∈ A, S.column (t - u) =
      (A.card : ℝ) * S.size + ∑ t ∈ A, ∑ u ∈ A.erase t, S.column (t - u) := by
  have : ∀ t ∈ A, ∑ u ∈ A, S.column (t - u) = S.size + ∑ u ∈ A.erase t, S.column (t - u) := by
    intro t ht
    rw [← Finset.add_sum_erase A _ ht, sub_self, column_zero]
  rw [Finset.sum_congr rfl this, Finset.sum_add_distrib]
  simp [nsmul_eq_mul]

/-- Some difference of `N ≥ 2` heights at level `θ` has level at least `θ² − (1 − θ²)/(N − 1)`. -/
theorem exists_pair_column_ge {A : Finset ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hS : 0 < S.size)
    (hN : 2 ≤ A.card) (hA : ∀ t ∈ A, t ∈ S.largeValue θ) :
    ∃ t ∈ A, ∃ u ∈ A, t ≠ u ∧
      (θ ^ 2 - (1 - θ ^ 2) / ((A.card : ℝ) - 1)) * S.size ≤ S.column (t - u) := by
  set c : ℝ := (θ ^ 2 - (1 - θ ^ 2) / ((A.card : ℝ) - 1)) * S.size with hc
  by_contra hcon
  push Not at hcon
  have hN' : (2 : ℝ) ≤ A.card := by exact_mod_cast hN
  have hN1 : 0 < (A.card : ℝ) - 1 := by linarith
  have hstrict : ∑ t ∈ A, ∑ u ∈ A.erase t, S.column (t - u) <
      (A.card : ℝ) * (((A.card : ℝ) - 1) * c) := by
    have hne : A.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨t₀, ht₀⟩ := hne
    have hstep : ∀ t ∈ A, ∑ u ∈ A.erase t, S.column (t - u) ≤ ((A.card : ℝ) - 1) * c := by
      intro t ht
      have hcard : ((A.erase t).card : ℝ) = (A.card : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem ht, Nat.cast_sub (by omega)]
        simp
      have := Finset.sum_le_card_nsmul (A.erase t) (fun u => S.column (t - u)) c
        (fun u hu => (hcon t ht u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu).symm).le)
      rwa [nsmul_eq_mul, hcard] at this
    have hstep' : ∑ u ∈ A.erase t₀, S.column (t₀ - u) < ((A.card : ℝ) - 1) * c := by
      have hne' : (A.erase t₀).Nonempty := by
        rw [← Finset.card_pos, Finset.card_erase_of_mem ht₀]
        omega
      have hcard : ((A.erase t₀).card : ℝ) = (A.card : ℝ) - 1 := by
        rw [Finset.card_erase_of_mem ht₀, Nat.cast_sub (by omega)]
        simp
      have := Finset.sum_lt_sum_of_nonempty hne' (fun u hu =>
        hcon t₀ ht₀ u (Finset.mem_of_mem_erase hu) (Finset.ne_of_mem_erase hu).symm)
      rwa [Finset.sum_const, nsmul_eq_mul, hcard] at this
    have := Finset.sum_lt_sum hstep ⟨t₀, ht₀, hstep'⟩
    simpa [nsmul_eq_mul] using this
  have hmain := S.sum_sum_column_ge hθ hS hA
  rw [S.sum_sum_column_eq A] at hmain
  have hexpand : (A.card : ℝ) * (((A.card : ℝ) - 1) * c) =
      (A.card : ℝ) * (θ ^ 2 * (A.card : ℝ) - 1) * S.size := by
    rw [hc]
    field_simp
    ring
  have : θ ^ 2 * (A.card : ℝ) ^ 2 * S.size <
      (A.card : ℝ) * S.size + (A.card : ℝ) * (θ ^ 2 * (A.card : ℝ) - 1) * S.size := by
    rw [← hexpand]
    linarith
  nlinarith

open Classical in
/-- A proportion `θ²/2` of the pairs of `N` heights at level `θ` has a difference at level `θ²/2`. -/
theorem card_pairs_ge {A : Finset ℝ} {θ : ℝ} (hθ : 0 ≤ θ) (hS : 0 < S.size)
    (hA : ∀ t ∈ A, t ∈ S.largeValue θ) :
    θ ^ 2 / 2 * (A.card : ℝ) ^ 2 ≤
      (((A ×ˢ A).filter fun x => θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2)).card : ℝ) := by
  set G := (A ×ˢ A).filter fun x => θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2) with hG
  have hmain := S.sum_sum_column_ge hθ hS hA
  rw [← Finset.sum_product'] at hmain
  have hsplit := Finset.sum_filter_add_sum_filter_not (A ×ˢ A)
    (fun x : ℝ × ℝ => θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2))
    (fun x : ℝ × ℝ => S.column (x.1 - x.2))
  have h1 : ∑ x ∈ G, S.column (x.1 - x.2) ≤ (G.card : ℝ) * S.size := by
    have := Finset.sum_le_card_nsmul G (fun x : ℝ × ℝ => S.column (x.1 - x.2)) S.size
      (fun x _ => S.column_le_size _)
    rwa [nsmul_eq_mul] at this
  have h2 : ∑ x ∈ (A ×ˢ A).filter (fun x => ¬ θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2)),
      S.column (x.1 - x.2) ≤ (A.card : ℝ) ^ 2 * (θ ^ 2 / 2 * S.size) := by
    have h3 := Finset.sum_le_card_nsmul
      ((A ×ˢ A).filter (fun x => ¬ θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2)))
      (fun x : ℝ × ℝ => S.column (x.1 - x.2)) (θ ^ 2 / 2 * S.size)
      (fun x hx => (not_le.mp (Finset.mem_filter.mp hx).2).le)
    rw [nsmul_eq_mul] at h3
    refine h3.trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    have hc : ((A ×ˢ A).filter
        (fun x => ¬ θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2))).card ≤ (A ×ˢ A).card :=
      Finset.card_filter_le _ _
    rw [Finset.card_product] at hc
    have : (((A ×ˢ A).filter
        (fun x => ¬ θ ^ 2 / 2 * S.size ≤ S.column (x.1 - x.2))).card : ℝ) ≤
        (A.card : ℝ) * A.card := by exact_mod_cast hc
    linarith [sq (A.card : ℝ)]
  have h4 : θ ^ 2 * (A.card : ℝ) ^ 2 * S.size ≤
      (G.card : ℝ) * S.size + (A.card : ℝ) ^ 2 * (θ ^ 2 / 2 * S.size) := by
    have e := hsplit
    rw [← hG] at e
    linarith
  have h5 : (θ ^ 2 / 2 * (A.card : ℝ) ^ 2) * S.size ≤ (G.card : ℝ) * S.size := by nlinarith
  exact le_of_mul_le_mul_right h5 hS

/-! ### Descent -/

/-- A subset of `[T, T + L]` with more than `J(m−1)` points has `m` points in an interval of length `L/J`. -/
theorem exists_subset_short_interval {A : Finset ℝ} {T L : ℝ} {J m : ℕ} (hL : 0 < L) (hJ : 0 < J)
    (hAI : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hcard : J * m < A.card) :
    ∃ A' ⊆ A, m < A'.card ∧ ∀ t ∈ A', ∀ u ∈ A', |t - u| ≤ L / J := by
  have hJ' : (0 : ℝ) < J := by exact_mod_cast hJ
  set w : ℝ := L / J with hw
  have hw0 : 0 < w := div_pos hL hJ'
  set f : ℝ → ℕ := fun t => min ⌊(t - T) / w⌋₊ (J - 1) with hf
  have hmaps : ∀ t ∈ A, f t ∈ Finset.range J := by
    intro t _
    rw [Finset.mem_range]
    have : min ⌊(t - T) / w⌋₊ (J - 1) ≤ J - 1 := min_le_right _ _
    simp only [hf]
    omega
  have hrange : (Finset.range J).card * m < A.card := by simpa using hcard
  obtain ⟨y, -, hy⟩ := Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to hmaps hrange
  refine ⟨A.filter fun x => f x = y, Finset.filter_subset _ _, hy, ?_⟩
  -- Points of one fibre lie in one cell of length `w`.
  have hcell : ∀ t ∈ A, f t = y → (y : ℝ) * w ≤ t - T ∧ t - T ≤ ((y : ℝ) + 1) * w := by
    intro t ht hft
    have h0 : 0 ≤ (t - T) / w := div_nonneg (by linarith [(hAI t ht).1]) hw0.le
    have htop : t - T ≤ J * w := by
      rw [hw, mul_div_cancel₀ _ hJ'.ne']
      linarith [(hAI t ht).2]
    have hfloor := Nat.floor_le h0
    have hlt := Nat.lt_floor_add_one ((t - T) / w)
    constructor
    · have hyle : (y : ℝ) ≤ (⌊(t - T) / w⌋₊ : ℝ) := by
        rw [← hft]
        exact_mod_cast min_le_left _ _
      have : (y : ℝ) ≤ (t - T) / w := hyle.trans hfloor
      rwa [le_div_iff₀ hw0] at this
    · by_cases hc : ⌊(t - T) / w⌋₊ ≤ J - 1
      · have hyeq : y = ⌊(t - T) / w⌋₊ := by
          rw [← hft]
          simp only [hf]
          exact min_eq_left hc
        rw [hyeq]
        have := (div_le_iff₀ hw0).mp hlt.le
        linarith
      · have hyeq : y = J - 1 := by
          rw [← hft]
          simp only [hf]
          exact min_eq_right (by omega)
        have hc1 : (y : ℝ) + 1 = J := by
          rw [hyeq]
          have : 1 ≤ J := hJ
          push_cast [Nat.cast_sub this]
          ring
        rw [hc1]
        exact htop
  intro t ht u hu
  obtain ⟨ht1, ht2⟩ := Finset.mem_filter.mp ht
  obtain ⟨hu1, hu2⟩ := Finset.mem_filter.mp hu
  have h1 := hcell t ht1 ht2
  have h2 := hcell u hu1 hu2
  rw [abs_le]
  constructor <;> nlinarith [h1.1, h1.2, h2.1, h2.2]

/-- **Descent.** More than `J(m−1)` heights at level `θ` in a window of length `L` force a difference of
size `≤ L/J` at level `θ² − (1 − θ²)/(m − 1)`. -/
theorem exists_low_return_of_many_large_values {A : Finset ℝ} {θ T L : ℝ} {J m : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hS : 0 < S.size) (hL : 0 < L) (hJ : 0 < J) (hm : 2 ≤ m)
    (hAI : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hA : ∀ t ∈ A, t ∈ S.largeValue θ)
    (hcard : J * (m - 1) < A.card) :
    ∃ t ∈ A, ∃ u ∈ A, t ≠ u ∧ |t - u| ≤ L / J ∧
      (θ ^ 2 - (1 - θ ^ 2) / ((m : ℝ) - 1)) * S.size ≤ S.column (t - u) := by
  obtain ⟨A', hsub, hc, hshort⟩ := exists_subset_short_interval hL hJ hAI hcard
  have hc' : 2 ≤ A'.card := by omega
  obtain ⟨t, ht, u, hu, htu, hle⟩ := S.exists_pair_column_ge hθ0 hS hc' fun t ht => hA t (hsub ht)
  refine ⟨t, hsub ht, u, hsub hu, htu, hshort t ht u hu, le_trans ?_ hle⟩
  refine mul_le_mul_of_nonneg_right ?_ S.size_nonneg
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hcm : (m : ℝ) ≤ A'.card := by
    have : m ≤ A'.card := by omega
    exact_mod_cast this
  have h1 : 0 < (m : ℝ) - 1 := by linarith
  have h2 : 0 ≤ 1 - θ ^ 2 := by nlinarith
  have : (1 - θ ^ 2) / ((A'.card : ℝ) - 1) ≤ (1 - θ ^ 2) / ((m : ℝ) - 1) :=
    div_le_div_of_nonneg_left h2 h1 (by linarith)
  linarith

/-- **Rare heights are controlled by the first return.** If the column stays below the level
`θ² − (1−θ²)/(m−1)` on `δ < |u| ≤ L/J`, a `δ`-separated set of heights at level `θ` in a window of length `L`
has at most `J(m−1)` points. -/
theorem card_le_of_no_low_return {A : Finset ℝ} {θ δ T L : ℝ} {J m : ℕ} (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1) (hS : 0 < S.size) (hL : 0 < L) (hJ : 0 < J) (hm : 2 ≤ m)
    (hAI : ∀ t ∈ A, t ∈ Set.Icc T (T + L)) (hA : ∀ t ∈ A, t ∈ S.largeValue θ)
    (hsep : ∀ t ∈ A, ∀ u ∈ A, t ≠ u → δ < |t - u|)
    (hlow : ∀ v, δ < |v| → |v| ≤ L / J →
      S.column v < (θ ^ 2 - (1 - θ ^ 2) / ((m : ℝ) - 1)) * S.size) :
    A.card ≤ J * (m - 1) := by
  by_contra hcon
  obtain ⟨t, ht, u, hu, htu, hshort, hle⟩ :=
    S.exists_low_return_of_many_large_values hθ0 hθ1 hS hL hJ hm hAI hA (not_le.mp hcon)
  exact absurd hle (not_le.mpr (hlow (t - u) (hsep t ht u hu htu) hshort))

end PhaseSystem

end

end GaloisForLFunctions.PrimeTorusTheory
