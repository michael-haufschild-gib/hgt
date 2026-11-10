import GaloisForLFunctions.InfiniteRankPurityTheory.TheLefschetzNumbersOfTheIntegersAreNotTraces
import GaloisForLFunctions.SurfaceOfSpecZ.ThePointCountOfSpecZ

/-!
# The archimedean fibre is a trace and the finite contacts are not

The Lefschetz number of the Frobenius at `n` on the glued square of `Spec ℤ` is
`Λ(n) + n²/(n² − 1)`: the finite contacts contribute `Λ(n)`, the archimedean fibre
`n²/(n² − 1) = Σ_{k ≥ 0} n^{−2k}`. This module decides which part is the trace of a Frobenius module.

**Traces determine the module** (`mergedWeight_eq_of_frobTrace_eventually_eq`). Two modules of trace
class at a Frobenius `q`, with weights without ascending chain, whose traces agree at all large
integers carry the same total weight at every mode. Modes may repeat: the statement is about the
merged weight `Σ_{ρ_i = w} b_i`. More generally the weight filtration is the growth filtration
(`frobTrace_bound_iff_mergedWeight`, `mergedWeight_eq_zero_of_frobTrace_bound_at`): `‖t(n)‖ ≤ C n^s`
at all large integers exactly when no weight is carried at a mode with `Re w > s`.

**The archimedean fibre** (`frobTrace_evenJets`, `archimedeanFibre_forced`). The module with modes
`0, −2, −4, …`, each of weight one, is of trace class of every order at the Frobenius `2`, not at the
identity (`evenJets_not_traceClassAt_one`), and has the trace `n²/(n² − 1)`. Conversely every module of trace class at `2` with that trace carries weight one
at each even jet `−2k` and weight zero elsewhere.

**The finite contacts** (`not_isTrace_gluedLefschetz`, `not_isTrace_pointCount`). Since `Λ` is not a
trace of any order, neither is the Lefschetz number of the glued square. Whatever cohomology a
diagonal of the square carries, its Frobenii are not of trace class at any Frobenius and of any
order: the Lefschetz formula of the square is an identity of distributions.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-! ### Weights without ascending chain -/

/-- Weights without ascending chain are bounded above. -/
theorem WeightsWellFounded.exists_le {ρ : ι → ℂ} (h : WeightsWellFounded ρ) :
    ∃ A : ℝ, ∀ i, (ρ i).re ≤ A := by
  rcases isEmpty_or_nonempty ι with he | ⟨⟨i₀⟩⟩
  · exact ⟨0, fun i => (he.false i).elim⟩
  · obtain ⟨σ, -, hσ⟩ := h (Set.range fun i => (ρ i).re) subset_rfl ⟨_, ⟨i₀, rfl⟩⟩
    exact ⟨σ, fun i => hσ _ ⟨i, rfl⟩⟩

/-- The sum of two modules with weights without ascending chain has weights without ascending
chain. -/
theorem WeightsWellFounded.sum_elim {ρ : ι → ℂ} {σ : κ → ℂ} (h₁ : WeightsWellFounded ρ)
    (h₂ : WeightsWellFounded σ) : WeightsWellFounded (Sum.elim ρ σ) := by
  intro S hS hne
  set S₁ : Set ℝ := S ∩ Set.range fun i => (ρ i).re with hS₁
  set S₂ : Set ℝ := S ∩ Set.range fun j => (σ j).re with hS₂
  have hcover : ∀ τ ∈ S, τ ∈ S₁ ∨ τ ∈ S₂ := by
    intro τ hτ
    obtain ⟨t, ht⟩ := hS hτ
    rcases t with i | j
    · exact Or.inl ⟨hτ, i, by simpa using ht⟩
    · exact Or.inr ⟨hτ, j, by simpa using ht⟩
  by_cases e₁ : S₁.Nonempty
  · obtain ⟨m₁, hm₁, hmax₁⟩ := h₁ S₁ Set.inter_subset_right e₁
    by_cases e₂ : S₂.Nonempty
    · obtain ⟨m₂, hm₂, hmax₂⟩ := h₂ S₂ Set.inter_subset_right e₂
      rcases le_total m₁ m₂ with h | h
      · exact ⟨m₂, hm₂.1, fun τ hτ =>
          (hcover τ hτ).elim (fun h' => (hmax₁ τ h').trans h) (hmax₂ τ)⟩
      · exact ⟨m₁, hm₁.1, fun τ hτ =>
          (hcover τ hτ).elim (hmax₁ τ) fun h' => (hmax₂ τ h').trans h⟩
    · exact ⟨m₁, hm₁.1, fun τ hτ =>
        (hcover τ hτ).elim (hmax₁ τ) fun h' => (e₂ ⟨τ, h'⟩).elim⟩
  · obtain ⟨τ₀, hτ₀⟩ := hne
    have e₂ : S₂.Nonempty := ⟨τ₀, (hcover τ₀ hτ₀).resolve_left fun h => e₁ ⟨τ₀, h⟩⟩
    obtain ⟨m₂, hm₂, hmax₂⟩ := h₂ S₂ Set.inter_subset_right e₂
    exact ⟨m₂, hm₂.1, fun τ hτ => (hcover τ hτ).elim (fun h' => (e₁ ⟨τ, h'⟩).elim) (hmax₂ τ)⟩

/-! ### Merged weights -/

/-- The total weight the module carries at the mode `w`. -/
noncomputable def mergedWeight (c ρ : ι → ℂ) (w : ℂ) : ℂ := ∑' i, if ρ i = w then c i else 0

theorem mergedWeight_eq_tsum_fiber (c ρ : ι → ℂ) (k : Set.range ρ) :
    mergedWeight c ρ k = ∑' i : (Set.rangeFactorization ρ) ⁻¹' {k}, c i := by
  classical
  rw [mergedWeight, tsum_subtype ((Set.rangeFactorization ρ) ⁻¹' {k}) c]
  refine tsum_congr fun i => ?_
  have hiff : (i ∈ (Set.rangeFactorization ρ) ⁻¹' {k}) ↔ ρ i = k := by
    simp [Set.rangeFactorization, Subtype.ext_iff]
  rw [Set.indicator_apply]
  by_cases h : ρ i = k
  · rw [if_pos h, if_pos (hiff.mpr h)]
  · rw [if_neg h, if_neg fun h' => h (hiff.mp h')]

/-- The merged module is of trace class. -/
theorem summable_norm_mergedWeight {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖) :
    Summable fun k : Set.range ρ => ‖mergedWeight c ρ k‖ := by
  have hfib := hc.hasSum.tsum_fiberwise (Set.rangeFactorization ρ)
  refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => ?_) hfib.summable
  rw [mergedWeight_eq_tsum_fiber]
  exact norm_tsum_le_tsum_norm (hc.subtype _)

/-- The merged module has the same trace. -/
theorem frobTrace_merged {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖) {A : ℝ}
    (hA : ∀ i, (ρ i).re ≤ A) {x : ℝ} (hx : 1 ≤ x) :
    frobTrace (fun k : Set.range ρ => mergedWeight c ρ k) (fun k : Set.range ρ => (k : ℂ)) x =
      frobTrace c ρ x := by
  have hfib := (summable_frobTerm hc hA hx).hasSum.tsum_fiberwise (Set.rangeFactorization ρ)
  have hinner : ∀ k : Set.range ρ,
      (∑' i : (Set.rangeFactorization ρ) ⁻¹' {k}, c i * (x : ℂ) ^ ρ i) =
        mergedWeight c ρ k * (x : ℂ) ^ (k : ℂ) := by
    intro k
    rw [mergedWeight_eq_tsum_fiber, ← tsum_mul_right]
    refine tsum_congr fun i => ?_
    have hfac : Set.rangeFactorization ρ i.1 = k := i.2
    have hi : ρ i = k := congrArg Subtype.val hfac
    rw [hi]
  simp_rw [hinner] at hfib
  rw [frobTrace, frobTrace]
  exact hfib.tsum_eq

theorem weightsWellFounded_range {ρ : ι → ℂ} (hwf : WeightsWellFounded ρ) :
    WeightsWellFounded fun k : Set.range ρ => (k : ℂ) := by
  intro S hS hne
  refine hwf S (hS.trans ?_) hne
  rintro _ ⟨⟨_, i, rfl⟩, rfl⟩
  exact ⟨i, rfl⟩

/-- **The growth of the trace bounds the weights, with repeated modes.** Summable weights, weights
without ascending chain: if `‖t(n)‖ ≤ C n^s` at all large integers, no weight is carried at a mode
`w` with `Re w > s`. -/
theorem mergedWeight_eq_zero_of_frobTrace_bound {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hwf : WeightsWellFounded ρ) {s C : ℝ} {n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) {w : ℂ} (hw : s < w.re) :
    mergedWeight c ρ w = 0 := by
  by_cases hmem : w ∈ Set.range ρ
  · obtain ⟨A, hA⟩ := hwf.exists_le
    by_contra hne
    have h0' : ∀ n : ℕ, max n₀ 1 ≤ n →
        ‖frobTrace (fun k : Set.range ρ => mergedWeight c ρ k)
          (fun k : Set.range ρ => (k : ℂ)) n‖ ≤ C * (n : ℝ) ^ s := by
      intro n hn
      rw [frobTrace_merged hc hA (by exact_mod_cast le_trans (le_max_right _ _) hn)]
      exact h0 n (le_trans (le_max_left _ _) hn)
    have hle := re_le_of_frobTrace_bound (summable_norm_mergedWeight hc) Subtype.val_injective
      (weightsWellFounded_range hwf) h0' ⟨w, hmem⟩ hne
    exact absurd hle (not_le.mpr hw)
  · rw [mergedWeight]
    refine (tsum_congr fun i => ?_).trans tsum_zero
    rw [if_neg fun h => hmem ⟨i, h⟩]

/-- **The weight filtration is the growth filtration, with repeated modes.** The trace is `O(n^s)`
at the integers exactly when no weight is carried at a mode `w` with `Re w > s`. -/
theorem frobTrace_bound_iff_mergedWeight {c ρ : ι → ℂ} (hc : Summable fun i => ‖c i‖)
    (hwf : WeightsWellFounded ρ) (s : ℝ) :
    (∃ C : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) ↔
      ∀ w : ℂ, s < w.re → mergedWeight c ρ w = 0 := by
  constructor
  · rintro ⟨C, n₀, h⟩ w hw
    exact mergedWeight_eq_zero_of_frobTrace_bound hc hwf h hw
  · intro hzero
    obtain ⟨A, hA⟩ := hwf.exists_le
    obtain ⟨C, n₀, h⟩ := (frobTrace_bound_iff (summable_norm_mergedWeight hc)
      Subtype.val_injective (weightsWellFounded_range hwf) s).mpr
      fun k hk => not_lt.mp fun hlt => hk (hzero k hlt)
    refine ⟨C, max n₀ 1, fun n hn => ?_⟩
    rw [← frobTrace_merged hc hA (by exact_mod_cast le_trans (le_max_right _ _) hn)]
    exact h n (le_trans (le_max_left _ _) hn)

theorem mergedWeight_dilate (c ρ : ι → ℂ) (q : ℕ) (w : ℂ) :
    mergedWeight (fun i => c i * (q : ℂ) ^ ρ i) ρ w = mergedWeight c ρ w * (q : ℂ) ^ w := by
  rw [mergedWeight, mergedWeight, ← tsum_mul_right]
  refine tsum_congr fun i => ?_
  by_cases h : ρ i = w
  · rw [if_pos h, if_pos h, h]
  · rw [if_neg h, if_neg h, zero_mul]

/-- The same at any Frobenius. -/
theorem mergedWeight_eq_zero_of_frobTrace_bound_at {c ρ : ι → ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hc : TraceClassAt q 0 c ρ) (hwf : WeightsWellFounded ρ) {s C : ℝ} {n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → ‖frobTrace c ρ n‖ ≤ C * (n : ℝ) ^ s) {w : ℂ} (hw : s < w.re) :
    mergedWeight c ρ w = 0 := by
  have hc' : Summable fun i => ‖c i * (q : ℂ) ^ ρ i‖ := by simpa using hc.dilated hq
  have h0' : ∀ n : ℕ, max n₀ 1 ≤ n → ‖frobTrace (fun i => c i * (q : ℂ) ^ ρ i) ρ n‖ ≤
      C * (q : ℝ) ^ s * (n : ℝ) ^ s := by
    intro n hn
    have hn0 : n₀ ≤ n := le_trans (le_max_left _ _) hn
    have h := h0 (q * n) (hn0.trans (Nat.le_mul_of_pos_left n hq))
    rw [← frobTrace_dilate c ρ q (Nat.cast_nonneg n)]
    push_cast at h
    rw [Real.mul_rpow (Nat.cast_nonneg q) (Nat.cast_nonneg n), ← mul_assoc] at h
    exact h
  have h := mergedWeight_eq_zero_of_frobTrace_bound hc' hwf h0' hw
  rw [mergedWeight_dilate] at h
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast (by omega : q ≠ 0)
  exact (mul_eq_zero.mp h).resolve_right (by simp [Complex.cpow_eq_zero_iff, hq0])

/-- A trace vanishing at all large integers carries no weight at any mode. -/
theorem mergedWeight_eq_zero_of_frobTrace_eventually_zero {c ρ : ι → ℂ} {q : ℕ} (hq : 1 ≤ q)
    (hc : TraceClassAt q 0 c ρ) (hwf : WeightsWellFounded ρ) {n₀ : ℕ}
    (h0 : ∀ n : ℕ, n₀ ≤ n → frobTrace c ρ n = 0) (w : ℂ) : mergedWeight c ρ w = 0 :=
  mergedWeight_eq_zero_of_frobTrace_bound_at hq hc hwf (s := w.re - 1) (C := 0) (n₀ := n₀)
    (fun n hn => by rw [h0 n hn]; simp) (by linarith)

/-- The weights at one mode are summable. -/
theorem summable_fiber {q : ℕ} (hq : 1 ≤ q) {b ρ : ι → ℂ} (hb : TraceClassAt q 0 b ρ) (w : ℂ) :
    Summable fun i => if ρ i = w then b i else 0 := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hpos : 0 < (q : ℝ) ^ w.re := Real.rpow_pos_of_pos hq0 _
  have hb' : Summable fun i => ‖b i‖ * (q : ℝ) ^ (ρ i).re := by simpa [TraceClassAt] using hb
  refine Summable.of_norm_bounded (hb'.mul_left ((q : ℝ) ^ w.re)⁻¹) fun i => ?_
  by_cases h : ρ i = w
  · rw [if_pos h, h, mul_comm ‖b i‖, ← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  · rw [if_neg h, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hpos.le)
      (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hq0.le _))

/-- **Traces determine the module.** Two modules of trace class at `q`, with weights without
ascending chain, whose traces agree at all large integers carry the same weight at every mode. -/
theorem mergedWeight_eq_of_frobTrace_eventually_eq {b ρ : ι → ℂ} {c σ : κ → ℂ} {q : ℕ}
    (hq : 1 ≤ q) (hb : TraceClassAt q 0 b ρ) (hc : TraceClassAt q 0 c σ)
    (hρ : WeightsWellFounded ρ) (hσ : WeightsWellFounded σ) {n₀ : ℕ}
    (h : ∀ n : ℕ, n₀ ≤ n → frobTrace b ρ n = frobTrace c σ n) (w : ℂ) :
    mergedWeight b ρ w = mergedWeight c σ w := by
  obtain ⟨A, hA⟩ := hρ.exists_le
  obtain ⟨B, hB⟩ := hσ.exists_le
  -- the difference module
  have hdsum : TraceClassAt q 0 (Sum.elim b fun j => -c j) (Sum.elim ρ σ) := by
    refine Summable.sum _ ?_ ?_
    · simpa only [TraceClassAt, Function.comp_def, Sum.elim_inl] using hb
    · simpa only [TraceClassAt, Function.comp_def, Sum.elim_inr, norm_neg] using hc
  have hzero : ∀ n : ℕ, max n₀ q ≤ n →
      frobTrace (Sum.elim b fun j => -c j) (Sum.elim ρ σ) n = 0 := by
    intro n hn
    have hx : (q : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_trans (le_max_right _ _) hn
    have s1 := (hb.summable_term hq hA hx).hasSum
    have s2 := ((hc.summable_term hq hB hx).neg).hasSum
    have hsum : HasSum (fun t : ι ⊕ κ => Sum.elim b (fun j => -c j) t *
        ((n : ℝ) : ℂ) ^ Sum.elim ρ σ t)
        ((∑' i, b i * ((n : ℝ) : ℂ) ^ ρ i) + ∑' j, -(c j * ((n : ℝ) : ℂ) ^ σ j)) := by
      refine HasSum.sum ?_ ?_
      · simpa only [Function.comp_def, Sum.elim_inl] using s1
      · simpa only [Function.comp_def, Sum.elim_inr, neg_mul] using s2
    have heq := h n (le_trans (le_max_left _ _) hn)
    rw [frobTrace, frobTrace] at heq
    rw [frobTrace, hsum.tsum_eq, tsum_neg, heq]
    ring
  have hm := mergedWeight_eq_zero_of_frobTrace_eventually_zero hq hdsum (hρ.sum_elim hσ) hzero w
  -- the weight of the difference module is the difference of the weights
  have hs : HasSum (fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
      Sum.elim b (fun j => -c j) t else 0)
      ((∑' i, if ρ i = w then b i else 0) + ∑' j, -(if σ j = w then c j else 0)) := by
    refine HasSum.sum ?_ ?_
    · have hfun : ((fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
          Sum.elim b (fun j => -c j) t else 0) ∘ Sum.inl) = fun i => if ρ i = w then b i else 0 := by
        funext i
        simp only [Function.comp_apply, Sum.elim_inl]
      rw [hfun]
      exact (summable_fiber hq hb w).hasSum
    · have hfun : ((fun t : ι ⊕ κ => if Sum.elim ρ σ t = w then
          Sum.elim b (fun j => -c j) t else 0) ∘ Sum.inr) =
          fun j => -(if σ j = w then c j else 0) := by
        funext j
        simp only [Function.comp_apply, Sum.elim_inr]
        split_ifs <;> simp
      rw [hfun]
      exact (summable_fiber hq hc w).neg.hasSum
  rw [mergedWeight, hs.tsum_eq, tsum_neg] at hm
  rw [mergedWeight, mergedWeight]
  linear_combination hm

/-! ### The archimedean fibre -/

/-- The modes of the archimedean fibre: the even jets `−2k`, `k ≥ 0`. -/
def evenJet (k : ℕ) : ℂ := -(2 * (k : ℂ))

theorem evenJet_re (k : ℕ) : (evenJet k).re = -(2 * (k : ℝ)) := by simp [evenJet]

theorem evenJet_injective : Function.Injective evenJet := by
  intro j k h
  have h' := congrArg Complex.re h
  rw [evenJet_re, evenJet_re] at h'
  have : (j : ℝ) = k := by linarith
  exact_mod_cast this

theorem weightsWellFounded_evenJet : WeightsWellFounded evenJet := by
  classical
  intro S hS hne
  have hex : ∃ k : ℕ, -(2 * (k : ℝ)) ∈ S := by
    obtain ⟨τ, hτ⟩ := hne
    obtain ⟨k, hk⟩ := hS hτ
    refine ⟨k, ?_⟩
    have hk' : -(2 * (k : ℝ)) = τ := by rw [← hk]; exact (evenJet_re k).symm
    rw [hk']
    exact hτ
  refine ⟨-(2 * (Nat.find hex : ℝ)), Nat.find_spec hex, fun τ hτ => ?_⟩
  obtain ⟨k, hk⟩ := hS hτ
  have hk' : τ = -(2 * (k : ℝ)) := by rw [← hk]; exact evenJet_re k
  have hmem : -(2 * (k : ℝ)) ∈ S := hk' ▸ hτ
  have hle : (Nat.find hex : ℝ) ≤ k := by exact_mod_cast Nat.find_min' hex hmem
  rw [hk']
  linarith

theorem ofReal_cpow_evenJet {x : ℝ} (hx : 0 < x) (k : ℕ) :
    (x : ℂ) ^ evenJet k = (((x ^ 2)⁻¹ : ℝ) : ℂ) ^ k := by
  have h1 : evenJet k = ((-(2 * (k : ℝ)) : ℝ) : ℂ) := by simp [evenJet]
  have h2 : (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
  rw [h1, ← Complex.ofReal_cpow hx.le, ← Complex.ofReal_pow]
  congr 1
  rw [Real.rpow_neg hx.le, h2, Real.rpow_natCast, pow_mul, inv_pow]

/-- **The trace of the archimedean fibre**: `Σ_{k ≥ 0} x^{−2k} = x²/(x² − 1)` for `x > 1`. -/
theorem frobTrace_evenJets {x : ℝ} (hx : 1 < x) :
    frobTrace (fun _ : ℕ => (1 : ℂ)) evenJet x = (x : ℂ) ^ 2 / ((x : ℂ) ^ 2 - 1) := by
  have hx0 : 0 < x := by linarith
  have hx2 : 1 < x ^ 2 := by nlinarith
  have hr0 : 0 ≤ (x ^ 2)⁻¹ := by positivity
  have hr1 : (x ^ 2)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hx2
  rw [frobTrace]
  simp_rw [one_mul, ofReal_cpow_evenJet hx0]
  rw [tsum_geometric_of_norm_lt_one
    (by rw [Complex.norm_real, Real.norm_of_nonneg hr0]; exact hr1)]
  have hxc : (x : ℂ) ^ 2 ≠ 0 := by exact_mod_cast (pow_pos hx0 2).ne'
  have hxc1 : (x : ℂ) ^ 2 - 1 ≠ 0 := by
    have : (x ^ 2 - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have h1 : (1 - ((x : ℂ) ^ 2)⁻¹) = ((x : ℂ) ^ 2 - 1) / (x : ℂ) ^ 2 := by
    rw [eq_div_iff hxc, sub_mul, one_mul, inv_mul_cancel₀ hxc]
  push_cast
  rw [h1, inv_div]

/-- The archimedean fibre is of trace class of every order at the Frobenius `2`. -/
theorem evenJets_traceClassAt (m : ℕ) : TraceClassAt 2 m (fun _ : ℕ => (1 : ℂ)) evenJet := by
  have hterm : ∀ k : ℕ, ‖(1 : ℂ)‖ * ((2 : ℕ) : ℝ) ^ (evenJet k).re * (1 + ‖evenJet k‖) ^ m =
      ∑ j ∈ Finset.range (m + 1),
        ((2 : ℝ) ^ j * (m.choose j : ℝ)) * ((k : ℝ) ^ j * (1 / 4 : ℝ) ^ k) := by
    intro k
    have hnorm : ‖evenJet k‖ = 2 * (k : ℝ) := by
      rw [evenJet, norm_neg, norm_mul]
      simp
    have hpow : ((2 : ℕ) : ℝ) ^ (-(2 * (k : ℝ))) = (1 / 4 : ℝ) ^ k := by
      have h2 : (2 * (k : ℝ)) = ((2 * k : ℕ) : ℝ) := by push_cast; ring
      rw [Real.rpow_neg (by norm_num), h2, Real.rpow_natCast, pow_mul]
      norm_num
      rw [one_div, inv_pow]
    rw [norm_one, one_mul, evenJet_re, hnorm, hpow, add_comm, add_pow, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_pow, mul_one, mul_pow]
    ring
  exact (summable_sum fun j _ => (summable_pow_mul_geometric_of_norm_lt_one j
    (by norm_num : ‖(1 / 4 : ℝ)‖ < 1)).mul_left _).congr fun k => (hterm k).symm

/-- At the identity the archimedean fibre is not of trace class: its rank is infinite. -/
theorem evenJets_not_traceClassAt_one : ¬ TraceClassAt 1 0 (fun _ : ℕ => (1 : ℂ)) evenJet := by
  intro h
  have h0 : Summable fun k : ℕ =>
      ‖(1 : ℂ)‖ * ((1 : ℕ) : ℝ) ^ (evenJet k).re * (1 + ‖evenJet k‖) ^ 0 := h
  have h1 : Summable fun _ : ℕ => (1 : ℝ) := h0.congr fun k => by simp
  exact one_ne_zero (tendsto_nhds_unique tendsto_const_nhds h1.tendsto_atTop_zero)

/-- The archimedean Lefschetz number `n²/(n² − 1)` is a trace of every order `m ≥ 1`. -/
theorem isTrace_archimedean {m : ℕ} (hm : 1 ≤ m) :
    IsTrace m fun n : ℕ => (n : ℂ) ^ 2 / ((n : ℂ) ^ 2 - 1) := by
  refine ⟨ℕ, fun _ => 1, evenJet, 0, 2, by norm_num, fun k => ?_, by exact_mod_cast hm,
    evenJets_traceClassAt m, ?_⟩
  · rw [evenJet_re]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    linarith
  · filter_upwards [eventually_ge_atTop 2] with n hn
    have h1 : (1 : ℝ) < n := by exact_mod_cast hn
    rw [frobTrace_evenJets h1]
    push_cast
    rfl

theorem mergedWeight_evenJets_self (k : ℕ) :
    mergedWeight (fun _ : ℕ => (1 : ℂ)) evenJet (evenJet k) = 1 := by
  rw [mergedWeight, tsum_eq_single k]
  · simp
  · intro j hj
    rw [if_neg fun h' => hj (evenJet_injective h')]

theorem mergedWeight_evenJets_of_ne {w : ℂ} (h : ∀ k : ℕ, w ≠ evenJet k) :
    mergedWeight (fun _ : ℕ => (1 : ℂ)) evenJet w = 0 := by
  rw [mergedWeight]
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [if_neg fun h' => h k h'.symm]

/-- **The archimedean fibre is forced by its Lefschetz numbers.** A module of trace class at the
Frobenius `2`, with weights without ascending chain, whose trace at all large integers is
`n²/(n² − 1)`, carries weight one at each even jet `−2k` and weight zero at every other mode. -/
theorem archimedeanFibre_forced {b ρ : ι → ℂ} (hb : TraceClassAt 2 0 b ρ)
    (hwf : WeightsWellFounded ρ) {n₀ : ℕ}
    (h : ∀ n : ℕ, n₀ ≤ n → frobTrace b ρ n = (n : ℂ) ^ 2 / ((n : ℂ) ^ 2 - 1)) :
    (∀ k : ℕ, mergedWeight b ρ (evenJet k) = 1) ∧
      ∀ w : ℂ, (∀ k : ℕ, w ≠ evenJet k) → mergedWeight b ρ w = 0 := by
  have key : ∀ w : ℂ, mergedWeight b ρ w = mergedWeight (fun _ : ℕ => (1 : ℂ)) evenJet w := by
    intro w
    refine mergedWeight_eq_of_frobTrace_eventually_eq (by norm_num) hb (evenJets_traceClassAt 0)
      hwf weightsWellFounded_evenJet (n₀ := max n₀ 2) (fun n hn => ?_) w
    have h1 : (1 : ℝ) < n := by exact_mod_cast le_trans (le_max_right _ _) hn
    rw [h n (le_trans (le_max_left _ _) hn), frobTrace_evenJets h1]
    push_cast
    rfl
  exact ⟨fun k => (key _).trans (mergedWeight_evenJets_self k),
    fun w hw => (key w).trans (mergedWeight_evenJets_of_ne hw)⟩

/-! ### The glued square -/

theorem IsTrace.congr' {m : ℕ} {f g : ℕ → ℂ} (hf : IsTrace m f)
    (h : ∀ᶠ n : ℕ in atTop, g n = f n) : IsTrace m g := by
  obtain ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, hfe⟩ := hf
  refine ⟨ι, b, ρ, A, q, hq, hA, hAm, hb, ?_⟩
  filter_upwards [h, hfe] with n h1 h2
  rw [h1, h2]

/-- **The Lefschetz numbers of the glued square are not a trace of any order.** -/
theorem not_isTrace_gluedLefschetz (m : ℕ) :
    ¬ IsTrace m fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) +
      (n : ℂ) ^ 2 / ((n : ℂ) ^ 2 - 1) := by
  intro hf
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- a trace of order zero tends to zero, the Lefschetz numbers are at least one
    have h0 := hf.tendsto_fwdDiff.norm
    simp only [Function.iterate_zero, id, norm_zero] at h0
    have hlt := h0.eventually (gt_mem_nhds one_pos)
    have hge : ∀ᶠ n : ℕ in atTop, (1 : ℝ) ≤ ‖((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) +
        (n : ℂ) ^ 2 / ((n : ℂ) ^ 2 - 1)‖ := by
      filter_upwards [eventually_ge_atTop 2] with n hn
      have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hpos : (0 : ℝ) < (n : ℝ) ^ 2 - 1 := by nlinarith
      have hcast : ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) + (n : ℂ) ^ 2 / ((n : ℂ) ^ 2 - 1) =
          ((ArithmeticFunction.vonMangoldt n + (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) : ℝ) : ℂ) := by
        push_cast
        rfl
      have h1 : (1 : ℝ) ≤ (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := (one_le_div hpos).mpr (by linarith)
      have h2 : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
      rw [hcast, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    obtain ⟨n, hn1, hn2⟩ := (hlt.and hge).exists
    linarith
  · refine not_isTrace_vonMangoldt m ((hf.sub (isTrace_archimedean hm)).congr'
      (Eventually.of_forall fun n => ?_))
    ring

/-- The point count of the Frobenius on the surface of `Spec ℤ` is not a trace of any order. -/
theorem not_isTrace_pointCount (m : ℕ) :
    ¬ IsTrace m fun n : ℕ => ((SurfaceOfSpecZ.pointCount n : ℝ) : ℂ) := by
  intro hf
  refine not_isTrace_gluedLefschetz m (hf.congr' ?_)
  filter_upwards [eventually_ge_atTop 2] with n hn
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hpos : (n : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  rw [SurfaceOfSpecZ.pointCount_eq hn]
  have hreal : (ArithmeticFunction.vonMangoldt n + 1 + 1 / ((n : ℝ) ^ 2 - 1) : ℝ) =
      ArithmeticFunction.vonMangoldt n + (n : ℝ) ^ 2 / ((n : ℝ) ^ 2 - 1) := by
    field_simp
    ring
  rw [hreal]
  push_cast
  rfl

end GaloisForLFunctions.InfiniteRankPurityTheory
