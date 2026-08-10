import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Thinning a divergent series below a fractional power

A positive series with divergent sum and terms tending to zero always contains a *convergent*
subseries whose fractional powers still diverge.  The construction is greedy: cut the index line
into consecutive blocks whose sums are about `2^{-j}` but whose terms are already smaller than
`(2^{-j})^{1/(1-s)}`.  Each block then contributes at least `1` to the `s`-power sum, because on it

```text
y^s = y · y^{s-1} ≥ y · δ^{s-1},     δ^{s-1} · (block sum) ≥ δ^{s-1} · τ = 1.
```

The union of the blocks is the required index set.  This separates two exponents inside one
divergent scale, which is what distinguishes a twisted product measure from its critical one when
both have divergent local masses.
-/

open Filter Finset
open scoped Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The target block masses, summing to one. -/
def thinTau (j : ℕ) : ℝ := (2 : ℝ)⁻¹ ^ (j + 1)

theorem thinTau_pos (j : ℕ) : 0 < thinTau j := by
  rw [thinTau]
  positivity

theorem thinTau_le_one (j : ℕ) : thinTau j ≤ 1 := by
  rw [thinTau]
  apply pow_le_one₀ (by norm_num) (by norm_num)

theorem summable_thinTau : Summable thinTau := by
  have hgeo : Summable (fun j : ℕ => (2 : ℝ)⁻¹ ^ j) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (hgeo.mul_left (2 : ℝ)⁻¹).congr fun j => ?_
  rw [thinTau, pow_succ]
  ring

/-- The maximal term size allowed inside the `j`-th block. -/
def thinDelta (s : ℝ) (j : ℕ) : ℝ := thinTau j ^ (1 / (1 - s))

theorem thinDelta_pos {s : ℝ} (j : ℕ) : 0 < thinDelta s j :=
  Real.rpow_pos_of_pos (thinTau_pos j) _

theorem thinDelta_le_thinTau {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    thinDelta s j ≤ thinTau j := by
  have hexp : (1 : ℝ) ≤ 1 / (1 - s) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have h := Real.rpow_le_rpow_of_exponent_ge (thinTau_pos j) (thinTau_le_one j) hexp
  rwa [Real.rpow_one] at h

/-- The exact gain of a block: `δ^{s-1} · τ = 1`. -/
theorem thinDelta_rpow_mul_thinTau {s : ℝ} (hs1 : s < 1) (j : ℕ) :
    thinDelta s j ^ (s - 1) * thinTau j = 1 := by
  have hpos := thinTau_pos j
  have hne : (1 : ℝ) - s ≠ 0 := (by linarith : (0 : ℝ) < 1 - s).ne'
  rw [thinDelta, ← Real.rpow_mul hpos.le]
  rw [show (1 / (1 - s)) * (s - 1) = -1 by
    field_simp
    ring]
  rw [Real.rpow_neg_one, inv_mul_cancel₀ hpos.ne']

/-! ## The greedy blocks -/

/-- The first index beyond which every term is at most `δ`. -/
def smallStart (y : ℕ → ℝ) (δ : ℝ) : ℕ := sInf {N | ∀ n, N ≤ n → y n ≤ δ}

theorem le_of_smallStart_le {y : ℕ → ℝ} {δ : ℝ} (hlim : Tendsto y atTop (𝓝 0)) (hδ : 0 < δ)
    {n : ℕ} (hn : smallStart y δ ≤ n) : y n ≤ δ := by
  have hne : {N | ∀ n, N ≤ n → y n ≤ δ}.Nonempty := by
    obtain ⟨N, hN⟩ := (hlim.eventually (eventually_le_nhds hδ)).exists_forall_of_atTop
    exact ⟨N, fun n hnN => (hN n hnN)⟩
  exact Nat.sInf_mem hne n hn

/-- The right end of the greedy block starting at `m` with target mass `τ`. -/
def blockEnd (y : ℕ → ℝ) (m : ℕ) (τ : ℝ) : ℕ :=
  sInf {M | m ≤ M ∧ τ ≤ ∑ n ∈ Finset.Ico m M, y n}

section Block

variable {y : ℕ → ℝ} {m : ℕ} {τ : ℝ}

theorem blockEnd_set_nonempty (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) :
    {M | m ≤ M ∧ τ ≤ ∑ n ∈ Finset.Ico m M, y n}.Nonempty := by
  have htend := (not_summable_iff_tendsto_nat_atTop_of_nonneg hy0).mp hdiv
  obtain ⟨M, hM⟩ := (htend.eventually_ge_atTop (τ + ∑ i ∈ Finset.range m, y i)).exists_forall_of_atTop
  refine ⟨max m M, le_max_left _ _, ?_⟩
  have hMle : M ≤ max m M := le_max_right _ _
  have hsum : τ + ∑ i ∈ Finset.range m, y i ≤ ∑ i ∈ Finset.range (max m M), y i := hM _ hMle
  rw [Finset.sum_Ico_eq_sub _ (le_max_left m M)]
  linarith

theorem le_blockEnd (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) :
    m ≤ blockEnd y m τ :=
  (Nat.sInf_mem (blockEnd_set_nonempty hy0 hdiv)).1

theorem blockEnd_sum_ge (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) :
    τ ≤ ∑ n ∈ Finset.Ico m (blockEnd y m τ), y n :=
  (Nat.sInf_mem (blockEnd_set_nonempty hy0 hdiv)).2

theorem lt_blockEnd (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (hτ : 0 < τ) :
    m < blockEnd y m τ := by
  rcases lt_or_eq_of_le (le_blockEnd (τ := τ) hy0 hdiv) with h | h
  · exact h
  · exfalso
    have := blockEnd_sum_ge (y := y) (m := m) (τ := τ) hy0 hdiv
    rw [← h] at this
    simp at this
    linarith

/-- Greedy minimality: the block overshoots its target by at most its last term. -/
theorem blockEnd_sum_le (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (hτ : 0 < τ) :
    ∑ n ∈ Finset.Ico m (blockEnd y m τ), y n ≤ τ + y (blockEnd y m τ - 1) := by
  have hlt : m < blockEnd y m τ := lt_blockEnd hy0 hdiv hτ
  obtain ⟨e, he⟩ : ∃ e, blockEnd y m τ = e + 1 := ⟨blockEnd y m τ - 1, by omega⟩
  have hme : m ≤ e := by omega
  have hlte : e < sInf {M | m ≤ M ∧ τ ≤ ∑ n ∈ Finset.Ico m M, y n} := by
    rw [← blockEnd, he]
    omega
  have hnot : e ∉ {M | m ≤ M ∧ τ ≤ ∑ n ∈ Finset.Ico m M, y n} := Nat.notMem_of_lt_sInf hlte
  have hlt' : ∑ n ∈ Finset.Ico m e, y n < τ := by
    by_contra hcon
    exact hnot ⟨hme, not_lt.mp hcon⟩
  rw [he, Finset.sum_Ico_succ_top hme]
  simp only [Nat.add_sub_cancel]
  linarith

end Block

/-- The left ends of the greedy blocks. -/
def thinStart (y : ℕ → ℝ) (s : ℝ) : ℕ → ℕ
  | 0 => smallStart y (thinDelta s 0)
  | j + 1 => max (smallStart y (thinDelta s (j + 1))) (blockEnd y (thinStart y s j) (thinTau j))

/-- The right ends of the greedy blocks. -/
def thinEnd (y : ℕ → ℝ) (s : ℝ) (j : ℕ) : ℕ := blockEnd y (thinStart y s j) (thinTau j)

theorem smallStart_le_thinStart (y : ℕ → ℝ) (s : ℝ) (j : ℕ) :
    smallStart y (thinDelta s j) ≤ thinStart y s j := by
  cases j with
  | zero => exact le_rfl
  | succ j => exact le_max_left _ _

theorem thinEnd_le_thinStart_succ (y : ℕ → ℝ) (s : ℝ) (j : ℕ) :
    thinEnd y s j ≤ thinStart y s (j + 1) := le_max_right _ _

theorem thinStart_le_thinEnd {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (s : ℝ)
    (j : ℕ) : thinStart y s j ≤ thinEnd y s j :=
  le_blockEnd hy0 hdiv

theorem thinStart_mono {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (s : ℝ) :
    Monotone (thinStart y s) := by
  apply monotone_nat_of_le_succ
  intro j
  exact le_trans (thinStart_le_thinEnd hy0 hdiv s j) (thinEnd_le_thinStart_succ y s j)

/-- The greedy blocks. -/
def thinBlock (y : ℕ → ℝ) (s : ℝ) (j : ℕ) : Finset ℕ :=
  Finset.Ico (thinStart y s j) (thinEnd y s j)

theorem thinBlock_disjoint {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (s : ℝ)
    {i j : ℕ} (hij : i ≠ j) : Disjoint (thinBlock y s i) (thinBlock y s j) := by
  wlog hlt : i < j generalizing i j
  · exact (this hij.symm (by omega)).symm
  refine Finset.disjoint_left.mpr fun n hni hnj => ?_
  rw [thinBlock, Finset.mem_Ico] at hni hnj
  have hchain : thinEnd y s i ≤ thinStart y s j :=
    le_trans (thinEnd_le_thinStart_succ y s i)
      (thinStart_mono hy0 hdiv s (by omega : i + 1 ≤ j))
  omega

theorem thinBlock_sum_ge {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y) (s : ℝ) (j : ℕ) :
    thinTau j ≤ ∑ n ∈ thinBlock y s j, y n :=
  blockEnd_sum_ge hy0 hdiv

theorem thinBlock_sum_le {y : ℕ → ℝ} (hy0 : ∀ n, 0 ≤ y n) (hdiv : ¬ Summable y)
    (hlim : Tendsto y atTop (𝓝 0)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    ∑ n ∈ thinBlock y s j, y n ≤ 2 * thinTau j := by
  have hlt : thinStart y s j < blockEnd y (thinStart y s j) (thinTau j) :=
    lt_blockEnd hy0 hdiv (thinTau_pos j)
  have hstart := smallStart_le_thinStart y s j
  have hlast : y (blockEnd y (thinStart y s j) (thinTau j) - 1) ≤ thinDelta s j := by
    apply le_of_smallStart_le hlim (thinDelta_pos j)
    omega
  have hover : ∑ n ∈ Finset.Ico (thinStart y s j) (blockEnd y (thinStart y s j) (thinTau j)), y n ≤
      thinTau j + y (blockEnd y (thinStart y s j) (thinTau j) - 1) :=
    blockEnd_sum_le hy0 hdiv (thinTau_pos j)
  have hdt := thinDelta_le_thinTau hs0 hs1 j
  rw [thinBlock, thinEnd]
  linarith

/-- Each block contributes at least one unit of `s`-power mass. -/
theorem thinBlock_rpow_sum_ge {y : ℕ → ℝ} (hy0 : ∀ n, 0 < y n) (hdiv : ¬ Summable y)
    (hlim : Tendsto y atTop (𝓝 0)) {s : ℝ} (_hs0 : 0 < s) (hs1 : s < 1) (j : ℕ) :
    1 ≤ ∑ n ∈ thinBlock y s j, y n ^ s := by
  have hy0' : ∀ n, 0 ≤ y n := fun n => (hy0 n).le
  have hterm : ∀ n ∈ thinBlock y s j, thinDelta s j ^ (s - 1) * y n ≤ y n ^ s := by
    intro n hn
    rw [thinBlock, Finset.mem_Ico] at hn
    have hsmall : y n ≤ thinDelta s j :=
      le_of_smallStart_le hlim (thinDelta_pos j)
        (le_trans (smallStart_le_thinStart y s j) hn.1)
    have hpow : thinDelta s j ^ (s - 1) ≤ y n ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos (hy0 n) hsmall (by linarith)
    have hsplit : y n ^ (s - 1) * y n = y n ^ s := by
      have hadd : y n ^ (s - 1) * y n ^ (1 : ℝ) = y n ^ ((s - 1) + 1) :=
        (Real.rpow_add (hy0 n) _ _).symm
      rw [Real.rpow_one] at hadd
      rw [hadd]
      norm_num
    rw [← hsplit]
    exact mul_le_mul_of_nonneg_right hpow (hy0 n).le
  calc (1 : ℝ) = thinDelta s j ^ (s - 1) * thinTau j :=
        (thinDelta_rpow_mul_thinTau hs1 j).symm
    _ ≤ thinDelta s j ^ (s - 1) * ∑ n ∈ thinBlock y s j, y n := by
        apply mul_le_mul_of_nonneg_left (thinBlock_sum_ge hy0' hdiv s j)
        exact (Real.rpow_pos_of_pos (thinDelta_pos j) _).le
    _ = ∑ n ∈ thinBlock y s j, thinDelta s j ^ (s - 1) * y n := by
        rw [Finset.mul_sum]
    _ ≤ ∑ n ∈ thinBlock y s j, y n ^ s := Finset.sum_le_sum hterm

/-! ## The thinned index set -/

/-- The union of the greedy blocks. -/
def thinSet (y : ℕ → ℝ) (s : ℝ) : Set ℕ := ⋃ j, ↑(thinBlock y s j)

/-- The index of the block containing a point of the thinned set. -/
def thinBlockIndex (y : ℕ → ℝ) (s : ℝ) (n : ℕ) : ℕ := sInf {j | n ∈ thinBlock y s j}

theorem mem_thinBlock_thinBlockIndex {y : ℕ → ℝ} {s : ℝ} {n : ℕ} (hn : n ∈ thinSet y s) :
    n ∈ thinBlock y s (thinBlockIndex y s n) := by
  have hne : {j | n ∈ thinBlock y s j}.Nonempty := by
    obtain ⟨B, ⟨j, rfl⟩, hnB⟩ := hn
    exact ⟨j, hnB⟩
  exact Nat.sInf_mem hne

theorem thinBlock_subset_thinSet (y : ℕ → ℝ) (s : ℝ) (j : ℕ) :
    (thinBlock y s j : Set ℕ) ⊆ thinSet y s := fun _ hn => Set.mem_iUnion.mpr ⟨j, hn⟩

theorem sum_range_thinTau_le (J : ℕ) : ∑ j ∈ Finset.range J, thinTau j ≤ 1 := by
  have hsum : ∑' j : ℕ, thinTau j = 1 := by
    have hgeo : ∑' j : ℕ, ((2 : ℝ)⁻¹) ^ j = 2 := by
      rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
      norm_num
    have hcongr : ∑' j : ℕ, thinTau j = (2 : ℝ)⁻¹ * ∑' j : ℕ, ((2 : ℝ)⁻¹) ^ j := by
      rw [← tsum_mul_left]
      exact tsum_congr fun j => by rw [thinTau, pow_succ]; ring
    rw [hcongr, hgeo]
    norm_num
  rw [← hsum]
  exact summable_thinTau.sum_le_tsum _ (fun j _ => (thinTau_pos j).le)

/-- **The thinned family is summable.** -/
theorem summable_indicator_thinSet {y : ℕ → ℝ} (hy0 : ∀ n, 0 < y n) (hdiv : ¬ Summable y)
    (hlim : Tendsto y atTop (𝓝 0)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    Summable (Set.indicator (thinSet y s) y) := by
  classical
  have hy0' : ∀ n, 0 ≤ y n := fun n => (hy0 n).le
  refine summable_of_sum_le (c := 2) (fun n => Set.indicator_nonneg (fun _ _ => hy0' _) n)
    fun F => ?_
  set G : Finset ℕ := F.filter (fun n => n ∈ thinSet y s) with hG
  have hFG : ∑ n ∈ F, Set.indicator (thinSet y s) y n = ∑ n ∈ G, y n := by
    rw [hG, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n ∈ thinSet y s <;> simp [hn, Set.indicator_of_mem, Set.indicator_of_notMem]
  set J : ℕ := (G.image (thinBlockIndex y s)).sup id + 1 with hJ
  set B : Finset ℕ := (Finset.range J).biUnion (thinBlock y s) with hB
  have hGB : G ⊆ B := by
    intro n hn
    have hmem : n ∈ thinSet y s := (Finset.mem_filter.mp hn).2
    refine Finset.mem_biUnion.mpr ⟨thinBlockIndex y s n, ?_, mem_thinBlock_thinBlockIndex hmem⟩
    rw [Finset.mem_range, hJ]
    have : thinBlockIndex y s n ≤ (G.image (thinBlockIndex y s)).sup id :=
      Finset.le_sup (f := id) (Finset.mem_image_of_mem _ hn)
    omega
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint (thinBlock y s) := by
    intro i _ j _ hij
    exact thinBlock_disjoint hy0' hdiv s hij
  calc ∑ n ∈ F, Set.indicator (thinSet y s) y n = ∑ n ∈ G, y n := hFG
    _ ≤ ∑ n ∈ B, y n := Finset.sum_le_sum_of_subset_of_nonneg hGB (fun n _ _ => hy0' n)
    _ = ∑ j ∈ Finset.range J, ∑ n ∈ thinBlock y s j, y n := Finset.sum_biUnion hdisj
    _ ≤ ∑ j ∈ Finset.range J, 2 * thinTau j :=
        Finset.sum_le_sum fun j _ => thinBlock_sum_le hy0' hdiv hlim hs0 hs1 j
    _ = 2 * ∑ j ∈ Finset.range J, thinTau j := by rw [Finset.mul_sum]
    _ ≤ 2 * 1 := by
        apply mul_le_mul_of_nonneg_left (sum_range_thinTau_le J) (by norm_num)
    _ = 2 := by norm_num

/-- **The `s`-powers of the thinned family still diverge.** -/
theorem not_summable_indicator_rpow_thinSet {y : ℕ → ℝ} (hy0 : ∀ n, 0 < y n)
    (hdiv : ¬ Summable y) (hlim : Tendsto y atTop (𝓝 0)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ¬ Summable (Set.indicator (thinSet y s) fun n => y n ^ s) := by
  classical
  have hy0' : ∀ n, 0 ≤ y n := fun n => (hy0 n).le
  intro hsum
  have hnonneg : ∀ n, 0 ≤ Set.indicator (thinSet y s) (fun n => y n ^ s) n := fun n =>
    Set.indicator_nonneg (fun m _ => (Real.rpow_pos_of_pos (hy0 m) s).le) n
  obtain ⟨J, hJ⟩ := exists_nat_gt (∑' n : ℕ, Set.indicator (thinSet y s) (fun n => y n ^ s) n)
  have hdisj : (↑(Finset.range J) : Set ℕ).PairwiseDisjoint (thinBlock y s) := by
    intro i _ j _ hij
    exact thinBlock_disjoint hy0' hdiv s hij
  set B : Finset ℕ := (Finset.range J).biUnion (thinBlock y s) with hB
  have hBsum : ∑ n ∈ B, Set.indicator (thinSet y s) (fun n => y n ^ s) n =
      ∑ j ∈ Finset.range J, ∑ n ∈ thinBlock y s j, y n ^ s := by
    rw [hB, Finset.sum_biUnion hdisj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun n hn => ?_
    exact Set.indicator_of_mem (thinBlock_subset_thinSet y s j hn) _
  have hge : (J : ℝ) ≤ ∑ n ∈ B, Set.indicator (thinSet y s) (fun n => y n ^ s) n := by
    rw [hBsum]
    calc (J : ℝ) = ∑ _j ∈ Finset.range J, (1 : ℝ) := by simp
      _ ≤ ∑ j ∈ Finset.range J, ∑ n ∈ thinBlock y s j, y n ^ s :=
          Finset.sum_le_sum fun j _ => thinBlock_rpow_sum_ge hy0 hdiv hlim hs0 hs1 j
  have hle : ∑ n ∈ B, Set.indicator (thinSet y s) (fun n => y n ^ s) n ≤
      ∑' n : ℕ, Set.indicator (thinSet y s) (fun n => y n ^ s) n :=
    hsum.sum_le_tsum _ (fun n _ => hnonneg n)
  linarith

/-- **Thinning a divergent series below a fractional power.**  A positive divergent series whose
terms tend to zero has a subfamily that converges while the sum of its `s`-th powers still
diverges, for every `0 < s < 1`. -/
theorem exists_thin_subset {y : ℕ → ℝ} (hy0 : ∀ n, 0 < y n) (hdiv : ¬ Summable y)
    (hlim : Tendsto y atTop (𝓝 0)) {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∃ T : Set ℕ, Summable (fun n : T => y n) ∧ ¬ Summable (fun n : T => y n ^ s) := by
  refine ⟨thinSet y s, ?_, ?_⟩
  · exact (summable_subtype_iff_indicator).mpr
      (summable_indicator_thinSet hy0 hdiv hlim hs0 hs1)
  · intro hcon
    exact not_summable_indicator_rpow_thinSet hy0 hdiv hlim hs0 hs1
      ((summable_subtype_iff_indicator).mp hcon)

end

end GaloisForLFunctions.HTGeometry
