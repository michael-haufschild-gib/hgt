import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Interior residual is label overcrowding

Suzuki's compactified inverse phase carries its spectral mass on a strictly increasing family of
phase labels obeying the reflection pairing `u (1 - k) = -u k`.  Strict monotonicity forces the
labels to leave every symmetric window in order: if one label of large index sits inside a window,
so does every intervening central label.  Consequently the number of labels inside a window bounds
the index of every label inside it.

That is the exact mechanism behind the residual dichotomy.  A weight supported in a fixed physical
window can only be fed by a uniformly finite head of labels, so the escaped-label tail vanishes
identically on the interior; interior residual mass therefore requires the label count in some
fixed window to be unbounded — local divisor overcrowding, not physical escape.

Everything here is order combinatorics of the label family: no measure, no analytic input, and no
RH premise.
-/

namespace GaloisForLFunctions.RHTower

open Set

variable {u : ℤ → ℝ}

/-- The reflection pairing puts the origin strictly between the two central labels. -/
theorem label_zero_neg (hmono : StrictMono u) (hrefl : ∀ k : ℤ, u (1 - k) = -u k) :
    u 0 < 0 ∧ 0 < u 1 := by
  have h1 : u 1 = -u 0 := by simpa using hrefl 0
  have hlt : u 0 < u 1 := hmono (by norm_num)
  rw [h1] at hlt
  constructor <;> linarith

/-- **Order transfer.**  If a positive label index lands inside a symmetric window, then so does
every intervening central index. -/
theorem abs_label_le_of_between (hmono : StrictMono u) (hrefl : ∀ k : ℤ, u (1 - k) = -u k)
    {r : ℝ} {k : ℤ} (hle : |u k| ≤ r) {j : ℤ} (hj1 : 1 ≤ j) (hjk : j ≤ k) :
    |u j| ≤ r := by
  obtain ⟨_, hpos⟩ := label_zero_neg hmono hrefl
  have hmono1 : u 1 ≤ u j := hmono.monotone hj1
  have hmonojk : u j ≤ u k := hmono.monotone hjk
  have hupper : u k ≤ r := le_trans (le_abs_self _) hle
  have hjpos : 0 < u j := lt_of_lt_of_le hpos hmono1
  rw [abs_of_pos hjpos]
  linarith

/-- The window label set, as a set of indices. -/
def labelWindow (u : ℤ → ℝ) (r : ℝ) : Set ℤ := {k : ℤ | |u k| ≤ r}

/-- **Positive indices in a window are bounded by its label count.** -/
theorem le_card_labelWindow (hmono : StrictMono u) (hrefl : ∀ k : ℤ, u (1 - k) = -u k)
    {r : ℝ} (hfin : (labelWindow u r).Finite) {k : ℤ} (hk : 0 < k) (hle : |u k| ≤ r) :
    k ≤ (hfin.toFinset.card : ℤ) := by
  classical
  have hsub : Finset.Icc (1 : ℤ) k ⊆ hfin.toFinset := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    rw [Set.Finite.mem_toFinset]
    exact abs_label_le_of_between hmono hrefl hle hj.1 hj.2
  have hcard : (Finset.Icc (1 : ℤ) k).card ≤ hfin.toFinset.card := Finset.card_le_card hsub
  rw [Int.card_Icc] at hcard
  have hk' : (k + 1 - 1).toNat = k.toNat := by ring_nf
  rw [hk'] at hcard
  have : (k.toNat : ℤ) ≤ (hfin.toFinset.card : ℤ) := by exact_mod_cast hcard
  rwa [Int.toNat_of_nonneg (le_of_lt hk)] at this

/-- **Uniform label-head bound.**  Every index whose label lies in a symmetric window has absolute
value bounded by the window's label count. -/
theorem abs_le_card_labelWindow (hmono : StrictMono u) (hrefl : ∀ k : ℤ, u (1 - k) = -u k)
    {r : ℝ} (hfin : (labelWindow u r).Finite) {k : ℤ} (hle : |u k| ≤ r) :
    |k| ≤ (hfin.toFinset.card : ℤ) := by
  classical
  rcases lt_or_ge 0 k with hk | hk
  · have hbound := le_card_labelWindow hmono hrefl hfin hk hle
    rw [abs_of_pos hk]
    exact hbound
  · have hk' : (0 : ℤ) < 1 - k := by omega
    have hrefl' : |u (1 - k)| ≤ r := by
      rw [hrefl k, abs_neg]
      exact hle
    have hbound := le_card_labelWindow hmono hrefl hfin hk' hrefl'
    have hnonneg : (0 : ℤ) ≤ (hfin.toFinset.card : ℤ) := Int.natCast_nonneg _
    rw [abs_of_nonpos hk]
    omega

/-- **Theorem B, tail form.**  A weight supported inside a symmetric window is fed only by the
uniformly finite label head: every tail index beyond the window's label count contributes zero.
Hence the escaped-label tail — and with it the interior residual — vanishes identically. -/
theorem escapedTail_eq_zero (hmono : StrictMono u) (hrefl : ∀ k : ℤ, u (1 - k) = -u k)
    {r : ℝ} (hfin : (labelWindow u r).Finite) {f : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0) {k : ℤ} (hk : (hfin.toFinset.card : ℤ) < |k|) :
    f (u k) = 0 := by
  refine hsupp (u k) ?_
  by_contra hcon
  push Not at hcon
  exact absurd (abs_le_card_labelWindow hmono hrefl hfin hcon) (not_le.mpr hk)

/-- **Uniform version over a family.**  If the window label counts of a whole family are bounded by
one integer, the vanishing threshold is uniform in the family. -/
theorem escapedTail_eq_zero_uniform {ι : Type*} {U : ι → ℤ → ℝ}
    (hmono : ∀ i, StrictMono (U i)) (hrefl : ∀ i, ∀ k : ℤ, U i (1 - k) = -U i k)
    {r : ℝ} (hfin : ∀ i, (labelWindow (U i) r).Finite) {N : ℤ}
    (hbound : ∀ i, ((hfin i).toFinset.card : ℤ) ≤ N) {f : ℝ → ℝ}
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0) (i : ι) {k : ℤ} (hk : N < |k|) :
    f (U i k) = 0 :=
  escapedTail_eq_zero (hmono i) (hrefl i) (hfin i) hsupp (lt_of_le_of_lt (hbound i) hk)

/-! ## Theorem A: the residual is the escaped-label tail -/

open Filter Topology

/-- The finite label head of a discrete spectral sum. -/
noncomputable def labelHead (p w : ℤ → ℝ) (K : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), p k * w k

/-- The head is monotone in the cutoff for nonnegative data. -/
theorem labelHead_mono {p w : ℤ → ℝ} (hp : ∀ k, 0 ≤ p k) (hw : ∀ k, 0 ≤ w k) :
    Monotone (labelHead p w) := by
  intro K L hKL
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun k _ _ => mul_nonneg (hp k) (hw k))
  intro k hk
  rw [Finset.mem_Icc] at hk ⊢
  have : (K : ℤ) ≤ (L : ℤ) := Int.ofNat_le.mpr hKL
  omega

/-- **`(5)`.**  For a fixed cutoff the escaped-label tail converges: the total converges by weak
convergence and the head converges coordinatewise, because it is a finite sum. -/
theorem tendsto_escapedTail {ι : Type*} {l : Filter ι}
    {P U : ι → ℤ → ℝ} {p u : ℤ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {S : ι → ℝ} {Sinf : ℝ}
    (hS : Tendsto S l (𝓝 Sinf))
    (hP : ∀ k, Tendsto (fun i => P i k) l (𝓝 (p k)))
    (hU : ∀ k, Tendsto (fun i => U i k) l (𝓝 (u k)))
    (K : ℕ) :
    Tendsto (fun i => S i - labelHead (P i) (fun k => f (U i k)) K) l
      (𝓝 (Sinf - labelHead p (fun k => f (u k)) K)) := by
  refine hS.sub ?_
  refine tendsto_finsetSum _ fun k _ => ?_
  exact (hP k).mul ((hf.continuousAt.tendsto).comp (hU k))

/-- **`(4)`.**  Letting the cutoff grow, the escaped-label tails converge to the residual, the
difference between the total limit and the labelled limit. -/
theorem tendsto_escapedTail_atTop {p u : ℤ → ℝ} {f : ℝ → ℝ} {Sinf L : ℝ}
    (hsum : Tendsto (fun K : ℕ => labelHead p (fun k => f (u k)) K) atTop (𝓝 L)) :
    Tendsto (fun K : ℕ => Sinf - labelHead p (fun k => f (u k)) K) atTop (𝓝 (Sinf - L)) :=
  (tendsto_const_nhds (x := Sinf)).sub hsum

/-- A summable family whose weight vanishes beyond a cutoff is its own label head. -/
theorem hasSum_eq_labelHead {P w : ℤ → ℝ} {S : ℝ} {N K : ℕ}
    (hNK : N ≤ K) (hsupp : ∀ k : ℤ, (N : ℤ) < |k| → w k = 0)
    (hS : HasSum (fun k => P k * w k) S) :
    S = labelHead P w K := by
  classical
  have hzero : ∀ k ∉ Finset.Icc (-(K : ℤ)) (K : ℤ), P k * w k = 0 := by
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hNK' : (N : ℤ) ≤ (K : ℤ) := Int.ofNat_le.mpr hNK
    have habs : (N : ℤ) < |k| := by
      rcases abs_cases k with ⟨heq, _⟩ | ⟨heq, _⟩ <;> omega
    rw [hsupp k habs, mul_zero]
  have hfs : HasSum (fun k => P k * w k)
      (∑ k ∈ Finset.Icc (-(K : ℤ)) (K : ℤ), P k * w k) :=
    hasSum_sum_of_ne_finset_zero hzero
  rw [hS.unique hfs, labelHead]

/-- **Theorem B, closed form.**  If the label counts of the whole family are bounded in one window
and the weight is supported there, then the residual vanishes: the total already equals the head
at every cutoff beyond the bound. -/
theorem residual_eq_zero_of_uniform_count {ι : Type*} {l : Filter ι} [l.NeBot]
    {U : ι → ℤ → ℝ} {P : ι → ℤ → ℝ} {p u : ℤ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {S : ι → ℝ} {Sinf L : ℝ}
    (hmono : ∀ i, StrictMono (U i)) (hrefl : ∀ i, ∀ k : ℤ, U i (1 - k) = -U i k)
    {r : ℝ} (hfin : ∀ i, (labelWindow (U i) r).Finite) {N : ℕ}
    (hbound : ∀ i, ((hfin i).toFinset.card : ℤ) ≤ (N : ℤ))
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0)
    (hSsum : ∀ i, HasSum (fun k => P i k * f (U i k)) (S i))
    (hS : Tendsto S l (𝓝 Sinf))
    (hP : ∀ k, Tendsto (fun i => P i k) l (𝓝 (p k)))
    (hU : ∀ k, Tendsto (fun i => U i k) l (𝓝 (u k)))
    (hL : Tendsto (fun K : ℕ => labelHead p (fun k => f (u k)) K) atTop (𝓝 L)) :
    Sinf = L := by
  have hstep : ∀ K : ℕ, N ≤ K → Sinf - labelHead p (fun k => f (u k)) K = 0 := by
    intro K hNK
    have hzero : ∀ i, S i - labelHead (P i) (fun k => f (U i k)) K = 0 := by
      intro i
      have := hasSum_eq_labelHead hNK
        (fun k hk => escapedTail_eq_zero_uniform hmono hrefl hfin hbound hsupp i hk)
        (hSsum i)
      rw [← this, sub_self]
    have hlim := tendsto_escapedTail hf hS hP hU K
    have hconst : Tendsto (fun i => S i - labelHead (P i) (fun k => f (U i k)) K) l (𝓝 0) := by
      refine tendsto_const_nhds.congr fun i => (hzero i).symm
    exact tendsto_nhds_unique hconst hlim ▸ rfl
  have hfinal : Tendsto (fun K : ℕ => Sinf - labelHead p (fun k => f (u k)) K) atTop
      (𝓝 (Sinf - L)) := tendsto_escapedTail_atTop hL
  have hzero : Tendsto (fun K : ℕ => Sinf - labelHead p (fun k => f (u k)) K) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop N] with K hK
    exact (hstep K hK).symm
  have := tendsto_nhds_unique hzero hfinal
  linarith

/-! ## Theorem C: the glue around Rouché's count stability -/

/-- **Zero-free gauges do not move the Clark points.**  The zero set of a gauged carrier is the
zero set of the carrier. -/
theorem setOf_gauge_mul_eq_zero {α : Type*} [MulZeroClass α] [NoZeroDivisors α]
    {g W : ℂ → α} (hg : ∀ z, g z ≠ 0) :
    {z : ℂ | g z * W z = 0} = {z : ℂ | W z = 0} := by
  ext z
  simp only [Set.mem_setOf_eq, mul_eq_zero]
  constructor
  · rintro (h | h)
    · exact absurd h (hg z)
    · exact h
  · intro h
    exact Or.inr h

/-- **An eventually bounded window count is uniformly bounded.**  Rouché's theorem delivers the
count stability only for late members of an aperture family; finitely many early members are
absorbed into the bound. -/
theorem exists_uniform_bound_of_eventually {N : ℕ → ℕ} {M : ℕ}
    (h : ∀ᶠ n in atTop, N n ≤ M) : ∃ M', ∀ n, N n ≤ M' := by
  classical
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp h
  refine ⟨max M ((Finset.range n₀).sup N), fun n => ?_⟩
  rcases lt_or_ge n n₀ with hn | hn
  · exact le_trans (Finset.le_sup (Finset.mem_range.mpr hn)) (le_max_right _ _)
  · exact le_trans (hn₀ n hn) (le_max_left _ _)

/-- **Theorem C, closed form.**  Eventual count stability in one window upgrades to the uniform
hypothesis `(7)`, and therefore — through the order engine and the tail bookkeeping — to the
vanishing of the interior residual. -/
theorem residual_eq_zero_of_eventually_count
    {U : ℕ → ℤ → ℝ} {P : ℕ → ℤ → ℝ} {p u : ℤ → ℝ} {f : ℝ → ℝ} (hf : Continuous f)
    {S : ℕ → ℝ} {Sinf L : ℝ}
    (hmono : ∀ i, StrictMono (U i)) (hrefl : ∀ i, ∀ k : ℤ, U i (1 - k) = -U i k)
    {r : ℝ} (hfin : ∀ i, (labelWindow (U i) r).Finite) {M : ℕ}
    (hcount : ∀ᶠ i in atTop, (hfin i).toFinset.card ≤ M)
    (hsupp : ∀ x : ℝ, r < |x| → f x = 0)
    (hSsum : ∀ i, HasSum (fun k => P i k * f (U i k)) (S i))
    (hS : Tendsto S atTop (𝓝 Sinf))
    (hP : ∀ k, Tendsto (fun i => P i k) atTop (𝓝 (p k)))
    (hU : ∀ k, Tendsto (fun i => U i k) atTop (𝓝 (u k)))
    (hL : Tendsto (fun K : ℕ => labelHead p (fun k => f (u k)) K) atTop (𝓝 L)) :
    Sinf = L := by
  obtain ⟨M', hM'⟩ := exists_uniform_bound_of_eventually hcount
  exact residual_eq_zero_of_uniform_count hf hmono hrefl hfin
    (fun i => by exact_mod_cast hM' i) hsupp hSsum hS hP hU hL

end GaloisForLFunctions.RHTower
