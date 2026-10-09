import GaloisForLFunctions.RHTower.ComplexFugacityLeeYangChain

/-!
# Lee–Yang trees with complex fugacities

`ComplexFugacityLeeYangChain` shows that chains need no ferromagnetic positivity.  The same holds
on every finite rooted tree.  Nodes are `1, …, N` with `parent n < n` for `n ≥ 2` (node `1` is the
root); every node `n` carries a field `u n` and the edge to its parent a complex fugacity `α n`.
The pair `(A_n, B_n)` of subtree weights with spin `+`, resp. `−`, at `n` satisfies

  `A_n = ∏_{m child of n} (A_m + α_m B_m)`,  `B_n = u_n ∏_{m child of n} (conj α_m · A_m + B_m)`.

* `treePair_inside`: if every field lies in the open unit disc and every fugacity in the closed
  disc, then `‖B_n‖ < ‖A_n‖` at every node (the chain identity of `normSq_conj_mul_add_sub`,
  multiplied over the children).
* `treePair_reciprocal`: global spin flip exchanges `A` and `B` and conjugates the fugacities.
* `treeZ_ne_zero_of_im_ne_zero`: with exponential fields `u_n = e^{−i λ_n z}`, `λ_n > 0`, every
  zero of the partition function `A_1 + B_1` is real.

Example: the divisibility tree `parent n = n / P(n)` (largest prime factor), with harmonic fields
`λ_n = 1/(Kn)` and prime-step fugacities, is real-rooted for all complex fugacities in the disc.
-/

open Complex Finset

namespace RHTower.LeeYangChain

noncomputable section

/-- A finite rooted tree on the nodes `1, …, N`, rooted at `1`. -/
structure RootedTree where
  N : ℕ
  parent : ℕ → ℕ
  parent_lt : ∀ n, 2 ≤ n → parent n < n
  parent_pos : ∀ n, 2 ≤ n → 1 ≤ parent n

/-- The children of `n` among the nodes `n+1, …, N`. -/
def RootedTree.children (T : RootedTree) (n : ℕ) : Finset ℕ :=
  (Ioc n T.N).filter fun m => 2 ≤ m ∧ T.parent m = n

theorem RootedTree.lt_of_mem_children {T : RootedTree} {n m : ℕ} (h : m ∈ T.children n) :
    n < m ∧ m ≤ T.N := by
  have h1 := (mem_filter.mp h).1
  exact ⟨(mem_Ioc.mp h1).1, (mem_Ioc.mp h1).2⟩

/-- Subtree weights `(A_n, B_n)`, defined from the leaves down. -/
def treePair (T : RootedTree) (α u : ℕ → ℂ) (n : ℕ) : ℂ × ℂ :=
  if n ≤ T.N then
    (∏ m ∈ (T.children n).attach,
        ((treePair T α u m.1).1 + α m.1 * (treePair T α u m.1).2),
      u n * ∏ m ∈ (T.children n).attach,
        ((starRingEnd ℂ) (α m.1) * (treePair T α u m.1).1 + (treePair T α u m.1).2))
  else (1, u n)
termination_by T.N + 1 - n
decreasing_by
  all_goals
    have h := RootedTree.lt_of_mem_children m.2
    omega

theorem treePair_eq (T : RootedTree) (α u : ℕ → ℂ) {n : ℕ} (hn : n ≤ T.N) :
    treePair T α u n =
      (∏ m ∈ T.children n, ((treePair T α u m).1 + α m * (treePair T α u m).2),
        u n * ∏ m ∈ T.children n,
          ((starRingEnd ℂ) (α m) * (treePair T α u m).1 + (treePair T α u m).2)) := by
  rw [treePair, if_pos hn]
  congr 1
  · exact prod_attach (T.children n)
      (fun m => (treePair T α u m).1 + α m * (treePair T α u m).2)
  · congr 1
    exact prod_attach (T.children n)
      (fun m => (starRingEnd ℂ) (α m) * (treePair T α u m).1 + (treePair T α u m).2)

/-- The tree partition function. -/
def treeZ (T : RootedTree) (α u : ℕ → ℂ) : ℂ := (treePair T α u 1).1 + (treePair T α u 1).2

/-- **Lee–Yang inside the disc for trees.** -/
theorem treePair_inside (T : RootedTree) {α u : ℕ → ℂ} (hα : ∀ k, ‖α k‖ ≤ 1)
    (hu : ∀ k, ‖u k‖ < 1) :
    ∀ k n, T.N + 1 - n = k → n ≤ T.N →
      (treePair T α u n).1 ≠ 0 ∧ ‖(treePair T α u n).2‖ < ‖(treePair T α u n).1‖ := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hn
    rw [treePair_eq T α u hn]
    have hchild : ∀ m ∈ T.children n,
        (treePair T α u m).1 ≠ 0 ∧ ‖(treePair T α u m).2‖ < ‖(treePair T α u m).1‖ := by
      intro m hm
      have h := RootedTree.lt_of_mem_children hm
      exact ih (T.N + 1 - m) (by omega) m rfl h.2
    have hfac : ∀ m ∈ T.children n,
        (treePair T α u m).1 + α m * (treePair T α u m).2 ≠ 0 ∧
        ‖(starRingEnd ℂ) (α m) * (treePair T α u m).1 + (treePair T α u m).2‖ ≤
          ‖(treePair T α u m).1 + α m * (treePair T α u m).2‖ := by
      intro m hm
      obtain ⟨hA, hB⟩ := hchild m hm
      set A := (treePair T α u m).1
      set B := (treePair T α u m).2
      have hαB : ‖α m * B‖ < ‖A‖ := by
        rw [norm_mul]
        calc ‖α m‖ * ‖B‖ ≤ 1 * ‖B‖ := mul_le_mul_of_nonneg_right (hα m) (norm_nonneg _)
          _ < ‖A‖ := by rw [one_mul]; exact hB
      have hA' : A + α m * B ≠ 0 := by
        intro h
        have : A = -(α m * B) := by linear_combination h
        rw [this, norm_neg] at hαB
        exact lt_irrefl _ hαB
      refine ⟨hA', ?_⟩
      have hsq : Complex.normSq ((starRingEnd ℂ) (α m) * A + B) ≤
          Complex.normSq (A + α m * B) := by
        have h := normSq_conj_mul_add_sub (α m) A B
        have hAB : Complex.normSq B < Complex.normSq A := by
          rw [← Complex.sq_norm, ← Complex.sq_norm]
          exact pow_lt_pow_left₀ hB (norm_nonneg _) two_ne_zero
        have hα2 : Complex.normSq (α m) - 1 ≤ 0 := by
          rw [← Complex.sq_norm]
          nlinarith [hα m, norm_nonneg (α m)]
        nlinarith
      rw [← Complex.sq_norm, ← Complex.sq_norm] at hsq
      exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp hsq
    refine ⟨prod_ne_zero_iff.mpr fun m hm => (hfac m hm).1, ?_⟩
    rw [norm_mul, norm_prod, norm_prod]
    have hprod : ∏ m ∈ T.children n,
        ‖(starRingEnd ℂ) (α m) * (treePair T α u m).1 + (treePair T α u m).2‖ ≤
        ∏ m ∈ T.children n, ‖(treePair T α u m).1 + α m * (treePair T α u m).2‖ :=
      prod_le_prod (fun m _ => norm_nonneg _) fun m hm => (hfac m hm).2
    have hpos : 0 < ∏ m ∈ T.children n, ‖(treePair T α u m).1 + α m * (treePair T α u m).2‖ :=
      prod_pos fun m hm => norm_pos_iff.mpr (hfac m hm).1
    calc ‖u n‖ * ∏ m ∈ T.children n,
          ‖(starRingEnd ℂ) (α m) * (treePair T α u m).1 + (treePair T α u m).2‖
        ≤ ‖u n‖ * ∏ m ∈ T.children n, ‖(treePair T α u m).1 + α m * (treePair T α u m).2‖ :=
          mul_le_mul_of_nonneg_left hprod (norm_nonneg _)
      _ < 1 * ∏ m ∈ T.children n, ‖(treePair T α u m).1 + α m * (treePair T α u m).2‖ :=
          mul_lt_mul_of_pos_right (hu n) hpos
      _ = _ := one_mul _

theorem treeZ_ne_zero_of_norm_lt_one (T : RootedTree) (hN : 1 ≤ T.N) {α u : ℕ → ℂ}
    (hα : ∀ k, ‖α k‖ ≤ 1) (hu : ∀ k, ‖u k‖ < 1) : treeZ T α u ≠ 0 := by
  obtain ⟨_, hB⟩ := treePair_inside T hα hu (T.N + 1 - 1) 1 rfl hN
  intro h
  rw [treeZ] at h
  have : (treePair T α u 1).2 = -(treePair T α u 1).1 := by linear_combination h
  rw [this, norm_neg] at hB
  exact lt_irrefl _ hB

/-- The product of the fields over the subtree of `n`. -/
def subtreeProd (T : RootedTree) (u : ℕ → ℂ) (n : ℕ) : ℂ :=
  if n ≤ T.N then u n * ∏ m ∈ (T.children n).attach, subtreeProd T u m.1 else u n
termination_by T.N + 1 - n
decreasing_by
  have h := RootedTree.lt_of_mem_children m.2
  omega

theorem subtreeProd_eq (T : RootedTree) (u : ℕ → ℂ) {n : ℕ} (hn : n ≤ T.N) :
    subtreeProd T u n = u n * ∏ m ∈ T.children n, subtreeProd T u m := by
  rw [subtreeProd, if_pos hn]
  congr 1
  exact prod_attach (T.children n) (fun m => subtreeProd T u m)

/-- **Global spin flip on trees.** -/
theorem treePair_reciprocal (T : RootedTree) (α : ℕ → ℂ) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) :
    ∀ k n, T.N + 1 - n = k → n ≤ T.N →
      (treePair T α u n).1 = subtreeProd T u n *
          (treePair T (fun i => (starRingEnd ℂ) (α i)) (fun i => (u i)⁻¹) n).2 ∧
        (treePair T α u n).2 = subtreeProd T u n *
          (treePair T (fun i => (starRingEnd ℂ) (α i)) (fun i => (u i)⁻¹) n).1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk hn
    set β : ℕ → ℂ := fun i => (starRingEnd ℂ) (α i)
    set v : ℕ → ℂ := fun i => (u i)⁻¹
    have hc : ∀ m ∈ T.children n,
        (treePair T α u m).1 = subtreeProd T u m * (treePair T β v m).2 ∧
          (treePair T α u m).2 = subtreeProd T u m * (treePair T β v m).1 := by
      intro m hm
      have h := RootedTree.lt_of_mem_children hm
      exact ih (T.N + 1 - m) (by omega) m rfl h.2
    rw [treePair_eq T α u hn, treePair_eq T β v hn, subtreeProd_eq T u hn]
    have hun := hu n
    constructor
    · simp only
      rw [prod_congr rfl fun m hm => by rw [(hc m hm).1, (hc m hm).2]]
      have : ∀ m ∈ T.children n,
          subtreeProd T u m * (treePair T β v m).2 + α m * (subtreeProd T u m *
            (treePair T β v m).1) =
          subtreeProd T u m * ((starRingEnd ℂ) (β m) * (treePair T β v m).1 +
            (treePair T β v m).2) := by
        intro m _
        simp only [β, Complex.conj_conj]
        ring
      rw [prod_congr rfl this, prod_mul_distrib]
      simp only [v]
      field_simp
    · simp only
      rw [prod_congr rfl fun m hm => by rw [(hc m hm).1, (hc m hm).2]]
      have : ∀ m ∈ T.children n,
          (starRingEnd ℂ) (α m) * (subtreeProd T u m * (treePair T β v m).2) +
            subtreeProd T u m * (treePair T β v m).1 =
          subtreeProd T u m * ((treePair T β v m).1 + β m * (treePair T β v m).2) := by
        intro m _
        simp only [β]
        ring
      rw [prod_congr rfl this, prod_mul_distrib]
      ring

theorem subtreeProd_ne_zero (T : RootedTree) {u : ℕ → ℂ} (hu : ∀ k, u k ≠ 0) :
    ∀ k n, T.N + 1 - n = k → subtreeProd T u n ≠ 0 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro n hk
    by_cases hn : n ≤ T.N
    · rw [subtreeProd_eq T u hn]
      refine mul_ne_zero (hu n) (prod_ne_zero_iff.mpr fun m hm => ?_)
      have h := RootedTree.lt_of_mem_children hm
      exact ih (T.N + 1 - m) (by omega) m rfl
    · rw [subtreeProd, if_neg hn]; exact hu n

/-- **Real zeros on trees without positivity.** With exponential fields of positive frequencies,
every zero of the tree partition function is real, for every family of complex fugacities in the
closed unit disc. -/
theorem treeZ_ne_zero_of_im_ne_zero (T : RootedTree) (hN : 1 ≤ T.N) {α : ℕ → ℂ}
    {freqs : ℕ → ℝ} (hα : ∀ k, ‖α k‖ ≤ 1) (hfreq : ∀ k, 0 < freqs k) {z : ℂ} (hz : z.im ≠ 0) :
    treeZ T α (chainExpField freqs z) ≠ 0 := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · refine treeZ_ne_zero_of_norm_lt_one T hN hα fun k => ?_
    rw [norm_chainExpField, Real.exp_lt_one_iff]
    exact mul_neg_of_pos_of_neg (hfreq k) hneg
  · have hne : ∀ k, chainExpField freqs z k ≠ 0 := fun k => Complex.exp_ne_zero _
    obtain ⟨h1, h2⟩ := treePair_reciprocal T α hne (T.N + 1 - 1) 1 rfl hN
    rw [treeZ, h1, h2, ← mul_add]
    refine mul_ne_zero (subtreeProd_ne_zero T hne _ 1 rfl) ?_
    rw [add_comm]
    refine treeZ_ne_zero_of_norm_lt_one T hN (fun k => by rw [Complex.norm_conj]; exact hα k)
      fun k => ?_
    rw [norm_inv, norm_chainExpField, inv_lt_one₀ (Real.exp_pos _), Real.one_lt_exp_iff]
    exact mul_pos (hfreq k) hpos


/-! ## The divisibility tree -/

/-- The largest prime factor of `n ≥ 2` (and `1` otherwise). -/
def largestPrimeFactor (n : ℕ) : ℕ :=
  if h : 1 < n then n.primeFactors.max' (Nat.nonempty_primeFactors.mpr h) else 1

theorem largestPrimeFactor_prime {n : ℕ} (h : 1 < n) : (largestPrimeFactor n).Prime := by
  rw [largestPrimeFactor, dif_pos h]
  exact Nat.prime_of_mem_primeFactors (Finset.max'_mem _ _)

theorem largestPrimeFactor_dvd {n : ℕ} (h : 1 < n) : largestPrimeFactor n ∣ n := by
  rw [largestPrimeFactor, dif_pos h]
  exact Nat.dvd_of_mem_primeFactors (Finset.max'_mem _ _)

/-- The divisibility tree on `1, …, N`: the parent of `n` is `n / P(n)`. -/
def divisibilityTree (N : ℕ) : RootedTree where
  N := N
  parent n := n / largestPrimeFactor n
  parent_lt n hn := Nat.div_lt_self (by omega) (largestPrimeFactor_prime (by omega)).one_lt
  parent_pos n hn := by
    have hP := largestPrimeFactor_prime (n := n) (by omega)
    have hle : largestPrimeFactor n ≤ n :=
      Nat.le_of_dvd (by omega) (largestPrimeFactor_dvd (by omega))
    exact Nat.div_pos hle hP.pos

/-- **The divisibility tree is real-rooted for every complex prime-step coupling.** -/
theorem divisibilityTreeZ_ne_zero_of_im_ne_zero {N : ℕ} (hN : 1 ≤ N) {α : ℕ → ℂ}
    {freqs : ℕ → ℝ} (hα : ∀ k, ‖α k‖ ≤ 1) (hfreq : ∀ k, 0 < freqs k) {z : ℂ} (hz : z.im ≠ 0) :
    treeZ (divisibilityTree N) α (chainExpField freqs z) ≠ 0 :=
  treeZ_ne_zero_of_im_ne_zero (divisibilityTree N) hN hα hfreq hz

end

end RHTower.LeeYangChain
