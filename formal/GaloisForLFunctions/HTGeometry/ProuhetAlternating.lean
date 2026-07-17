import Mathlib

/-!
# Prouhet alternating annihilation

The signed sum of a polynomial over a cube of subset-sums vanishes whenever the polynomial
degree is smaller than the dimension: for any weights `w₀, …, w_{n−1}` and any polynomial `p`
with `natDegree p < n`,

`∑_{S ⊆ {0,…,n−1}} (−1)^{|S|} · p(∑_{i∈S} wᵢ) = 0`  (`prouhet_alternating_annihilation`).

Splitting on the top index turns the sum into the same sum for the one-step difference
`p(· + w_{n−1}) − p(·)`, whose degree has dropped; induction finishes.  With dyadic weights
`wᵢ = 2^i` the subsets enumerate an interval of integers and the sign is the Thue–Morse
parity, so this is the Prouhet–Tarry–Escott cancellation: a Prouhet class annihilates all
polynomial moments below its depth — the mechanism by which Prouhet clusters kill the
polynomial-scale part of coefficient identities, leaving only the phase relation.
-/

open Polynomial

namespace GaloisForLFunctions

/-- **Prouhet alternating annihilation**: a polynomial of degree less than the number of
weights is annihilated by the signed inclusion–exclusion over subset sums. -/
theorem prouhet_alternating_annihilation {n : ℕ} (w : ℕ → ℂ) (p : Polynomial ℂ)
    (hdeg : p.natDegree < n) :
    ∑ S ∈ (Finset.range n).powerset, (-1 : ℂ) ^ S.card * p.eval (∑ i ∈ S, w i) = 0 := by
  induction n generalizing p with
  | zero => exact absurd hdeg (Nat.not_lt_zero _)
  | succ n ih =>
    rw [Finset.range_add_one,
      Finset.sum_powerset_insert (Finset.notMem_range_self)
        (fun S => (-1 : ℂ) ^ S.card * p.eval (∑ i ∈ S, w i)),
      ← Finset.sum_add_distrib]
    set q : Polynomial ℂ := taylor (w n) p - p with hq
    have heval : ∀ x : ℂ, q.eval x = p.eval (x + w n) - p.eval x := by
      intro x
      rw [hq, eval_sub, taylor_apply, eval_comp, eval_add, eval_X, eval_C]
    have hstep : ∀ T ∈ (Finset.range n).powerset,
        (-1 : ℂ) ^ T.card * p.eval (∑ i ∈ T, w i)
          + (-1 : ℂ) ^ (insert n T).card * p.eval (∑ i ∈ insert n T, w i)
        = -((-1 : ℂ) ^ T.card * q.eval (∑ i ∈ T, w i)) := by
      intro T hT
      have hnT : n ∉ T := fun hmem =>
        Finset.notMem_range_self (Finset.mem_powerset.mp hT hmem)
      rw [Finset.card_insert_of_notMem hnT, Finset.sum_insert hnT, heval, pow_succ]
      ring_nf
    rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib]
    by_cases hq0 : q = 0
    · simp [hq0]
    · have hp0 : p ≠ 0 := by
        intro h0
        apply hq0
        rw [hq, h0, map_zero, sub_zero]
      have hpdeg : p.natDegree ≠ 0 → q.natDegree < p.natDegree := by
        intro hpd
        have htp0 : taylor (w n) p ≠ 0 := by
          intro h0
          apply hp0
          have h1 := congrArg (taylor (-w n)) h0
          rwa [taylor_taylor, neg_add_cancel, taylor_zero', LinearMap.id_apply, map_zero]
            at h1
        have hdegeq : (taylor (w n) p).degree = p.degree := by
          rw [degree_eq_natDegree htp0, degree_eq_natDegree hp0, natDegree_taylor]
        have hlc : (taylor (w n) p).leadingCoeff = p.leadingCoeff := by
          rw [taylor_apply, leadingCoeff_comp (by simp), leadingCoeff_X_add_C,
            one_pow, mul_one]
        have hdlt : q.degree < p.degree := by
          rw [hq]
          exact hdegeq ▸ degree_sub_lt hdegeq htp0 hlc
        exact natDegree_lt_natDegree hq0 hdlt
      rcases Nat.eq_zero_or_pos p.natDegree with hpd | hpd
      · exfalso
        apply hq0
        obtain ⟨c, rfl⟩ := natDegree_eq_zero.mp hpd
        rw [hq, taylor_C, sub_self]
      · have hqn : q.natDegree < n := by
          have := hpdeg (by omega)
          omega
        rw [ih q hqn, neg_zero]

/-! ### The Boolean logarithmic observable -/

noncomputable section

/-- The parity-graded trace of the diagonal affine logarithmic observable on an `n`-cube.  The
basis vectors are subsets `S ⊆ {0, ..., n-1}`, their parity is `(-1)^|S|`, and their observable
value is `B - ∑ i∈S, w i`. -/
def booleanLogObservableSupertrace (n : ℕ) (B : ℂ) (w : ℕ → ℂ) : ℂ :=
  ∑ S ∈ (Finset.range n).powerset,
    (-1 : ℂ) ^ S.card * (B - ∑ i ∈ S, w i)

/-- The empty Boolean cube retains the constant observable value. -/
@[simp]
theorem booleanLogObservableSupertrace_zero (B : ℂ) (w : ℕ → ℂ) :
    booleanLogObservableSupertrace 0 B w = B := by
  simp [booleanLogObservableSupertrace]

/-- A one-dimensional Boolean cube retains exactly its marked edge weight. -/
@[simp]
theorem booleanLogObservableSupertrace_one (B : ℂ) (w : ℕ → ℂ) :
    booleanLogObservableSupertrace 1 B w = w 0 := by
  rw [booleanLogObservableSupertrace, show Finset.range 1 = insert 0 ∅ by simp,
    Finset.sum_powerset_insert (by simp : 0 ∉ (∅ : Finset ℕ))
      (fun S => (-1 : ℂ) ^ S.card * (B - ∑ i ∈ S, w i))]
  simp

/-- Every affine logarithmic observable has zero supertrace on a Boolean cube of dimension at
least two.  This is the finite cancellation that removes every mixed-prime support. -/
theorem booleanLogObservableSupertrace_eq_zero {n : ℕ} (hn : 2 ≤ n)
    (B : ℂ) (w : ℕ → ℂ) :
    booleanLogObservableSupertrace n B w = 0 := by
  let p : Polynomial ℂ := C B - X
  have hpdeg : p.natDegree < n := by
    have hp : p = -(X - C B) := by
      simp only [p]
      ring
    rw [hp, natDegree_neg, natDegree_X_sub_C]
    omega
  have h := prouhet_alternating_annihilation w p hpdeg
  simpa only [booleanLogObservableSupertrace, p, eval_sub, eval_C, eval_X] using h

/-- **Boolean singleton-support law.**  The affine logarithmic supertrace is the empty-cube value
in dimension zero, the marked edge weight in dimension one, and zero in every higher interaction
grade.  Coupled with the finite Hodge-transgression identity, this is the combinatorial trace law
behind the von Mangoldt singleton-prime selector. -/
theorem booleanLogObservableSupertrace_eq (n : ℕ) (B : ℂ) (w : ℕ → ℂ) :
    booleanLogObservableSupertrace n B w =
      if n = 0 then B else if n = 1 then w 0 else 0 := by
  by_cases h0 : n = 0
  · subst n
    simp
  by_cases h1 : n = 1
  · subst n
    simp
  rw [if_neg h0, if_neg h1]
  exact booleanLogObservableSupertrace_eq_zero (by omega) B w

/-- The relative logarithmic observable obtained by subtracting the even empty-face projector.
Its graded trace is the local prime current minus one unit of polar density. -/
def booleanAugmentedLogObservableSupertrace (n : ℕ) (B : ℂ) (w : ℕ → ℂ) : ℂ :=
  booleanLogObservableSupertrace n B w - 1

/-- The augmented Boolean trace is `B - 1` on the empty cube, `w 0 - 1` on a singleton cube,
and `-1` on every higher interaction grade. -/
theorem booleanAugmentedLogObservableSupertrace_eq
    (n : ℕ) (B : ℂ) (w : ℕ → ℂ) :
    booleanAugmentedLogObservableSupertrace n B w =
      if n = 0 then B - 1 else if n = 1 then w 0 - 1 else -1 := by
  rw [booleanAugmentedLogObservableSupertrace,
    booleanLogObservableSupertrace_eq]
  by_cases h0 : n = 0
  · simp [h0]
  by_cases h1 : n = 1
  · simp [h0, h1]
  simp [h0, h1]

end

end GaloisForLFunctions

namespace GaloisForLFunctions

/-- Geometric sum of dyadic weights. -/
theorem sum_range_two_pow (m : ℕ) : ∑ i ∈ Finset.range m, (2 : ℕ) ^ i = 2 ^ m - 1 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hp : (2 : ℕ) ^ (m + 1) = 2 * 2 ^ m := by ring
    have h1 : 1 ≤ (2 : ℕ) ^ m := Nat.one_le_two_pow
    omega

theorem sum_two_pow_finset_eq (S : Finset ℕ) :
    ∑ i ∈ S, (2 : ℕ) ^ i = ((S.sort (· ≤ ·)).map fun i => 2 ^ i).sum := by
  have h := List.sum_toFinset (fun i => (2 : ℕ) ^ i)
    ((Finset.sortedLT_sort S).pairwise.nodup)
  rw [Finset.sort_toFinset] at h
  exact h

/-- The binary support of a subset sum of distinct dyadic powers is the subset itself. -/
theorem bitIndices_sum_two_pow_finset (S : Finset ℕ) :
    (∑ i ∈ S, (2 : ℕ) ^ i).bitIndices = S.sort (· ≤ ·) := by
  rw [sum_two_pow_finset_eq, Nat.bitIndices_sum_map_two_pow (Finset.sortedLT_sort S)]

/-- **Prouhet–Thue–Morse annihilation**: the Thue–Morse-signed sum of a polynomial over
`[0, 2^n)` vanishes when the degree is below `n` — the sign at `k` being the parity of the
binary digit sum of `k`. -/
theorem prouhet_thue_morse (n : ℕ) (p : Polynomial ℂ) (hdeg : p.natDegree < n) :
    ∑ k ∈ Finset.range (2 ^ n), (-1 : ℂ) ^ k.bitIndices.length * p.eval (k : ℂ) = 0 := by
  have hgen := prouhet_alternating_annihilation (fun i => (2 : ℂ) ^ i) p hdeg
  rw [Finset.sum_nbij' (fun S => ∑ i ∈ S, 2 ^ i) (fun k => k.bitIndices.toFinset)
    ?hi ?hj ?hji ?hij ?hval] at hgen
  · exact hgen
  case hi =>
    intro S hS
    rw [Finset.mem_range]
    have hle : ∑ i ∈ S, (2 : ℕ) ^ i ≤ ∑ i ∈ Finset.range n, (2 : ℕ) ^ i :=
      Finset.sum_le_sum_of_subset (Finset.mem_powerset.mp hS)
    rw [sum_range_two_pow] at hle
    have h1 : 1 ≤ (2 : ℕ) ^ n := Nat.one_le_two_pow
    show ∑ i ∈ S, (2 : ℕ) ^ i < 2 ^ n
    omega
  case hj =>
    intro k hk
    rw [Finset.mem_powerset]
    intro i hi
    rw [List.mem_toFinset] at hi
    have h2 := Nat.two_pow_le_of_mem_bitIndices hi
    rw [Finset.mem_range] at hk ⊢
    by_contra hni
    push Not at hni
    have h3 : (2 : ℕ) ^ n ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) hni
    omega
  case hji =>
    intro S _
    show (∑ i ∈ S, (2 : ℕ) ^ i).bitIndices.toFinset = S
    rw [bitIndices_sum_two_pow_finset, Finset.sort_toFinset]
  case hij =>
    intro k _
    show ∑ i ∈ k.bitIndices.toFinset, (2 : ℕ) ^ i = k
    rw [List.sum_toFinset _ Nat.bitIndices_nodup, Nat.sum_map_two_pow_bitIndices]
  case hval =>
    intro S _
    have hlen : (∑ i ∈ S, (2 : ℕ) ^ i).bitIndices.length = S.card := by
      rw [bitIndices_sum_two_pow_finset, Finset.length_sort]
    have hcast : ((∑ i ∈ S, (2 : ℕ) ^ i : ℕ) : ℂ) = ∑ i ∈ S, (2 : ℂ) ^ i := by
      push_cast
      rfl
    show (-1 : ℂ) ^ S.card * p.eval (∑ i ∈ S, (2 : ℂ) ^ i)
      = (-1 : ℂ) ^ (∑ i ∈ S, (2 : ℕ) ^ i).bitIndices.length
        * p.eval ((∑ i ∈ S, (2 : ℕ) ^ i : ℕ) : ℂ)
    rw [hlen, hcast]

end GaloisForLFunctions
