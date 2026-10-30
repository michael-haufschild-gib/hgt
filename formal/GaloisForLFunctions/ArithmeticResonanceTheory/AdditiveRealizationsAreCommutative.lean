import Mathlib

/-!
# Additive realizations of the primes are commutative

A Markov shift on an arbitrary alphabet `α` (finite or countable: the infinite prime alphabet is
allowed) with a **locally constant** roof `r : α → ℝ` — an edge-weighted graph — is
**prime-length** (`IsAdditivePrimeLength`) when every admissible periodic point `x` of least
period `L` has `e^{Σ_{i<L} r(xᵢ)}` prime.

A **first-return word** at a symbol `a` (`IsFirstReturn`) starts with `a`, contains no other `a`
and closes back to `a`. Its periodic point has least period its length. Two different first-return
words `u`, `v` at `a` concatenate to a periodic point `(uv)^∞` of least period `|u| + |v|`
(`minimalPeriod_concat`): the occurrences of `a` sit at the residues `0` and `|u|`, and a smaller
period would rotate `uv` onto itself, forcing `u = v`.

**Theorem** (`firstReturn_unique`). In an additive prime-length shift each symbol has at most one
first-return word. Unique factorization does the rest: the roof is additive, so the exponentiated
length of `(uv)^∞` is the product `p_u p_v` of two primes. Every symbol lies on a single cycle —
the realization is the **commutative** one, disjoint loops, with no mixing.

**Corollary** (`not_isAdditivePrimeLength_full`). The free realization (full shift on the prime
alphabet, roof `log p`) is not prime-length: `[2]` and `[2, 3]` are two first-return words at `2`.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticResonanceTheory

variable {α : Type*}

/-- The shift `(x_{i+m})_i` on sequences over any alphabet. -/
def shiftSeq (m : ℕ) (x : ℕ → α) : ℕ → α := fun i => x (i + m)

/-- Admissibility for a transition relation on the alphabet. -/
def IsAdm (adm : α → α → Prop) (x : ℕ → α) : Prop := ∀ i, adm (x i) (x (i + 1))

/-- **Additive prime-length shift**: every admissible periodic point of least period `L > 0` has
prime exponentiated length `e^{Σ_{i<L} r(xᵢ)}`. -/
def IsAdditivePrimeLength (adm : α → α → Prop) (r : α → ℝ) : Prop :=
  ∀ x : ℕ → α, IsAdm adm x → ∀ L, 0 < L → Function.minimalPeriod (shiftSeq 1) x = L →
    ∃ q : ℕ, q.Prime ∧ Real.exp (∑ i ∈ range L, r (x i)) = q

/-- The periodic point of the word `w 0, …, w (P − 1)`. -/
def perSeq (w : ℕ → α) (P : ℕ) : ℕ → α := fun i => w (i % P)

/-- The concatenation of the words `u` (length `L`) and `v`. -/
def catWord (u : ℕ → α) (L : ℕ) (v : ℕ → α) : ℕ → α := fun i => if i < L then u i else v (i - L)

/-- A **first-return word** at `a`: it starts with `a`, contains no other `a`, is admissible and
closes back to `a`. -/
structure IsFirstReturn (adm : α → α → Prop) (a : α) (u : ℕ → α) (L : ℕ) : Prop where
  pos : 0 < L
  start : u 0 = a
  avoid : ∀ i, 0 < i → i < L → u i ≠ a
  adm_in : ∀ i, i + 1 < L → adm (u i) (u (i + 1))
  adm_close : adm (u (L - 1)) a

theorem shiftSeq_one_iterate (m : ℕ) (x : ℕ → α) : (shiftSeq 1)^[m] x = shiftSeq m x := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', ih]
    funext i; simp [shiftSeq, Nat.add_assoc, Nat.add_comm 1 m]

/-- A periodic point of period `P > 0` all of whose periods are multiples of `P` has least
period `P`. -/
theorem minimalPeriod_perSeq {w : ℕ → α} {P : ℕ} (hP : 0 < P)
    (hdvd : ∀ m, 0 < m → (∀ i, perSeq w P (i + m) = perSeq w P i) → P ∣ m) :
    Function.minimalPeriod (shiftSeq 1) (perSeq w P) = P := by
  have hper : shiftSeq P (perSeq w P) = perSeq w P := by
    funext i; simp [shiftSeq, perSeq, Nat.add_mod_right]
  have hpt : Function.IsPeriodicPt (shiftSeq 1) P (perSeq w P) := by
    rw [Function.IsPeriodicPt, Function.IsFixedPt, shiftSeq_one_iterate, hper]
  have hpos := hpt.minimalPeriod_pos hP
  refine Nat.dvd_antisymm hpt.minimalPeriod_dvd (hdvd _ hpos fun i => ?_)
  have h := Function.isPeriodicPt_minimalPeriod (shiftSeq 1) (perSeq w P)
  rw [Function.IsPeriodicPt, Function.IsFixedPt, shiftSeq_one_iterate] at h
  exact congrFun h i

/-! ## One first-return word -/

section FirstReturn

variable {adm : α → α → Prop} {a : α} {u v : ℕ → α} {L L' : ℕ}

theorem succ_mod_eq {P : ℕ} (hP : 0 < P) (i : ℕ) :
    (i + 1) % P = if i % P + 1 < P then i % P + 1 else 0 := by
  have hlt := Nat.mod_lt i hP
  rw [Nat.add_mod]
  rcases Nat.lt_or_ge 1 P with h1 | h1
  · rw [Nat.mod_eq_of_lt h1]
    split_ifs with h
    · exact Nat.mod_eq_of_lt h
    · rw [show i % P + 1 = P by omega, Nat.mod_self]
  · have : P = 1 := by omega
    subst this; simp [Nat.mod_one]

theorem IsFirstReturn.isAdm (hu : IsFirstReturn adm a u L) : IsAdm adm (perSeq u L) := by
  intro i
  simp only [perSeq]
  rw [succ_mod_eq hu.pos]
  have hjlt := Nat.mod_lt i hu.pos
  split_ifs with h
  · exact hu.adm_in _ h
  · rw [show i % L = L - 1 by omega, hu.start]; exact hu.adm_close

/-- The periodic point of a first-return word has least period its length. -/
theorem IsFirstReturn.minimalPeriod (hu : IsFirstReturn adm a u L) :
    Function.minimalPeriod (shiftSeq 1) (perSeq u L) = L := by
  refine minimalPeriod_perSeq hu.pos fun m _ hm => ?_
  have h := hm 0
  simp only [perSeq, zero_add, Nat.zero_mod, hu.start] at h
  by_contra hndvd
  exact hu.avoid (m % L) (Nat.pos_of_ne_zero fun h0 => hndvd (Nat.dvd_of_mod_eq_zero h0))
    (Nat.mod_lt _ hu.pos) h

/-! ## Two first-return words -/

/-- Inside one period of `(uv)^∞` the symbol `a` occurs exactly at `0` and `|u|`. -/
theorem catWord_eq_iff (hu : IsFirstReturn adm a u L) (hv : IsFirstReturn adm a v L') {j : ℕ}
    (hj : j < L + L') : catWord u L v j = a ↔ j = 0 ∨ j = L := by
  simp only [catWord]
  split_ifs with h
  · constructor
    · intro hja; left; by_contra h0; exact hu.avoid j (Nat.pos_of_ne_zero h0) h hja
    · rintro (rfl | rfl)
      · exact hu.start
      · omega
  · constructor
    · intro hja; right; by_contra hL
      exact hv.avoid (j - L) (by omega) (by omega) hja
    · rintro (rfl | rfl)
      · have := hu.pos; omega
      · rw [Nat.sub_self]; exact hv.start

theorem isAdm_concat (hu : IsFirstReturn adm a u L) (hv : IsFirstReturn adm a v L') :
    IsAdm adm (perSeq (catWord u L v) (L + L')) := by
  have hL := hu.pos
  have hL' := hv.pos
  have hP : 0 < L + L' := by omega
  intro i
  simp only [perSeq]
  rw [succ_mod_eq hP]
  have hjlt := Nat.mod_lt i hP
  set j := i % (L + L') with hj
  by_cases hlast : j + 1 < L + L'
  · rw [if_pos hlast]
    by_cases h1 : j + 1 < L
    · simp only [catWord, if_pos h1, if_pos (show j < L by omega)]
      exact hu.adm_in j h1
    · by_cases h2 : j < L
      · simp only [catWord, if_pos h2, if_neg h1]
        rw [show j + 1 - L = 0 by omega, hv.start, show j = L - 1 by omega]
        exact hu.adm_close
      · simp only [catWord, if_neg h2, if_neg h1]
        rw [show j + 1 - L = j - L + 1 by omega]
        exact hv.adm_in (j - L) (by omega)
  · rw [if_neg hlast]
    simp only [catWord, if_neg (show ¬ j < L by omega), if_pos hL]
    rw [hu.start, show j - L = L' - 1 by omega]
    exact hv.adm_close

/-- **Concatenation is primitive.** For different first-return words `u`, `v` at the same symbol,
`(uv)^∞` has least period `|u| + |v|`. -/
theorem minimalPeriod_concat (hu : IsFirstReturn adm a u L) (hv : IsFirstReturn adm a v L')
    (hne : ¬ (L = L' ∧ ∀ i < L, u i = v i)) :
    Function.minimalPeriod (shiftSeq 1) (perSeq (catWord u L v) (L + L')) = L + L' := by
  have hL := hu.pos
  have hL' := hv.pos
  set P := L + L' with hPdef
  have hP : 0 < P := by omega
  refine minimalPeriod_perSeq hP fun m _ hm => ?_
  have hmod : ∀ i, (i + m) % P = (i + m % P) % P := fun i => by
    rw [Nat.add_mod i m P, Nat.add_mod i (m % P) P, Nat.mod_mod]
  -- the shift by `m` moves the `a` at residue `0` to an `a`
  have h0 := hm 0
  simp only [perSeq, zero_add, Nat.zero_mod] at h0
  have hc0 : catWord u L v 0 = a := (catWord_eq_iff hu hv hP).mpr (Or.inl rfl)
  rw [hc0, catWord_eq_iff hu hv (Nat.mod_lt _ hP)] at h0
  rcases h0 with h0 | h0
  · exact Nat.dvd_of_mod_eq_zero h0
  · exfalso
    -- the shift by `|u|` is a period; it moves the `a` at residue `|u|` to residue `2|u|`
    have hL2 := hm L
    simp only [perSeq] at hL2
    rw [hmod, h0, Nat.mod_eq_of_lt (show L < P by omega)] at hL2
    have hcL : catWord u L v L = a := (catWord_eq_iff hu hv (show L < P by omega)).mpr (Or.inr rfl)
    rw [hcL, catWord_eq_iff hu hv (Nat.mod_lt _ hP)] at hL2
    -- so `2|u| ≡ 0`, i.e. `|u| = |v|`
    have hLL : L = L' := by
      by_cases h2 : L + L < P
      · rw [Nat.mod_eq_of_lt h2] at hL2; omega
      · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)] at hL2; omega
    -- and the rotation by `|u|` identifies `v` with `u`
    refine hne ⟨hLL, fun i hi => ?_⟩
    have hi' := hm i
    simp only [perSeq] at hi'
    rw [hmod, h0, Nat.mod_eq_of_lt (show i + L < P by omega), Nat.mod_eq_of_lt (show i < P by omega)]
      at hi'
    simp only [catWord, if_neg (show ¬ i + L < L by omega), if_pos hi, Nat.add_sub_cancel] at hi'
    exact hi'.symm

/-- The exponentiated length of `(uv)^∞` over its period is the product of those of `u` and `v`. -/
theorem lengthSum_concat (r : α → ℝ) (u v : ℕ → α) (L L' : ℕ) :
    ∑ i ∈ range (L + L'), r (perSeq (catWord u L v) (L + L') i) =
      ∑ i ∈ range L, r (u i) + ∑ i ∈ range L', r (v i) := by
  rw [Finset.sum_range_add]
  congr 1
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    simp [perSeq, catWord, Nat.mod_eq_of_lt (show i < L + L' by omega), hi]
  · refine Finset.sum_congr rfl fun i hi => ?_
    have hi := Finset.mem_range.mp hi
    simp [perSeq, catWord, Nat.mod_eq_of_lt (show L + i < L + L' by omega)]

theorem lengthSum_perSeq (r : α → ℝ) (u : ℕ → α) {L : ℕ} :
    ∑ i ∈ range L, r (perSeq u L i) = ∑ i ∈ range L, r (u i) :=
  Finset.sum_congr rfl fun i hi => by
    simp [perSeq, Nat.mod_eq_of_lt (Finset.mem_range.mp hi)]

/-- **Additive rigidity.** In an additive prime-length shift, a symbol has at most one
first-return word. -/
theorem firstReturn_unique {r : α → ℝ} (hPL : IsAdditivePrimeLength adm r)
    (hu : IsFirstReturn adm a u L) (hv : IsFirstReturn adm a v L') :
    L = L' ∧ ∀ i < L, u i = v i := by
  by_contra hne
  obtain ⟨p, hp, hpu⟩ := hPL _ hu.isAdm L hu.pos hu.minimalPeriod
  obtain ⟨q, hq, hqv⟩ := hPL _ hv.isAdm L' hv.pos hv.minimalPeriod
  obtain ⟨t, ht, htuv⟩ := hPL _ (isAdm_concat hu hv) (L + L') (by have := hu.pos; omega)
    (minimalPeriod_concat hu hv hne)
  rw [lengthSum_perSeq] at hpu hqv
  rw [lengthSum_concat, Real.exp_add, hpu, hqv] at htuv
  have hpq : p * q = t := by exact_mod_cast htuv
  rw [← hpq, Nat.prime_mul_iff] at ht
  rcases ht with ⟨-, h⟩ | ⟨-, h⟩
  · exact hq.one_lt.ne' h
  · exact hp.one_lt.ne' h

end FirstReturn

/-- **The free realization is not prime-length.** On the full shift over the primes with roof
`log p`, the words `[2]` and `[2, 3]` are different first-return words at `2`. -/
theorem not_isAdditivePrimeLength_full :
    ¬ IsAdditivePrimeLength (fun _ _ : Nat.Primes => True) fun p => Real.log (p : ℕ) := by
  intro hPL
  set two : Nat.Primes := ⟨2, Nat.prime_two⟩
  set three : Nat.Primes := ⟨3, Nat.prime_three⟩
  have h23 : three ≠ two := by intro h; have := congrArg Subtype.val h; simp [two, three] at this
  have hu : IsFirstReturn (fun _ _ : Nat.Primes => True) two (fun _ => two) 1 :=
    ⟨one_pos, rfl, fun i h0 h1 => by omega, fun _ _ => trivial, trivial⟩
  have hv : IsFirstReturn (fun _ _ : Nat.Primes => True) two
      (fun i => if i = 0 then two else three) 2 :=
    ⟨two_pos, rfl, fun i h0 h1 => by simp only [if_neg (show i ≠ 0 by omega)]; exact h23,
      fun _ _ => trivial, trivial⟩
  have h := (firstReturn_unique hPL hu hv).1
  omega

end GaloisForLFunctions.ArithmeticResonanceTheory
