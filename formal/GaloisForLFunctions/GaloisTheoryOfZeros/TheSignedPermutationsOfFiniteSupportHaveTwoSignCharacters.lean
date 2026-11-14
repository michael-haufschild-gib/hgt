import GaloisForLFunctions.GaloisTheoryOfZeros.APermutationOfFiniteSupportHasAMultiplicativeSign

/-!
# The signed permutations of finite support have two sign characters

Let `n` be an involution without fixed points; its orbits `{x, n x}` are the *pairs*. A *signed*
permutation commutes with `n`. On the signed permutations of finite support:

* `finSign w`: the sign of `w` as a permutation of the points;
* `pairSign n hn w`: the sign of the permutation that `w` induces on the pairs;
* `signedCharacter n hn ε w = pairSign w · finSign w ^ ε`, for `ε ∈ {0, 1}`.

Both signs are multiplicative. The flip of one pair has `finSign = −1` and `pairSign = 1`; the
exchange of two pairs has `finSign = 1` and `pairSign = −1`.

* `signedKernel n hn ε`: the signed permutations of finite support with
  `signedCharacter = 1`, a subgroup. Of two signed permutations of finite support one lies in
  it or their quotient does; it contains no exchange; it contains the flips exactly when
  `ε = 0`.

Proof. The exchange is a product of two transpositions of points and a transposition of pairs;
the flip is one transposition of points and the identity on the pairs.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {α : Type*} {n : Perm α}

/-! ## Signed permutations -/

theorem signedPerm_mul {w₁ w₂ : Perm α} (h₁ : ∀ x, w₁ (n x) = n (w₁ x))
    (h₂ : ∀ x, w₂ (n x) = n (w₂ x)) (x : α) : (w₁ * w₂) (n x) = n ((w₁ * w₂) x) := by
  rw [Perm.mul_apply, Perm.mul_apply, h₂, h₁]

theorem signedPerm_inv {w : Perm α} (h : ∀ x, w (n x) = n (w x)) (x : α) :
    w⁻¹ (n x) = n (w⁻¹ x) := by
  rw [Perm.inv_eq_iff_eq, h]
  exact congrArg n (w.apply_symm_apply x).symm

/-! ## The permutation of the pairs -/

/-- The pairs `{x, n x}` of an involution. -/
def pairSetoid (n : Perm α) (hn : ∀ x, n (n x) = x) : Setoid α where
  r x y := y = x ∨ y = n x
  iseqv := ⟨fun x => Or.inl rfl,
    fun {x y} h => h.elim (fun h => Or.inl h.symm) fun h => Or.inr (by rw [h, hn]),
    fun {x y z} h1 h2 => by
      rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact Or.inr rfl
      · exact Or.inl (hn _)⟩

variable {hn : ∀ x, n (n x) = x}

theorem pair_mk_eq_iff {x y : α} :
    Quotient.mk (pairSetoid n hn) x = Quotient.mk (pairSetoid n hn) y ↔ y = x ∨ y = n x :=
  ⟨fun h => Quotient.exact h, fun h => Quotient.sound h⟩

theorem pair_mk_apply (x : α) :
    Quotient.mk (pairSetoid n hn) (n x) = Quotient.mk (pairSetoid n hn) x :=
  pair_mk_eq_iff.2 (Or.inr (hn x).symm)

theorem pair_mk_ne {x a : α} (h1 : x ≠ a) (h2 : x ≠ n a) :
    Quotient.mk (pairSetoid n hn) x ≠ Quotient.mk (pairSetoid n hn) a := fun h => by
  rcases pair_mk_eq_iff.1 h with h' | h'
  · exact h1 h'.symm
  · exact h2 (by rw [h', hn])

open Classical in
/-- The permutation of the pairs induced by a signed permutation; `1` for other permutations. -/
noncomputable def inducedPairPerm (n : Perm α) (hn : ∀ x, n (n x) = x) (w : Perm α) :
    Perm (Quotient (pairSetoid n hn)) :=
  if hw : ∀ x, w (n x) = n (w x) then
    Quotient.congr w (fun a₁ a₂ => by
      show (a₂ = a₁ ∨ a₂ = n a₁) ↔ (w a₂ = w a₁ ∨ w a₂ = n (w a₁))
      rw [← hw, w.injective.eq_iff, w.injective.eq_iff])
  else 1

theorem inducedPairPerm_mk {w : Perm α} (hw : ∀ x, w (n x) = n (w x)) (x : α) :
    inducedPairPerm n hn w (Quotient.mk (pairSetoid n hn) x) =
      Quotient.mk (pairSetoid n hn) (w x) := by
  unfold inducedPairPerm
  rw [dif_pos hw]
  exact Quotient.congr_mk _ _ _

theorem inducedPairPerm_mul {w₁ w₂ : Perm α} (h₁ : ∀ x, w₁ (n x) = n (w₁ x))
    (h₂ : ∀ x, w₂ (n x) = n (w₂ x)) :
    inducedPairPerm n hn (w₁ * w₂) = inducedPairPerm n hn w₁ * inducedPairPerm n hn w₂ := by
  refine Perm.ext fun q => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  rw [Perm.mul_apply, inducedPairPerm_mk (signedPerm_mul h₁ h₂), inducedPairPerm_mk h₂,
    inducedPairPerm_mk h₁,
    Perm.mul_apply]

/-- A signed permutation of finite support moves finitely many pairs. -/
theorem finite_setOf_inducedPairPerm_ne {w : Perm α} (hw : ∀ x, w (n x) = n (w x))
    (hfin : {x | w x ≠ x}.Finite) : {q | inducedPairPerm n hn w q ≠ q}.Finite := by
  refine (hfin.image (Quotient.mk (pairSetoid n hn))).subset fun q hq => ?_
  obtain ⟨x, rfl⟩ := Quotient.exists_rep q
  refine ⟨x, fun h => hq ?_, rfl⟩
  rw [inducedPairPerm_mk hw, h]

/-! ## The two signs -/

/-- The sign of a signed permutation on the pairs. -/
noncomputable def pairSign (n : Perm α) (hn : ∀ x, n (n x) = x) (w : Perm α) : ℤˣ :=
  finSign (inducedPairPerm n hn w)

theorem pairSign_mul {w₁ w₂ : Perm α} (h₁ : ∀ x, w₁ (n x) = n (w₁ x))
    (hf₁ : {x | w₁ x ≠ x}.Finite) (h₂ : ∀ x, w₂ (n x) = n (w₂ x))
    (hf₂ : {x | w₂ x ≠ x}.Finite) :
    pairSign n hn (w₁ * w₂) = pairSign n hn w₁ * pairSign n hn w₂ := by
  unfold pairSign
  rw [inducedPairPerm_mul h₁ h₂]
  exact finSign_mul (finite_setOf_inducedPairPerm_ne h₁ hf₁)
    (finite_setOf_inducedPairPerm_ne h₂ hf₂)

theorem finite_setOf_swap_ne [DecidableEq α] (a b : α) : {x | swap a b x ≠ x}.Finite :=
  (Set.toFinite ({a, b} : Set α)).subset fun x hx => by
    by_contra h
    rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
    exact hx (swap_apply_of_ne_of_ne h.1 h.2)

section Values

variable (hn0 : ∀ x, n x ≠ x)

section Exchange

variable {e : Perm α} {a a' : α} (h1 : a' ≠ a) (h2 : a' ≠ n a) (hea : e a = a')
  (hea' : e a' = a) (he : ∀ x, e (n x) = n (e x))
  (heo : ∀ x, x ≠ a → x ≠ n a → x ≠ a' → x ≠ n a' → e x = x)
include hn0 h1 h2 hea hea' he heo

/-- **The exchange of two pairs is an even permutation of the points.** -/
theorem finSign_exchange (hn : ∀ x, n (n x) = x) : finSign e = 1 := by
  classical
  have h3 : n a ≠ n a' := fun h => h1 (n.injective h).symm
  have h4 : a ≠ n a' := fun h => h2 (by rw [h, hn])
  have heq : e = swap a a' * swap (n a) (n a') := by
    refine Perm.ext fun x => ?_
    show e x = swap a a' (swap (n a) (n a') x)
    by_cases hx1 : x = a
    · rw [hx1, hea, swap_apply_of_ne_of_ne (hn0 a).symm h4, swap_apply_left]
    by_cases hx2 : x = a'
    · rw [hx2, hea', swap_apply_of_ne_of_ne h2 (hn0 a').symm, swap_apply_right]
    by_cases hx3 : x = n a
    · rw [hx3, he, hea, swap_apply_left, swap_apply_of_ne_of_ne (fun h => h4 h.symm) (hn0 a')]
    by_cases hx4 : x = n a'
    · rw [hx4, he, hea', swap_apply_right,
        swap_apply_of_ne_of_ne (hn0 a) (fun h => h2 h.symm)]
    · rw [heo x hx1 hx3 hx2 hx4, swap_apply_of_ne_of_ne hx3 hx4,
        swap_apply_of_ne_of_ne hx1 hx2]
  rw [heq, finSign_mul (finite_setOf_swap_ne _ _) (finite_setOf_swap_ne _ _),
    finSign_swap h1.symm, finSign_swap h3]
  exact Int.units_mul_self (-1)

omit hn0 in
/-- **The exchange of two pairs is an odd permutation of the pairs.** -/
theorem pairSign_exchange (hn : ∀ x, n (n x) = x) : pairSign n hn e = -1 := by
  classical
  have hne : Quotient.mk (pairSetoid n hn) a ≠ Quotient.mk (pairSetoid n hn) a' := fun h => by
    rcases pair_mk_eq_iff.1 h with h' | h'
    · exact h1 h'
    · exact h2 h'
  have heq : inducedPairPerm n hn e =
      swap (Quotient.mk (pairSetoid n hn) a) (Quotient.mk (pairSetoid n hn) a') := by
    refine Perm.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rw [inducedPairPerm_mk he]
    by_cases hx1 : x = a
    · rw [hx1, hea, swap_apply_left]
    by_cases hx2 : x = a'
    · rw [hx2, hea', swap_apply_right]
    by_cases hx3 : x = n a
    · rw [hx3, he, hea, pair_mk_apply, pair_mk_apply, swap_apply_left]
    by_cases hx4 : x = n a'
    · rw [hx4, he, hea', pair_mk_apply, pair_mk_apply, swap_apply_right]
    · rw [heo x hx1 hx3 hx2 hx4,
        swap_apply_of_ne_of_ne (pair_mk_ne hx1 hx3) (pair_mk_ne hx2 hx4)]
  unfold pairSign
  rw [heq]
  exact finSign_swap hne

end Exchange

section Flip

variable {f : Perm α} {a : α} (hfa : f a = n a) (hfn : ∀ x, f (n x) = n (f x))
  (hfo : ∀ x, x ≠ a → x ≠ n a → f x = x)
include hfa hfn hfo

include hn0 in
/-- **The flip of one pair is an odd permutation of the points.** -/
theorem finSign_flip (hn : ∀ x, n (n x) = x) : finSign f = -1 := by
  classical
  have heq : f = swap a (n a) := by
    refine Perm.ext fun x => ?_
    by_cases hx1 : x = a
    · rw [hx1, hfa, swap_apply_left]
    by_cases hx2 : x = n a
    · rw [hx2, hfn, hfa, hn, swap_apply_right]
    · rw [hfo x hx1 hx2, swap_apply_of_ne_of_ne hx1 hx2]
  rw [heq]
  exact finSign_swap (hn0 a).symm

/-- **The flip of one pair fixes every pair.** -/
theorem pairSign_flip (hn : ∀ x, n (n x) = x) : pairSign n hn f = 1 := by
  have heq : inducedPairPerm n hn f = 1 := by
    refine Perm.ext fun q => ?_
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    rw [inducedPairPerm_mk hfn, Perm.one_apply]
    by_cases hx1 : x = a
    · rw [hx1, hfa, pair_mk_apply]
    by_cases hx2 : x = n a
    · rw [hx2, hfn, hfa, pair_mk_apply]
    · rw [hfo x hx1 hx2]
  unfold pairSign
  rw [heq, finSign_one]

end Flip

end Values

/-- **The exchange of two pairs exists.** Two points `a`, `a'` that are not partners are
exchanged, with their partners, by a signed permutation that fixes every other point. -/
theorem exists_signedExchange (hn : ∀ x, n (n x) = x) (hn0 : ∀ x, n x ≠ x) {a a' : α}
    (h2 : a' ≠ n a) :
    ∃ e : Perm α, e a = a' ∧ e a' = a ∧ (∀ x, e (n x) = n (e x)) ∧
      ∀ x, x ≠ a → x ≠ n a → x ≠ a' → x ≠ n a' → e x = x := by
  classical
  have h3 : a ≠ n a' := fun h => h2 (by rw [h, hn])
  have ea : (swap a a' * swap (n a) (n a')) a = a' := by
    show swap a a' (swap (n a) (n a') a) = a'
    rw [swap_apply_of_ne_of_ne (hn0 a).symm h3, swap_apply_left]
  have ea' : (swap a a' * swap (n a) (n a')) a' = a := by
    show swap a a' (swap (n a) (n a') a') = a
    rw [swap_apply_of_ne_of_ne h2 (hn0 a').symm, swap_apply_right]
  have ena : (swap a a' * swap (n a) (n a')) (n a) = n a' := by
    show swap a a' (swap (n a) (n a') (n a)) = n a'
    rw [swap_apply_left]
    exact swap_apply_of_ne_of_ne (Ne.symm h3) (hn0 a')
  have ena' : (swap a a' * swap (n a) (n a')) (n a') = n a := by
    show swap a a' (swap (n a) (n a') (n a')) = n a
    rw [swap_apply_right]
    exact swap_apply_of_ne_of_ne (hn0 a) (Ne.symm h2)
  have eo : ∀ x, x ≠ a → x ≠ n a → x ≠ a' → x ≠ n a' →
      (swap a a' * swap (n a) (n a')) x = x := fun x k1 k2 k3 k4 => by
    show swap a a' (swap (n a) (n a') x) = x
    rw [swap_apply_of_ne_of_ne k2 k4, swap_apply_of_ne_of_ne k1 k3]
  refine ⟨_, ea, ea', fun x => ?_, eo⟩
  by_cases k1 : x = a
  · rw [k1, ena, ea]
  by_cases k2 : x = n a
  · rw [k2, hn, ea, ena, hn]
  by_cases k3 : x = a'
  · rw [k3, ena', ea']
  by_cases k4 : x = n a'
  · rw [k4, hn, ea', ena', hn]
  · rw [eo x k1 k2 k3 k4]
    exact eo (n x) (fun h => k2 (by rw [← h, hn])) (fun h => k1 (n.injective h))
      (fun h => k4 (by rw [← h, hn])) (fun h => k3 (n.injective h))

/-! ## The characters and their kernels -/

/-- The character `pairSign · finSign ^ ε` of the signed permutations of finite support. -/
noncomputable def signedCharacter (n : Perm α) (hn : ∀ x, n (n x) = x) (ε : ℕ) (w : Perm α) :
    ℤˣ :=
  pairSign n hn w * finSign w ^ ε

variable {ε : ℕ}

theorem signedCharacter_mul {w₁ w₂ : Perm α} (h₁ : ∀ x, w₁ (n x) = n (w₁ x))
    (hf₁ : {x | w₁ x ≠ x}.Finite) (h₂ : ∀ x, w₂ (n x) = n (w₂ x))
    (hf₂ : {x | w₂ x ≠ x}.Finite) :
    signedCharacter n hn ε (w₁ * w₂) = signedCharacter n hn ε w₁ * signedCharacter n hn ε w₂ := by
  unfold signedCharacter
  rw [pairSign_mul h₁ hf₁ h₂ hf₂, finSign_mul hf₁ hf₂, mul_pow]
  exact mul_mul_mul_comm _ _ _ _

theorem signedCharacter_one : signedCharacter n hn ε (1 : Perm α) = 1 := by
  have h := signedCharacter_mul (n := n) (hn := hn) (ε := ε) (w₁ := 1) (w₂ := 1)
    (fun _ => rfl) finite_setOf_one_ne (fun _ => rfl) finite_setOf_one_ne
  rw [mul_one] at h
  have h2 := Int.units_mul_self (signedCharacter n hn ε (1 : Perm α))
  rw [← h] at h2
  exact h2

theorem signedCharacter_inv {w : Perm α} (hw : ∀ x, w (n x) = n (w x))
    (hf : {x | w x ≠ x}.Finite) : signedCharacter n hn ε w⁻¹ = signedCharacter n hn ε w := by
  have h := signedCharacter_mul (hn := hn) (ε := ε) hw hf (signedPerm_inv hw)
    (finite_setOf_inv_ne hf)
  rw [mul_inv_cancel, signedCharacter_one] at h
  exact mul_left_cancel (h.symm.trans (Int.units_mul_self (signedCharacter n hn ε w)).symm)

/-- The signed permutations of finite support on which `pairSign · finSign ^ ε` is `1`. -/
noncomputable def signedKernel (n : Perm α) (hn : ∀ x, n (n x) = x) (ε : ℕ) :
    Subgroup (Perm α) where
  carrier := {w | (∀ x, w (n x) = n (w x)) ∧ {x | w x ≠ x}.Finite ∧
    signedCharacter n hn ε w = 1}
  mul_mem' := by
    rintro w₁ w₂ ⟨h₁, hf₁, hc₁⟩ ⟨h₂, hf₂, hc₂⟩
    exact ⟨signedPerm_mul h₁ h₂, finite_setOf_mul_ne hf₁ hf₂, by
      rw [signedCharacter_mul h₁ hf₁ h₂ hf₂, hc₁, hc₂, one_mul]⟩
  one_mem' := ⟨fun _ => rfl, finite_setOf_one_ne, signedCharacter_one⟩
  inv_mem' := by
    rintro w ⟨h, hf, hc⟩
    exact ⟨signedPerm_inv h, finite_setOf_inv_ne hf, by rw [signedCharacter_inv h hf, hc]⟩

theorem mem_signedKernel {w : Perm α} :
    w ∈ signedKernel n hn ε ↔ (∀ x, w (n x) = n (w x)) ∧ {x | w x ≠ x}.Finite ∧
      signedCharacter n hn ε w = 1 :=
  Iff.rfl

/-- **The kernel has index at most two.** Of two signed permutations of finite support one lies
in the kernel or their quotient does. -/
theorem mem_signedKernel_or_mem_or_mul_inv_mem {w₁ w₂ : Perm α}
    (h₁ : ∀ x, w₁ (n x) = n (w₁ x)) (hf₁ : {x | w₁ x ≠ x}.Finite)
    (h₂ : ∀ x, w₂ (n x) = n (w₂ x)) (hf₂ : {x | w₂ x ≠ x}.Finite) :
    w₁ ∈ signedKernel n hn ε ∨ w₂ ∈ signedKernel n hn ε ∨ w₁ * w₂⁻¹ ∈ signedKernel n hn ε := by
  rcases Int.units_eq_one_or (signedCharacter n hn ε w₁) with c1 | c1
  · exact Or.inl ⟨h₁, hf₁, c1⟩
  rcases Int.units_eq_one_or (signedCharacter n hn ε w₂) with c2 | c2
  · exact Or.inr (Or.inl ⟨h₂, hf₂, c2⟩)
  · refine Or.inr (Or.inr ⟨signedPerm_mul h₁ (signedPerm_inv h₂),
      finite_setOf_mul_ne hf₁ (finite_setOf_inv_ne hf₂), ?_⟩)
    rw [signedCharacter_mul h₁ hf₁ (signedPerm_inv h₂) (finite_setOf_inv_ne hf₂),
      signedCharacter_inv h₂ hf₂, c1, c2]
    exact Int.units_mul_self (-1)

/-- **The kernel contains no exchange of two pairs.** -/
theorem exchange_not_mem_signedKernel (hn0 : ∀ x, n x ≠ x) {e : Perm α} {a a' : α}
    (h1 : a' ≠ a) (h2 : a' ≠ n a) (hea : e a = a') (hea' : e a' = a)
    (he : ∀ x, e (n x) = n (e x))
    (heo : ∀ x, x ≠ a → x ≠ n a → x ≠ a' → x ≠ n a' → e x = x) :
    e ∉ signedKernel n hn ε := by
  rintro ⟨-, -, hc⟩
  unfold signedCharacter at hc
  rw [pairSign_exchange h1 h2 hea hea' he heo hn,
    finSign_exchange hn0 h1 h2 hea hea' he heo hn, one_pow, mul_one] at hc
  exact absurd hc (by decide)

/-- **The kernel contains the flips of single pairs exactly when `ε = 0`.** -/
theorem flip_mem_signedKernel_iff (hn0 : ∀ x, n x ≠ x) (hε : ε = 0 ∨ ε = 1) {f : Perm α}
    {a : α} (hfa : f a = n a) (hfn : ∀ x, f (n x) = n (f x))
    (hfo : ∀ x, x ≠ a → x ≠ n a → f x = x) : f ∈ signedKernel n hn ε ↔ ε = 0 := by
  have hfin : {x | f x ≠ x}.Finite :=
    (Set.toFinite ({a, n a} : Set α)).subset fun x hx => by
      by_contra h
      rw [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at h
      exact hx (hfo x h.1 h.2)
  have hc : signedCharacter n hn ε f = (-1) ^ ε := by
    unfold signedCharacter
    rw [pairSign_flip hfa hfn hfo hn, finSign_flip hn0 hfa hfn hfo hn, one_mul]
  rcases hε with rfl | rfl
  · exact ⟨fun _ => rfl, fun _ => ⟨hfn, hfin, by rw [hc, pow_zero]⟩⟩
  · refine ⟨fun h => ?_, fun h => absurd h one_ne_zero⟩
    obtain ⟨-, -, hc'⟩ := h
    rw [hc, pow_one] at hc'
    exact absurd hc' (by decide)

end GaloisForLFunctions.GaloisTheoryOfZeros
