import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupContainsTheFlipOfEveryPairUpToOneExchange
import GaloisForLFunctions.GaloisTheoryOfZeros.ASignedGroupWithTheEvenPermutationsAndAFlipUpToAnExchangeHasIndexAtMostTwo

/-!
# The forward monodromy group has index at most two in the signed permutations of finite support

Let `b` be a forward time off the branch times and let `W(b)` be the group of the permutations
of the zeros of `H_b` that commute with `z ↦ −z` and move finitely many zeros. The forward
monodromy group `G₊(b)` is a subgroup of `W(b)`.

* **Index at most two** (`mem_forwardMonodromy_or_mem_or_mul_inv_mem`). Of two elements of
  `W(b)`, one lies in `G₊(b)` or their quotient does.
* **Normal** (`conj_mem_forwardMonodromy`). `w g w⁻¹ ∈ G₊(b)` for `g ∈ G₊(b)` and `w ∈ W(b)`.
* **One coset** (`mem_forwardMonodromy_or_mul_exchange_mem`). For the exchange `e` of any two
  pairs `a ↔ a'`, `−a ↔ −a'`, every `w ∈ W(b)` lies in `G₊(b)` or `w e` does.
* **One exchange decides** (`mem_forwardMonodromy_of_exchange_mem`). `G₊(b) = W(b)` as soon as
  `G₊(b)` contains the exchange of two pairs.

So the group of the zeros over the forward times is determined up to one sign: it is `W(b)` or a
subgroup of index two that contains no exchange of two pairs.

Proof. `G₊(b)` contains every signed 3-cycle, every double flip, and the flip of a pair alone or
times one exchange. Such a group has index at most two
(`IsWindowedSignedGroup.mem_or_mem_or_mul_inv_mem`).
-/

open RHTower Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

variable {b : ℂ}

/-- Over a time off the branch times no zero is its own reflection. -/
theorem fibreNeg_apply_ne_self (hb : b ∉ branchTimes) (x : {z : ℂ // complexHeat b z = 0}) :
    fibreNeg b x ≠ x := by
  intro h
  have h1 : -x.1 = x.1 := congrArg Subtype.val h
  have h2 : (2 : ℂ) * x.1 = 0 := by linear_combination -h1
  have h3 : x.1 = 0 := (mul_eq_zero.mp h2).resolve_left two_ne_zero
  have h4 := x.2
  rw [h3] at h4
  exact hb (mem_branchTimes_of_complexHeat_center_eq_zero h4)

variable (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)

/-- **`G₊(b)` has index at most two in the signed permutations of finite support.** Of two
permutations of the zeros of `H_b` that commute with `z ↦ −z` and move finitely many zeros, one
lies in `G₊(b)` or their quotient does. -/
theorem mem_forwardMonodromy_or_mem_or_mul_inv_mem
    {w₁ w₂ : Perm {z : ℂ // complexHeat b z = 0}}
    (hw₁ : ∀ x, w₁ (fibreNeg b x) = fibreNeg b (w₁ x)) (hfin₁ : {x | w₁ x ≠ x}.Finite)
    (hw₂ : ∀ x, w₂ (fibreNeg b x) = fibreNeg b (w₂ x)) (hfin₂ : {x | w₂ x ≠ x}.Finite) :
    w₁ ∈ forwardMonodromy b hb₀ hb ∨ w₂ ∈ forwardMonodromy b hb₀ hb ∨
      w₁ * w₂⁻¹ ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨P, hP, hG, hodd⟩ :=
    exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange hb₀ hb
  exact hG.mem_or_mem_or_mul_inv_mem (fun x => by rw [hP]; exact fibreNeg_apply_ne_self hb x)
    hodd (fun x => by rw [hP, hP]; exact hw₁ x) hfin₁ (fun x => by rw [hP, hP]; exact hw₂ x)
    hfin₂

/-- **`G₊(b)` is normal in the signed permutations of finite support.** -/
theorem conj_mem_forwardMonodromy {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite)
    {g : Perm {z : ℂ // complexHeat b z = 0}} (hg : g ∈ forwardMonodromy b hb₀ hb) :
    w * g * w⁻¹ ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨P, hP, hG, hodd⟩ :=
    exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange hb₀ hb
  exact hG.conj_mem (fun x => by rw [hP]; exact fibreNeg_apply_ne_self hb x) hodd
    (fun x => by rw [hP, hP]; exact hw x) hfin hg

variable {a a' : {z : ℂ // complexHeat b z = 0}} {e : Perm {z : ℂ // complexHeat b z = 0}}

/-- **`G₊(b)` or its coset by one exchange.** Let `e` exchange two zeros `a`, `a'` in distinct
pairs, and their reflections, and fix every other zero. Every permutation `w` of the zeros of
`H_b` that commutes with `z ↦ −z` and moves finitely many zeros lies in `G₊(b)`, or `w e` does. -/
theorem mem_forwardMonodromy_or_mul_exchange_mem (h1 : a' ≠ a) (h2 : a' ≠ fibreNeg b a)
    (hea : e a = a') (hea' : e a' = a) (he : ∀ x, e (fibreNeg b x) = fibreNeg b (e x))
    (heo : ∀ x, x ≠ a → x ≠ fibreNeg b a → x ≠ a' → x ≠ fibreNeg b a' → e x = x)
    {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb ∨ w * e ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨P, hP, hG, hodd⟩ :=
    exists_pairCoordinate_forall_hasFlip_or_forall_hasFlipExchange hb₀ hb
  have hne : ∀ {x y : {z : ℂ // complexHeat b z = 0}}, P.pair x ≠ P.pair y →
      x ≠ y ∧ x ≠ fibreNeg b y := by
    intro x y h
    refine ⟨fun h' => h (by rw [h']), fun h' => h ?_⟩
    rw [h', ← hP, P.pair_flip]
  have haa' : P.pair a ≠ P.pair a' := fun h => by
    rcases (P.pair_eq_iff a a').mp h with h' | h'
    · exact h1 h'
    · exact h2 (h'.trans (hP a))
  exact hG.mem_or_mul_mem hodd haa' hea hea' (fun x => by rw [hP, hP]; exact he x)
    (fun x hx hx' => heo x (hne hx).1 (hne hx).2 (hne hx').1 (hne hx').2)
    (fun x => by rw [hP, hP]; exact hw x) hfin

/-- **One exchange decides.** If `G₊(b)` contains the exchange of two pairs, it contains every
permutation of the zeros of `H_b` that commutes with `z ↦ −z` and moves finitely many zeros. -/
theorem mem_forwardMonodromy_of_exchange_mem (h1 : a' ≠ a) (h2 : a' ≠ fibreNeg b a)
    (hea : e a = a') (hea' : e a' = a) (he : ∀ x, e (fibreNeg b x) = fibreNeg b (e x))
    (heo : ∀ x, x ≠ a → x ≠ fibreNeg b a → x ≠ a' → x ≠ fibreNeg b a' → e x = x)
    (heG : e ∈ forwardMonodromy b hb₀ hb) {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ x, w (fibreNeg b x) = fibreNeg b (w x)) (hfin : {x | w x ≠ x}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb := by
  rcases mem_forwardMonodromy_or_mul_exchange_mem hb₀ hb h1 h2 hea hea' he heo hw hfin with h | h
  · exact h
  · exact ((forwardMonodromy b hb₀ hb).mul_mem_cancel_right heG).mp h

end GaloisForLFunctions.GaloisTheoryOfZeros
