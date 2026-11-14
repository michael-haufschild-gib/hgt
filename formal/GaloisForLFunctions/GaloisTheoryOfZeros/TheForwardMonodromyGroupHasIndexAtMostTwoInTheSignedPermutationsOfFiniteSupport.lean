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
  `G₊(b)` contains the exchange of two pairs, and then at every base time
  (`mem_forwardMonodromy_of_exchange_mem_base`).

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

/-- **One exchange at one base time decides at every base time.** If `G₊(b₁)` contains the
exchange of two pairs, then `G₊(b)` contains every permutation of the zeros of `H_b` that
commutes with `z ↦ −z` and moves finitely many zeros: the transport along a forward path from
`b₁` to `b` conjugates the exchange to an exchange in `G₊(b)`. -/
theorem mem_forwardMonodromy_of_exchange_mem_base {b₁ : ℂ} (hb₁₀ : 0 < b₁.re)
    (hb₁ : b₁ ∉ branchTimes) {x x' : {z : ℂ // complexHeat b₁ z = 0}}
    {ε : Perm {z : ℂ // complexHeat b₁ z = 0}} (h1 : x' ≠ x) (h2 : x' ≠ fibreNeg b₁ x)
    (hx : ε x = x') (hx' : ε x' = x) (hε : ∀ y, ε (fibreNeg b₁ y) = fibreNeg b₁ (ε y))
    (ho : ∀ y, y ≠ x → y ≠ fibreNeg b₁ x → y ≠ x' → y ≠ fibreNeg b₁ x' → ε y = y)
    (hεG : ε ∈ forwardMonodromy b₁ hb₁₀ hb₁) {w : Perm {z : ℂ // complexHeat b z = 0}}
    (hw : ∀ q, w (fibreNeg b q) = fibreNeg b (w q)) (hfin : {q | w q ≠ q}.Finite) :
    w ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨γ, hγ, g0, g1⟩ := exists_isForwardPath hb₁₀ hb₀ hb₁ hb
  obtain ⟨φ, hφ⟩ := hγ.exists_fibreEquiv g0 g1
  have hφn : ∀ q, φ (fibreNeg b₁ q) = fibreNeg b (φ q) := fun q =>
    Subtype.ext (hγ.transports_unique (hφ (fibreNeg b₁ q)) (hφ q).neg)
  have hφs : ∀ y, φ.symm (fibreNeg b y) = fibreNeg b₁ (φ.symm y) := fun y => by
    rw [Equiv.symm_apply_eq, hφn, Equiv.apply_symm_apply]
  refine mem_forwardMonodromy_of_exchange_mem hb₀ hb (a := φ x) (a' := φ x')
    (e := φ.permCongr ε) (fun h => h1 (φ.injective h))
    (fun h => h2 (φ.injective (h.trans (hφn x).symm))) ?_ ?_ (fun y => ?_)
    (fun y k1 k2 k3 k4 => ?_) (hγ.permCongr_mem_forwardMonodromy g0 g1 hφ hεG) hw hfin
  · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hx]
  · rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, hx']
  · rw [Equiv.permCongr_apply, Equiv.permCongr_apply, hφs, hε, hφn]
  · rw [Equiv.permCongr_apply, ho (φ.symm y) (fun h => k1 ((Equiv.symm_apply_eq φ).mp h))
      (fun h => k2 (by rw [(Equiv.symm_apply_eq φ).mp h, hφn]))
      (fun h => k3 ((Equiv.symm_apply_eq φ).mp h))
      (fun h => k4 (by rw [(Equiv.symm_apply_eq φ).mp h, hφn])), Equiv.apply_symm_apply]

end GaloisForLFunctions.GaloisTheoryOfZeros
