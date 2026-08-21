import GaloisForLFunctions.HTGeometry.WickNormalOrdering

/-!
# Wick's theorem

For a creation/annihilation system `W : WickSystem K A ι` and a word `l : List (WickMode ι)`,
Wick's theorem expands the ordered operator product `op l₀ * op l₁ * ⋯` as the normal-ordered
product plus the sum of all *partial contractions*: for every set of disjoint pairs of letters one
multiplies the corresponding contraction scalars and normally orders whatever letters are left.

The partial contractions are enumerated by `WickSystem.wickExpand`.  Reading its recursion,

```text
wickExpand φ []       = φ []
wickExpand φ (u :: t) = wickExpand (fun s => φ (u :: s)) t
                        + ∑ (positions k of t) contract u t[k] • wickExpand φ (t.eraseIdx k)
```

the first letter `u` is either left uncontracted — in which case it is prepended to the residual
word that the rest of the recursion produces — or contracted against one of the later letters
`t[k]`, which is then deleted along with `u`.  Running the recursion to the end therefore visits
each partial pairing of the word exactly once, weights it by the product of its contractions and
applies `φ` to the list of uncontracted letters.  Taking `φ = W.nord` gives the Wick expansion:

```text
(l.map op).prod = wickExpand nord l .
```

## Proof

The induction is the one in the physics literature.  Multiplying the expansion of `t` on the left by
one further operator `op u` is handled by `WickSystem.op_mul_nord`: `op u` either enters the
normal-ordered word or is contracted against one of its letters.  The contraction terms so produced
are indexed by *a partial pairing of `t` together with an uncontracted letter of it*, whereas the
recursion for `wickExpand` on `u :: t` indexes them by *a letter of `t` together with a partial
pairing of the rest*.  That these two enumerations agree is `wickExpand_positionSum`, proved from
the exchange law `positionSum_swap`.
-/

universe u v w

namespace GaloisForLFunctions.HTGeometry

namespace WickSystem

variable {K : Type u} {A : Type v} {ι : Type w}
variable [CommSemiring K] [Semiring A] [Algebra K A] (W : WickSystem K A ι)

/-- **The Wick expansion.**  Sum over all partial pairings of a word of the product of the
contractions of the paired letters, times `φ` applied to the list of unpaired letters. -/
def wickExpand (V : WickSystem K A ι) (φ : List (WickMode ι) → A) : List (WickMode ι) → A
  | [] => φ []
  | (u :: t) => wickExpand V (fun s => φ (u :: s)) t
      + ∑ k : Fin t.length, V.contract u t[(k : ℕ)] • wickExpand V φ (t.eraseIdx (k : ℕ))
termination_by l => l.length
decreasing_by
  · simp
  · have h := List.length_eraseIdx_le t (k : ℕ)
    simp only [List.length_cons]
    omega

@[simp] theorem wickExpand_nil (φ : List (WickMode ι) → A) :
    W.wickExpand φ [] = φ [] := by
  rw [wickExpand]

/-- The recursion defining the Wick expansion: the head is either left uncontracted or paired with
one of the later letters. -/
theorem wickExpand_cons (φ : List (WickMode ι) → A) (u : WickMode ι) (t : List (WickMode ι)) :
    W.wickExpand φ (u :: t)
      = W.wickExpand (fun s => φ (u :: s)) t
        + positionSum t (fun a s => W.contract u a • W.wickExpand φ s) := by
  rw [wickExpand]
  rfl

/-! ## Linearity of the expansion in the leftover functional -/

private theorem wickExpand_add_aux :
    ∀ (n : ℕ) (l : List (WickMode ι)), l.length ≤ n → ∀ (φ ψ : List (WickMode ι) → A),
      W.wickExpand (fun s => φ s + ψ s) l = W.wickExpand φ l + W.wickExpand ψ l := by
  intro n
  induction n with
  | zero =>
      intro l hl φ ψ
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl φ ψ
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [wickExpand_cons, wickExpand_cons, wickExpand_cons,
          ih t ht (fun s => φ (u :: s)) (fun s => ψ (u :: s))]
        have hsum : positionSum t (fun a s =>
              W.contract u a • W.wickExpand (fun s' => φ s' + ψ s') s)
            = positionSum t (fun a s => W.contract u a • W.wickExpand φ s)
              + positionSum t (fun a s => W.contract u a • W.wickExpand ψ s) := by
          rw [← positionSum_add]
          refine positionSum_congr' fun k => ?_
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ ψ, smul_add]
        rw [hsum]
        abel

/-- The Wick expansion is additive in the leftover functional. -/
theorem wickExpand_add (φ ψ : List (WickMode ι) → A) (l : List (WickMode ι)) :
    W.wickExpand (fun s => φ s + ψ s) l = W.wickExpand φ l + W.wickExpand ψ l :=
  wickExpand_add_aux W l.length l le_rfl φ ψ

private theorem wickExpand_smul_aux :
    ∀ (n : ℕ) (l : List (WickMode ι)), l.length ≤ n → ∀ (c : K) (φ : List (WickMode ι) → A),
      W.wickExpand (fun s => c • φ s) l = c • W.wickExpand φ l := by
  intro n
  induction n with
  | zero =>
      intro l hl c φ
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl c φ
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [wickExpand_cons, wickExpand_cons, ih t ht c (fun s => φ (u :: s))]
        have hsum : positionSum t (fun a s => W.contract u a • W.wickExpand (fun s' => c • φ s') s)
            = c • positionSum t (fun a s => W.contract u a • W.wickExpand φ s) := by
          rw [← positionSum_smul]
          refine positionSum_congr' fun k => ?_
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) c φ, smul_comm]
        rw [hsum, smul_add]

/-- The Wick expansion is homogeneous in the leftover functional. -/
theorem wickExpand_smul (c : K) (φ : List (WickMode ι) → A) (l : List (WickMode ι)) :
    W.wickExpand (fun s => c • φ s) l = c • W.wickExpand φ l :=
  wickExpand_smul_aux W l.length l le_rfl c φ

private theorem wickExpand_mul_left_aux :
    ∀ (n : ℕ) (l : List (WickMode ι)), l.length ≤ n → ∀ (x : A) (φ : List (WickMode ι) → A),
      x * W.wickExpand φ l = W.wickExpand (fun s => x * φ s) l := by
  intro n
  induction n with
  | zero =>
      intro l hl x φ
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl x φ
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [wickExpand_cons, wickExpand_cons, mul_add, ih t ht x (fun s => φ (u :: s)),
          mul_positionSum]
        congr 1
        refine positionSum_congr' fun k => ?_
        rw [Algebra.mul_smul_comm, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) x φ]

/-- Left multiplication passes through the Wick expansion into the leftover functional. -/
theorem wickExpand_mul_left (x : A) (φ : List (WickMode ι) → A) (l : List (WickMode ι)) :
    x * W.wickExpand φ l = W.wickExpand (fun s => x * φ s) l :=
  wickExpand_mul_left_aux W l.length l le_rfl x φ

/-! ## The two enumerations of a pairing together with a marked free letter -/

private theorem wickExpand_positionSum_aux :
    ∀ (n : ℕ) (t : List (WickMode ι)), t.length ≤ n →
      ∀ (ψ : WickMode ι → List (WickMode ι) → A),
        W.wickExpand (fun s => positionSum s ψ) t
          = positionSum t (fun a s => W.wickExpand (ψ a) s) := by
  intro n
  induction n with
  | zero =>
      intro t ht ψ
      match t with
      | [] => simp
      | (_ :: _) => simp at ht
  | succ n ih =>
      intro t ht ψ
      match t with
      | [] => simp
      | (w :: r) =>
        have hr : r.length ≤ n := by simpa using ht
        rw [wickExpand_cons, positionSum_cons]
        have e1 : W.wickExpand (fun s => positionSum (w :: s) ψ) r
            = W.wickExpand (ψ w) r
              + positionSum r (fun a s => W.wickExpand (fun t' => ψ a (w :: t')) s) := by
          have hfun : (fun s => positionSum (w :: s) ψ)
              = fun s => ψ w s + positionSum s (fun b t' => ψ b (w :: t')) := by
            funext s
            exact positionSum_cons _ _ _
          rw [hfun, wickExpand_add, ih r hr (fun b t' => ψ b (w :: t'))]
        have e2 : positionSum r (fun a s =>
              W.contract w a • W.wickExpand (fun s' => positionSum s' ψ) s)
            = positionSum r (fun a s => positionSum s
                (fun b t' => W.contract w a • W.wickExpand (ψ b) t')) := by
          refine positionSum_congr' fun k => ?_
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) hr) ψ, ← positionSum_smul]
        have e3 : positionSum r (fun a s => W.wickExpand (ψ a) (w :: s))
            = positionSum r (fun a s => W.wickExpand (fun t' => ψ a (w :: t')) s)
              + positionSum r (fun a s => positionSum s
                  (fun b t' => W.contract w b • W.wickExpand (ψ a) t')) := by
          rw [← positionSum_add]
          exact positionSum_congr fun a s => wickExpand_cons _ _ _ _
        rw [e1, e2, e3,
          positionSum_swap r (fun a b t' => W.contract w a • W.wickExpand (ψ b) t'), add_assoc]

/-- **The exchange law for Wick expansions.**  Expanding a word and then marking a free letter of
the residual word enumerates the same data as marking a letter of the word and then expanding what
is left. -/
theorem wickExpand_positionSum (ψ : WickMode ι → List (WickMode ι) → A) (t : List (WickMode ι)) :
    W.wickExpand (fun s => positionSum s ψ) t = positionSum t (fun a s => W.wickExpand (ψ a) s) :=
  wickExpand_positionSum_aux W t.length t le_rfl ψ

/-! ## Wick's theorem -/

/-- **Wick's theorem.**  The ordered product of the operators of a word equals the sum, over all
partial pairings of the word, of the product of the contractions of the paired letters times the
normal-ordered product of the unpaired letters. -/
theorem prod_op_eq_wickExpand_nord (l : List (WickMode ι)) :
    (l.map W.op).prod = W.wickExpand W.nord l := by
  induction l with
  | nil => simp
  | cons u t ih =>
      rw [List.map_cons, List.prod_cons, ih, wickExpand_mul_left]
      have hfun : (fun s => W.op u * W.nord s)
          = fun s => W.nord (u :: s)
              + positionSum s (fun a s' => W.contract u a • W.nord s') := by
        funext s
        exact W.op_mul_nord u s
      rw [hfun, wickExpand_add, wickExpand_cons]
      congr 1
      rw [wickExpand_positionSum W (fun a s' => W.contract u a • W.nord s')]
      exact positionSum_congr fun a s => wickExpand_smul W (W.contract u a) W.nord s

end WickSystem

end GaloisForLFunctions.HTGeometry
