import GaloisForLFunctions.HTGeometry.CompletePairing
import Mathlib.Algebra.Algebra.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

/-!
# Expansion over the partial pairings of a word

Fix a kernel `c : α → α → K` on an alphabet and a *leftover functional* `φ : List α → M` with values
in a `K`-module.  The **partial-pairing expansion**

```text
pairingExpand c φ []       = φ []
pairingExpand c φ (u :: t) = pairingExpand c (fun s => φ (u :: s)) t
                             + ∑ (positions k of t) c u t[k] • pairingExpand c φ (t.eraseIdx k)
```

runs over all ways of choosing a set of disjoint pairs of positions of the word: the head is either
left free — and then prepended to whatever residual word the rest of the recursion produces — or
paired with a later letter, which is deleted along with it.  Each pairing contributes the product of
its kernel values times `φ` of the list of free letters.

This is the combinatorial skeleton of Wick's theorem, separated from any algebra of operators.  The
file proves what an induction over such expansions needs: linearity in `φ`, compatibility with
linear maps and with left multiplication, the collapse to `completePairing` when `φ` is supported on
the empty word, and the exchange law `pairingExpand_positionSum`, which identifies the two ways of
enumerating "a partial pairing together with a marked free letter".
-/

universe u v w x

namespace GaloisForLFunctions.HTGeometry

variable {α : Type u} {K : Type v} {M : Type w} {N : Type x}
variable [CommSemiring K] [AddCommMonoid M] [Module K M]

/-- **The partial-pairing expansion of a word.**  The sum over all sets of disjoint pairs of
positions of the product of the kernel values of the pairs, times the leftover functional evaluated
on the list of unpaired letters. -/
def pairingExpand (c : α → α → K) (φ : List α → M) : List α → M
  | [] => φ []
  | (u :: t) => pairingExpand c (fun s => φ (u :: s)) t
      + ∑ k : Fin t.length, c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ))
termination_by l => l.length
decreasing_by
  · simp
  · have h := List.length_eraseIdx_le t (k : ℕ)
    simp only [List.length_cons]
    omega

@[simp] theorem pairingExpand_nil (c : α → α → K) (φ : List α → M) :
    pairingExpand c φ [] = φ [] := by
  rw [pairingExpand]

/-- The head of the word is either left free or paired with a later letter. -/
theorem pairingExpand_cons (c : α → α → K) (φ : List α → M) (u : α) (t : List α) :
    pairingExpand c φ (u :: t)
      = pairingExpand c (fun s => φ (u :: s)) t
        + positionSum t (fun a s => c u a • pairingExpand c φ s) := by
  rw [pairingExpand]
  rfl

/-! ## Linearity in the leftover functional -/

private theorem pairingExpand_zero_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → pairingExpand c (fun _ => (0 : M)) l = 0 := by
  intro n
  induction n with
  | zero =>
      intro l hl
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [pairingExpand_cons, ih t ht, zero_add]
        simp only [positionSum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht), smul_zero]

@[simp] theorem pairingExpand_zero (c : α → α → K) (l : List α) :
    pairingExpand c (fun _ => (0 : M)) l = 0 :=
  pairingExpand_zero_aux c l.length l le_rfl

private theorem pairingExpand_add_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (φ ψ : List α → M),
      pairingExpand c (fun s => φ s + ψ s) l = pairingExpand c φ l + pairingExpand c ψ l := by
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
        rw [pairingExpand_cons, pairingExpand_cons, pairingExpand_cons,
          ih t ht (fun s => φ (u :: s)) (fun s => ψ (u :: s))]
        have hsum : positionSum t (fun a s =>
              c u a • pairingExpand c (fun s' => φ s' + ψ s') s)
            = positionSum t (fun a s => c u a • pairingExpand c φ s)
              + positionSum t (fun a s => c u a • pairingExpand c ψ s) := by
          rw [← positionSum_add]
          refine positionSum_congr' fun k => ?_
          show c u t[(k : ℕ)] • pairingExpand c (fun s' => φ s' + ψ s') (t.eraseIdx (k : ℕ))
              = c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ))
                + c u t[(k : ℕ)] • pairingExpand c ψ (t.eraseIdx (k : ℕ))
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ ψ, smul_add]
        rw [hsum]
        abel

/-- The expansion is additive in the leftover functional. -/
theorem pairingExpand_add (c : α → α → K) (φ ψ : List α → M) (l : List α) :
    pairingExpand c (fun s => φ s + ψ s) l = pairingExpand c φ l + pairingExpand c ψ l :=
  pairingExpand_add_aux c l.length l le_rfl φ ψ

private theorem pairingExpand_smul_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (b : K) (φ : List α → M),
      pairingExpand c (fun s => b • φ s) l = b • pairingExpand c φ l := by
  intro n
  induction n with
  | zero =>
      intro l hl b φ
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl b φ
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [pairingExpand_cons, pairingExpand_cons, ih t ht b (fun s => φ (u :: s))]
        have hsum : positionSum t (fun a s => c u a • pairingExpand c (fun s' => b • φ s') s)
            = b • positionSum t (fun a s => c u a • pairingExpand c φ s) := by
          rw [← positionSum_smul]
          refine positionSum_congr' fun k => ?_
          show c u t[(k : ℕ)] • pairingExpand c (fun s' => b • φ s') (t.eraseIdx (k : ℕ))
              = b • (c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ)))
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) b φ, smul_comm]
        rw [hsum, smul_add]

/-- The expansion is homogeneous in the leftover functional. -/
theorem pairingExpand_smul (c : α → α → K) (b : K) (φ : List α → M) (l : List α) :
    pairingExpand c (fun s => b • φ s) l = b • pairingExpand c φ l :=
  pairingExpand_smul_aux c l.length l le_rfl b φ

theorem pairingExpand_congr {c : α → α → K} {φ ψ : List α → M} (h : ∀ s, φ s = ψ s)
    (l : List α) : pairingExpand c φ l = pairingExpand c ψ l := by
  have : φ = ψ := funext h
  rw [this]

/-! ## Transport along a linear map -/

variable [AddCommMonoid N] [Module K N]

private theorem map_pairingExpand_aux (c : α → α → K) (g : M →ₗ[K] N) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ φ : List α → M,
      g (pairingExpand c φ l) = pairingExpand c (fun s => g (φ s)) l := by
  intro n
  induction n with
  | zero =>
      intro l hl φ
      match l with
      | [] => simp
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl φ
      match l with
      | [] => simp
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        rw [pairingExpand_cons, pairingExpand_cons, map_add, ih t ht (fun s => φ (u :: s)),
          map_positionSum]
        congr 1
        refine positionSum_congr' fun k => ?_
        show g (c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ)))
            = c u t[(k : ℕ)] • pairingExpand c (fun s => g (φ s)) (t.eraseIdx (k : ℕ))
        rw [map_smul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ]

/-- A linear map passes through the expansion into the leftover functional. -/
theorem map_pairingExpand (c : α → α → K) (g : M →ₗ[K] N) (φ : List α → M) (l : List α) :
    g (pairingExpand c φ l) = pairingExpand c (fun s => g (φ s)) l :=
  map_pairingExpand_aux c g l.length l le_rfl φ

/-! ## The exchange law -/

private theorem pairingExpand_positionSum_aux (c : α → α → K) :
    ∀ (n : ℕ) (t : List α), t.length ≤ n → ∀ (ψ : α → List α → M),
      pairingExpand c (fun s => positionSum s ψ) t
        = positionSum t (fun a s => pairingExpand c (ψ a) s) := by
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
        rw [pairingExpand_cons, positionSum_cons]
        have e1 : pairingExpand c (fun s => positionSum (w :: s) ψ) r
            = pairingExpand c (ψ w) r
              + positionSum r (fun a s => pairingExpand c (fun t' => ψ a (w :: t')) s) := by
          have hfun : (fun s => positionSum (w :: s) ψ)
              = fun s => ψ w s + positionSum s (fun b t' => ψ b (w :: t')) := by
            funext s
            exact positionSum_cons _ _ _
          rw [hfun, pairingExpand_add, ih r hr (fun b t' => ψ b (w :: t'))]
        have e2 : positionSum r (fun a s => c w a • pairingExpand c (fun s' => positionSum s' ψ) s)
            = positionSum r (fun a s => positionSum s
                (fun b t' => c w a • pairingExpand c (ψ b) t')) := by
          refine positionSum_congr' fun k => ?_
          show c w r[(k : ℕ)] • pairingExpand c (fun s' => positionSum s' ψ) (r.eraseIdx (k : ℕ))
              = positionSum (r.eraseIdx (k : ℕ))
                  (fun b t' => c w r[(k : ℕ)] • pairingExpand c (ψ b) t')
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) hr) ψ, ← positionSum_smul]
        have e3 : positionSum r (fun a s => pairingExpand c (ψ a) (w :: s))
            = positionSum r (fun a s => pairingExpand c (fun t' => ψ a (w :: t')) s)
              + positionSum r (fun a s => positionSum s
                  (fun b t' => c w b • pairingExpand c (ψ a) t')) := by
          rw [← positionSum_add]
          exact positionSum_congr fun a s => pairingExpand_cons _ _ _ _
        rw [e1, e2, e3,
          positionSum_swap r (fun a b t' => c w a • pairingExpand c (ψ b) t'), add_assoc]

/-- **The exchange law.**  Expanding a word and then marking a free letter of the residual word
enumerates the same data as marking a letter of the word and then expanding what is left. -/
theorem pairingExpand_positionSum (c : α → α → K) (ψ : α → List α → M) (t : List α) :
    pairingExpand c (fun s => positionSum s ψ) t
      = positionSum t (fun a s => pairingExpand c (ψ a) s) :=
  pairingExpand_positionSum_aux c t.length t le_rfl ψ

/-! ## Left multiplication -/

section Algebra

variable {A : Type w} [Semiring A] [Algebra K A]

private theorem mul_pairingExpand_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (x : A) (φ : List α → A),
      x * pairingExpand c φ l = pairingExpand c (fun s => x * φ s) l := by
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
        rw [pairingExpand_cons, pairingExpand_cons, mul_add, ih t ht x (fun s => φ (u :: s)),
          mul_positionSum]
        congr 1
        refine positionSum_congr' fun k => ?_
        show x * (c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ)))
            = c u t[(k : ℕ)] • pairingExpand c (fun s => x * φ s) (t.eraseIdx (k : ℕ))
        rw [Algebra.mul_smul_comm, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) x φ]

/-- Left multiplication passes through the expansion into the leftover functional. -/
theorem mul_pairingExpand (c : α → α → K) (x : A) (φ : List α → A) (l : List α) :
    x * pairingExpand c φ l = pairingExpand c (fun s => x * φ s) l :=
  mul_pairingExpand_aux c l.length l le_rfl x φ

end Algebra

/-! ## Collapse to the complete pairings -/

private theorem pairingExpand_eq_completePairing_aux (c : α → α → K) (φ : List α → K)
    (h0 : φ [] = 1) (hne : ∀ u t, φ (u :: t) = 0) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → pairingExpand c φ l = completePairing c l := by
  intro n
  induction n with
  | zero =>
      intro l hl
      match l with
      | [] => simpa using h0
      | (_ :: _) => simp at hl
  | succ n ih =>
      intro l hl
      match l with
      | [] => simpa using h0
      | (u :: t) =>
        have ht : t.length ≤ n := by simpa using hl
        have hz : pairingExpand c (fun s => φ (u :: s)) t = 0 := by
          rw [pairingExpand_congr (fun s => hne u s) t]
          exact pairingExpand_zero c t
        rw [pairingExpand_cons, hz, zero_add, completePairing_cons]
        refine positionSum_congr' fun k => ?_
        show c u t[(k : ℕ)] • pairingExpand c φ (t.eraseIdx (k : ℕ))
            = c u t[(k : ℕ)] * completePairing c (t.eraseIdx (k : ℕ))
        rw [smul_eq_mul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht)]

/-- **Only the complete pairings survive** when the leftover functional is normalised on the empty
word and vanishes on every nonempty one. -/
theorem pairingExpand_eq_completePairing (c : α → α → K) (φ : List α → K)
    (h0 : φ [] = 1) (hne : ∀ u t, φ (u :: t) = 0) (l : List α) :
    pairingExpand c φ l = completePairing c l :=
  pairingExpand_eq_completePairing_aux c φ h0 hne l.length l le_rfl

end GaloisForLFunctions.HTGeometry
