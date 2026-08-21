import GaloisForLFunctions.HTGeometry.ListSignedPositionSum

/-!
# Signed expansion over the partial pairings of a word

The fermionic analogue of `pairingExpand`: each contraction of the head with the letter at position
`k` of the tail carries the crossing sign `(-1) ^ k`,

```text
signedPairingExpand c φ []       = φ []
signedPairingExpand c φ (u :: t) = signedPairingExpand c (fun s => φ (u :: s)) t
                                   + ∑ k, (-1) ^ k • c u t[k] • signedPairingExpand c φ (t.eraseIdx k)
```

The scalar shadow, obtained when `φ` is supported on the empty word, is the **Pfaffian** expansion
`pfaffianPairing`: the signed sum over the perfect matchings of the word.

Although the individual terms carry signs, the exchange law holds in exactly the same form as in the
unsigned case — the antisymmetry of `signedPositionSum_swap` cancels the sign produced by the
head/tail recursion of `signedPositionSum`.
-/

universe u v w x

namespace GaloisForLFunctions.HTGeometry

variable {α : Type u} {M : Type w}

/-- The Pfaffian expansion: the signed sum over the perfect matchings of a word. -/
def pfaffianPairing (K : Type v) [CommRing K] (c : α → α → K) : List α → K
  | [] => 1
  | (u :: t) => ∑ k : Fin t.length,
      (-1 : K) ^ (k : ℕ) * (c u t[(k : ℕ)] * pfaffianPairing K c (t.eraseIdx (k : ℕ)))
termination_by l => l.length
decreasing_by
  have h := List.length_eraseIdx_le t (k : ℕ)
  simp only [List.length_cons]
  omega

/-- **The signed partial-pairing expansion of a word.** -/
def signedPairingExpand (K : Type v) [CommRing K] [AddCommGroup M] [Module K M]
    (c : α → α → K) (φ : List α → M) : List α → M
  | [] => φ []
  | (u :: t) => signedPairingExpand K c (fun s => φ (u :: s)) t
      + ∑ k : Fin t.length, (-1 : K) ^ (k : ℕ) •
          (c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ)))
termination_by l => l.length
decreasing_by
  · simp
  · have h := List.length_eraseIdx_le t (k : ℕ)
    simp only [List.length_cons]
    omega

variable {K : Type v} [CommRing K] [AddCommGroup M] [Module K M]

@[simp] theorem pfaffianPairing_nil (c : α → α → K) : pfaffianPairing K c [] = 1 := by
  rw [pfaffianPairing]

theorem pfaffianPairing_cons (c : α → α → K) (u : α) (t : List α) :
    pfaffianPairing K c (u :: t)
      = signedPositionSum K t (fun a s => c u a * pfaffianPairing K c s) := by
  rw [pfaffianPairing]
  rfl

@[simp] theorem signedPairingExpand_nil (c : α → α → K) (φ : List α → M) :
    signedPairingExpand K c φ [] = φ [] := by
  rw [signedPairingExpand]

theorem signedPairingExpand_cons (c : α → α → K) (φ : List α → M) (u : α) (t : List α) :
    signedPairingExpand K c φ (u :: t)
      = signedPairingExpand K c (fun s => φ (u :: s)) t
        + signedPositionSum K t (fun a s => c u a • signedPairingExpand K c φ s) := by
  rw [signedPairingExpand]
  rfl

/-! ## Linearity in the leftover functional -/

private theorem signedPairingExpand_zero_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → signedPairingExpand K c (fun _ => (0 : M)) l = 0 := by
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
        rw [signedPairingExpand_cons, ih t ht, zero_add]
        simp only [signedPositionSum]
        refine Finset.sum_eq_zero fun k _ => ?_
        rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht), smul_zero, smul_zero]

@[simp] theorem signedPairingExpand_zero (c : α → α → K) (l : List α) :
    signedPairingExpand K c (fun _ => (0 : M)) l = 0 :=
  signedPairingExpand_zero_aux c l.length l le_rfl

private theorem signedPairingExpand_sub_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (φ ψ : List α → M),
      signedPairingExpand K c (fun s => φ s - ψ s) l
        = signedPairingExpand K c φ l - signedPairingExpand K c ψ l := by
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
        rw [signedPairingExpand_cons, signedPairingExpand_cons, signedPairingExpand_cons,
          ih t ht (fun s => φ (u :: s)) (fun s => ψ (u :: s))]
        have hsum : signedPositionSum K t (fun a s =>
              c u a • signedPairingExpand K c (fun s' => φ s' - ψ s') s)
            = signedPositionSum K t (fun a s => c u a • signedPairingExpand K c φ s)
              - signedPositionSum K t (fun a s => c u a • signedPairingExpand K c ψ s) := by
          rw [← signedPositionSum_sub]
          refine signedPositionSum_congr' fun k => ?_
          show c u t[(k : ℕ)] • signedPairingExpand K c (fun s' => φ s' - ψ s') (t.eraseIdx (k : ℕ))
              = c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ))
                - c u t[(k : ℕ)] • signedPairingExpand K c ψ (t.eraseIdx (k : ℕ))
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ ψ, smul_sub]
        rw [hsum]
        abel

theorem signedPairingExpand_sub (c : α → α → K) (φ ψ : List α → M) (l : List α) :
    signedPairingExpand K c (fun s => φ s - ψ s) l
      = signedPairingExpand K c φ l - signedPairingExpand K c ψ l :=
  signedPairingExpand_sub_aux c l.length l le_rfl φ ψ

private theorem signedPairingExpand_add_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (φ ψ : List α → M),
      signedPairingExpand K c (fun s => φ s + ψ s) l
        = signedPairingExpand K c φ l + signedPairingExpand K c ψ l := by
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
        rw [signedPairingExpand_cons, signedPairingExpand_cons, signedPairingExpand_cons,
          ih t ht (fun s => φ (u :: s)) (fun s => ψ (u :: s))]
        have hsum : signedPositionSum K t (fun a s =>
              c u a • signedPairingExpand K c (fun s' => φ s' + ψ s') s)
            = signedPositionSum K t (fun a s => c u a • signedPairingExpand K c φ s)
              + signedPositionSum K t (fun a s => c u a • signedPairingExpand K c ψ s) := by
          rw [← signedPositionSum_add]
          refine signedPositionSum_congr' fun k => ?_
          show c u t[(k : ℕ)] • signedPairingExpand K c (fun s' => φ s' + ψ s') (t.eraseIdx (k : ℕ))
              = c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ))
                + c u t[(k : ℕ)] • signedPairingExpand K c ψ (t.eraseIdx (k : ℕ))
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ ψ, smul_add]
        rw [hsum]
        abel

theorem signedPairingExpand_add (c : α → α → K) (φ ψ : List α → M) (l : List α) :
    signedPairingExpand K c (fun s => φ s + ψ s) l
      = signedPairingExpand K c φ l + signedPairingExpand K c ψ l :=
  signedPairingExpand_add_aux c l.length l le_rfl φ ψ

private theorem signedPairingExpand_smul_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (b : K) (φ : List α → M),
      signedPairingExpand K c (fun s => b • φ s) l = b • signedPairingExpand K c φ l := by
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
        rw [signedPairingExpand_cons, signedPairingExpand_cons, ih t ht b (fun s => φ (u :: s))]
        have hsum : signedPositionSum K t
              (fun a s => c u a • signedPairingExpand K c (fun s' => b • φ s') s)
            = b • signedPositionSum K t (fun a s => c u a • signedPairingExpand K c φ s) := by
          rw [← signedPositionSum_smul]
          refine signedPositionSum_congr' fun k => ?_
          show c u t[(k : ℕ)] • signedPairingExpand K c (fun s' => b • φ s') (t.eraseIdx (k : ℕ))
              = b • (c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ)))
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) b φ, smul_comm]
        rw [hsum, smul_add]

theorem signedPairingExpand_smul (c : α → α → K) (b : K) (φ : List α → M) (l : List α) :
    signedPairingExpand K c (fun s => b • φ s) l = b • signedPairingExpand K c φ l :=
  signedPairingExpand_smul_aux c l.length l le_rfl b φ

theorem signedPairingExpand_congr {c : α → α → K} {φ ψ : List α → M} (h : ∀ s, φ s = ψ s)
    (l : List α) : signedPairingExpand K c φ l = signedPairingExpand K c ψ l := by
  have : φ = ψ := funext h
  rw [this]

/-! ## Transport along a linear map -/

private theorem map_signedPairingExpand_aux {N : Type x} [AddCommGroup N] [Module K N]
    (c : α → α → K) (g : M →ₗ[K] N) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ φ : List α → M,
      g (signedPairingExpand K c φ l) = signedPairingExpand K c (fun s => g (φ s)) l := by
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
        rw [signedPairingExpand_cons, signedPairingExpand_cons, map_add,
          ih t ht (fun s => φ (u :: s)), map_signedPositionSum]
        congr 1
        refine signedPositionSum_congr' fun k => ?_
        show g (c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ)))
            = c u t[(k : ℕ)] • signedPairingExpand K c (fun s => g (φ s)) (t.eraseIdx (k : ℕ))
        rw [map_smul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) φ]

theorem map_signedPairingExpand {N : Type x} [AddCommGroup N] [Module K N] (c : α → α → K)
    (g : M →ₗ[K] N) (φ : List α → M) (l : List α) :
    g (signedPairingExpand K c φ l) = signedPairingExpand K c (fun s => g (φ s)) l :=
  map_signedPairingExpand_aux c g l.length l le_rfl φ

/-! ## The exchange law -/

private theorem signedPairingExpand_signedPositionSum_aux (c : α → α → K) :
    ∀ (n : ℕ) (t : List α), t.length ≤ n → ∀ (ψ : α → List α → M),
      signedPairingExpand K c (fun s => signedPositionSum K s ψ) t
        = signedPositionSum K t (fun a s => signedPairingExpand K c (ψ a) s) := by
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
        rw [signedPairingExpand_cons, signedPositionSum_cons]
        have e1 : signedPairingExpand K c (fun s => signedPositionSum K (w :: s) ψ) r
            = signedPairingExpand K c (ψ w) r
              - signedPositionSum K r
                  (fun a s => signedPairingExpand K c (fun t' => ψ a (w :: t')) s) := by
          have hfun : (fun s => signedPositionSum K (w :: s) ψ)
              = fun s => ψ w s - signedPositionSum K s (fun b t' => ψ b (w :: t')) := by
            funext s
            exact signedPositionSum_cons _ _ _
          rw [hfun, signedPairingExpand_sub, ih r hr (fun b t' => ψ b (w :: t'))]
        have e2 : signedPositionSum K r (fun a s =>
              c w a • signedPairingExpand K c (fun s' => signedPositionSum K s' ψ) s)
            = signedPositionSum K r (fun a s => signedPositionSum K s
                (fun b t' => c w a • signedPairingExpand K c (ψ b) t')) := by
          refine signedPositionSum_congr' fun k => ?_
          show c w r[(k : ℕ)] •
                signedPairingExpand K c (fun s' => signedPositionSum K s' ψ) (r.eraseIdx (k : ℕ))
              = signedPositionSum K (r.eraseIdx (k : ℕ))
                  (fun b t' => c w r[(k : ℕ)] • signedPairingExpand K c (ψ b) t')
          rw [ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) hr) ψ, ← signedPositionSum_smul]
        have e3 : signedPositionSum K r (fun a s => signedPairingExpand K c (ψ a) (w :: s))
            = signedPositionSum K r
                (fun a s => signedPairingExpand K c (fun t' => ψ a (w :: t')) s)
              + signedPositionSum K r (fun a s => signedPositionSum K s
                  (fun b t' => c w b • signedPairingExpand K c (ψ a) t')) := by
          rw [← signedPositionSum_add]
          exact signedPositionSum_congr fun a s => signedPairingExpand_cons _ _ _ _
        rw [e1, e2, e3,
          signedPositionSum_swap r (fun a b t' => c w a • signedPairingExpand K c (ψ b) t')]
        abel

/-- **The exchange law**, in the same form as in the unsigned case: the antisymmetry of the signed
position sum cancels the sign of its head/tail recursion. -/
theorem signedPairingExpand_signedPositionSum (c : α → α → K) (ψ : α → List α → M) (t : List α) :
    signedPairingExpand K c (fun s => signedPositionSum K s ψ) t
      = signedPositionSum K t (fun a s => signedPairingExpand K c (ψ a) s) :=
  signedPairingExpand_signedPositionSum_aux c t.length t le_rfl ψ

/-! ## Left multiplication -/

section Algebra

variable {A : Type w} [Ring A] [Algebra K A]

private theorem mul_signedPairingExpand_aux (c : α → α → K) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n → ∀ (x : A) (φ : List α → A),
      x * signedPairingExpand K c φ l = signedPairingExpand K c (fun s => x * φ s) l := by
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
        rw [signedPairingExpand_cons, signedPairingExpand_cons, mul_add,
          ih t ht x (fun s => φ (u :: s)), mul_signedPositionSum]
        congr 1
        refine signedPositionSum_congr' fun k => ?_
        show x * (c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ)))
            = c u t[(k : ℕ)] • signedPairingExpand K c (fun s => x * φ s) (t.eraseIdx (k : ℕ))
        rw [Algebra.mul_smul_comm, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht) x φ]

theorem mul_signedPairingExpand (c : α → α → K) (x : A) (φ : List α → A) (l : List α) :
    x * signedPairingExpand K c φ l = signedPairingExpand K c (fun s => x * φ s) l :=
  mul_signedPairingExpand_aux c l.length l le_rfl x φ

end Algebra

/-! ## Collapse to the Pfaffian -/

private theorem signedPairingExpand_eq_pfaffianPairing_aux (c : α → α → K) (φ : List α → K)
    (h0 : φ [] = 1) (hne : ∀ u t, φ (u :: t) = 0) :
    ∀ (n : ℕ) (l : List α), l.length ≤ n →
      signedPairingExpand K c φ l = pfaffianPairing K c l := by
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
        have hz : signedPairingExpand K c (fun s => φ (u :: s)) t = 0 := by
          rw [signedPairingExpand_congr (fun s => hne u s) t]
          exact signedPairingExpand_zero c t
        rw [signedPairingExpand_cons, hz, zero_add, pfaffianPairing_cons]
        refine signedPositionSum_congr' fun k => ?_
        show c u t[(k : ℕ)] • signedPairingExpand K c φ (t.eraseIdx (k : ℕ))
            = c u t[(k : ℕ)] * pfaffianPairing K c (t.eraseIdx (k : ℕ))
        rw [smul_eq_mul, ih _ (le_trans (le_of_lt (length_eraseIdx_lt k)) ht)]

/-- **Only the complete pairings survive**, with their crossing signs: the Pfaffian. -/
theorem signedPairingExpand_eq_pfaffianPairing (c : α → α → K) (φ : List α → K)
    (h0 : φ [] = 1) (hne : ∀ u t, φ (u :: t) = 0) (l : List α) :
    signedPairingExpand K c φ l = pfaffianPairing K c l :=
  signedPairingExpand_eq_pfaffianPairing_aux c φ h0 hne l.length l le_rfl

end GaloisForLFunctions.HTGeometry
