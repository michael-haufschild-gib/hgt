import Mathlib

/-!
# The deletion sieve identity

Deleting a set `B` of primes from the rational primes leaves the generalized number system whose
integers are the `B`-free integers.  Its counting function is given exactly by inclusion–exclusion
over the squarefree products of elements of `B`:

```
#{ n ≤ x : no p ∈ B divides n }  =  ∑_{S ⊆ B} (-1)^{|S|} ⌊x / ∏_{p ∈ S} p⌋.
```

This finite identity is an input to deletion error analysis.  It supplies no asymptotic bound on
the squarefree products, no probabilistic cancellation estimate, and no exponent below `1/2`.

The proof is induction on `B`; the only arithmetic input is that the multiples of `d` in `[1,x]`
number `x / d`, and that for `q ∉ S` the map `m ↦ q * m` identifies the `S`-free integers `≤ x / q`
with the `S`-free multiples of `q` in `[1, x]`.
-/

open Finset

namespace RHTower.ThinDeletion

/-- The `B`-free integers in `[1, x]`. -/
def freeCount (B : Finset ℕ) (x : ℕ) : ℕ :=
  ((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).card

/-- Multiples of `d` in `[1, x]` number `x / d`. -/
theorem card_multiples {d : ℕ} (hd : 0 < d) (x : ℕ) :
    ((Finset.Icc 1 x).filter (fun n => d ∣ n)).card = x / d := by
  classical
  have himg : (Finset.Icc 1 x).filter (fun n => d ∣ n) =
      (Finset.Icc 1 (x / d)).image (fun m => d * m) := by
    ext n
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨h1, h2⟩, m, rfl⟩
      refine ⟨m, ⟨?_, ?_⟩, rfl⟩
      · rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp at h1
        · exact hm
      · exact (Nat.le_div_iff_mul_le hd).mpr (by rw [Nat.mul_comm]; exact h2)
    · rintro ⟨m, ⟨hm1, hm2⟩, rfl⟩
      refine ⟨⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
      · calc d * m ≤ d * (x / d) := Nat.mul_le_mul_left d hm2
          _ ≤ x := Nat.mul_div_le x d
  rw [himg, Finset.card_image_of_injective _ (fun a b h => by
    exact Nat.eq_of_mul_eq_mul_left hd h), Nat.card_Icc]
  simp

/-- Splitting off one prime: the `insert q B`-free integers are the `B`-free integers minus the
`B`-free multiples of `q`, and the latter are counted by `freeCount B (x / q)`. -/
theorem freeCount_insert {q : ℕ} (hq : 0 < q) {B : Finset ℕ}
    (hcop : ∀ p ∈ B, Nat.Coprime q p) (x : ℕ) :
    freeCount (insert q B) x + freeCount B (x / q) = freeCount B x := by
  classical
  have hsplit := Finset.card_filter_add_card_filter_not
      (s := (Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)) (fun n => q ∣ n)
  have hleft :
      (((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).filter (fun n => ¬ q ∣ n)) =
        (Finset.Icc 1 x).filter (fun n => ∀ p ∈ insert q B, ¬ p ∣ n) := by
    ext n
    simp only [mem_filter, mem_insert, forall_eq_or_imp]
    tauto
  have hright :
      (((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).filter (fun n => q ∣ n)).card =
        freeCount B (x / q) := by
    have himg :
        (((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).filter (fun n => q ∣ n)) =
          ((Finset.Icc 1 (x / q)).filter (fun m => ∀ p ∈ B, ¬ p ∣ m)).image (fun m => q * m) := by
      ext n
      simp only [mem_filter, mem_Icc, mem_image]
      constructor
      · rintro ⟨⟨⟨h1, h2⟩, hB⟩, m, rfl⟩
        have hm0 : 0 < m := by
          rcases Nat.eq_zero_or_pos m with rfl | hm
          · simp at h1
          · exact hm
        refine ⟨m, ⟨⟨hm0, (Nat.le_div_iff_mul_le hq).mpr (by rw [Nat.mul_comm]; exact h2)⟩,
          ?_⟩, rfl⟩
        intro p hp hdvd
        exact hB p hp (hdvd.mul_left q)
      · rintro ⟨m, ⟨⟨hm1, hm2⟩, hmB⟩, rfl⟩
        refine ⟨⟨⟨Nat.one_le_iff_ne_zero.mpr (by positivity), ?_⟩, ?_⟩, ⟨m, rfl⟩⟩
        · calc q * m ≤ q * (x / q) := Nat.mul_le_mul_left q hm2
            _ ≤ x := Nat.mul_div_le x q
        · intro p hp hdvd
          exact hmB p hp ((Nat.Coprime.dvd_of_dvd_mul_left (hcop p hp).symm) hdvd)
    rw [himg, Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hq h)]
    rfl
  have hleftcard : (((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).filter
      (fun n => ¬ q ∣ n)).card = freeCount (insert q B) x := by
    rw [hleft]
    rfl
  rw [← hleftcard, ← hright]
  show _ = ((Finset.Icc 1 x).filter (fun n => ∀ p ∈ B, ¬ p ∣ n)).card
  omega

/-- **The deletion sieve identity.**  For a finite set `B` of pairwise coprime moduli, the number of
`B`-free integers in `[1, x]` is the alternating sum over subsets of `B` of `⌊x / ∏ S⌋`.

The right-hand side ranges over subset products of `B`.  A sparsity or cancellation estimate for
an increasing family of such sets is a separate obligation. -/
theorem freeCount_eq_sum :
    ∀ B : Finset ℕ, (∀ p ∈ B, 0 < p) → ((B : Set ℕ).Pairwise Nat.Coprime) →
      ∀ x : ℕ, (freeCount B x : ℤ) =
        ∑ S ∈ B.powerset, (-1 : ℤ) ^ S.card * ((x / ∏ p ∈ S, p : ℕ) : ℤ) := by
  classical
  intro B
  induction B using Finset.induction_on with
  | empty => intro _ _ x; simp [freeCount]
  | insert q B hqB ih =>
    intro hpos hcop
    have hq : 0 < q := hpos q (Finset.mem_insert_self q B)
    have hposB : ∀ p ∈ B, 0 < p := fun p hp => hpos p (Finset.mem_insert_of_mem hp)
    have hcopB : ((B : Set ℕ).Pairwise Nat.Coprime) :=
      Set.Pairwise.mono (by intro a ha; exact Finset.mem_insert_of_mem ha) hcop
    have hqcop : ∀ p ∈ B, Nat.Coprime q p := by
      intro p hp
      refine hcop (by simp) (by simp [hp]) ?_
      rintro rfl
      exact hqB hp
    intro x
    have hins := freeCount_insert (q := q) hq (B := B) hqcop x
    rw [Finset.sum_powerset_insert hqB]
    have hstep : ∀ S ∈ B.powerset,
        (-1 : ℤ) ^ (insert q S).card * ((x / ∏ p ∈ insert q S, p : ℕ) : ℤ) =
          -((-1 : ℤ) ^ S.card * ((x / q / ∏ p ∈ S, p : ℕ) : ℤ)) := by
      intro S hS
      have hqS : q ∉ S := fun h => hqB (Finset.mem_powerset.mp hS h)
      rw [Finset.card_insert_of_notMem hqS, Finset.prod_insert hqS, pow_succ,
        Nat.div_div_eq_div_mul]
      ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_neg_distrib,
      ← ih hposB hcopB x, ← ih hposB hcopB (x / q)]
    omega

end RHTower.ThinDeletion
