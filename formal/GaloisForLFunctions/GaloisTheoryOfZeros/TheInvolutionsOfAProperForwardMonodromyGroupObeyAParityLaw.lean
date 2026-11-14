import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupHasIndexAtMostTwoInTheSignedPermutationsOfFiniteSupport
import GaloisForLFunctions.GaloisTheoryOfZeros.TheForwardMonodromyGroupIsTransitiveOnTheZeros

/-!
# The involutions of a proper forward monodromy group obey a parity law

An involution `σ` of the zeros that commutes with `z ↦ −z` and moves finitely many zeros is a
product of `a` sign flips of pairs and `b` exchanges of two pairs, with disjoint supports: it
carries `2a` zeros to their negatives and moves `2a + 4b` zeros.

* **Abstract form** (`exists_flips_exchanges_parity`). Let `G` be a group of permutations with
  `w₁ ∈ G` or `w₂ ∈ G` or `w₁w₂⁻¹ ∈ G` for all signed permutations of finite support, without
  an exchange of two pairs, and let `ε = 0` if `G` contains the flips of single pairs and
  `ε = 1` if it contains none. Then `σ ∈ G` if and only if `b + εa` is even.
* **The forward monodromy group** (`exists_parity_of_not_mem_forwardMonodromy`). If `G₊(b)` is
  not the group of all signed permutations of finite support, there is `ε ∈ {0, 1}` such that
  every involution in `G₊(b)` with `2a` flipped and `2a + 4c` moved zeros has `c + εa` even.

Proof. Cut `σ` along the orbit `T = {z, σz, −z, −σz}` of a moved zero: `σ = σ'τ` with `τ = σ` on
`T` and the identity elsewhere. `τ` is a flip when `σz = −z` and an exchange otherwise. An
exchange is not in `G`, and a flip is in `G` exactly when `ε = 0`; index two turns the class of
`τ` into the parity. Induct on the number of moved zeros. For `G₊` the flips of single pairs are
conjugate in `G₊`, which is transitive on the zeros, so all of them lie in `G₊` or none does.
-/

open Equiv

namespace GaloisForLFunctions.GaloisTheoryOfZeros

set_option autoImplicit false

/-! ## Cutting an involution along an invariant set -/

section Abstract

variable {X : Type*}

/-- **An involution splits along an invariant set.** If `σ² = 1` and `σ` preserves `T`, then
`σ = σ'τ` with `τ = σ` on `T`, `τ = 1` off `T`, `σ' = 1` on `T`, `σ' = σ` off `T`. -/
theorem exists_split_involution {σ : Perm X} (hσ : ∀ x, σ (σ x) = x) (T : Set X)
    (hT : ∀ x ∈ T, σ x ∈ T) :
    ∃ σ' τ : Perm X, σ = σ' * τ ∧ (∀ x ∈ T, τ x = σ x) ∧ (∀ x, x ∉ T → τ x = x) ∧
      (∀ x ∈ T, σ' x = x) ∧ (∀ x, x ∉ T → σ' x = σ x) := by
  classical
  have hT' : ∀ x, x ∉ T → σ x ∉ T := fun x hx h => hx (by
    have h1 := hT _ h
    rwa [hσ] at h1)
  have h1 : Function.Involutive fun x => if x ∈ T then x else σ x := fun x => by
    show (if (if x ∈ T then x else σ x) ∈ T then (if x ∈ T then x else σ x)
      else σ (if x ∈ T then x else σ x)) = x
    by_cases h : x ∈ T
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg (hT' x h), hσ]
  have h2 : Function.Involutive fun x => if x ∈ T then σ x else x := fun x => by
    show (if (if x ∈ T then σ x else x) ∈ T then σ (if x ∈ T then σ x else x)
      else (if x ∈ T then σ x else x)) = x
    by_cases h : x ∈ T
    · rw [if_pos h, if_pos (hT x h), hσ]
    · rw [if_neg h, if_neg h]
  refine ⟨Function.Involutive.toPerm _ h1, Function.Involutive.toPerm _ h2,
    Perm.ext fun x => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
  · show σ x = (if (if x ∈ T then σ x else x) ∈ T then (if x ∈ T then σ x else x)
      else σ (if x ∈ T then σ x else x))
    by_cases h : x ∈ T
    · rw [if_pos h, if_pos (hT x h)]
    · rw [if_neg h, if_neg h]
  · show (if x ∈ T then σ x else x) = σ x
    rw [if_pos hx]
  · show (if x ∈ T then σ x else x) = x
    rw [if_neg hx]
  · show (if x ∈ T then x else σ x) = x
    rw [if_pos hx]
  · show (if x ∈ T then x else σ x) = σ x
    rw [if_neg hx]

variable {G : Subgroup (Perm X)}

/-- In a group of index at most two, multiplying by an involution outside the group changes the
class. -/
theorem mem_iff_not_mem_of_eq_mul {σ σ' τ : Perm X} (hστ : σ = σ' * τ) (hτ2 : τ * τ = 1)
    (hτG : τ ∉ G) (hor : σ' ∈ G ∨ τ ∈ G ∨ σ' * τ⁻¹ ∈ G) : σ ∈ G ↔ σ' ∉ G := by
  have hinv : τ⁻¹ = τ := inv_eq_of_mul_eq_one_left hτ2
  constructor
  · intro hσ hσ'
    rw [hστ] at hσ
    exact hτG ((G.mul_mem_cancel_left hσ').mp hσ)
  · intro hσ'
    rcases hor with h | h | h
    · exact absurd h hσ'
    · exact absurd h hτG
    · rw [hστ, ← hinv]
      exact h

variable {n : Perm X} {ε : ℕ}

/-- **The parity of an involution.** Let `G` have index at most two on the signed permutations
of finite support, contain no exchange of two pairs, and contain the flips of single pairs
exactly when `ε = 0`. An involution `σ` that commutes with the reflection `n` and moves `N`
points carries `2a` points to their reflections, `N = 2a + 4b`, and `σ ∈ G` if and only if
`b + εa` is even. -/
theorem exists_flips_exchanges_parity (hn : ∀ x, n (n x) = x) (hn0 : ∀ x, n x ≠ x)
    (hA : ∀ w₁ w₂ : Perm X, (∀ x, w₁ (n x) = n (w₁ x)) → {x | w₁ x ≠ x}.Finite →
      (∀ x, w₂ (n x) = n (w₂ x)) → {x | w₂ x ≠ x}.Finite →
      w₁ ∈ G ∨ w₂ ∈ G ∨ w₁ * w₂⁻¹ ∈ G)
    (hE : ∀ (e : Perm X) (a a' : X), a' ≠ a → a' ≠ n a → e a = a' → e a' = a →
      (∀ x, e (n x) = n (e x)) → (∀ x, x ≠ a → x ≠ n a → x ≠ a' → x ≠ n a' → e x = x) → e ∉ G)
    (hε : ε = 0 ∨ ε = 1)
    (hF : ∀ (f : Perm X) (a : X), f a = n a → (∀ x, f (n x) = n (f x)) →
      (∀ x, x ≠ a → x ≠ n a → f x = x) → (f ∈ G ↔ ε = 0)) :
    ∀ (N : ℕ) (σ : Perm X), (∀ x, σ (σ x) = x) → (∀ x, σ (n x) = n (σ x)) →
      ∀ s : Finset X, (∀ x, x ∈ s ↔ σ x ≠ x) → s.card = N →
        ∃ a b : ℕ, {x | σ x = n x}.ncard = 2 * a ∧ N = 2 * a + 4 * b ∧
          (σ ∈ G ↔ Even (b + ε * a)) := by
  classical
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
  intro σ hσ hσn s hs hcard
  by_cases hN : s = ∅
  · -- no moved point: `σ = 1`
    have h1 : σ = 1 := Perm.ext fun x => by
      by_contra h
      have h2 := (hs x).2 h
      rw [hN] at h2
      exact absurd h2 (Finset.notMem_empty x)
    refine ⟨0, 0, ?_, ?_, ?_⟩
    · have h2 : {x | σ x = n x} = ∅ := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rw [h1]
        exact fun h => hn0 x h.symm
      rw [h2, Set.ncard_empty]
    · rw [← hcard, hN, Finset.card_empty]
    · rw [h1]
      exact ⟨fun _ => ⟨0, by ring⟩, fun _ => G.one_mem⟩
  obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hN
  have hzm : σ z ≠ z := (hs z).1 hz
  have hninj : ∀ {x y : X}, n x = n y → x = y := fun h => n.injective h
  -- the orbit of `z` under `σ` and the reflection
  obtain ⟨T, hTdef⟩ : ∃ T : Finset X, T = {z, σ z, n z, n (σ z)} := ⟨_, rfl⟩
  have hmemT : ∀ x, x ∈ T ↔ x = z ∨ x = σ z ∨ x = n z ∨ x = n (σ z) := fun x => by
    rw [hTdef]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  have hT : ∀ x ∈ (T : Set X), σ x ∈ (T : Set X) := by
    intro x hx
    rw [Finset.mem_coe, hmemT] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inl (hσ _)
    · exact Or.inr (Or.inr (Or.inr (hσn _)))
    · exact Or.inr (Or.inr (Or.inl (by rw [hσn, hσ])))
  have hTn : ∀ x, x ∈ T → n x ∈ T := by
    intro x hx
    rw [hmemT] at hx ⊢
    rcases hx with rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inl (hn _)
    · exact Or.inr (Or.inl (hn _))
  have hTn' : ∀ x, x ∉ T → n x ∉ T := fun x hx h => hx (by
    have h1 := hTn _ h
    rwa [hn] at h1)
  have hT' : ∀ x, x ∉ T → σ x ∉ T := fun x hx h => hx (by
    have h1 := hT _ (Finset.mem_coe.mpr h)
    rw [hσ] at h1
    exact Finset.mem_coe.mp h1)
  obtain ⟨σ', τ, hστ, hτT, hτo, hσ'T, hσ'o⟩ := exists_split_involution hσ (T : Set X) hT
  have hτT' : ∀ x, x ∈ T → τ x = σ x := fun x hx => hτT x (Finset.mem_coe.mpr hx)
  have hτo' : ∀ x, x ∉ T → τ x = x := fun x hx => hτo x (fun h => hx (Finset.mem_coe.mp h))
  have hσ'T' : ∀ x, x ∈ T → σ' x = x := fun x hx => hσ'T x (Finset.mem_coe.mpr hx)
  have hσ'o' : ∀ x, x ∉ T → σ' x = σ x := fun x hx =>
    hσ'o x (fun h => hx (Finset.mem_coe.mp h))
  -- the two factors are signed involutions of finite support
  have hσ'2 : ∀ x, σ' (σ' x) = x := fun x => by
    by_cases hx : x ∈ T
    · rw [hσ'T' x hx, hσ'T' x hx]
    · rw [hσ'o' x hx, hσ'o' _ (hT' x hx), hσ]
  have hσ'n : ∀ x, σ' (n x) = n (σ' x) := fun x => by
    by_cases hx : x ∈ T
    · rw [hσ'T' _ (hTn x hx), hσ'T' x hx]
    · rw [hσ'o' _ (hTn' x hx), hσ'o' x hx, hσn]
  have hτ2 : τ * τ = 1 := Perm.ext fun x => by
    show τ (τ x) = x
    by_cases hx : x ∈ T
    · rw [hτT' x hx, hτT' _ (Finset.mem_coe.mp (hT x (Finset.mem_coe.mpr hx))), hσ]
    · rw [hτo' x hx, hτo' x hx]
  have hτn : ∀ x, τ (n x) = n (τ x) := fun x => by
    by_cases hx : x ∈ T
    · rw [hτT' _ (hTn x hx), hτT' x hx, hσn]
    · rw [hτo' _ (hTn' x hx), hτo' x hx]
  have hτfin : {x | τ x ≠ x}.Finite :=
    T.finite_toSet.subset fun x hx => by
      by_contra h
      exact hx (hτo' x fun h' => h (Finset.mem_coe.mpr h'))
  -- the moved points of `σ'`
  have hs' : ∀ x, x ∈ s \ T ↔ σ' x ≠ x := fun x => by
    rw [Finset.mem_sdiff]
    by_cases hx : x ∈ T
    · exact ⟨fun h => absurd hx h.2, fun h => absurd (hσ'T' x hx) h⟩
    · rw [hσ'o' x hx, hs x]
      exact ⟨fun h => h.1, fun h => ⟨h, hx⟩⟩
  have hσ'fin : {x | σ' x ≠ x}.Finite :=
    (s \ T).finite_toSet.subset fun x hx => Finset.mem_coe.mpr ((hs' x).2 hx)
  have hTs : T ⊆ s := by
    intro x hx
    rw [hs x]
    rw [hmemT] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hzm
    · rw [hσ]
      exact hzm.symm
    · rw [hσn]
      exact fun h => hzm (hninj h)
    · rw [hσn, hσ]
      exact fun h => hzm (hninj h).symm
  have hcard' : (s \ T).card + T.card = N := by
    rw [Finset.card_sdiff_add_card_eq_card hTs, hcard]
  have hor := hA σ' τ hσ'n hσ'fin hτn hτfin
  have hzT : z ∈ T := (hmemT z).2 (Or.inl rfl)
  by_cases hfl : σ z = n z
  · -- the orbit is one pair and `τ` is its flip
    have hTeq : T = {z, n z} := by
      ext x
      rw [hmemT, Finset.mem_insert, Finset.mem_singleton, hfl, hn]
      tauto
    have hT2 : T.card = 2 := by
      rw [hTeq]
      exact Finset.card_pair (hn0 z).symm
    obtain ⟨a', b', hF', hN', hG'⟩ :=
      ih (s \ T).card (by omega) σ' hσ'2 hσ'n (s \ T) hs' rfl
    have hτG := hF τ z (by rw [hτT' z hzT, hfl]) hτn (fun x h1 h2 => hτo' x (by
      rw [hTeq, Finset.mem_insert, Finset.mem_singleton]
      exact fun h => h.elim h1 h2))
    refine ⟨a' + 1, b', ?_, by omega, ?_⟩
    · -- the flipped points of `σ` are those of `σ'` and the pair of `z`
      have hfin' : {x | σ' x = n x}.Finite :=
        hσ'fin.subset fun x hx h => hn0 x (by rw [← hx, h])
      have hset : {x | σ x = n x} = insert z (insert (n z) {x | σ' x = n x}) := by
        ext x
        simp only [Set.mem_setOf_eq, Set.mem_insert_iff]
        by_cases hx : x ∈ T
        · have hx' := hx
          rw [hTeq, Finset.mem_insert, Finset.mem_singleton] at hx'
          rcases hx' with rfl | rfl
          · exact ⟨fun _ => Or.inl rfl, fun _ => hfl⟩
          · exact ⟨fun _ => Or.inr (Or.inl rfl), fun _ => by rw [hσn, hfl]⟩
        · rw [hσ'o' x hx]
          constructor
          · exact fun h => Or.inr (Or.inr h)
          · rintro (rfl | rfl | h)
            · exact absurd hzT hx
            · exact absurd (hTn _ hzT) hx
            · exact h
      have hz1 : n z ∉ {x | σ' x = n x} := fun h => by
        have h1 : σ' (n z) = n (n z) := h
        rw [hσ'T' _ (hTn z hzT)] at h1
        exact hn0 (n z) h1.symm
      have hz2 : z ∉ insert (n z) {x | σ' x = n x} := by
        rintro (h | h)
        · exact hn0 z h.symm
        · have h1 : σ' z = n z := h
          rw [hσ'T' z hzT] at h1
          exact hn0 z h1.symm
      rw [hset, Set.ncard_insert_of_notMem hz2 (hfin'.insert _),
        Set.ncard_insert_of_notMem hz1 hfin', hF']
      ring
    · rcases hε with rfl | rfl
      · have hτmem : τ ∈ G := hτG.2 rfl
        rw [hστ, G.mul_mem_cancel_right hτmem, hG']
        simp only [Nat.zero_mul, Nat.add_zero]
      · have hτnot : τ ∉ G := fun h => absurd (hτG.1 h) one_ne_zero
        rw [mem_iff_not_mem_of_eq_mul hστ hτ2 hτnot hor, hG',
          show b' + 1 * (a' + 1) = b' + 1 * a' + 1 by ring, Nat.even_add_one]
  · -- the orbit is two pairs and `τ` is their exchange
    have hz3 : z ≠ n (σ z) := fun h => hfl (by
      have h1 := congrArg n h
      rw [hn] at h1
      exact h1.symm)
    have hT4 : T.card = 4 := by
      rw [hTdef, Finset.card_insert_of_notMem, Finset.card_insert_of_notMem,
        Finset.card_insert_of_notMem, Finset.card_singleton]
      · rw [Finset.mem_singleton]
        exact fun h => hzm (hninj h).symm
      · rw [Finset.mem_insert, Finset.mem_singleton]
        exact fun h => h.elim hfl fun h' => hn0 (σ z) h'.symm
      · rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
        exact fun h => h.elim (fun h' => hzm h'.symm) fun h' =>
          h'.elim (fun h'' => hn0 z h''.symm) hz3
    obtain ⟨a', b', hF', hN', hG'⟩ :=
      ih (s \ T).card (by omega) σ' hσ'2 hσ'n (s \ T) hs' rfl
    have hτG : τ ∉ G := hE τ z (σ z) hzm hfl (hτT' z hzT)
      (by rw [hτT' _ ((hmemT _).2 (Or.inr (Or.inl rfl))), hσ]) hτn
      (fun x h1 h2 h3 h4 => hτo' x (by
        rw [hmemT]
        exact fun h => h.elim h1 fun h' => h'.elim h3 fun h'' => h''.elim h2 h4))
    refine ⟨a', b' + 1, ?_, by omega, ?_⟩
    · -- no point of the orbit is flipped
      have hset : {x | σ x = n x} = {x | σ' x = n x} := by
        ext x
        simp only [Set.mem_setOf_eq]
        by_cases hx : x ∈ T
        · rw [hσ'T' x hx]
          have hx' := hx
          rw [hmemT] at hx'
          refine ⟨fun h => ?_, fun h => absurd h.symm (hn0 x)⟩
          exfalso
          rcases hx' with rfl | rfl | rfl | rfl
          · exact hfl h
          · rw [hσ] at h
            exact hz3 h
          · rw [hσn] at h
            exact hfl (hninj h)
          · rw [hσn, hσ] at h
            exact hz3 (hninj h)
        · rw [hσ'o' x hx]
      rw [hset, hF']
    · rw [mem_iff_not_mem_of_eq_mul hστ hτ2 hτG hor, hG',
        show b' + 1 + ε * a' = b' + ε * a' + 1 by ring, Nat.even_add_one]

end Abstract

/-! ## The forward monodromy group -/

section Forward

variable {b : ℂ} (hb₀ : 0 < b.re) (hb : b ∉ branchTimes)

/-- A permutation that flips the pair of `a` and fixes every other zero is determined by `a`. -/
theorem flip_eq_of_spec {f f' : Perm {z : ℂ // complexHeat b z = 0}}
    {a : {z : ℂ // complexHeat b z = 0}} (hfa : f a = fibreNeg b a)
    (hfn : ∀ x, f (fibreNeg b x) = fibreNeg b (f x))
    (hfo : ∀ x, x ≠ a → x ≠ fibreNeg b a → f x = x) (hfa' : f' a = fibreNeg b a)
    (hfn' : ∀ x, f' (fibreNeg b x) = fibreNeg b (f' x))
    (hfo' : ∀ x, x ≠ a → x ≠ fibreNeg b a → f' x = x) : f = f' :=
  Perm.ext fun x => by
    by_cases h1 : x = a
    · rw [h1, hfa, hfa']
    by_cases h2 : x = fibreNeg b a
    · rw [h2, hfn, hfn', hfa, hfa']
    · rw [hfo x h1 h2, hfo' x h1 h2]

/-- **The flips of single pairs lie in `G₊(b)` together.** If `G₊(b)` contains the flip of one
pair it contains the flip of every pair: `G₊(b)` is transitive on the zeros. -/
theorem flip_mem_forwardMonodromy_of_flip_mem {f₀ f : Perm {z : ℂ // complexHeat b z = 0}}
    {a₀ a : {z : ℂ // complexHeat b z = 0}} (h₀a : f₀ a₀ = fibreNeg b a₀)
    (h₀n : ∀ x, f₀ (fibreNeg b x) = fibreNeg b (f₀ x))
    (h₀o : ∀ x, x ≠ a₀ → x ≠ fibreNeg b a₀ → f₀ x = x)
    (h₀G : f₀ ∈ forwardMonodromy b hb₀ hb) (hfa : f a = fibreNeg b a)
    (hfn : ∀ x, f (fibreNeg b x) = fibreNeg b (f x))
    (hfo : ∀ x, x ≠ a → x ≠ fibreNeg b a → f x = x) : f ∈ forwardMonodromy b hb₀ hb := by
  obtain ⟨g, hg, hga⟩ := exists_mem_forwardMonodromy_apply_eq b hb₀ hb a₀ a
  have hgn : ∀ x, g (fibreNeg b x) = fibreNeg b (g x) := fun x => by
    have h := congrArg (fun w : Perm {z : ℂ // complexHeat b z = 0} => w x)
      (forwardMonodromy_commute_fibreNeg hg)
    exact h
  have hgs : ∀ x, g.symm (fibreNeg b x) = fibreNeg b (g.symm x) := fun x => by
    rw [Equiv.symm_apply_eq, hgn, Equiv.apply_symm_apply]
  have hconj : g * f₀ * g⁻¹ ∈ forwardMonodromy b hb₀ hb :=
    (forwardMonodromy b hb₀ hb).mul_mem ((forwardMonodromy b hb₀ hb).mul_mem hg h₀G)
      ((forwardMonodromy b hb₀ hb).inv_mem hg)
  have heq : f = g * f₀ * g⁻¹ := by
    refine flip_eq_of_spec hfa hfn hfo ?_ (fun x => ?_) (fun x h1 h2 => ?_)
    · show g (f₀ (g.symm a)) = fibreNeg b a
      rw [← hga, Equiv.symm_apply_apply, h₀a, hgn]
    · show g (f₀ (g.symm (fibreNeg b x))) = fibreNeg b (g (f₀ (g.symm x)))
      rw [hgs, h₀n, hgn]
    · show g (f₀ (g.symm x)) = x
      rw [h₀o (g.symm x) (fun h => h1 (by rw [← hga, ← h, Equiv.apply_symm_apply]))
        (fun h => h2 (by rw [← hga, ← hgn, ← h, Equiv.apply_symm_apply])),
        Equiv.apply_symm_apply]
  rw [heq]
  exact hconj

/-- **The parity law of the involutions of a proper group.** If some permutation of the zeros of
`H_b` that commutes with `z ↦ −z` and moves finitely many zeros is not in `G₊(b)`, then there is
`ε ∈ {0, 1}`, equal to `0` exactly when `G₊(b)` contains the flip of a single pair, such that
every involution `σ ∈ G₊(b)` carries `2a` zeros to their negatives and moves `2a + 4c` zeros
with `c + εa` even. -/
theorem exists_parity_of_not_mem_forwardMonodromy
    {w₀ : Perm {z : ℂ // complexHeat b z = 0}}
    (hw₀ : ∀ x, w₀ (fibreNeg b x) = fibreNeg b (w₀ x)) (hfin₀ : {x | w₀ x ≠ x}.Finite)
    (hw₀G : w₀ ∉ forwardMonodromy b hb₀ hb) :
    ∃ ε : ℕ, (ε = 0 ∨ ε = 1) ∧
      (ε = 0 ↔ ∃ (f : Perm {z : ℂ // complexHeat b z = 0})
        (a : {z : ℂ // complexHeat b z = 0}), f a = fibreNeg b a ∧
          (∀ x, f (fibreNeg b x) = fibreNeg b (f x)) ∧
          (∀ x, x ≠ a → x ≠ fibreNeg b a → f x = x) ∧ f ∈ forwardMonodromy b hb₀ hb) ∧
      ∀ σ ∈ forwardMonodromy b hb₀ hb, (∀ x, σ (σ x) = x) →
        ∃ a c : ℕ, {x | σ x = fibreNeg b x}.ncard = 2 * a ∧
          {x | σ x ≠ x}.ncard = 2 * a + 4 * c ∧ Even (c + ε * a) := by
  classical
  obtain ⟨Q, hQ⟩ : ∃ Q : Prop, Q ↔ ∃ (f : Perm {z : ℂ // complexHeat b z = 0})
      (a : {z : ℂ // complexHeat b z = 0}), f a = fibreNeg b a ∧
        (∀ x, f (fibreNeg b x) = fibreNeg b (f x)) ∧
        (∀ x, x ≠ a → x ≠ fibreNeg b a → f x = x) ∧ f ∈ forwardMonodromy b hb₀ hb :=
    ⟨_, Iff.rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℕ, ε = if Q then 0 else 1 := ⟨_, rfl⟩
  have hε01 : ε = 0 ∨ ε = 1 := by
    by_cases h : Q
    · exact Or.inl (by rw [hε, if_pos h])
    · exact Or.inr (by rw [hε, if_neg h])
  have hεQ : ε = 0 ↔ Q := by
    by_cases h : Q
    · exact ⟨fun _ => h, fun _ => by rw [hε, if_pos h]⟩
    · refine ⟨fun h' => ?_, fun h' => absurd h' h⟩
      rw [hε, if_neg h] at h'
      exact absurd h' one_ne_zero
  have hε0 := hεQ.trans hQ
  refine ⟨ε, hε01, hε0, fun σ hσ hσ2 => ?_⟩
  have hfin := finite_setOf_forwardMonodromy_ne hσ
  have hσn : ∀ x, σ (fibreNeg b x) = fibreNeg b (σ x) := fun x => by
    have h := congrArg (fun w : Perm {z : ℂ // complexHeat b z = 0} => w x)
      (forwardMonodromy_commute_fibreNeg hσ)
    exact h
  obtain ⟨a, c, h1, h2, h3⟩ := exists_flips_exchanges_parity
    (n := fibreNeg b) (G := forwardMonodromy b hb₀ hb) (ε := ε)
    (fun x => Subtype.ext (neg_neg _)) (fibreNeg_apply_ne_self hb)
    (fun w₁ w₂ h1 h2 h3 h4 => mem_forwardMonodromy_or_mem_or_mul_inv_mem hb₀ hb h1 h2 h3 h4)
    (fun e a a' h1 h2 hea hea' he heo heG =>
      hw₀G (mem_forwardMonodromy_of_exchange_mem hb₀ hb h1 h2 hea hea' he heo heG hw₀ hfin₀))
    hε01
    (fun f a hfa hfn hfo => ⟨fun hf => hε0.2 ⟨f, a, hfa, hfn, hfo, hf⟩, fun h0 => by
      obtain ⟨f₀, a₀, h₀a, h₀n, h₀o, h₀G⟩ := hε0.1 h0
      exact flip_mem_forwardMonodromy_of_flip_mem hb₀ hb h₀a h₀n h₀o h₀G hfa hfn hfo⟩)
    hfin.toFinset.card σ hσ2 hσn hfin.toFinset
    (fun x => by rw [Set.Finite.mem_toFinset]; exact Iff.rfl) rfl
  refine ⟨a, c, h1, ?_, (h3.1 hσ)⟩
  rw [Set.ncard_eq_toFinset_card _ hfin, h2]

end Forward

end GaloisForLFunctions.GaloisTheoryOfZeros
