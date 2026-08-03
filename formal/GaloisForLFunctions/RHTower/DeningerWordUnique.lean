import GaloisForLFunctions.RHTower.DeningerConjPowCycRed

/-!
# Two words with the same product

Reduced alternating words are not determined by their products — the letters can be shifted by the
base group — but their sequences of factors are, since that sequence is read off the normal form.

* `deningerWords_map_fst_eq` : two reduced alternating words with the same product run through the
  same factors.
* `deningerWords_head_shift` : their first letters differ by the base group, and the shift passes to
  the rest of the word.
* `deningerWords_singleton` : a single letter is determined by its product.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **Two reduced alternating words with the same product run through the same factors.** -/
theorem deningerWords_map_fst_eq (L M : List (Σ i, G i))
    (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (h : deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) M) :
    L.map Sigma.fst = M.map Sigma.fst := by
  rw [← deningerNormalWord_map_fst (d := d) L hLred hLalt,
    ← deningerNormalWord_map_fst (d := d) M hMred hMalt, h]

include d in
/-- Two reduced alternating words with the same product have the same length. -/
theorem deningerWords_length_eq (L M : List (Σ i, G i))
    (hLred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (h : deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) M) :
    L.length = M.length := by
  have := congrArg List.length
    (deningerWords_map_fst_eq (d := d) L M hLred hLalt hMred hMalt h)
  simpa using this

include d in
/-- **The first letters of two reduced alternating words with the same product differ by the base
group**, and the difference passes to the rest of the word.  Were the difference not in the base
group it would be a further letter, and the two words would have different lengths. -/
theorem deningerWords_head_shift (i : ι) (x y : G i) (L' M' : List (Σ i, G i))
    (hLred : ∀ p ∈ (⟨i, x⟩ : Σ i, G i) :: L', p.2 ∉ (φ p.1).range)
    (hLalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((⟨i, x⟩ : Σ i, G i) :: L'))
    (hMred : ∀ p ∈ (⟨i, y⟩ : Σ i, G i) :: M', p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) ((⟨i, y⟩ : Σ i, G i) :: M'))
    (h : deningerLetterProd (φ := φ) ((⟨i, x⟩ : Σ i, G i) :: L') =
      deningerLetterProd (φ := φ) ((⟨i, y⟩ : Σ i, G i) :: M')) :
    ∃ k : H, x = y * φ i k ∧
      deningerLetterProd (φ := φ) M' = PushoutI.base φ k * deningerLetterProd (φ := φ) L' := by
  classical
  have hlen : L'.length = M'.length := by
    have := deningerWords_length_eq (d := d) _ _ hLred hLalt hMred hMalt h
    simpa using this
  have hstep : PushoutI.of (φ := φ) i (y⁻¹ * x) * deningerLetterProd (φ := φ) L' =
      deningerLetterProd (φ := φ) M' := by
    rw [map_mul, map_inv]
    rw [deningerLetterProd_cons, deningerLetterProd_cons] at h
    show (PushoutI.of (φ := φ) i y)⁻¹ * PushoutI.of (φ := φ) i x *
      deningerLetterProd (φ := φ) L' = _
    rw [mul_assoc]
    show (PushoutI.of (φ := φ) i y)⁻¹ * (PushoutI.of (φ := φ) i x *
      deningerLetterProd (φ := φ) L') = _
    rw [show PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) L' =
        PushoutI.of (φ := φ) i y * deningerLetterProd (φ := φ) M' from h,
      ← mul_assoc, inv_mul_cancel, one_mul]
  have hmem : (y⁻¹ * x) ∈ (φ i).range := by
    by_contra hc
    have hred : ∀ p ∈ (⟨i, y⁻¹ * x⟩ : Σ i, G i) :: L', p.2 ∉ (φ p.1).range := by
      intro p hp
      rcases List.mem_cons.1 hp with rfl | hp
      · exact hc
      · exact hLred p (List.mem_cons_of_mem _ hp)
    have halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
        ((⟨i, y⁻¹ * x⟩ : Σ i, G i) :: L') :=
      List.isChain_cons.2 ⟨(List.isChain_cons.1 hLalt).1, (List.isChain_cons.1 hLalt).2⟩
    have hprod : deningerLetterProd (φ := φ) ((⟨i, y⁻¹ * x⟩ : Σ i, G i) :: L') =
        deningerLetterProd (φ := φ) M' := by
      rw [deningerLetterProd_cons]
      exact hstep
    have := deningerWords_length_eq (d := d) _ _ hred halt
      (fun p hp => hMred p (List.mem_cons_of_mem _ hp))
      (List.isChain_cons.1 hMalt).2 hprod
    simp only [List.length_cons] at this
    omega
  obtain ⟨k, hk⟩ := hmem
  refine ⟨k, ?_, ?_⟩
  · rw [hk]
    group
  · rw [← hstep, ← hk, PushoutI.of_apply_eq_base]

include d in
/-- **A single letter is determined by its product.** -/
theorem deningerWords_singleton (hφ : ∀ i, Function.Injective (φ i)) (p q : Σ i, G i)
    (hp : p.2 ∉ (φ p.1).range) (hq : q.2 ∉ (φ q.1).range)
    (h : deningerLetterProd (φ := φ) [p] = deningerLetterProd (φ := φ) [q]) : p = q := by
  obtain ⟨i, x⟩ := p
  obtain ⟨j, y⟩ := q
  have hij : i = j := by
    have := deningerWords_map_fst_eq (d := d) [(⟨i, x⟩ : Σ i, G i)] [(⟨j, y⟩ : Σ i, G i)]
      (by simpa using hp) (List.isChain_singleton _) (by simpa using hq)
      (List.isChain_singleton _) h
    simpa using this
  subst hij
  have hxy : PushoutI.of (φ := φ) i x = PushoutI.of (φ := φ) i y := by
    rw [deningerLetterProd_cons, deningerLetterProd_nil, mul_one, deningerLetterProd_cons,
      deningerLetterProd_nil, mul_one] at h
    exact h
  rw [PushoutI.of_injective hφ i hxy]

end RHTower
