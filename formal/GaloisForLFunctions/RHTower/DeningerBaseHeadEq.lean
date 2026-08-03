import GaloisForLFunctions.RHTower.DeningerBlockInv

/-!
# Equal powers of cyclically reduced elements are equal

The words of two cyclically reduced elements with the same positive power agree, so the two elements
differ by a base group element.  Descending the block recursion, the difference of the heads at each
stage is the difference at the stage below multiplied by the original difference, because a shift
producing the same word preserves differences.  At the top the heads agree, so the original
difference has trivial power, and a torsion free base group forces it to be trivial.

* `deningerBlockHead_rel` : the head difference is a power of the original difference.
* `deningerBaseHead_pow_eq` : equal powers of cyclically reduced elements are equal.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The head difference is a power of the original difference.** -/
theorem deningerBlockHead_rel (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hcomm : ∀ u v : H, u * v = v * u)
    (M : List (Σ i, G i)) (hMne : M ≠ [])
    (hMset : ∀ p ∈ M, p.2 ∈ d.set p.1) (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hMcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1) (j k : H) :
    ∀ (n : ℕ) (h h' : H) (N N' : List (Σ i, G i)),
      N.length = n * M.length → N'.length = n * M.length →
      (∀ p ∈ N ++ M, p.2 ∈ d.set p.1) → (∀ p ∈ N ++ M, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (N ++ M) →
      (∀ p ∈ N' ++ M, p.2 ∈ d.set p.1) → (∀ p ∈ N' ++ M, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (N' ++ M) →
      (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 1) =
        PushoutI.base φ h * deningerLetterProd (φ := φ) (N ++ M) →
      (PushoutI.base φ k * deningerLetterProd (φ := φ) M) ^ (n + 1) =
        PushoutI.base φ h' * deningerLetterProd (φ := φ) (N' ++ M) →
      N = N' → h * h'⁻¹ = (j * k⁻¹) ^ (n + 1) := by
  have hswap : ∀ a b c e : H, (a * b) * (c * e)⁻¹ = (a * c⁻¹) * (b * e⁻¹) := by
    intro a b c e
    calc (a * b) * (c * e)⁻¹ = a * (b * (e⁻¹ * c⁻¹)) := by rw [mul_inv_rev]; group
      _ = a * ((b * e⁻¹) * c⁻¹) := by rw [mul_assoc]
      _ = a * (c⁻¹ * (b * e⁻¹)) := by rw [hcomm (b * e⁻¹) c⁻¹]
      _ = (a * c⁻¹) * (b * e⁻¹) := by rw [mul_assoc]
  intro n
  induction n with
  | zero =>
    intro h h' N N' hNlen hN'len _ _ _ _ _ _ hNeq hN'eq _
    have hN : N = [] := List.length_eq_zero_iff.1 (by simpa using hNlen)
    have hN' : N' = [] := List.length_eq_zero_iff.1 (by simpa using hN'len)
    subst hN
    subst hN'
    rw [pow_one, List.nil_append] at hNeq hN'eq
    have hj : j = h := PushoutI.base_injective hφ (mul_right_cancel hNeq)
    have hk : k = h' := PushoutI.base_injective hφ (mul_right_cancel hN'eq)
    rw [pow_one, hj, hk]
  | succ n ih =>
    intro h h' N N' hNlen hN'len hNset hNred hNalt hN'set hN'red hN'alt hNeq hN'eq hNN'
    obtain ⟨g, s, P, W, hPlen, hPset, hPred, hPalt, hPhead, hPeq, hshift, hmapW, hh, hNW⟩ :=
      deningerBlock_succ_inv (d := d) hφ M hMne hMset hMred hMalt hMcyc j n h N hNlen
        hNset hNred hNalt hNeq
    obtain ⟨g', s', P', W', hP'len, hP'set, hP'red, hP'alt, hP'head, hP'eq, hshift', hmapW',
      hh', hN'W⟩ :=
      deningerBlock_succ_inv (d := d) hφ M hMne hMset hMred hMalt hMcyc k n h' N' hN'len
        hN'set hN'red hN'alt hN'eq
    have hWlen : W.length = W'.length := by
      have e1 : W.length = M.length := by
        have := congrArg List.length hmapW
        simpa using this
      have e2 : W'.length = M.length := by
        have := congrArg List.length hmapW'
        simpa using this
      rw [e1, e2]
    have hWW : W = W' := by
      refine List.append_inj_left (?_ : W ++ P = W' ++ P') hWlen
      rw [← hNW, ← hN'W]
      exact hNN'
    have hPP : P = P' := by
      refine List.append_inj_right (?_ : W ++ P = W' ++ P') hWlen
      rw [← hNW, ← hN'W]
      exact hNN'
    have hIH : g * g'⁻¹ = (j * k⁻¹) ^ (n + 1) :=
      ih g g' P P' hPlen hP'len hPset hPred hPalt hP'set hP'red hP'alt hPeq hP'eq hPP
    have hss : s * s'⁻¹ = g * g'⁻¹ := by
      refine deningerShift_diff_fixed (d := d) hφ hcent M W hMred hMalt g g' s s' hshift ?_
      rw [hWW]
      exact hshift'
    rw [hh, hh', hswap, hss, hIH, ← pow_succ']

include d in
/-- **Equal powers of cyclically reduced elements are equal.** -/
theorem deningerBaseHead_pow_eq (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hcomm : ∀ u v : H, u * v = v * u)
    (htf : ∀ (u : H) (n : ℕ), 0 < n → u ^ n = 1 → u = 1)
    (M : List (Σ i, G i)) (hMne : M ≠ [])
    (hMset : ∀ p ∈ M, p.2 ∈ d.set p.1) (hMred : ∀ p ∈ M, p.2 ∉ (φ p.1).range)
    (hMalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) M)
    (hMcyc : ∀ p ∈ M.getLast?, ∀ q ∈ M.head?, p.1 ≠ q.1) (j k : H) (n : ℕ)
    (heq : (PushoutI.base φ j * deningerLetterProd (φ := φ) M) ^ (n + 1) =
      (PushoutI.base φ k * deningerLetterProd (φ := φ) M) ^ (n + 1)) :
    PushoutI.base φ j * deningerLetterProd (φ := φ) M =
      PushoutI.base φ k * deningerLetterProd (φ := φ) M := by
  obtain ⟨h, N, hNlen, hNset, hNred, hNalt, -, hNeq⟩ :=
    deningerBaseHead_pow_word (d := d) M hMne hMset hMred hMalt hMcyc j n
  obtain ⟨h', N', hN'len, hN'set, hN'red, hN'alt, -, hN'eq⟩ :=
    deningerBaseHead_pow_word (d := d) M hMne hMset hMred hMalt hMcyc k n
  obtain ⟨hhead, hwords⟩ :=
    deningerBaseWord_head_eq (d := d) hφ h h' (N ++ M) (N' ++ M) hNset hNred hNalt
      hN'set hN'red hN'alt (by rw [← hNeq, ← hN'eq, heq])
  have hNN' : N = N' := by
    refine List.append_inj_left hwords ?_
    rw [hNlen, hN'len]
  have hrel := deningerBlockHead_rel (d := d) hφ hcent hcomm M hMne hMset hMred hMalt hMcyc j k
    n h h' N N' hNlen hN'len hNset hNred hNalt hN'set hN'red hN'alt hNeq hN'eq hNN'
  rw [hhead, mul_inv_cancel] at hrel
  have hjk : j * k⁻¹ = 1 := htf _ (n + 1) (by omega) hrel.symm
  rw [mul_inv_eq_one.mp hjk]

end RHTower
