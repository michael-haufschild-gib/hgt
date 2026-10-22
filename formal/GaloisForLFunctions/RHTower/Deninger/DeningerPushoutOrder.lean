import GaloisForLFunctions.RHTower.Deninger.DeningerPushoutMetric

/-!
# Cyclically reduced elements have infinite order

A nonempty cyclically reduced word has powers of strictly growing length, so all its integer powers
are distinct.  The same holds for any conjugate of such an element.

* `deningerPow_ne_one_cycRed` : positive powers are nontrivial.
* `deningerZpow_injective_cycRed` : the integer powers are distinct.
* `deningerZpow_injective_conj` : the same for a conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- A positive power of a nonempty cyclically reduced word is nontrivial. -/
theorem deningerPow_ne_one_cycRed (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) (n : ℕ) :
    (deningerLetterProd (φ := φ) L) ^ (n + 1) ≠ 1 := by
  intro hc
  have hlen := deningerLen_pow (d := d) L 1 n hne hred halt hcyc
  rw [map_one, mul_one, hc, deningerLen_one] at hlen
  have hzero : (n + 1) * L.length = 0 := hlen.symm
  have hL0 : L.length = 0 := by
    rcases Nat.mul_eq_zero.1 hzero with h | h
    · omega
    · exact h
  exact hne (List.length_eq_zero_iff.1 hL0)

include d in
/-- The integer powers of a nonempty cyclically reduced word are distinct. -/
theorem deningerZpow_injective_cycRed (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) (a b : ℤ)
    (h : (deningerLetterProd (φ := φ) L) ^ a = (deningerLetterProd (φ := φ) L) ^ b) :
    a = b := by
  set g := deningerLetterProd (φ := φ) L with hgdef
  have hsub : g ^ (a - b) = 1 := by
    rw [zpow_sub, h, mul_inv_cancel]
  have hpos : ∀ m : ℕ, g ^ ((m : ℤ) + 1) ≠ 1 := by
    intro m hm
    refine deningerPow_ne_one_cycRed (d := d) L hne hred halt hcyc m ?_
    rw [← hgdef, ← zpow_natCast g (m + 1)]
    push_cast
    exact hm
  rcases lt_trichotomy a b with hlt | heq | hgt
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, b - a = (m : ℤ) + 1 := ⟨(b - a - 1).toNat, by omega⟩
    refine hpos m ?_
    rw [← hm, zpow_sub, ← h, ← zpow_sub, sub_self, zpow_zero]
  · exact heq
  · exfalso
    obtain ⟨m, hm⟩ : ∃ m : ℕ, a - b = (m : ℤ) + 1 := ⟨(a - b - 1).toNat, by omega⟩
    exact hpos m (hm ▸ hsub)

include d in
/-- The integer powers of a conjugate of a nonempty cyclically reduced word are distinct. -/
theorem deningerZpow_injective_conj (c g : PushoutI φ) (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1)
    (hg : c⁻¹ * g * c = deningerLetterProd (φ := φ) L) (a b : ℤ) (h : g ^ a = g ^ b) :
    a = b := by
  refine deningerZpow_injective_cycRed (d := d) L hne hred halt hcyc a b ?_
  rw [← hg]
  have hca : ∀ k : ℤ, (c⁻¹ * g * c) ^ k = c⁻¹ * g ^ k * c := by
    intro k
    have hmap := map_zpow (MulAut.conj c⁻¹) g k
    simp only [MulAut.conj_apply, inv_inv] at hmap
    exact hmap.symm
  rw [hca, hca, h]

end RHTower
