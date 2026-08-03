import GaloisForLFunctions.RHTower.DeningerPushoutOrder

/-!
# Equal powers have cyclic reductions of the same length

If two elements have equal `n`-th powers then all common multiples of `n` give equal powers, so the
lengths of their cyclic reductions cannot differ: the difference would be amplified without bound,
while the conjugators only ever contribute a fixed amount.

* `deningerCycLen_eq` : the cyclic reductions have the same length.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

theorem deningerConj_zpow (c g : PushoutI φ) (k : ℕ) :
    c⁻¹ * g ^ k * c = (c⁻¹ * g * c) ^ k := by
  have hmap := map_pow (MulAut.conj c⁻¹) g k
  simp only [MulAut.conj_apply, inv_inv] at hmap
  exact hmap

include d in
/-- The word length of a power, in terms of a cyclic reduction. -/
theorem deningerLen_pow_conj_bounds (x c : PushoutI φ) (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1)
    (hx : c⁻¹ * x * c = deningerLetterProd (φ := φ) L) (m : ℕ) (hm : 0 < m) :
    deningerLen d (x ^ m) ≤ m * L.length + 2 * deningerLen d c ∧
      m * L.length ≤ deningerLen d (x ^ m) + 2 * deningerLen d c := by
  obtain ⟨j, rfl⟩ : ∃ j, m = j + 1 := ⟨m - 1, by omega⟩
  have hconj : c⁻¹ * x ^ (j + 1) * c = (deningerLetterProd (φ := φ) L) ^ (j + 1) := by
    rw [deningerConj_zpow, hx]
  have hlen : deningerLen d ((deningerLetterProd (φ := φ) L) ^ (j + 1)) = (j + 1) * L.length := by
    have hp := deningerLen_pow (d := d) L 1 j hne hred halt hcyc
    rwa [map_one, mul_one] at hp
  have hge := deningerLen_conj_ge (d := d) c (x ^ (j + 1))
  have hle := deningerLen_conj_le (d := d) c (x ^ (j + 1))
  rw [hconj, hlen] at hge hle
  exact ⟨by omega, by omega⟩

include d in
/-- **Equal powers force cyclic reductions of the same length.** -/
theorem deningerCycLen_eq (x y : PushoutI φ) (n : ℕ) (hn : 0 < n) (cx cy : PushoutI φ)
    (Lx Ly : List (Σ i, G i))
    (hxne : Lx ≠ []) (hxred : ∀ p ∈ Lx, p.2 ∉ (φ p.1).range)
    (hxalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) Lx)
    (hxcyc : ∀ p ∈ Lx.getLast?, ∀ q ∈ Lx.head?, p.1 ≠ q.1)
    (hyne : Ly ≠ []) (hyred : ∀ p ∈ Ly, p.2 ∉ (φ p.1).range)
    (hyalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) Ly)
    (hycyc : ∀ p ∈ Ly.getLast?, ∀ q ∈ Ly.head?, p.1 ≠ q.1)
    (hx : cx⁻¹ * x * cx = deningerLetterProd (φ := φ) Lx)
    (hy : cy⁻¹ * y * cy = deningerLetterProd (φ := φ) Ly)
    (h : x ^ n = y ^ n) : Lx.length = Ly.length := by
  have key : ∀ a b : List (Σ i, G i), ∀ u v cu cv : PushoutI φ,
      a ≠ [] → (∀ p ∈ a, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) a →
      (∀ p ∈ a.getLast?, ∀ q ∈ a.head?, p.1 ≠ q.1) →
      b ≠ [] → (∀ p ∈ b, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) b →
      (∀ p ∈ b.getLast?, ∀ q ∈ b.head?, p.1 ≠ q.1) →
      cu⁻¹ * u * cu = deningerLetterProd (φ := φ) a →
      cv⁻¹ * v * cv = deningerLetterProd (φ := φ) b →
      u ^ n = v ^ n → a.length ≤ b.length := by
    intro a b u v cu cv hane hared haalt hacyc hbne hbred hbalt hbcyc hu hv huv
    by_contra hlt
    have hlt' : b.length + 1 ≤ a.length := by omega
    set S := 2 * deningerLen d cu + 2 * deningerLen d cv with hS
    set M := (S + 1) * n with hM
    have hMpos : 0 < M := by
      rw [hM]
      positivity
    have hMge : S + 1 ≤ M := by
      rw [hM]
      exact Nat.le_mul_of_pos_right _ hn
    have hpow : u ^ M = v ^ M := by
      rw [hM, mul_comm, pow_mul, huv, ← pow_mul, mul_comm]
    obtain ⟨hu1, hu2⟩ := deningerLen_pow_conj_bounds (d := d) u cu a hane hared haalt hacyc hu M hMpos
    obtain ⟨hv1, hv2⟩ := deningerLen_pow_conj_bounds (d := d) v cv b hbne hbred hbalt hbcyc hv M hMpos
    rw [hpow] at hu1 hu2
    have hmul : M * (b.length + 1) ≤ M * a.length := Nat.mul_le_mul_left M hlt'
    rw [Nat.mul_add, Nat.mul_one] at hmul
    omega
  exact le_antisymm
    (key Lx Ly x y cx cy hxne hxred hxalt hxcyc hyne hyred hyalt hycyc hx hy h)
    (key Ly Lx y x cy cx hyne hyred hyalt hycyc hxne hxred hxalt hxcyc hy hx h.symm)

end RHTower
