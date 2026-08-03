import GaloisForLFunctions.RHTower.DeningerFactorCentralizer

/-!
# The centralizer of a base element

An element commuting with a nontrivial base group element conjugates it to itself, which has length
zero.  A conjugator with a nonempty word is impossible: its first letter either moves the base
element out of the base group, and then the conjugate is a reduced word of odd positive length, or
it centralizes it, and then the letter itself lies in the base group, which a reduced word forbids.
So the centralizer of a nontrivial base element is the base group, provided each factor centralizes
it only there.

* `deningerCentralizer_base` : the centralizer of a base element.
* `deningerPow_eq_of_basePow` : uniqueness of roots of a base element.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The centralizer of a nontrivial base element is the base group**, when each factor centralizes
it only inside the base group. -/
theorem deningerCentralizer_base
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hself : ∀ (i : ι) (x : G i) (v : H), v ≠ 1 → x * φ i v * x⁻¹ = φ i v → x ∈ (φ i).range)
    (k : H) (hk : k ≠ 1) (w : PushoutI φ)
    (hcomm : w * PushoutI.base φ k = PushoutI.base φ k * w) :
    w ∈ (PushoutI.base φ).range := by
  classical
  have hfix : w⁻¹ * PushoutI.base φ k * w = PushoutI.base φ k := by
    calc w⁻¹ * PushoutI.base φ k * w = w⁻¹ * (PushoutI.base φ k * w) := by group
      _ = w⁻¹ * (w * PushoutI.base φ k) := by rw [← hcomm]
      _ = PushoutI.base φ k := by group
  rcases deningerExists_letterProd (d := d) w with ⟨h₀, hw, -⟩ | ⟨L, hLne, hLred, hLalt, -, hw⟩
  · exact ⟨h₀, hw.symm⟩
  exfalso
  cases L with
  | nil => exact absurd rfl hLne
  | cons p L' =>
    obtain ⟨j, x⟩ := p
    have hxred : x ∉ (φ j).range := hLred _ (List.mem_cons_self ..)
    have hsplit : deningerLetterProd (φ := φ) ((⟨j, x⟩ : Σ i, G i) :: L') =
        PushoutI.of (φ := φ) j x * deningerLetterProd (φ := φ) L' :=
      deningerLetterProd_cons _ _
    have hconj : w⁻¹ * PushoutI.base φ k * w =
        (deningerLetterProd (φ := φ) L')⁻¹ *
          PushoutI.of (φ := φ) j (x⁻¹ * φ j k * x) * deningerLetterProd (φ := φ) L' := by
      rw [hw, hsplit, map_mul, map_mul, map_inv, ← PushoutI.of_apply_eq_base φ j k]
      group
    by_cases hmem : x⁻¹ * φ j k * x ∈ (φ j).range
    · obtain ⟨k', hk'⟩ := hmem
      have hkk : k' = k := hcent j x⁻¹ k k' (by rw [inv_inv, hk'])
      subst hkk
      refine hxred (hself j x k' hk ?_)
      calc x * φ j k' * x⁻¹ = x * (x⁻¹ * φ j k' * x) * x⁻¹ := by rw [← hk']
        _ = φ j k' := by group
    · have hhead : ∀ q ∈ L'.head?, j ≠ q.1 := (List.isChain_cons.1 hLalt).1
      have hlen := deningerLen_conj_word_letter (d := d) L'
        (fun q hq => hLred q (List.mem_cons_of_mem _ hq))
        (List.isChain_cons.1 hLalt).2 j (x⁻¹ * φ j k * x) hmem hhead
      rw [← hconj, hfix, deningerLen_base] at hlen
      omega

include d in
/-- **Uniqueness of roots of a nontrivial base element.** -/
theorem deningerPow_eq_of_basePow (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (hself : ∀ (i : ι) (x : G i) (v : H), v ≠ 1 → x * φ i v * x⁻¹ = φ i v → x ∈ (φ i).range)
    (hH : ∀ (a b : H) (n : ℕ), 0 < n → a ^ n = b ^ n → a = b)
    (k : H) (hk : k ≠ 1) (x y : PushoutI φ) (n : ℕ)
    (hx : x ^ (n + 1) = PushoutI.base φ k) (hy : y ^ (n + 1) = PushoutI.base φ k) : x = y := by
  obtain ⟨a, ha⟩ := deningerCentralizer_base (d := d) hcent hself k hk x (by
    rw [← hx]; exact ((Commute.refl x).pow_right (n + 1)))
  obtain ⟨b, hb⟩ := deningerCentralizer_base (d := d) hcent hself k hk y (by
    rw [← hy]; exact ((Commute.refl y).pow_right (n + 1)))
  have hab : a ^ (n + 1) = b ^ (n + 1) := by
    refine PushoutI.base_injective hφ ?_
    rw [map_pow, map_pow, ha, hb, hx, hy]
  rw [← ha, ← hb, hH a b (n + 1) (by omega) hab]

end RHTower
