import GaloisForLFunctions.RHTower.DeningerBaseCentralizer

/-!
# The centralizer of a base element with one exceptional factor

A factor may centralize the base group without lying in it — an abelian factor always does.  If
exactly one factor is exceptional in that way, the centralizer of a nontrivial base element is
contained in it: every letter of a centralizing word centralizes the base element, so a letter of a
non exceptional factor would lie in the base group, which a reduced word forbids, and peeling an
exceptional letter leaves the same problem.

* `deningerCentralizer_base_one` : the centralizer lies in the exceptional factor.
* `deningerPow_eq_of_basePow_one` : uniqueness of roots of a base element.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The centralizer of a nontrivial base element lies in the exceptional factor.** -/
theorem deningerCentralizer_base_one
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (i₀ : ι)
    (hself : ∀ (i : ι) (x : G i) (v : H), i ≠ i₀ → v ≠ 1 → x * φ i v * x⁻¹ = φ i v →
      x ∈ (φ i).range)
    (k : H) (hk : k ≠ 1) (w : PushoutI φ)
    (hcomm : w * PushoutI.base φ k = PushoutI.base φ k * w) :
    ∃ x : G i₀, w = PushoutI.of (φ := φ) i₀ x := by
  classical
  have hfix : w⁻¹ * PushoutI.base φ k * w = PushoutI.base φ k := by
    calc w⁻¹ * PushoutI.base φ k * w = w⁻¹ * (PushoutI.base φ k * w) := by group
      _ = w⁻¹ * (w * PushoutI.base φ k) := by rw [← hcomm]
      _ = PushoutI.base φ k := by group
  suffices Hn : ∀ n : ℕ, ∀ w : PushoutI φ, deningerLen d w ≤ n →
      w⁻¹ * PushoutI.base φ k * w = PushoutI.base φ k →
      ∃ x : G i₀, w = PushoutI.of (φ := φ) i₀ x from
    Hn (deningerLen d w) w le_rfl hfix
  clear hfix hcomm w
  intro n
  induction n with
  | zero =>
    intro w hlen _
    obtain ⟨h₀, hw⟩ := (deningerLen_eq_zero_iff (d := d) w).1 (by omega)
    exact ⟨φ i₀ h₀, by rw [← hw, PushoutI.of_apply_eq_base]⟩
  | succ n ih =>
    intro w hlen hfix
    rcases deningerExists_letterProd (d := d) w with ⟨h₀, hw, -⟩ | ⟨L, hLne, hLred, hLalt, hLlen, hw⟩
    · exact ⟨φ i₀ h₀, by rw [hw, PushoutI.of_apply_eq_base]⟩
    · cases L with
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
          have hxc : x * φ j k' * x⁻¹ = φ j k' := by
            calc x * φ j k' * x⁻¹ = x * (x⁻¹ * φ j k' * x) * x⁻¹ := by rw [← hk']
              _ = φ j k' := by group
          by_cases hj : j = i₀
          · subst hj
            have h1 : PushoutI.of (φ := φ) j (x⁻¹ * φ j k' * x) = PushoutI.base φ k' := by
              rw [← hk', PushoutI.of_apply_eq_base]
            have hfix' : (deningerLetterProd (φ := φ) L')⁻¹ * PushoutI.base φ k' *
                deningerLetterProd (φ := φ) L' = PushoutI.base φ k' := by
              calc (deningerLetterProd (φ := φ) L')⁻¹ * PushoutI.base φ k' *
                    deningerLetterProd (φ := φ) L'
                  = (deningerLetterProd (φ := φ) L')⁻¹ *
                    PushoutI.of (φ := φ) j (x⁻¹ * φ j k' * x) *
                    deningerLetterProd (φ := φ) L' := by rw [h1]
                _ = w⁻¹ * PushoutI.base φ k' * w := hconj.symm
                _ = PushoutI.base φ k' := hfix
            have hlen' : deningerLen d (deningerLetterProd (φ := φ) L') ≤ n := by
              have h1 : deningerLen d (deningerLetterProd (φ := φ) L') = L'.length :=
                deningerLen_letterProd (d := d) L'
                  (fun q hq => hLred q (List.mem_cons_of_mem _ hq))
                  (List.isChain_cons.1 hLalt).2
              have h2 : ((⟨j, x⟩ : Σ i, G i) :: L').length = deningerLen d w := hLlen
              simp only [List.length_cons] at h2
              omega
            obtain ⟨x', hx'⟩ := ih (deningerLetterProd (φ := φ) L') hlen' hfix'
            exact ⟨x * x', by rw [hw, hsplit, hx', map_mul]⟩
          · exact absurd (hself j x k' hj hk hxc) hxred
        · have hhead : ∀ q ∈ L'.head?, j ≠ q.1 := (List.isChain_cons.1 hLalt).1
          have hlen2 := deningerLen_conj_word_letter (d := d) L'
            (fun q hq => hLred q (List.mem_cons_of_mem _ hq))
            (List.isChain_cons.1 hLalt).2 j (x⁻¹ * φ j k * x) hmem hhead
          rw [← hconj, hfix, deningerLen_base] at hlen2
          omega

include d in
/-- **Uniqueness of roots of a nontrivial base element**, with one exceptional factor. -/
theorem deningerPow_eq_of_basePow_one (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (i₀ : ι)
    (hself : ∀ (i : ι) (x : G i) (v : H), i ≠ i₀ → v ≠ 1 → x * φ i v * x⁻¹ = φ i v →
      x ∈ (φ i).range)
    (hG₀ : ∀ (a b : G i₀) (m : ℕ), 0 < m → a ^ m = b ^ m → a = b)
    (k : H) (hk : k ≠ 1) (x y : PushoutI φ) (n : ℕ)
    (hx : x ^ (n + 1) = PushoutI.base φ k) (hy : y ^ (n + 1) = PushoutI.base φ k) : x = y := by
  obtain ⟨a, ha⟩ := deningerCentralizer_base_one (d := d) hcent i₀ hself k hk x (by
    rw [← hx]; exact ((Commute.refl x).pow_right (n + 1)))
  obtain ⟨b, hb⟩ := deningerCentralizer_base_one (d := d) hcent i₀ hself k hk y (by
    rw [← hy]; exact ((Commute.refl y).pow_right (n + 1)))
  have hab : a ^ (n + 1) = b ^ (n + 1) := by
    refine PushoutI.of_injective hφ i₀ ?_
    rw [map_pow, map_pow, ← ha, ← hb, hx, hy]
  rw [ha, hb, hG₀ a b (n + 1) (by omega) hab]

end RHTower
