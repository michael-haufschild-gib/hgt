import GaloisForLFunctions.RHTower.Deninger.DeningerCrossConjWord

/-!
# The conjugacy criterion for short elements

A conjugator carrying an element of a factor to an element of length at most one cannot start
outside that factor, since crossing to another factor lengthens the conjugate beyond one.  Peeling
its first letter conjugates inside the factor and shortens the conjugator, so the induction runs
until the conjugator is exhausted — unless the conjugated element falls into the base group, which
is the only escape.

* `deningerShortConj_cases` : the criterion, on the conjugator.
* `deningerShortConj_conj_eq` : the resulting form of the conjugate.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

include d in
/-- **The conjugacy criterion for short elements.**  Either the conjugator lies in the factor, or
the element conjugates into the base group inside its factor. -/
theorem deningerShortConj_cases (i : ι) (u : G i) (hu : u ∉ (φ i).range) (w : PushoutI φ)
    (hshort : deningerLen d (w⁻¹ * PushoutI.of (φ := φ) i u * w) ≤ 1) :
    (∃ x : G i, w = PushoutI.of (φ := φ) i x) ∨
      ∃ (x : G i) (k : H), x⁻¹ * u * x = φ i k := by
  classical
  suffices Hn : ∀ n : ℕ, ∀ (u : G i) (w : PushoutI φ), u ∉ (φ i).range →
      deningerLen d w ≤ n →
      deningerLen d (w⁻¹ * PushoutI.of (φ := φ) i u * w) ≤ 1 →
      (∃ x : G i, w = PushoutI.of (φ := φ) i x) ∨
        ∃ (x : G i) (k : H), x⁻¹ * u * x = φ i k from
    Hn (deningerLen d w) u w hu le_rfl hshort
  clear hshort hu u
  intro n
  induction n with
  | zero =>
    intro u w hu hlen _
    obtain ⟨h₀, hw⟩ := (deningerLen_eq_zero_iff (d := d) w).1 (by omega)
    refine Or.inl ⟨φ i h₀, ?_⟩
    rw [← hw, PushoutI.of_apply_eq_base]
  | succ n ih =>
    intro u w hu hlen hshort
    rcases deningerExists_letterProd (d := d) w with ⟨h₀, hw, -⟩ | ⟨L, hLne, hLred, hLalt, hLlen, hw⟩
    · refine Or.inl ⟨φ i h₀, ?_⟩
      rw [hw, PushoutI.of_apply_eq_base]
    · cases L with
      | nil => exact absurd rfl hLne
      | cons p L' =>
        obtain ⟨j, x⟩ := p
        by_cases hji : j = i
        · subst hji
          have hsplit : deningerLetterProd (φ := φ) ((⟨j, x⟩ : Σ i, G i) :: L') =
              PushoutI.of (φ := φ) j x * deningerLetterProd (φ := φ) L' :=
            deningerLetterProd_cons _ _
          have hconj : w⁻¹ * PushoutI.of (φ := φ) j u * w =
              (deningerLetterProd (φ := φ) L')⁻¹ *
                PushoutI.of (φ := φ) j (x⁻¹ * u * x) * deningerLetterProd (φ := φ) L' := by
            rw [hw, hsplit, map_mul, map_mul, map_inv]
            group
          by_cases hmem : x⁻¹ * u * x ∈ (φ j).range
          · obtain ⟨k, hk⟩ := hmem
            exact Or.inr ⟨x, k, hk.symm⟩
          · have hlen' : deningerLen d (deningerLetterProd (φ := φ) L') ≤ n := by
              have h1 : deningerLen d (deningerLetterProd (φ := φ) L') = L'.length :=
                deningerLen_letterProd (d := d) L'
                  (fun q hq => hLred q (List.mem_cons_of_mem _ hq))
                  (List.isChain_cons.1 hLalt).2
              have h2 : ((⟨j, x⟩ : Σ i, G i) :: L').length = deningerLen d w := hLlen
              simp only [List.length_cons] at h2
              omega
            rcases ih (x⁻¹ * u * x) (deningerLetterProd (φ := φ) L') hmem hlen'
              (by rw [← hconj]; exact hshort) with ⟨x', hx'⟩ | ⟨x', k, hk⟩
            · refine Or.inl ⟨x * x', ?_⟩
              rw [hw, hsplit, hx', map_mul]
            · exact Or.inr ⟨x * x', k, by rw [← hk]; group⟩
        · exfalso
          have hhead : ∀ q ∈ ((⟨j, x⟩ : Σ i, G i) :: L').head?, i ≠ q.1 := by
            intro q hq
            simp only [List.head?_cons, Option.mem_def, Option.some.injEq] at hq
            subst hq
            exact fun hc => hji hc.symm
          have hcross := deningerLen_conj_word_letter (d := d) ((⟨j, x⟩ : Σ i, G i) :: L')
            hLred hLalt i u hu hhead
          rw [← hw] at hcross
          simp only [List.length_cons] at hcross
          omega

include d in
/-- **The resulting form of the conjugate.**  When the conjugator lies in the factor, the conjugate
is computed inside it. -/
theorem deningerShortConj_conj_eq (i : ι) (u : G i) (hu : u ∉ (φ i).range) (w : PushoutI φ)
    (hshort : deningerLen d (w⁻¹ * PushoutI.of (φ := φ) i u * w) ≤ 1) :
    (∃ x : G i, w⁻¹ * PushoutI.of (φ := φ) i u * w =
        PushoutI.of (φ := φ) i (x⁻¹ * u * x)) ∨
      ∃ (x : G i) (k : H), x⁻¹ * u * x = φ i k := by
  rcases deningerShortConj_cases (d := d) i u hu w hshort with ⟨x, hx⟩ | hesc
  · refine Or.inl ⟨x, ?_⟩
    rw [hx, map_mul, map_mul, map_inv]
  · exact Or.inr hesc

end RHTower
