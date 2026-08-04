import GaloisForLFunctions.RHTower.DeningerConjWordLength

/-!
# The trichotomy in word form

The one letter trichotomy, stated so that the lengthening branches produce the word of the conjugate
rather than only its length.  A lengthened conjugate carries the conjugating letter at both ends, so
its two extreme letters lie in the same factor: nothing further out can cancel against it.

* `deningerConj_letter_word` : a conjugation by one letter is a rotation or produces a longer word
  with both ends in the factor of that letter.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The one letter trichotomy in word form.** -/
theorem deningerConj_letter_word (U : List (Σ i, G i)) (hlen2 : 2 ≤ U.length)
    (hred : ∀ p ∈ U, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) U)
    (hcyc : ∀ p ∈ U.getLast?, ∀ q ∈ U.head?, p.1 ≠ q.1)
    (i : ι) (x : G i) (hx : x ∉ (φ i).range) :
    (∃ (t : ℕ) (m : H) (e : ℤ), t ≤ U.length ∧
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
          (PushoutI.of (φ := φ) i x)⁻¹ =
        PushoutI.base φ m * deningerLetterProd (φ := φ) (U.rotate t) *
          (PushoutI.base φ m)⁻¹ ∧
      deningerLetterProd (φ := φ) (U.take t) * (PushoutI.base φ m)⁻¹ *
          PushoutI.of (φ := φ) i x = deningerLetterProd (φ := φ) U ^ e) ∨
    (∃ W : List (Σ i, G i),
      PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
          (PushoutI.of (φ := φ) i x)⁻¹ = deningerLetterProd (φ := φ) W ∧
      (∀ p ∈ W, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) W ∧
      U.length < W.length ∧
      (∀ p ∈ W.head?, p.1 = i) ∧ (∀ p ∈ W.getLast?, p.1 = i)) := by
  classical
  have hxinv : (x : G i)⁻¹ ∉ (φ i).range := by
    rintro ⟨w, hw⟩
    exact hx ⟨w⁻¹, by rw [map_inv, hw, inv_inv]⟩
  obtain ⟨q, rest, hU⟩ : ∃ q rest, U = q :: rest := by
    cases U with
    | nil => simp at hlen2
    | cons q rest => exact ⟨q, rest, rfl⟩
  have hrestne : rest ≠ [] := by
    intro hc
    rw [hU, hc] at hlen2
    simp at hlen2
  have hUhead : U.head? = some q := by rw [hU, List.head?_cons]
  obtain ⟨U₀, p, hUp⟩ : ∃ U₀ p, U = U₀ ++ [p] := by
    obtain ⟨w, hw⟩ : ∃ w, U.getLast? = some w := by
      cases hUg : U.getLast? with
      | none =>
        rw [List.getLast?_eq_none_iff.1 hUg] at hlen2
        simp at hlen2
      | some w => exact ⟨w, rfl⟩
    exact ⟨U.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
  have hUlast : U.getLast? = some p := by rw [hUp]; simp
  have hU₀ne : U₀ ≠ [] := by
    intro hc
    rw [hUp, hc] at hlen2
    simp at hlen2
  by_cases hiq : q.1 = i
  · subst hiq
    have hqeta : (⟨q.1, q.2⟩ : Σ i, G i) = q := rfl
    by_cases hmem : x * q.2 ∈ (φ q.1).range
    · obtain ⟨k, hk⟩ := hmem
      refine Or.inl ⟨1, k, 0, by omega, ?_, ?_⟩
      · have := deningerConj_head_merge (φ := φ) q.1 q.2 rest x k hk.symm
        rw [hqeta] at this
        rw [hU]
        exact this
      · have hbase : PushoutI.base φ k = PushoutI.of (φ := φ) q.1 (x * q.2) := by
          rw [← hk, PushoutI.of_apply_eq_base]
        have htake : U.take 1 = [q] := by rw [hU, List.take_succ_cons, List.take_zero]
        rw [htake, hbase, zpow_zero, deningerLetterProd_cons, deningerLetterProd_nil, mul_one,
          ← map_inv, ← map_mul, ← map_mul]
        show PushoutI.of (φ := φ) q.1 (q.2 * (x * q.2)⁻¹ * x) = 1
        rw [show q.2 * (x * q.2)⁻¹ * x = 1 by group, map_one]
    · refine Or.inr ⟨(⟨q.1, x * q.2⟩ : Σ i, G i) ::
        (rest ++ [(⟨q.1, (x : G q.1)⁻¹⟩ : Σ i, G i)]), ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hU, deningerLetterProd_cons, deningerLetterProd_cons, deningerLetterProd_append,
          deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
        show PushoutI.of (φ := φ) q.1 x * (PushoutI.of (φ := φ) q.1 q.2 *
            deningerLetterProd (φ := φ) rest) * (PushoutI.of (φ := φ) q.1 x)⁻¹ =
          PushoutI.of (φ := φ) q.1 (x * q.2) * (deningerLetterProd (φ := φ) rest *
            PushoutI.of (φ := φ) q.1 (x : G q.1)⁻¹)
        rw [map_mul, map_inv]
        group
      · intro r hr
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hmem
        · rcases List.mem_append.1 hr with hr | hr
          · exact hred r (by rw [hU]; exact List.mem_cons_of_mem _ hr)
          · rw [List.mem_singleton] at hr
            subst hr
            exact hxinv
      · refine List.isChain_cons.2 ⟨fun r hr => ?_, ?_⟩
        · rw [List.head?_append_of_ne_nil _ hrestne] at hr
          exact (List.isChain_cons.1 (by rw [← hU]; exact halt)).1 r hr
        · refine List.isChain_append.2 ⟨(List.isChain_cons.1 (by rw [← hU]; exact halt)).2,
            List.isChain_singleton _, fun r hr s hs => ?_⟩
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
          subst hs
          refine hcyc r ?_ q hUhead
          rw [hU, List.getLast?_cons_of_ne_nil hrestne]
          exact hr
      · rw [hU]
        simp
      · intro r hr
        rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
        subst hr
        rfl
      · intro r hr
        have hgl : ((⟨q.1, x * q.2⟩ : Σ i, G i) ::
            (rest ++ [(⟨q.1, (x : G q.1)⁻¹⟩ : Σ i, G i)])).getLast? =
            some (⟨q.1, (x : G q.1)⁻¹⟩ : Σ i, G i) := by
          rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append]
          simp
        rw [hgl, Option.mem_def, Option.some.injEq] at hr
        subst hr
        rfl
  · by_cases hip : p.1 = i
    · subst hip
      have hpeta : (⟨p.1, p.2⟩ : Σ i, G i) = p := rfl
      have hhead' : ∀ r ∈ U₀.head?, p.1 ≠ r.1 := by
        intro r hr
        refine hcyc p hUlast r ?_
        rw [hUp, List.head?_append_of_ne_nil _ hU₀ne]
        exact hr
      by_cases hmem : p.2 * (x : G p.1)⁻¹ ∈ (φ p.1).range
      · obtain ⟨k, hk⟩ := hmem
        refine Or.inl ⟨U₀.length, k⁻¹, 1, by rw [hUp]; simp, ?_, ?_⟩
        · have := deningerConj_last_merge (φ := φ) p.1 p.2 U₀ x k hk.symm
          rw [hpeta] at this
          rw [hUp]
          exact this
        · have hbase : (PushoutI.base φ k⁻¹)⁻¹ = PushoutI.of (φ := φ) p.1 (p.2 * (x : G p.1)⁻¹) := by
            rw [← hk, PushoutI.of_apply_eq_base, ← map_inv, inv_inv]
          have htake : U.take U₀.length = U₀ := by rw [hUp, List.take_left]
          rw [htake, hbase, zpow_one, hUp, deningerLetterProd_snoc, mul_assoc, ← map_mul]
          show deningerLetterProd (φ := φ) U₀ *
              PushoutI.of (φ := φ) p.1 (p.2 * (x : G p.1)⁻¹ * x) =
            deningerLetterProd (φ := φ) U₀ * PushoutI.of (φ := φ) p.1 p.2
          rw [show p.2 * (x : G p.1)⁻¹ * x = p.2 by group]
      · refine Or.inr ⟨(⟨p.1, x⟩ : Σ i, G i) ::
          (U₀ ++ [(⟨p.1, p.2 * (x : G p.1)⁻¹⟩ : Σ i, G i)]), ?_, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hUp, deningerLetterProd_cons, deningerLetterProd_append, deningerLetterProd_snoc,
            deningerLetterProd_cons, deningerLetterProd_nil, mul_one]
          show PushoutI.of (φ := φ) p.1 x * (deningerLetterProd (φ := φ) U₀ *
              PushoutI.of (φ := φ) p.1 p.2) * (PushoutI.of (φ := φ) p.1 x)⁻¹ =
            PushoutI.of (φ := φ) p.1 x * (deningerLetterProd (φ := φ) U₀ *
              PushoutI.of (φ := φ) p.1 (p.2 * (x : G p.1)⁻¹))
          rw [map_mul, map_inv]
          group
        · intro r hr
          rw [List.mem_cons] at hr
          rcases hr with rfl | hr
          · exact hx
          · rcases List.mem_append.1 hr with hr | hr
            · exact hred r (by rw [hUp]; exact List.mem_append.2 (Or.inl hr))
            · rw [List.mem_singleton] at hr
              subst hr
              exact hmem
        · obtain ⟨hU₀alt, _, hjunc⟩ := List.isChain_append.1 (by rw [← hUp]; exact halt)
          refine List.isChain_cons.2 ⟨fun r hr => ?_, ?_⟩
          · rw [List.head?_append_of_ne_nil _ hU₀ne] at hr
            exact hhead' r hr
          · refine List.isChain_append.2 ⟨hU₀alt, List.isChain_singleton _, fun r hr s hs => ?_⟩
            rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
            subst hs
            exact hjunc r hr p rfl
        · rw [hUp]
          simp
        · intro r hr
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
          subst hr
          rfl
        · intro r hr
          have hgl : ((⟨p.1, x⟩ : Σ i, G i) ::
              (U₀ ++ [(⟨p.1, p.2 * (x : G p.1)⁻¹⟩ : Σ i, G i)])).getLast? =
              some (⟨p.1, p.2 * (x : G p.1)⁻¹⟩ : Σ i, G i) := by
            rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append]
            simp
          rw [hgl, Option.mem_def, Option.some.injEq] at hr
          subst hr
          rfl
    · refine Or.inr ⟨(⟨i, x⟩ : Σ i, G i) :: (U ++ [(⟨i, (x : G i)⁻¹⟩ : Σ i, G i)]),
        ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [deningerLetterProd_cons, deningerLetterProd_append, deningerLetterProd_cons,
          deningerLetterProd_nil, mul_one]
        show PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) U *
            (PushoutI.of (φ := φ) i x)⁻¹ =
          PushoutI.of (φ := φ) i x * (deningerLetterProd (φ := φ) U *
            PushoutI.of (φ := φ) i (x : G i)⁻¹)
        rw [map_inv, mul_assoc]
      · intro r hr
        rw [List.mem_cons] at hr
        rcases hr with rfl | hr
        · exact hx
        · rcases List.mem_append.1 hr with hr | hr
          · exact hred r hr
          · rw [List.mem_singleton] at hr
            subst hr
            exact hxinv
      · have hne : U ≠ [] := by rw [hU]; simp
        refine List.isChain_cons.2 ⟨fun r hr => ?_, ?_⟩
        · rw [List.head?_append_of_ne_nil _ hne, hUhead, Option.mem_def,
            Option.some.injEq] at hr
          subst hr
          exact fun hc => hiq hc.symm
        · refine List.isChain_append.2 ⟨halt, List.isChain_singleton _, fun r hr s hs => ?_⟩
          rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hs
          subst hs
          rw [hUlast, Option.mem_def, Option.some.injEq] at hr
          subst hr
          exact hip
      · simp
      · intro r hr
        rw [List.head?_cons, Option.mem_def, Option.some.injEq] at hr
        subst hr
        rfl
      · intro r hr
        have hgl : ((⟨i, x⟩ : Σ i, G i) ::
            (U ++ [(⟨i, (x : G i)⁻¹⟩ : Σ i, G i)])).getLast? =
            some (⟨i, (x : G i)⁻¹⟩ : Σ i, G i) := by
          rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append]
          simp
        rw [hgl, Option.mem_def, Option.some.injEq] at hr
        subst hr
        rfl

end RHTower
