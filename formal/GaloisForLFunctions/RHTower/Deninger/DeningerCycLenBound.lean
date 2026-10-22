import GaloisForLFunctions.RHTower.Deninger.DeningerCycDecomp

/-!
# The cyclic reduction recursion

Every nonempty reduced alternating word splits as a conjugator followed by a tail, together with a
cyclically reduced part (or a single letter), the tail and the cyclically reduced part beginning in
the same factor.

* `deningerExists_cycData_len` : the recursion, with the length bound.
* `deningerCycRed_of_cycLen_eq` : a word as long as its cyclic word is itself cyclically reduced.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- **The base case, with the length bound.** -/
theorem deningerCycData_of_cycRed_len (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L)
    (hyp : L.length ≤ 1 ∨ ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1) :
    ∃ C R V : List (Σ i, G i),
      L = C ++ R ∧ R ≠ [] ∧ V ≠ [] ∧
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V ∧
      V.head?.map Sigma.fst = R.head?.map Sigma.fst ∧
      deningerLetterProd (φ := φ) R =
        deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹ ∧
      (V.length ≤ 1 ∨ ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) ∧
      V.length ≤ R.length :=
  ⟨[], L, L, by simp, hne, hne, hred, halt, rfl,
    by rw [deningerLetterProd_nil, inv_one, mul_one], hyp, le_rfl⟩

/-- **The cyclic reduction recursion, with the length bound.** -/
theorem deningerExists_cycData_len (L : List (Σ i, G i)) (hne : L ≠ [])
    (hred : ∀ p ∈ L, p.2 ∉ (φ p.1).range)
    (halt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L) :
    ∃ C R V : List (Σ i, G i),
      L = C ++ R ∧ R ≠ [] ∧ V ≠ [] ∧
      (∀ p ∈ V, p.2 ∉ (φ p.1).range) ∧
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V ∧
      V.head?.map Sigma.fst = R.head?.map Sigma.fst ∧
      deningerLetterProd (φ := φ) R =
        deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹ ∧
      (V.length ≤ 1 ∨ ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) ∧
      V.length ≤ R.length := by
  classical
  suffices Hn : ∀ n : ℕ, ∀ L : List (Σ i, G i), L.length ≤ n → L ≠ [] →
      (∀ p ∈ L, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L →
      ∃ C R V : List (Σ i, G i),
        L = C ++ R ∧ R ≠ [] ∧ V ≠ [] ∧
        (∀ p ∈ V, p.2 ∉ (φ p.1).range) ∧
        List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) V ∧
        V.head?.map Sigma.fst = R.head?.map Sigma.fst ∧
        deningerLetterProd (φ := φ) R =
          deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹ ∧
        (V.length ≤ 1 ∨ ∀ p ∈ V.getLast?, ∀ q ∈ V.head?, p.1 ≠ q.1) ∧
        V.length ≤ R.length from
    Hn L.length L le_rfl hne hred halt
  intro n
  induction n with
  | zero =>
    intro L hn hne _ _
    exact absurd (List.length_eq_zero_iff.1 (by omega)) hne
  | succ n ih =>
    intro L hn hne hred halt
    by_cases hcyc : ∀ p ∈ L.getLast?, ∀ q ∈ L.head?, p.1 ≠ q.1
    · exact deningerCycData_of_cycRed_len L hne hred halt (Or.inr hcyc)
    by_cases hshort : L.length ≤ 1
    · exact deningerCycData_of_cycRed_len L hne hred halt (Or.inl hshort)
    obtain ⟨j, z, y, M, hMne, hL⟩ := deningerNotCycRed_decomp L hne halt hshort hcyc
    subst hL
    have haltTail : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
        (M ++ [(⟨j, y⟩ : Σ i, G i)]) := halt.tail
    have hlenL : ((⟨j, z⟩ : Σ i, G i) :: (M ++ [(⟨j, y⟩ : Σ i, G i)])).length = M.length + 2 := by
      simp
    by_cases hmem : y * z ∈ (φ j).range
    · obtain ⟨k, hk⟩ := hmem
      obtain ⟨M', p, hM'⟩ : ∃ M' p, M = M' ++ [p] := by
        obtain ⟨w, hw⟩ : ∃ w, M.getLast? = some w := by
          cases hMg : M.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hMg) hMne
          | some w => exact ⟨w, rfl⟩
        exact ⟨M.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
      subst hM'
      set a : Σ i, G i := ⟨p.1, p.2 * φ p.1 k⟩ with ha
      have hstep : deningerLetterProd (φ := φ) (M' ++ [a]) =
          (PushoutI.of j z)⁻¹ *
            deningerLetterProd (φ := φ)
              ((⟨j, z⟩ : Σ i, G i) :: (M' ++ ([p, (⟨j, y⟩ : Σ i, G i)]))) * PushoutI.of j z := by
        rw [show M' ++ ([p, (⟨j, y⟩ : Σ i, G i)]) = M' ++ [p] ++ [(⟨j, y⟩ : Σ i, G i)] by simp]
        exact (deningerCycStep_mem (⟨j, z⟩ : Σ i, G i) M' p y k hk).symm
      have hredM : ∀ q ∈ M' ++ [p], q.2 ∉ (φ q.1).range := fun q hq =>
        hred q (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl hq)))
      have hredL₁ : ∀ q ∈ M' ++ [a], q.2 ∉ (φ q.1).range :=
        deningerAbsorbRight_reduced M' p k hredM
      have haltL₁ : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (M' ++ [a]) :=
        deningerIsChain_of_map_fst (M' ++ [p]) (M' ++ [a])
          (deningerAbsorbRight_map_fst M' p k) ((List.isChain_append.1 haltTail).1)
      have hlenL₁ : (M' ++ [a]).length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlenL hn ⊢
        omega
      obtain ⟨C₁, R₁, V, hsplit, hR₁, hVne, hVred, hValt, hhead, hprod, hdisj, hlen₁⟩ :=
        ih (M' ++ [a]) hlenL₁ (by simp) hredL₁ haltL₁
      obtain ⟨h1, h2, h3, h4⟩ := deningerCycData_reassemble j z M' [p, (⟨j, y⟩ : Σ i, G i)]
        C₁ R₁ V a hstep hsplit.symm hR₁ hhead hprod (by simp [ha]) (by simp)
      refine ⟨(⟨j, z⟩ : Σ i, G i) :: C₁, _, V, ?_, h2, hVne, hVred, hValt, h3, h4, hdisj, ?_⟩
      · rw [show M' ++ [p] ++ [(⟨j, y⟩ : Σ i, G i)] = M' ++ ([p, (⟨j, y⟩ : Σ i, G i)]) by simp]
        exact h1
      · have e1 : (C₁ ++ R₁).length = (M' ++ [a]).length := by rw [hsplit]
        simp only [List.length_append, List.length_cons, List.length_nil,
          List.length_drop] at e1 ⊢
        omega
    · set a : Σ i, G i := ⟨j, y * z⟩ with ha
      have hstep : deningerLetterProd (φ := φ) (M ++ [a]) =
          (PushoutI.of j z)⁻¹ *
            deningerLetterProd (φ := φ)
              ((⟨j, z⟩ : Σ i, G i) :: (M ++ [(⟨j, y⟩ : Σ i, G i)])) * PushoutI.of j z :=
        (deningerCycStep_notMem (⟨j, z⟩ : Σ i, G i) M y).symm
      have hredL₁ : ∀ q ∈ M ++ [a], q.2 ∉ (φ q.1).range := by
        intro q hq
        rcases List.mem_append.1 hq with hq | hq
        · exact hred q (List.mem_cons_of_mem _ (List.mem_append.2 (Or.inl hq)))
        · rw [List.mem_singleton] at hq
          subst hq
          exact hmem
      have haltL₁ : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) (M ++ [a]) :=
        deningerIsChain_of_map_fst (M ++ [(⟨j, y⟩ : Σ i, G i)]) (M ++ [a]) (by simp [ha])
          haltTail
      have hlenL₁ : (M ++ [a]).length ≤ n := by
        simp only [List.length_append, List.length_cons, List.length_nil] at hlenL hn ⊢
        omega
      obtain ⟨C₁, R₁, V, hsplit, hR₁, hVne, hVred, hValt, hhead, hprod, hdisj, hlen₁⟩ :=
        ih (M ++ [a]) hlenL₁ (by simp) hredL₁ haltL₁
      obtain ⟨h1, h2, h3, h4⟩ := deningerCycData_reassemble j z M [(⟨j, y⟩ : Σ i, G i)]
        C₁ R₁ V a hstep hsplit.symm hR₁ hhead hprod (by simp [ha]) (by simp)
      refine ⟨(⟨j, z⟩ : Σ i, G i) :: C₁, _, V, h1, h2, hVne, hVred, hValt, h3, h4, hdisj, ?_⟩
      have e1 : (C₁ ++ R₁).length = (M ++ [a]).length := by rw [hsplit]
      simp only [List.length_append, List.length_cons, List.length_nil, List.length_drop] at e1 ⊢
      omega

/-- **A word as long as its cyclic word is itself cyclically reduced**: the conjugator of the cyclic
reduction is empty, so the word and its cyclic word have the same product. -/
theorem deningerCycRed_of_cycLen_eq (L C R V : List (Σ i, G i))
    (hsplit : L = C ++ R)
    (hprod : deningerLetterProd (φ := φ) R =
      deningerLetterProd (φ := φ) V * (deningerLetterProd (φ := φ) C)⁻¹)
    (hVR : V.length ≤ R.length) (hlen : L.length ≤ V.length) :
    C = [] ∧ deningerLetterProd (φ := φ) L = deningerLetterProd (φ := φ) V := by
  have h1 : L.length = C.length + R.length := by rw [hsplit]; simp
  have hC : C = [] := List.length_eq_zero_iff.1 (by omega)
  subst hC
  refine ⟨rfl, ?_⟩
  rw [hsplit, List.nil_append, hprod, deningerLetterProd_nil, inv_one, mul_one]

end RHTower
