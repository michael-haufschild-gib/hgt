import GaloisForLFunctions.RHTower.Deninger.DeningerShiftDiff
import GaloisForLFunctions.RHTower.Deninger.DeningerWordUnique

/-!
# Conjugating a base element back into the base group

If conjugating a base group element by a word lands back in the base group, the conjugation is
carried out letter by letter: the two words obtained by absorbing the element on the right and its
partner on the left have the same product, so their letters differ by base group elements, and
peeling one letter at a time reduces the length.  Hence a hypothesis on the individual factors —
that a factor element conjugating a base element into the base group does not move it — propagates
to the whole amalgam.

* `deningerHead_of_map_fst` : the head index depends only on the indices.
* `deningerConj_base_eq` : conjugation by a word does not move the base group.
-/

namespace RHTower

open Monoid Monoid.PushoutI Monoid.CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i} {d : NormalWord.Transversal φ}
  [DecidableEq ι] [∀ i, DecidableEq (G i)]

omit [∀ i, Group (G i)] [DecidableEq ι] [∀ i, DecidableEq (G i)] in
/-- **The head index depends only on the indices.** -/
theorem deningerHead_of_map_fst (L M : List (Σ i, G i))
    (hmap : M.map Sigma.fst = L.map Sigma.fst) (i : ι)
    (h : ∀ q ∈ L.head?, i ≠ q.1) : ∀ q ∈ M.head?, i ≠ q.1 := by
  intro q hq
  have h2 : M.head?.map Sigma.fst = L.head?.map Sigma.fst := by
    rw [← List.head?_map, ← List.head?_map, hmap]
  rw [Option.mem_def] at hq
  rw [hq] at h2
  cases hL : L.head? with
  | none => rw [hL] at h2; simp at h2
  | some q' =>
    rw [hL] at h2
    have hq1 : q.1 = q'.1 := by simpa using h2
    rw [hq1]
    exact h q' (by rw [hL]; rfl)

include d in
/-- **Conjugation by a word does not move the base group.**  If every factor element conjugating a
base element into the base group leaves it fixed, then so does every word. -/
theorem deningerConj_base_eq (hφ : ∀ i, Function.Injective (φ i))
    (hcent : ∀ (i : ι) (x : G i) (u v : H), x * φ i u * x⁻¹ = φ i v → v = u)
    (c e : H) : ∀ L : List (Σ i, G i), (∀ p ∈ L, p.2 ∉ (φ p.1).range) →
      List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L →
      deningerLetterProd (φ := φ) L * PushoutI.base φ c =
        PushoutI.base φ e * deningerLetterProd (φ := φ) L → e = c := by
  intro L
  induction L with
  | nil =>
    intro _ _ h
    rw [deningerLetterProd_nil, one_mul, mul_one] at h
    exact (PushoutI.base_injective hφ h).symm
  | cons p L' ih =>
    obtain ⟨i, x⟩ := p
    intro hred halt h
    have hxred : x ∉ (φ i).range := hred _ (List.mem_cons_self ..)
    have hL'red : ∀ p ∈ L', p.2 ∉ (φ p.1).range := fun p hp =>
      hred p (List.mem_cons_of_mem _ hp)
    have hL'alt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) L' :=
      (List.isChain_cons.1 halt).2
    have hL'head : ∀ q ∈ L'.head?, i ≠ q.1 := (List.isChain_cons.1 halt).1
    have hcons : deningerLetterProd (φ := φ) ((⟨i, x⟩ : Σ i, G i) :: L') =
        PushoutI.of (φ := φ) i x * deningerLetterProd (φ := φ) L' :=
      deningerLetterProd_cons _ _
    rcases eq_or_ne L' [] with rfl | hL'ne
    · rw [hcons, deningerLetterProd_nil, mul_one] at h
      have hx : PushoutI.of (φ := φ) i (x * φ i c) = PushoutI.of (φ := φ) i (φ i e * x) := by
        rw [map_mul, map_mul, PushoutI.of_apply_eq_base, PushoutI.of_apply_eq_base]
        exact h
      have hxc : x * φ i c = φ i e * x := PushoutI.of_injective hφ i hx
      refine hcent i x c e ?_
      rw [hxc]
      group
    · obtain ⟨N, q, hL'⟩ : ∃ N q, L' = N ++ [q] := by
        obtain ⟨w, hw⟩ : ∃ w, L'.getLast? = some w := by
          cases hL'g : L'.getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.1 hL'g) hL'ne
          | some w => exact ⟨w, rfl⟩
        exact ⟨L'.dropLast, w, (List.dropLast_append_getLast? _ hw).symm⟩
      set Lp : List (Σ i, G i) := N ++ [(⟨q.1, q.2 * φ q.1 c⟩ : Σ i, G i)] with hLp
      have hmapp : Lp.map Sigma.fst = L'.map Sigma.fst := by
        rw [hLp, hL', deningerAbsorbRight_map_fst]
      have hredp : ∀ p ∈ Lp, p.2 ∉ (φ p.1).range :=
        deningerAbsorbRight_reduced N q c (by rw [← hL']; exact hL'red)
      have haltp : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1) Lp :=
        deningerIsChain_of_map_fst L' Lp hmapp hL'alt
      have hprodp : deningerLetterProd (φ := φ) Lp =
          deningerLetterProd (φ := φ) L' * PushoutI.base φ c := by
        rw [hLp, ← deningerLetterProd_mul_base_snoc N q c, hL']
      have hAred : ∀ p ∈ (⟨i, x⟩ : Σ i, G i) :: Lp, p.2 ∉ (φ p.1).range := by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · exact hxred
        · exact hredp p hp
      have hAalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
          ((⟨i, x⟩ : Σ i, G i) :: Lp) :=
        List.isChain_cons.2 ⟨deningerHead_of_map_fst L' Lp hmapp i hL'head, haltp⟩
      have hBred : ∀ p ∈ (⟨i, φ i e * x⟩ : Σ i, G i) :: L', p.2 ∉ (φ p.1).range := by
        intro p hp
        rcases List.mem_cons.1 hp with rfl | hp
        · rintro ⟨y, hy⟩
          exact hxred ⟨e⁻¹ * y, by rw [map_mul, hy, map_inv]; group⟩
        · exact hL'red p hp
      have hBalt : List.IsChain (fun p q : Σ i, G i => p.1 ≠ q.1)
          ((⟨i, φ i e * x⟩ : Σ i, G i) :: L') :=
        List.isChain_cons.2 ⟨hL'head, hL'alt⟩
      have hAB : deningerLetterProd (φ := φ) ((⟨i, x⟩ : Σ i, G i) :: Lp) =
          deningerLetterProd (φ := φ) ((⟨i, φ i e * x⟩ : Σ i, G i) :: L') := by
        rw [deningerLetterProd_cons, deningerLetterProd_cons, hprodp, map_mul,
          PushoutI.of_apply_eq_base]
        rw [hcons] at h
        simpa [mul_assoc] using h
      obtain ⟨k, hk1, hk2⟩ :=
        deningerWords_head_shift (d := d) i x (φ i e * x) Lp L' hAred hAalt hBred hBalt hAB
      have hke : k = e⁻¹ := by
        refine hcent i x⁻¹ e⁻¹ k ?_
        rw [map_inv, inv_inv]
        have hthis : φ i e * x * φ i k = x := hk1.symm
        have hkey : φ i k = (φ i e * x)⁻¹ * x := by
          rw [eq_inv_mul_iff_mul_eq]
          exact hthis
        rw [hkey]
        group
      refine ih hL'red hL'alt ?_
      rw [hprodp, hke, map_inv] at hk2
      calc deningerLetterProd (φ := φ) L' * PushoutI.base φ c
          = PushoutI.base φ e * ((PushoutI.base φ e)⁻¹ *
            (deningerLetterProd (φ := φ) L' * PushoutI.base φ c)) := by group
        _ = PushoutI.base φ e * deningerLetterProd (φ := φ) L' := by rw [← hk2]

end RHTower
