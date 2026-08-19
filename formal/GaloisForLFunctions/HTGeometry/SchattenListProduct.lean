/-
# Products of Schatten operators

Hölder for two factors iterates along a list: a product of `n` operators of Schatten class `p` lies
in Schatten `p/n`, hence in the trace class as soon as `n ≥ p`.  This is the statement the
telescoping identity for power traces consumes, where the factors are the two operators being
compared and their powers.

Main results:
* `memSchattenClass_list_prod` — **a product of `n` Schatten-`p` operators is Schatten `p/n`**.
* `memSchattenClass_one_list_prod` — hence trace class once the list is long enough.
-/
import GaloisForLFunctions.HTGeometry.SchattenTraceNormPower

open Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
/-- **A product of `n` Schatten-`p` operators lies in Schatten `p/n`.** -/
theorem memSchattenClass_list_prod {p : ℝ} (hp : 0 < p) :
    ∀ L : List (H →L[ℂ] H), L ≠ [] → (∀ X ∈ L, MemSchattenClass p X) →
      MemSchattenClass (p / (L.length : ℝ)) L.prod := by
  intro L
  induction L with
  | nil => intro h _; exact absurd rfl h
  | cons x L ih =>
      intro _ hmem
      rcases eq_or_ne L [] with rfl | hL
      · have hx : MemSchattenClass p x := hmem x (by simp)
        simpa using hx
      · have hLmem : ∀ X ∈ L, MemSchattenClass p X := fun X hX => hmem X (List.mem_cons_of_mem x hX)
        have hIH := ih hL hLmem
        have hn : 0 < L.length := List.length_pos_of_ne_nil hL
        have hnR : (0 : ℝ) < (L.length : ℝ) := by exact_mod_cast hn
        have htriple : Real.HolderTriple p (p / (L.length : ℝ)) (p / ((L.length : ℝ) + 1)) := by
          refine ⟨?_, hp, div_pos hp hnR⟩
          field_simp
          ring
        have hcomp : MemSchattenClass (p / ((L.length : ℝ) + 1)) (x ∘L L.prod) :=
          memSchattenClass_comp htriple (hmem x (by simp)) hIH
        have hlen : (((x :: L).length : ℕ) : ℝ) = (L.length : ℝ) + 1 := by
          simp
        rw [hlen]
        have hprod : (x :: L).prod = x ∘L L.prod := by
          rw [List.prod_cons]
          rfl
        rw [hprod]
        exact hcomp

omit [CompleteSpace H] in
/-- A long enough product of Schatten-`p` operators is trace class. -/
theorem memSchattenClass_one_list_prod {p : ℝ} (hp : 0 < p) (L : List (H →L[ℂ] H))
    (hL : L ≠ []) (hmem : ∀ X ∈ L, MemSchattenClass p X) (hlen : p ≤ (L.length : ℝ)) :
    MemSchattenClass 1 L.prod := by
  have hn : 0 < L.length := List.length_pos_of_ne_nil hL
  have hnR : (0 : ℝ) < (L.length : ℝ) := by exact_mod_cast hn
  have hdivpos : 0 < p / (L.length : ℝ) := div_pos hp hnR
  have hdivle : p / (L.length : ℝ) ≤ 1 := by
    rw [div_le_one hnR]
    exact hlen
  exact (memSchattenClass_list_prod hp L hL hmem).mono hdivpos hdivle

end

end GaloisForLFunctions.HTGeometry
