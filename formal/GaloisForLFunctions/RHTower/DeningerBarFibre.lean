import GaloisForLFunctions.RHTower.DeningerBarInsertComm

/-!
# The bar differential as a pushforward along the faces

The fibre of the `j`-th face over a word is the two-element set of unit insertions, which
degenerates to one element exactly when the letter at `j` is the unit.  Writing the coefficient
description of the bar differential as a sum over that fibre exhibits `b` as the pushforward
along the faces, which is the form in which the simplicial cancellation applies.

* `deningerBarFibre` : the fibre of a face, as a finite set of words.
* `deningerBarFibreSum_eq_sum` : **the fibre sum is a sum over the fibre.**
* `deningerBarFibre_disjoint` : fibres over distinct words are disjoint.
-/

namespace RHTower

open GaloisForLFunctions

open scoped Classical

noncomputable section

variable {L : ℕ}

/-- **The fibre of the `j`-th bar face** over a word: the two unit insertions. -/
def deningerBarFibre (j : Fin (L + 1)) (f : Fin (L + 1) → DeningerLattice) :
    Finset (Fin (L + 2) → DeningerLattice) :=
  {deningerInsertUnit j.castSucc f, deningerInsertUnit j.succ f}

theorem mem_deningerBarFibre {j : Fin (L + 1)} {f : Fin (L + 1) → DeningerLattice}
    {v : Fin (L + 2) → DeningerLattice} :
    v ∈ deningerBarFibre j f ↔ deningerBarFaceWord j v = some f := by
  rw [deningerBarFibre, deningerBarFaceWord_eq_some_iff]
  simp [Finset.mem_insert, Finset.mem_singleton]

/-- Two unit insertions at consecutive positions differ exactly when the merged letter is
nonunit. -/
theorem deningerInsertUnit_ne_of_ne_zero {j : Fin (L + 1)}
    {f : Fin (L + 1) → DeningerLattice} (h : f j ≠ 0) :
    deningerInsertUnit j.castSucc f ≠ deningerInsertUnit j.succ f := by
  intro heq
  apply h
  have := congrFun heq j.castSucc
  rw [deningerInsertUnit_same, deningerInsertUnit_succ_apply_castSucc] at this
  exact this.symm

/-- **The fibre sum of the bar differential is a sum over the face fibre.** -/
theorem deningerBarFibreSum_eq_sum (c : DeningerBarWord → ℂ)
    (f : Fin (L + 1) → DeningerLattice) (j : Fin (L + 1)) :
    deningerBarFibreSum c f j
      = ∑ v ∈ deningerBarFibre j f, c (⟨L + 1, v⟩ : DeningerBarWord) := by
  rw [deningerBarFibre, deningerBarFibreSum]
  by_cases h : f j = 0
  · rw [if_pos h, deningerInsertUnit_succ_eq_castSucc h]
    simp [deningerInsertUnitWord]
  · rw [if_neg h, Finset.sum_pair (deningerInsertUnit_ne_of_ne_zero h)]
    rfl

/-- Fibres of the same face over distinct words are disjoint. -/
theorem deningerBarFibre_disjoint {j : Fin (L + 1)}
    {f g : Fin (L + 1) → DeningerLattice} (h : f ≠ g) :
    Disjoint (deningerBarFibre j f) (deningerBarFibre j g) := by
  rw [Finset.disjoint_left]
  intro v hv hv'
  rw [mem_deningerBarFibre] at hv hv'
  exact h (Option.some_injective _ (hv.symm.trans hv'))

/-- **The bar differential is the signed pushforward along the faces.** -/
theorem deningerBarDiffCoe_eq_sum (c : DeningerBarWord → ℂ)
    (f : Fin (L + 1) → DeningerLattice) :
    deningerBarDiffCoe c (⟨L, f⟩ : DeningerBarWord)
      = ∑ j : Fin (L + 1), (-1 : ℂ) ^ (j : ℕ) *
          ∑ v ∈ deningerBarFibre j f, c (⟨L + 1, v⟩ : DeningerBarWord) := by
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deningerBarFibreSum_eq_sum]

end

end RHTower
