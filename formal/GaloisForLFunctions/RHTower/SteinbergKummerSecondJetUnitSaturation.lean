import Mathlib

/-!
# Steinberg--Kummer second-jet unit saturation

Exact Euler-derivation certificate for the universal Steinberg cell. In characteristic not two,
with both logarithmic weights nonzero, the cell and its first two jets generate the unit ideal;
equivalently every derivation-stable ideal containing the cell is the whole ring.
-/

namespace RHTower

noncomputable section

open MvPolynomial

variable {k : Type*} [Field k]

abbrev SKPoly (k : Type*) [Field k] := MvPolynomial (Fin 2) k

def skX : SKPoly k := X 0
def skY : SKPoly k := X 1

noncomputable def skEuler (A B : k) : Derivation k (SKPoly k) (SKPoly k) :=
  ((C A * skX) • pderiv (0 : Fin 2)) +
    ((C B * skY) • pderiv (1 : Fin 2))

def skCell : SKPoly k := (skX - 1) * (skY - 1)

theorem skEuler_cell (A B : k) :
    skEuler A B skCell =
      C (A + B) * skCell + C A * (skY - 1) + C B * (skX - 1) := by
  simp [skEuler, skCell, skX, skY, Derivation.leibniz]
  ring

theorem skEuler_cell_two (A B : k) :
    skEuler A B (skEuler A B skCell) =
      (C A + C B) ^ (2 : ℕ) * skCell +
        C A * (C A + 2 * C B) * (skY - 1) +
        C B * (2 * C A + C B) * (skX - 1) + 2 * C A * C B := by
  rw [skEuler_cell]
  simp [skEuler, skCell, skX, skY, Derivation.leibniz]
  ring

def skJetIdeal (A B : k) : Ideal (SKPoly k) :=
  Ideal.span {skCell, skEuler A B skCell, skEuler A B (skEuler A B skCell)}

/-- SKJS-1: the Steinberg cell and its first two Euler jets generate the unit ideal. -/
theorem skJetIdeal_eq_top (A B : k) (hA : A ≠ 0) (hB : B ≠ 0)
    (h2 : (2 : k) ≠ 0) : skJetIdeal A B = ⊤ := by
  let I := skJetIdeal A B
  let U : SKPoly k := skX - 1
  let V : SKPoly k := skY - 1
  have hc : skCell ∈ I := by
    exact Ideal.subset_span (by simp)
  have hdc : skEuler A B skCell ∈ I := by
    exact Ideal.subset_span (by simp)
  have hd2c : skEuler A B (skEuler A B skCell) ∈ I := by
    exact Ideal.subset_span (by simp)
  have hg : skEuler A B skCell - (C A + C B) * skCell ∈ I :=
    I.sub_mem hdc (I.mul_mem_left _ hc)
  have hg_eq : skEuler A B skCell - (C A + C B) * skCell = C A * V + C B * U := by
    rw [skEuler_cell]
    rw [map_add]
    dsimp [U, V]
    ring
  have hBU2 : C B * U ^ (2 : ℕ) ∈ I := by
    have hm := I.sub_mem (I.mul_mem_left U hg) (I.mul_mem_left (C A) hc)
    rw [hg_eq] at hm
    have heq : U * (C A * V + C B * U) - C A * skCell = C B * U ^ (2 : ℕ) := by
      simp [U, V, skCell]
      ring
    rw [heq] at hm
    exact hm
  let h : SKPoly k :=
    skEuler A B (skEuler A B skCell) - (C A + C B) ^ (2 : ℕ) * skCell -
      (C A + 2 * C B) * (skEuler A B skCell - (C A + C B) * skCell)
  have hh : h ∈ I := by
    exact I.sub_mem (I.sub_mem hd2c (I.mul_mem_left _ hc)) (I.mul_mem_left _ hg)
  have hh_eq : h = 2 * C A * C B + C B * (C A - C B) * U := by
    dsimp [h]
    rw [skEuler_cell_two]
    rw [hg_eq]
    simp [U, V, skCell]
    ring
  let h' : SKPoly k := 2 * C A * C B - C B * (C A - C B) * U
  have hconst : C ((2 * A * B) ^ (2 : ℕ)) ∈ I := by
    have hm := I.add_mem (I.mul_mem_right h' hh)
      (I.mul_mem_left (C B * (C A - C B) ^ (2 : ℕ)) hBU2)
    rw [hh_eq] at hm
    have heq :
        (2 * C A * C B + C B * (C A - C B) * U) * h' +
            C B * (C A - C B) ^ (2 : ℕ) * (C B * U ^ (2 : ℕ)) =
          C ((2 * A * B) ^ (2 : ℕ)) := by
      simp only [map_pow, map_mul, map_ofNat]
      dsimp [h']
      ring
    rw [heq] at hm
    exact hm
  apply (Ideal.eq_top_iff_one I).2
  have hs : (2 * A * B) ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 (mul_ne_zero (mul_ne_zero h2 hA) hB)
  have hm := I.mul_mem_left (C (((2 * A * B) ^ (2 : ℕ))⁻¹)) hconst
  have hone : C (((2 * A * B) ^ (2 : ℕ))⁻¹) * C ((2 * A * B) ^ (2 : ℕ)) = (1 : SKPoly k) := by
    rw [← map_mul]
    simp [hs]
  rw [hone] at hm
  exact hm

/-- Stable-ideal form of SKJS-1. -/
theorem skStableIdeal_eq_top (A B : k) (hA : A ≠ 0) (hB : B ≠ 0)
    (h2 : (2 : k) ≠ 0) (I : Ideal (SKPoly k))
    (hc : skCell ∈ I)
    (hstable : ∀ f ∈ I, skEuler A B f ∈ I) : I = ⊤ := by
  apply top_unique
  rw [← skJetIdeal_eq_top A B hA hB h2]
  rw [skJetIdeal, Ideal.span_le]
  intro f hf
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf
  rcases hf with rfl | rfl | rfl
  · exact hc
  · exact hstable skCell hc
  · exact hstable _ (hstable skCell hc)

end

end RHTower
