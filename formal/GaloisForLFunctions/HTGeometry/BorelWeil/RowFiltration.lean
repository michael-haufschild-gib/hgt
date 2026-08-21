/-
Copyright (c) 2026 Michael Barenbaum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Barenbaum
-/
import GaloisForLFunctions.HTGeometry.BorelWeil.PolySections
import GaloisForLFunctions.HTGeometry.BorelWeil.LUDecomposition

/-!
# The row-weight filtration and unipotence of the lower unitriangular action

Left translation by a lower unitriangular matrix replaces the coordinate `X_{ij}` by
`X_{ij} + ∑_{r < i} L_{ir} X_{rj}`, i.e. by itself plus terms of strictly smaller *row weight*.
Consequently the induced operator on polynomials is the identity plus an operator that strictly
lowers the row-weight filtration.  This is the elementary substitute for Kolchin's theorem used to
produce highest weight vectors.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.rowWeight` — the row weight of a monomial.
* `GaloisForLFunctions.HTGeometry.BorelWeil.Fle`, `Flt` — the (non-strict and strict) filtration.

## Main results

* `substLeft_sub_mem_Flt` — `substLeft L p - p` has strictly smaller row weight than `p`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The weight assigning to a matrix coordinate its row index. -/
def rowW (N : ℕ) : Fin N × Fin N → ℕ := fun ij => (ij.1 : ℕ)

/-- The row weight of a monomial exponent. -/
def rowWeight (d : (Fin N × Fin N) →₀ ℕ) : ℕ := Finsupp.weight (rowW N) d

theorem rowWeight_add (d e : (Fin N × Fin N) →₀ ℕ) :
    rowWeight (d + e) = rowWeight d + rowWeight e := by
  simp [rowWeight]

@[simp] theorem rowWeight_zero : rowWeight (0 : (Fin N × Fin N) →₀ ℕ) = 0 := by
  simp [rowWeight]

theorem rowWeight_single (ij : Fin N × Fin N) (m : ℕ) :
    rowWeight (Finsupp.single ij m) = m * (ij.1 : ℕ) := by
  simp [rowWeight, Finsupp.weight_apply, Finsupp.sum_single_index, rowW, mul_comm]

variable (k) in
/-- Polynomials all of whose monomials have row weight at most `a`. -/
def Fle (a : ℕ) : Submodule k (MvPolynomial (Fin N × Fin N) k) where
  carrier := {p | ∀ d ∈ p.support, rowWeight d ≤ a}
  add_mem' {p q} hp hq d hd := by
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact hp d h
    · exact hq d h
  zero_mem' := by simp
  smul_mem' c p hp d hd := hp d (MvPolynomial.support_smul hd)

variable (k) in
/-- Polynomials all of whose monomials have row weight strictly less than `a`. -/
def Flt (a : ℕ) : Submodule k (MvPolynomial (Fin N × Fin N) k) where
  carrier := {p | ∀ d ∈ p.support, rowWeight d < a}
  add_mem' {p q} hp hq d hd := by
    rcases Finset.mem_union.mp (MvPolynomial.support_add hd) with h | h
    · exact hp d h
    · exact hq d h
  zero_mem' := by simp
  smul_mem' c p hp d hd := hp d (MvPolynomial.support_smul hd)

theorem mem_Fle {a : ℕ} {p : MvPolynomial (Fin N × Fin N) k} :
    p ∈ Fle k a ↔ ∀ d ∈ p.support, rowWeight d ≤ a := Iff.rfl

theorem mem_Flt {a : ℕ} {p : MvPolynomial (Fin N × Fin N) k} :
    p ∈ Flt k a ↔ ∀ d ∈ p.support, rowWeight d < a := Iff.rfl

theorem Flt_le_Fle (a : ℕ) : Flt k (N := N) a ≤ Fle k a := fun _ hp d hd => le_of_lt (hp d hd)

theorem Fle_mono {a b : ℕ} (h : a ≤ b) : Fle k (N := N) a ≤ Fle k b :=
  fun _ hp d hd => le_trans (hp d hd) h

theorem Flt_mono {a b : ℕ} (h : a ≤ b) : Flt k (N := N) a ≤ Flt k b :=
  fun _ hp d hd => lt_of_lt_of_le (hp d hd) h

theorem C_mem_Fle (c : k) : (MvPolynomial.C c : MvPolynomial (Fin N × Fin N) k) ∈ Fle k 0 := by
  intro d hd
  have : d = 0 := by
    have := MvPolynomial.support_C_subset (a := c) (σ := Fin N × Fin N) hd
    simpa using this
  simp [this]

theorem X_mem_Fle (ij : Fin N × Fin N) :
    (MvPolynomial.X ij : MvPolynomial (Fin N × Fin N) k) ∈ Fle k (rowW N ij) := by
  intro d hd
  have : d = Finsupp.single ij 1 := by
    have := MvPolynomial.support_X (R := k) (n := ij)
    rw [this] at hd
    simpa using hd
  rw [this, rowWeight_single]
  simp [rowW]

theorem mul_mem_Fle {a b : ℕ} {p q : MvPolynomial (Fin N × Fin N) k}
    (hp : p ∈ Fle k a) (hq : q ∈ Fle k b) : p * q ∈ Fle k (a + b) := by
  classical
  intro d hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [rowWeight_add]
  exact Nat.add_le_add (hp d₁ hd₁) (hq d₂ hd₂)

theorem mul_mem_Flt_left {a b : ℕ} {p q : MvPolynomial (Fin N × Fin N) k}
    (hp : p ∈ Flt k a) (hq : q ∈ Fle k b) : p * q ∈ Flt k (a + b) := by
  classical
  intro d hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [rowWeight_add]
  exact Nat.add_lt_add_of_lt_of_le (hp d₁ hd₁) (hq d₂ hd₂)

theorem mul_mem_Flt_right {a b : ℕ} {p q : MvPolynomial (Fin N × Fin N) k}
    (hp : p ∈ Fle k a) (hq : q ∈ Flt k b) : p * q ∈ Flt k (a + b) := by
  classical
  intro d hd
  obtain ⟨d₁, hd₁, d₂, hd₂, rfl⟩ := Finset.mem_add.mp (MvPolynomial.support_mul p q hd)
  rw [rowWeight_add]
  exact Nat.add_lt_add_of_le_of_lt (hp d₁ hd₁) (hq d₂ hd₂)

theorem substLeft_X (L : Matrix (Fin N) (Fin N) k) (ij : Fin N × Fin N) :
    substLeft L (MvPolynomial.X ij)
      = ∑ r : Fin N, MvPolynomial.C (L ij.1 r) * MvPolynomial.X (r, ij.2) := by
  simp [substLeft]

/-- The key step: left translation by a lower unitriangular matrix moves a coordinate by terms of
strictly smaller row weight. -/
theorem substLeft_X_sub_mem_Flt {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    (ij : Fin N × Fin N) :
    substLeft L (MvPolynomial.X ij) - MvPolynomial.X ij ∈ Flt k (rowW N ij) := by
  classical
  rw [substLeft_X, ← Finset.add_sum_erase _ _ (Finset.mem_univ ij.1), hL.2 ij.1,
    map_one, one_mul]
  have hij : (ij.1, ij.2) = ij := rfl
  rw [hij, add_sub_cancel_left]
  refine Submodule.sum_mem _ fun r hr => ?_
  have hrne : r ≠ ij.1 := (Finset.mem_erase.mp hr).1
  rcases lt_or_gt_of_ne hrne with hlt | hgt
  · refine mul_mem_Flt_right (C_mem_Fle _) ?_
    intro d hd
    have hd' : d = Finsupp.single (r, ij.2) 1 := by
      have := MvPolynomial.support_X (R := k) (n := (r, ij.2))
      rw [this] at hd
      simpa using hd
    rw [hd', rowWeight_single]
    simpa [rowW] using hlt
  · rw [hL.1 ij.1 r hgt, map_zero, zero_mul]
    exact Submodule.zero_mem _

/-- Multiplicativity of the filtration estimate. -/
theorem substLeft_prod_sub_mem {L : Matrix (Fin N) (Fin N) k} (hL : IsLowerUni L)
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (x : ι → MvPolynomial (Fin N × Fin N) k) (a : ι → ℕ)
    (hx : ∀ i ∈ s, x i ∈ Fle k (a i))
    (hdx : ∀ i ∈ s, substLeft L (x i) - x i ∈ Flt k (a i)) :
    (∏ i ∈ s, x i) ∈ Fle k (∑ i ∈ s, a i) ∧
      substLeft L (∏ i ∈ s, x i) - ∏ i ∈ s, x i ∈ Flt k (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty =>
    refine ⟨?_, ?_⟩
    · simpa using (C_mem_Fle (k := k) (N := N) 1)
    · simp
  | insert i s hi ih =>
    have hx' : ∀ j ∈ s, x j ∈ Fle k (a j) := fun j hj => hx j (Finset.mem_insert_of_mem hj)
    have hdx' : ∀ j ∈ s, substLeft L (x j) - x j ∈ Flt k (a j) := fun j hj =>
      hdx j (Finset.mem_insert_of_mem hj)
    obtain ⟨hP, hdP⟩ := ih hx' hdx'
    have hxi : x i ∈ Fle k (a i) := hx i (Finset.mem_insert_self i s)
    have hdxi : substLeft L (x i) - x i ∈ Flt k (a i) := hdx i (Finset.mem_insert_self i s)
    have hphiP : substLeft L (∏ j ∈ s, x j) ∈ Fle k (∑ j ∈ s, a j) := by
      have : substLeft L (∏ j ∈ s, x j)
          = (substLeft L (∏ j ∈ s, x j) - ∏ j ∈ s, x j) + ∏ j ∈ s, x j := by ring
      rw [this]
      exact Submodule.add_mem _ (Flt_le_Fle _ hdP) hP
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    refine ⟨mul_mem_Fle hxi hP, ?_⟩
    have hsplit : substLeft L (x i * ∏ j ∈ s, x j) - x i * ∏ j ∈ s, x j
        = (substLeft L (x i) - x i) * substLeft L (∏ j ∈ s, x j)
          + x i * (substLeft L (∏ j ∈ s, x j) - ∏ j ∈ s, x j) := by
      rw [map_mul]; ring
    rw [hsplit]
    exact Submodule.add_mem _ (mul_mem_Flt_left hdxi hphiP) (mul_mem_Flt_right hxi hdP)

end GaloisForLFunctions.HTGeometry.BorelWeil
