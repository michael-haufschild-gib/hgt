import GaloisForLFunctions.HTGeometry.MonoidTangentTranslation
import GaloisForLFunctions.HTGeometry.FreeJetTangentClosure

/-!
# The big cell of a differential algebraic monoid in `SL₂`

The tangent space of `SL₂` at a point `g` is three-dimensional inside the four-dimensional space of
matrices, so the derivation-closure argument that pins a differential algebraic monoid down cannot
run in the four matrix coordinates.  It does run in the three coordinates
`X₀₀, X₀₁, X₁₀`: on the locus `X₀₀ ≠ 0` the fourth entry is determined, and the projection of the
tangent hyperplane `tr(adj(g)·W) = 0` onto the first three coordinates is *surjective*.

The bridge is one multiplication: a differential polynomial `Q` in those three coordinates vanishing
on the big cell of the monoid becomes, after multiplication by `X₀₀`, a differential polynomial
vanishing on the whole monoid, and the Leibniz rule for the linearisation then transports the
vanishing of the linearisation of `X₀₀·Q` to that of `Q`.

* `linearisationForm_mul` — Leibniz for the linearisation;
* `trace_adjugate_mul_fin_two` — the tangent hyperplane in coordinates;
* `bigCellPoints`, `bigCellIdeal`;
* `linearisationForm_eq_zero_of_mem_bigCellIdeal` — **the tangent space of the big cell is the whole
  three-dimensional coordinate space**;
* `bigCellIdeal_eq_zero` — **hence no nonzero differential polynomial in the three coordinates
  vanishes on the big cell of the monoid.**
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open scoped Differential
open GaloisForLFunctions

variable {C : Type*} [Field C] [Differential C]

/-! ### Leibniz for the linearisation -/

variable {ι : Type*}

/-- **The linearisation is a derivation.** -/
theorem linearisationForm_mul (p : ι → C) (F G : DifferentialPolynomial ι C)
    (s : Finset (ι × ℕ)) (X : ι → C) :
    linearisationForm p (F * G) s X
      = differentialPolynomialEvalOver (K := C) p F * linearisationForm p G s X
        + differentialPolynomialEvalOver (K := C) p G * linearisationForm p F s X := by
  rw [linearisationForm, linearisationForm, linearisationForm, Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [MvPolynomial.pderiv_mul, map_add, map_mul, map_mul]
  ring

/-- The linearisation only sees the perturbation at the indeterminates occurring in the
polynomial. -/
theorem linearisationForm_congr (p : ι → C) (F : DifferentialPolynomial ι C)
    {X Y : ι → C} (h : ∀ v ∈ F.vars, X v.1 = Y v.1) :
    linearisationForm p F F.vars X = linearisationForm p F F.vars Y := by
  rw [linearisationForm, linearisationForm]
  exact Finset.sum_congr rfl fun v hv => by rw [h v hv]

/-! ### The tangent hyperplane of `SL₂` in coordinates -/

omit [Differential C] in
/-- The tangent hyperplane at `g`, written out. -/
theorem trace_adjugate_mul_fin_two (g W : Matrix (Fin 2) (Fin 2) C) :
    (Matrix.adjugate g * W).trace
      = g 1 1 * W 0 0 - g 0 1 * W 1 0 - g 1 0 * W 0 1 + g 0 0 * W 1 1 := by
  rw [Matrix.adjugate_fin_two, Matrix.trace_fin_two]
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.of_apply]
  ring

/-! ### The big cell -/

variable (S : Set (DifferentialPolynomial (Fin 2 × Fin 2) C))

/-- The points of the zero set whose upper-left entry is invertible, as coordinate functions. -/
def bigCellPoints : Set ((Fin 2 × Fin 2) → C) :=
  {p | ∃ g : Matrix (Fin 2) (Fin 2) C, g ∈ matrixZeroSet (C := C) (A := C) S ∧
    g 0 0 ≠ 0 ∧ p = fun q => g q.1 q.2}

/-- Differential polynomials in the three coordinates other than the lower-right entry, vanishing
on the big cell of the zero set. -/
def bigCellIdeal : Set (DifferentialPolynomial (Fin 2 × Fin 2) C) :=
  {Q | (∀ v ∈ Q.vars, v.1 ≠ ((1 : Fin 2), (1 : Fin 2))) ∧
    ∀ p ∈ bigCellPoints S, differentialPolynomialEvalOver (K := C) p Q = 0}

variable {S}

/-- The identity is a point of the big cell. -/
theorem bigCellPoints_nonempty
    (hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S) :
    (bigCellPoints S).Nonempty :=
  ⟨fun q => (1 : Matrix (Fin 2) (Fin 2) C) q.1 q.2, 1, hone, by simp, rfl⟩

/-- Multiplying by the upper-left coordinate carries the big-cell ideal into the vanishing ideal of
the whole zero set. -/
theorem X_mul_mem_of_mem_bigCellIdeal
    (hrad : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ h ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0) →
      P ∈ S)
    {Q : DifferentialPolynomial (Fin 2 × Fin 2) C} (hQ : Q ∈ bigCellIdeal S) :
    MvPolynomial.X (((0 : Fin 2), (0 : Fin 2)), 0) * Q ∈ S := by
  refine hrad _ fun h hh => ?_
  rw [map_mul, differentialPolynomialEvalOver_X, differentialJet_zero]
  by_cases h00 : h 0 0 = 0
  · have hz : h (((0 : Fin 2), (0 : Fin 2)) : Fin 2 × Fin 2).1
        (((0 : Fin 2), (0 : Fin 2)) : Fin 2 × Fin 2).2 = 0 := h00
    rw [hz, zero_mul]
  · rw [hQ.2 _ ⟨h, hh, h00, rfl⟩, mul_zero]

/-- **The tangent space of the big cell is the whole three-dimensional coordinate space.** -/
theorem linearisationForm_eq_zero_of_mem_bigCellIdeal
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) S, h.det = 1)
    (hrad : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ h ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0) →
      P ∈ S)
    {Q : DifferentialPolynomial (Fin 2 × Fin 2) C} (hQ : Q ∈ bigCellIdeal S)
    {p : (Fin 2 × Fin 2) → C} (hp : p ∈ bigCellPoints S) (V : (Fin 2 × Fin 2) → C) :
    linearisationForm p Q Q.vars V = 0 := by
  classical
  obtain ⟨g, hg, hg00, rfl⟩ := hp
  set A : DifferentialPolynomial (Fin 2 × Fin 2) C :=
    MvPolynomial.X (((0 : Fin 2), (0 : Fin 2)), 0) with hA
  -- complete `V` to a matrix tangent to `SL₂` at `g`
  set w11 : C := (g 1 0 * V ((0 : Fin 2), (1 : Fin 2)) + g 0 1 * V ((1 : Fin 2), (0 : Fin 2))
      - g 1 1 * V ((0 : Fin 2), (0 : Fin 2))) / g 0 0 with hw11
  set W : Matrix (Fin 2) (Fin 2) C :=
    Matrix.of (fun i j => if (i, j) = ((1 : Fin 2), (1 : Fin 2)) then w11 else V (i, j)) with hW
  have hW00 : W 0 0 = V ((0 : Fin 2), (0 : Fin 2)) := by rw [hW]; simp
  have hW01 : W 0 1 = V ((0 : Fin 2), (1 : Fin 2)) := by rw [hW]; simp
  have hW10 : W 1 0 = V ((1 : Fin 2), (0 : Fin 2)) := by rw [hW]; simp
  have hW11 : W 1 1 = w11 := by rw [hW]; simp
  have hWtr : (Matrix.adjugate g * W).trace = 0 := by
    rw [trace_adjugate_mul_fin_two, hW00, hW01, hW10, hW11, hw11]
    field_simp
    ring
  -- the linearisation of `A * Q` at `g` kills `W`
  have hAQ : A * Q ∈ S := X_mul_mem_of_mem_bigCellIdeal hrad hQ
  have hlin := linearisationForm_eq_zero_of_trace_adjugate_zero S htrans hfull hg
    (hdet g hg) hWtr hAQ
  -- pass to a common index set and apply Leibniz
  set s : Finset ((Fin 2 × Fin 2) × ℕ) := (A * Q).vars ∪ A.vars ∪ Q.vars with hs
  have hsub1 : (A * Q).vars ⊆ s := by rw [hs]; exact (Finset.subset_union_left).trans Finset.subset_union_left
  have hsub2 : A.vars ⊆ s := by rw [hs]; exact (Finset.subset_union_right).trans Finset.subset_union_left
  have hsub3 : Q.vars ⊆ s := by rw [hs]; exact Finset.subset_union_right
  have hcongrAQ := sum_pderiv_eval_congr (fun q : Fin 2 × Fin 2 => g q.1 q.2)
    (fun q : Fin 2 × Fin 2 => W q.1 q.2) (A * Q) hsub1 (Finset.Subset.refl _)
  have hlin' : linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) (A * Q) s
      (fun q : Fin 2 × Fin 2 => W q.1 q.2) = 0 := hcongrAQ.symm.trans hlin
  rw [linearisationForm_mul] at hlin'
  have hQg : differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => g q.1 q.2) Q = 0 :=
    hQ.2 _ ⟨g, hg, hg00, rfl⟩
  rw [hQg, zero_mul, add_zero] at hlin'
  have hAg : differentialPolynomialEvalOver (K := C)
      (fun q : Fin 2 × Fin 2 => g q.1 q.2) A = g 0 0 := by
    rw [hA, differentialPolynomialEvalOver_X, differentialJet_zero]
  rw [hAg] at hlin'
  have hzero : linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) Q s
      (fun q : Fin 2 × Fin 2 => W q.1 q.2) = 0 := by
    rcases mul_eq_zero.mp hlin' with h | h
    · exact absurd h hg00
    · exact h
  -- restrict back to the variables of `Q` and replace `W` by `V`
  have hcongrQ := sum_pderiv_eval_congr (fun q : Fin 2 × Fin 2 => g q.1 q.2)
    (fun q : Fin 2 × Fin 2 => W q.1 q.2) Q hsub3 (Finset.Subset.refl _)
  have hback : linearisationForm (fun q : Fin 2 × Fin 2 => g q.1 q.2) Q Q.vars
      (fun q : Fin 2 × Fin 2 => W q.1 q.2) = 0 := hcongrQ.trans hzero
  rw [← hback]
  refine linearisationForm_congr _ _ fun v hv => ?_
  have hne : v.1 ≠ ((1 : Fin 2), (1 : Fin 2)) := hQ.1 v hv
  rw [hW]
  simp only [Matrix.of_apply, Prod.mk.eta, if_neg hne]

/-- **No nonzero differential polynomial in the three big-cell coordinates vanishes on the big cell
of a differential algebraic monoid in `SL₂` whose tangent space at the identity is all of
`sl₂`.** -/
theorem bigCellIdeal_eq_zero [CharZero C]
    (hrank : NoUniversalJetRelation C)
    {hone : (1 : Matrix (Fin 2) (Fin 2) C) ∈ matrixZeroSet (C := C) (A := C) S}
    (htrans : TangentTranslates S hone)
    (hfull : ∀ Z : Matrix (Fin 2) (Fin 2) C, Z.trace = 0 → Z ∈ matrixTangentM S hone)
    (hdet : ∀ h ∈ matrixZeroSet (C := C) (A := C) S, h.det = 1)
    (hrad : ∀ P : DifferentialPolynomial (Fin 2 × Fin 2) C,
      (∀ h ∈ matrixZeroSet (C := C) (A := C) S,
        differentialPolynomialEvalOver (K := C) (fun q : Fin 2 × Fin 2 => h q.1 q.2) P = 0) →
      P ∈ S) :
    ∀ Q ∈ bigCellIdeal S, Q = 0 := by
  classical
  refine eq_zero_of_pderiv_closed (T := bigCellPoints S) (bigCellPoints_nonempty hone)
    (fun Q hQ p hp => hQ.2 p hp) ?_
  intro Q hQ v
  refine ⟨fun u hu => hQ.1 u (vars_pderiv_subset Q v hu), fun p hp => ?_⟩
  exact pderiv_mem_vanishing_of_full_tangent (T := bigCellPoints S) hrank
    (fun p' hp' V => linearisationForm_eq_zero_of_mem_bigCellIdeal htrans hfull hdet hrad
      hQ hp' V) v p hp

end

end GaloisForLFunctions.HTGeometry
