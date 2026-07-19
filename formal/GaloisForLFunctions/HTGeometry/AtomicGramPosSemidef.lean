import GaloisForLFunctions.HTGeometry.ComplexIntegralGram
import GaloisForLFunctions.HTGeometry.ChamberNegInertiaBound
import GaloisForLFunctions.HTGeometry.TotalGramMatrix

/-!
# The rank-one decomposition of the atomic Gram and its positive-semidefinite correction

The atomic part of the scaled Pick kernel is a weighted sum of rank-one conjugate Gram terms, one
per atom, with the atom coefficients as weights.  Only the negative coefficients obstruct positive
semidefiniteness, and each contributes exactly one rank-one term.

Adding back those terms replaces every coefficient by its positive part, which leaves a manifestly
positive semidefinite matrix.  The number of corrections is the chamber grading, so this supplies
the witness the inertia bound consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Matrix Finset

noncomputable section

open scoped Classical ComplexOrder

/-- The scaled Cauchy kernel of one atom, evaluated at the node above another. -/
def atomFeature {d : ℕ} (a : Fin d → ℝ) (y : ℝ) (j l : Fin d) : ℂ :=
  (y : ℂ) / ((a j : ℂ) - upperNode (a l) y)

/-- **The atomic Gram is the coefficient-weighted sum of the atom rank-one terms.** -/
theorem atomicGram_eq_sum_atomFeature {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (l m : Fin d) :
    atomicGram a c y l m
      = ∑ j, (c j : ℂ) * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)) := by
  rw [atomicGram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [atomFeature, atomFeature, map_div₀, Complex.conj_ofReal, map_sub, Complex.conj_ofReal]
  simp only [div_eq_mul_inv, mul_inv]
  ring

/-- The atom index carrying the `i`-th negative coefficient. -/
def negIndex {d : ℕ} (c : Fin d → ℝ) (i : Fin (negCount c)) : Fin d :=
  (((negIndicesEquiv c).symm i : {j // j ∈ negIndices c}) : Fin d)

/-- The coefficient at a negative index is negative. -/
theorem c_negIndex_neg {d : ℕ} (c : Fin d → ℝ) (i : Fin (negCount c)) : c (negIndex c i) < 0 := by
  have h := ((negIndicesEquiv c).symm i).2
  rwa [mem_negIndices] at h

/-- The rank-one correction attached to the `i`-th negative coefficient. -/
def negAtomWitness {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (i : Fin (negCount c)) (l : Fin d) : ℂ :=
  (Real.sqrt (-(c (negIndex c i))) : ℂ) * atomFeature a y (negIndex c i) l

/-- Each correction term is the rank-one term of its atom, weighted by the modulus of its
coefficient. -/
theorem negAtomWitness_mul_star {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (i : Fin (negCount c))
    (l m : Fin d) :
    negAtomWitness a c y i l * star (negAtomWitness a c y i m)
      = ((-(c (negIndex c i)) : ℝ) : ℂ)
        * (atomFeature a y (negIndex c i) l
            * (starRingEnd ℂ) (atomFeature a y (negIndex c i) m)) := by
  have hnn : (0 : ℝ) ≤ -(c (negIndex c i)) := by linarith [c_negIndex_neg c i]
  have hsq : (Real.sqrt (-(c (negIndex c i))) : ℝ) * Real.sqrt (-(c (negIndex c i)))
      = -(c (negIndex c i)) := Real.mul_self_sqrt hnn
  rw [negAtomWitness, negAtomWitness, RCLike.star_def, map_mul, Complex.conj_ofReal]
  rw [show ((-(c (negIndex c i)) : ℝ) : ℂ)
      = ((Real.sqrt (-(c (negIndex c i))) : ℝ) : ℂ) * ((Real.sqrt (-(c (negIndex c i))) : ℝ) : ℂ) by
    rw [← Complex.ofReal_mul, hsq]]
  ring

/-- **Correcting the negative coefficients replaces each coefficient by its positive part.** -/
theorem atomicGram_add_negAtomWitness {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) (l m : Fin d) :
    atomicGram a c y l m
        + (∑ i, Matrix.of fun j k => negAtomWitness a c y i j
            * star (negAtomWitness a c y i k)) l m
      = ∑ j, ((max (c j) 0 : ℝ) : ℂ)
          * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)) := by
  classical
  have hcorr : (∑ i, Matrix.of fun j k => negAtomWitness a c y i j
        * star (negAtomWitness a c y i k)) l m
      = ∑ j ∈ negIndices c, ((-(c j) : ℝ) : ℂ)
          * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)) := by
    rw [Matrix.sum_apply]
    have hterm : ∀ i : Fin (negCount c),
        (Matrix.of fun j k => negAtomWitness a c y i j * star (negAtomWitness a c y i k)) l m
          = ((-(c (negIndex c i)) : ℝ) : ℂ)
            * (atomFeature a y (negIndex c i) l
                * (starRingEnd ℂ) (atomFeature a y (negIndex c i) m)) := by
      intro i
      exact negAtomWitness_mul_star a c y i l m
    rw [Finset.sum_congr rfl fun i _ => hterm i]
    simp only [negIndex]
    rw [Equiv.sum_comp (negIndicesEquiv c).symm fun j : {j // j ∈ negIndices c} =>
      ((-(c (j : Fin d)) : ℝ) : ℂ)
        * (atomFeature a y (j : Fin d) l * (starRingEnd ℂ) (atomFeature a y (j : Fin d) m))]
    exact Finset.sum_coe_sort (negIndices c) (fun j : Fin d => ((-(c j) : ℝ) : ℂ)
      * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)))
  rw [atomicGram_eq_sum_atomFeature, hcorr, negIndices, Finset.sum_filter, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : c j < 0
  · rw [if_pos hj, max_eq_right hj.le]
    push_cast
    ring
  · rw [if_neg hj, max_eq_left (not_lt.1 hj)]
    ring

/-- The matrix of square-rooted positive parts times the atom features. -/
def posPartAtomFactor {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.of fun l j => (Real.sqrt (max (c j) 0) : ℂ) * atomFeature a y j l

/-- **The positive-part atomic Gram is positive semidefinite.**  It is `B Bᴴ` for the matrix of
square-rooted positive parts times the atom features. -/
theorem posPartAtomicGram_posSemidef {d : ℕ} (a c : Fin d → ℝ) (y : ℝ) :
    (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ)
      * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m))).PosSemidef := by
  classical
  have hBB : (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ)
      * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)))
      = posPartAtomFactor a c y * (posPartAtomFactor a c y)ᴴ := by
    ext l m
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      posPartAtomFactor, RCLike.star_def]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hnn : (0 : ℝ) ≤ max (c j) 0 := le_max_right _ _
    have hsq : (Real.sqrt (max (c j) 0) : ℝ) * Real.sqrt (max (c j) 0) = max (c j) 0 :=
      Real.mul_self_sqrt hnn
    rw [map_mul, Complex.conj_ofReal]
    rw [show ((max (c j) 0 : ℝ) : ℂ)
        = ((Real.sqrt (max (c j) 0) : ℝ) : ℂ) * ((Real.sqrt (max (c j) 0) : ℝ) : ℂ) by
      rw [← Complex.ofReal_mul, hsq]]
    ring
  rw [hBB]
  exact Matrix.posSemidef_self_mul_conjTranspose (posPartAtomFactor a c y)

/-- **The chamber witness makes the scaled Pick Gram positive semidefinite.**  One rank-one
correction per negative coefficient turns the atomic part into its positive-part Gram, and the
measure part is positive semidefinite on its own. -/
theorem totalGram_add_negAtomWitness_posSemidef {d : ℕ} (ν : Measure ℝ) (a c : Fin d → ℝ) (y : ℝ)
    (hprod : ∀ l m : Fin d, Integrable (fun t : ℝ =>
      ((y : ℂ) * ((t : ℂ) - upperNode (a l) y)⁻¹) *
        (starRingEnd ℂ) ((y : ℂ) * ((t : ℂ) - upperNode (a m) y)⁻¹)) ν) :
    (totalGram ν a c y
      + ∑ i, Matrix.of fun j k => negAtomWitness a c y i j
          * star (negAtomWitness a c y i k)).PosSemidef := by
  have hsplit : totalGram ν a c y
      + (∑ i, Matrix.of fun j k => negAtomWitness a c y i j * star (negAtomWitness a c y i k))
      = (Matrix.of fun l m => ∑ j, ((max (c j) 0 : ℝ) : ℂ)
          * (atomFeature a y j l * (starRingEnd ℂ) (atomFeature a y j m)))
        + measureGram ν a y := by
    ext l m
    simp only [Matrix.add_apply, totalGram_apply, Matrix.of_apply]
    rw [← atomicGram_add_negAtomWitness a c y l m]
    simp only [Matrix.sum_apply, Matrix.of_apply]
    ring
  rw [hsplit]
  exact (posPartAtomicGram_posSemidef a c y).add (measureGram_posSemidef ν a y hprod)

end

end GaloisForLFunctions.HTGeometry
