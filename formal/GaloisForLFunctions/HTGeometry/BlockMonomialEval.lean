import GaloisForLFunctions.HTGeometry.BlockMonomialDeterminant
import GaloisForLFunctions.HTGeometry.PolynomialZeroSetNowhereDense

/-!
# Evaluating the block-monomial determinant

The entry of the block-monomial matrix evaluates to the monomial of the corresponding sample block,
and determinants commute with ring homomorphisms, so the evaluated determinant is the evaluation of
the polynomial determinant.  Since that polynomial is nonzero for distinct monomials, and a nonzero
polynomial does not vanish on a nonempty open set, sample blocks with nonsingular evaluation matrix
exist in every nonempty open set of block values.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {σ : Type*} {K : ℕ}

/-- The evaluated block monomial. -/
theorem eval_blockMonomial (m : σ →₀ ℕ) (a : Fin K) (V : (Fin K × σ) → ℂ) :
    MvPolynomial.eval V (MvPolynomial.monomial (blockShift a m) (1 : ℂ)) =
      m.prod fun v e => (V (a, v)) ^ e := by
  classical
  rw [MvPolynomial.eval_monomial, one_mul, blockShift,
    Finsupp.prod_mapDomain_index_inj (fun s t h => by simpa using h)]

/-- The evaluated block-monomial matrix. -/
theorem eval_blockMonomialMatrix (M : Fin K → (σ →₀ ℕ)) (V : (Fin K × σ) → ℂ) (i a : Fin K) :
    MvPolynomial.eval V (blockMonomialMatrix M i a) =
      (M i).prod fun v e => (V (a, v)) ^ e :=
  eval_blockMonomial (M i) a V

/-- **The evaluated determinant is the evaluation of the polynomial determinant.** -/
theorem det_eval_blockMonomialMatrix (M : Fin K → (σ →₀ ℕ)) (V : (Fin K × σ) → ℂ) :
    Matrix.det (fun i a : Fin K => (M i).prod fun v e => (V (a, v)) ^ e) =
      MvPolynomial.eval V ((blockMonomialMatrix M).det) := by
  classical
  rw [RingHom.map_det (MvPolynomial.eval V) (blockMonomialMatrix M)]
  congr 1
  ext i a
  exact (eval_blockMonomialMatrix M V i a).symm

/-- **Sample blocks with nonsingular evaluation matrix exist in every nonempty open set.** -/
theorem exists_blockValues_det_ne_zero [Fintype σ] {M : Fin K → (σ →₀ ℕ)}
    (hM : Function.Injective M) {U : Set ((Fin K × σ) → ℂ)} (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ V ∈ U, Matrix.det (fun i a : Fin K => (M i).prod fun v e => (V (a, v)) ^ e) ≠ 0 := by
  obtain ⟨V, hVU, hV⟩ :=
    exists_eval_ne_zero_of_isOpen (blockMonomialMatrix_det_ne_zero hM) hU hne
  exact ⟨V, hVU, by rw [det_eval_blockMonomialMatrix]; exact hV⟩

end

end GaloisForLFunctions.HTGeometry
