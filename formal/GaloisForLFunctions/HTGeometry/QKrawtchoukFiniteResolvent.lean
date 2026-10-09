import GaloisForLFunctions.HTGeometry.QKrawtchoukFiniteSpectralModel
import GaloisForLFunctions.HTGeometry.ResolventCompactness
import GaloisForLFunctions.HTGeometry.QuasiMeasureIntegral

/-!
# Actual finite Jacobi resolvents

The finite quadrature operators have bounded two-sided resolvents on the
common sequence space. Their entries in the finite coordinate block are
exactly the polynomial Cauchy integrals of their quadrature measures.
These are the finite operator entries required by the scalar-to-operator
limit argument of arXiv:2609.24149, Theorem 6.1.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators LinearPMap ComplexConjugate
open GaloisForLFunctions.HTGeometry
  (resolventCLM resolventLinear shiftedEquiv shiftedMap_resolventLinear norm_resolventLinear_le)

namespace HTGeometry

/-- The resolvent of the actual finite self-adjoint operator. -/
def inverseQHermiteFiniteResolvent (t u : ℝ) (n : ℕ) (τ a b : ℝ) :
    lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  resolventCLM (inverseQHermiteFiniteJacobi_isSelfAdjoint t u n τ)
    (z := Complex.mk a (Real.exp b)) (Real.exp_pos b).ne'

/-- The finite resolvent is a right inverse on the whole common space. -/
theorem inverseQHermiteFiniteJacobi_resolvent (t u : ℝ) (n : ℕ) (τ a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    inverseQHermiteFiniteJacobiCLM t u n τ (inverseQHermiteFiniteResolvent t u n τ a b f) -
      Complex.mk a (Real.exp b) • inverseQHermiteFiniteResolvent t u n τ a b f = f :=
  shiftedMap_resolventLinear (inverseQHermiteFiniteJacobi_isSelfAdjoint t u n τ)
    (Real.exp_pos b).ne' f

/-- It is also a left inverse, since the finite operator has full domain. -/
theorem inverseQHermiteFiniteResolvent_jacobi (t u : ℝ) (n : ℕ) (τ a b : ℝ)
    (f : lp (fun _ : ℕ => ℂ) 2) :
    inverseQHermiteFiniteResolvent t u n τ a b
      (inverseQHermiteFiniteJacobiCLM t u n τ f - Complex.mk a (Real.exp b) • f) = f := by
  exact congrArg Subtype.val
    ((shiftedEquiv (inverseQHermiteFiniteJacobi_isSelfAdjoint t u n τ)
      (z := Complex.mk a (Real.exp b)) (Real.exp_pos b).ne').symm_apply_apply ⟨f, by trivial⟩)

/-- The finite resolvent bound is uniform in both level and terminal parameter. -/
theorem inverseQHermiteFiniteResolvent_norm_le (t u : ℝ) (n : ℕ) (τ a b : ℝ) :
    ‖inverseQHermiteFiniteResolvent t u n τ a b‖ ≤ Real.exp (-b) := by
  apply ContinuousLinearMap.opNorm_le_bound _ (Real.exp_pos (-b)).le
  intro f
  simpa only [inverseQHermiteFiniteResolvent,
    GaloisForLFunctions.HTGeometry.resolventCLM_apply, Real.exp_neg,
    abs_of_pos (Real.exp_pos b)] using
    norm_resolventLinear_le (inverseQHermiteFiniteJacobi_isSelfAdjoint t u n τ)
      (z := Complex.mk a (Real.exp b)) (Real.exp_pos b).ne' f

private theorem nonreal_difference_ne_zero (a b y : ℝ) :
    (y : ℂ) - Complex.mk a (Real.exp b) ≠ 0 := by
  intro h
  have hi := congrArg Complex.im h
  simp only [Complex.sub_im, Complex.ofReal_im, Complex.zero_im, zero_sub] at hi
  linarith [Real.exp_pos b]

/-- The finite resolvent acts diagonally on the actual quadrature spectral vectors. -/
theorem inverseQHermiteFiniteResolvent_eigenvector (t u : ℝ) (n : ℕ) (τ a b : ℝ)
    (j : Fin (n + 1)) :
    inverseQHermiteFiniteResolvent t u n τ a b (inverseQHermiteFiniteVector t u n τ j) =
      ((inverseQHermiteQuadratureNode t u n τ j : ℂ) - Complex.mk a (Real.exp b))⁻¹ •
        inverseQHermiteFiniteVector t u n τ j := by
  let c := ((inverseQHermiteQuadratureNode t u n τ j : ℂ) - Complex.mk a (Real.exp b))⁻¹
  have hc : c * (inverseQHermiteQuadratureNode t u n τ j : ℂ) - Complex.mk a (Real.exp b) * c = 1 := by
    calc
      _ = c * ((inverseQHermiteQuadratureNode t u n τ j : ℂ) - Complex.mk a (Real.exp b)) := by ring
      _ = 1 := inv_mul_cancel₀ (nonreal_difference_ne_zero a b _)
  have hs : inverseQHermiteFiniteJacobiCLM t u n τ (c • inverseQHermiteFiniteVector t u n τ j) -
      Complex.mk a (Real.exp b) • (c • inverseQHermiteFiniteVector t u n τ j) =
      inverseQHermiteFiniteVector t u n τ j := by
    rw [map_smul, inverseQHermiteFiniteJacobiCLM_eigenvector, smul_smul, smul_smul,
      ← sub_smul, hc, one_smul]
  have h := inverseQHermiteFiniteResolvent_jacobi t u n τ a b
    (c • inverseQHermiteFiniteVector t u n τ j)
  rw [hs] at h
  exact h

/-- Exact finite spectral expansion of every resolvent entry in the coordinate block. -/
theorem inverseQHermiteFiniteResolvent_matrixElement (t u : ℝ) (n : ℕ) (τ a b : ℝ)
    (i j : Fin (n + 1)) :
    inner ℂ (lp.single 2 (i : ℕ) (1 : ℂ))
      (inverseQHermiteFiniteResolvent t u n τ a b (lp.single 2 (j : ℕ) (1 : ℂ))) =
      ∑ k : Fin (n + 1), (inverseQHermiteQuadratureMatrix t u n τ i k : ℂ) *
        (inverseQHermiteQuadratureMatrix t u n τ j k : ℂ) *
          ((inverseQHermiteQuadratureNode t u n τ k : ℂ) - Complex.mk a (Real.exp b))⁻¹ := by
  rw [← inverseQHermiteFiniteVector_reconstruct t u n τ j, map_sum]
  simp only [map_smul, inverseQHermiteFiniteResolvent_eigenvector, inner_sum,
    inner_smul_right, inverseQHermiteFiniteVector_coordinate_inner]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem quadrature_integral (t u : ℝ) (n : ℕ) (τ : ℝ) (f : ℝ → ℂ) :
    (∫ y, f y ∂(quasiProbMeasure (inverseQHermiteMoment_positive t u) n τ : Measure ℝ)) =
      ∑ k : Fin (n + 1), inverseQHermiteQuadratureWeight t u n τ k •
        f (inverseQHermiteQuadratureNode t u n τ k) := by
  change (∫ y, f y ∂quasiProb (inverseQHermiteMoment t u) n τ) = _
  rw [quasiProb_eq_quasiMeasure (inverseQHermiteMoment_zero t u), quasiMeasure,
    integral_finsetWeightedDirac_vector _ _
      (fun y hy => (quasiWeight_pos (inverseQHermiteMoment_positive t u) n τ hy).le)]
  have hsum := Finset.sum_map Finset.univ
    ((quasiNodes (inverseQHermiteMoment t u) n τ).orderEmbOfFin
      (quasiNodes_card (inverseQHermiteMoment_positive t u) n τ)).toEmbedding
    (fun y => quasiWeight (inverseQHermiteMoment t u) n τ y • f y)
  rw [Finset.map_orderEmbOfFin_univ] at hsum
  exact hsum

private theorem matrix_product (t u : ℝ) (n : ℕ) (τ : ℝ) (i j k : Fin (n + 1)) :
    (inverseQHermiteQuadratureMatrix t u n τ i k : ℂ) *
      (inverseQHermiteQuadratureMatrix t u n τ j k : ℂ) =
      (inverseQHermiteQuadratureWeight t u n τ k : ℂ) *
        (((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ k) *
          (orthonormalPoly (inverseQHermiteMoment t u) j).eval (inverseQHermiteQuadratureNode t u n τ k) : ℝ) : ℂ) := by
  have hs := Real.sq_sqrt (inverseQHermiteQuadratureWeight_pos t u n τ k).le
  have hr : inverseQHermiteQuadratureMatrix t u n τ i k * inverseQHermiteQuadratureMatrix t u n τ j k =
      inverseQHermiteQuadratureWeight t u n τ k *
        ((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ k) *
          (orthonormalPoly (inverseQHermiteMoment t u) j).eval (inverseQHermiteQuadratureNode t u n τ k)) := by
    unfold inverseQHermiteQuadratureMatrix
    calc
      _ = Real.sqrt (inverseQHermiteQuadratureWeight t u n τ k) ^ 2 *
          ((orthonormalPoly (inverseQHermiteMoment t u) i).eval (inverseQHermiteQuadratureNode t u n τ k) *
            (orthonormalPoly (inverseQHermiteMoment t u) j).eval (inverseQHermiteQuadratureNode t u n τ k)) := by ring
      _ = _ := by rw [hs]
  simpa only [Complex.ofReal_mul] using congrArg Complex.ofReal hr

/-- The actual finite operator entries are exactly the quadrature Cauchy integrals. -/
theorem inverseQHermiteFiniteResolvent_matrixElement_integral (t u : ℝ) (n : ℕ) (τ a b : ℝ)
    (i j : Fin (n + 1)) :
    inner ℂ (lp.single 2 (i : ℕ) (1 : ℂ))
      (inverseQHermiteFiniteResolvent t u n τ a b (lp.single 2 (j : ℕ) (1 : ℂ))) =
      ∫ y, (((orthonormalPoly (inverseQHermiteMoment t u) i).eval y *
        (orthonormalPoly (inverseQHermiteMoment t u) j).eval y : ℝ) : ℂ) *
          ((y : ℂ) - Complex.mk a (Real.exp b))⁻¹
        ∂(quasiProbMeasure (inverseQHermiteMoment_positive t u) n τ : Measure ℝ) := by
  rw [inverseQHermiteFiniteResolvent_matrixElement, quadrature_integral]
  apply Finset.sum_congr rfl
  intro k _
  rw [matrix_product, Complex.real_smul]
  ring

end HTGeometry
