import GaloisForLFunctions.HTGeometry.NumberFieldArchimedeanUnitBalancing
import GaloisForLFunctions.HTGeometry.ComplexJacobiDecomposition
import GaloisForLFunctions.HTGeometry.SiegelSet

/-!
# Simultaneous Jacobi coordinates over all infinite places

Every point of the number-field archimedean cone has real Jacobi data at real places and complex
Hermitian Jacobi data at complex places.  Their positive diagonals form one real place-weight
table, so unconditional Dirichlet-unit balancing applies directly.  All decompositions, positivity
proofs, and determinant-one units are constructed internally.
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix NumberField NumberField.InfinitePlace
open scoped Classical ComplexOrder NumberField

noncomputable section

variable {K : Type*} [Field K] [NumberField K]
variable {n : ℕ}

/-- Simultaneous real and complex Jacobi coordinates of one archimedean cone point. -/
structure NumberFieldArchimedeanJacobiData
    (A : numberFieldArchimedeanPositiveForms K n) where
  realU : {w : InfinitePlace K // w.IsReal} → Matrix (Fin n) (Fin n) ℝ
  realD : {w : InfinitePlace K // w.IsReal} → Fin n → ℝ
  realPos : ∀ w i, 0 < realD w i
  realUpper : ∀ w i j, j < i → realU w i j = 0
  realUnit : ∀ w i, realU w i i = 1
  realForm : ∀ w,
    (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) =
      (realU w)ᵀ * Matrix.diagonal (realD w) * realU w
  complexU : {w : InfinitePlace K // w.IsComplex} → Matrix (Fin n) (Fin n) ℂ
  complexD : {w : InfinitePlace K // w.IsComplex} → Fin n → ℂ
  complexPos : ∀ w i, 0 < complexD w i
  complexUpper : ∀ w i j, j < i → complexU w i j = 0
  complexUnit : ∀ w i, complexU w i i = 1
  complexForm : ∀ w,
    (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) =
      (complexU w)ᴴ * Matrix.diagonal (complexD w) * complexU w

omit [NumberField K] in
/-- Every archimedean cone point has simultaneous Jacobi data at all infinite places. -/
theorem exists_numberFieldArchimedeanJacobiData
    (A : numberFieldArchimedeanPositiveForms K n) :
    Nonempty (NumberFieldArchimedeanJacobiData A) := by
  classical
  have hr : ∀ w : {w : InfinitePlace K // w.IsReal},
      ∃ (U : Matrix (Fin n) (Fin n) ℝ) (d : Fin n → ℝ),
        (∀ i, 0 < d i) ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧
        (A.1.1 w : Matrix (Fin n) (Fin n) ℝ) = Uᵀ * Matrix.diagonal d * U :=
    fun w => exists_jacobi_decomposition (A.2.1 w)
  choose realU realD realPos realUpper realUnit realForm using hr
  have hc : ∀ w : {w : InfinitePlace K // w.IsComplex},
      ∃ (U : Matrix (Fin n) (Fin n) ℂ) (d : Fin n → ℂ),
        (∀ i, 0 < d i) ∧ (∀ i j, j < i → U i j = 0) ∧ (∀ i, U i i = 1) ∧
        (A.1.2 w : Matrix (Fin n) (Fin n) ℂ) = Uᴴ * Matrix.diagonal d * U :=
    fun w => exists_complex_jacobi_decomposition (A.2.2 w)
  choose complexU complexD complexPos complexUpper complexUnit complexForm using hc
  exact ⟨⟨realU, realD, realPos, realUpper, realUnit, realForm,
    complexU, complexD, complexPos, complexUpper, complexUnit, complexForm⟩⟩

/-- Positive real Jacobi weight at an arbitrary infinite place. -/
def numberFieldArchimedeanJacobiWeight
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (i : Fin n) (w : InfinitePlace K) : ℝ :=
  if hw : w.IsReal then J.realD ⟨w, hw⟩ i
  else (J.complexD ⟨w, not_isReal_iff_isComplex.mp hw⟩ i).re

omit [NumberField K] in
theorem numberFieldArchimedeanJacobiWeight_pos
    {A : numberFieldArchimedeanPositiveForms K n}
    (J : NumberFieldArchimedeanJacobiData A)
    (i : Fin n) (w : InfinitePlace K) :
    0 < numberFieldArchimedeanJacobiWeight J i w := by
  classical
  rw [numberFieldArchimedeanJacobiWeight]
  split_ifs with hw
  · exact J.realPos ⟨w, hw⟩ i
  · simpa using (Complex.lt_def.1
      (J.complexPos ⟨w, not_isReal_iff_isComplex.mp hw⟩ i)).1

/-- One field-only radius balances the Jacobi diagonals of every archimedean cone point.  Jacobi
data, positive weights, and determinant-one units are all constructed internally. -/
theorem exists_numberFieldArchimedeanJacobi_balancingRadius :
    ∃ R : ℝ, 0 < R ∧ ∀ (m : ℕ)
      (A : numberFieldArchimedeanPositiveForms K (m + 1)),
      ∃ J : NumberFieldArchimedeanJacobiData A,
        ∃ u : Fin (m + 1) → (𝓞 K)ˣ,
          (∏ i, u i = 1) ∧
          ∀ i w,
            Real.exp (-(2 * (m + 1 : ℝ) * R)) *
                  (Real.exp (numberFieldWeightedPlaceMean
                      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                    Real.exp (numberFieldCenteredPlaceProfileAverage
                      (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)) ≤
              numberFieldArchimedeanJacobiWeight J i w *
                (w (((u i : 𝓞 K) : K))) ^ 2 ∧
            numberFieldArchimedeanJacobiWeight J i w *
                (w (((u i : 𝓞 K) : K))) ^ 2 ≤
              Real.exp (2 * (m + 1 : ℝ) * R) *
                  (Real.exp (numberFieldWeightedPlaceMean
                      (fun v => Real.log (numberFieldArchimedeanJacobiWeight J i v))) *
                    Real.exp (numberFieldCenteredPlaceProfileAverage
                      (fun j v => Real.log (numberFieldArchimedeanJacobiWeight J j v)) w)) := by
  obtain ⟨R, hR, hbalance⟩ :=
    exists_numberFieldDetOneUnit_positiveWeight_balancingRadius (K := K)
  refine ⟨R, hR, ?_⟩
  intro m A
  let J : NumberFieldArchimedeanJacobiData A :=
    Classical.choice (exists_numberFieldArchimedeanJacobiData A)
  obtain ⟨u, hu, hbounds⟩ := hbalance m
    (fun i w => numberFieldArchimedeanJacobiWeight J i w)
    (fun i w => numberFieldArchimedeanJacobiWeight_pos J i w)
  exact ⟨J, u, hu, hbounds⟩

end

end GaloisForLFunctions.HTGeometry
