import GaloisForLFunctions.HTGeometry.BilinearExteriorPairFactorization
import GaloisForLFunctions.RHTower.SoninEulerCornerConcrete

/-!
# The ordered Sonin prime-pair seam is one exterior tensor

Let `C_p` be the positive Euler-normalized one-prime Sonin corner and let `a_p` be arbitrary complex
prime potentials.  The two one-particle sections are `A_F(a) = ∑ a_p C_p` and `B_F = ∑ C_p`, and the
ordered two-particle difference section is `W_F(a) = ∑_{p,q} (a_p − a_q)(C_p ⊗ C_q)`.  Pure
bilinearity gives the exterior factorization

`W_F(a) = A_F(a) ⊗ B_F − B_F ⊗ A_F(a)`,

so the complete pair coboundary is a **decomposable rank-two exterior tensor**, not an irreducible
double-prime family; the diagonal coefficients vanish automatically.

The same identity holds with the tensor carrier replaced by multiplication in the operator algebra:
the one-particle Gram coboundary `G_F(a) = ∑_{p,q} (a_p − a_q)/√(pq) · L_p^* L_q` is
`L_{conj a}^* L_1 − L_1^* L_a`.  This removes the Hilbert tensor product from the route.
-/

namespace RHTower

open scoped BigOperators TensorProduct

noncomputable section

/-- The positive Euler-normalized one-prime Sonin corner `C_p`, at cutoff `t` and scale `r > 1`. -/
def positiveEulerSoninCorner (t r : ℝ) (hr : 1 < r) : SoninL2 →L[ℂ] SoninL2 :=
  crossBoundary (centralSoninProjection t) (positiveEulerDilationOperator r hr)

/-- `C_p` is the Euler coefficient times the raw dilation corner. -/
theorem positiveEulerSoninCorner_eq_smul (t r : ℝ) (hr : 1 < r) :
    positiveEulerSoninCorner t r hr =
      (-((Real.sqrt r : ℂ)⁻¹)) •
        (crossBoundary (centralSoninProjection t) (dilationSum r hr) :
          SoninL2 →L[ℂ] SoninL2) :=
  centralPositiveEulerCorner_eq_smul t r hr

/-- `(1)`: the `a`-weighted one-particle section `A_F(a) = ∑_p a_p C_p`. -/
def soninWeightedSection {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (a : Fin n → ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ i, a i • positiveEulerSoninCorner t (r i) (hr i)

/-- `(1)`: the universal one-particle section `B_F = ∑_p C_p`. -/
def soninUniversalSection {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i) :
    SoninL2 →L[ℂ] SoninL2 :=
  ∑ i, positiveEulerSoninCorner t (r i) (hr i)

/-- `(2)`: the ordered two-particle difference section `W_F(a)`. -/
def soninOrderedPairSection {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (a : Fin n → ℂ) : SoninL2 ⊗[ℂ] SoninL2 →ₗ[ℂ] SoninL2 ⊗[ℂ] SoninL2 :=
  ∑ i, ∑ j, (a i - a j) •
    TensorProduct.map (positiveEulerSoninCorner t (r i) (hr i)).toLinearMap
      (positiveEulerSoninCorner t (r j) (hr j)).toLinearMap

/-- **`(3)`: the ordered Sonin prime-pair seam is one exterior tensor.** -/
theorem soninOrderedPairSection_eq_exterior {n : ℕ} (t : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 1 < r i) (a : Fin n → ℂ) :
    soninOrderedPairSection t r hr a =
      TensorProduct.map (soninWeightedSection t r hr a).toLinearMap
          (soninUniversalSection t r hr).toLinearMap -
        TensorProduct.map (soninUniversalSection t r hr).toLinearMap
          (soninWeightedSection t r hr a).toLinearMap := by
  have hkey := HTGeometry.sum_sub_smul_tensorMap (R := ℂ)
    (M := SoninL2) (N := SoninL2) (ι := Fin n) a
    (fun i => (positiveEulerSoninCorner t (r i) (hr i)).toLinearMap)
  have hA : (soninWeightedSection t r hr a).toLinearMap =
      ∑ i, a i • (positiveEulerSoninCorner t (r i) (hr i)).toLinearMap := by
    rw [soninWeightedSection]
    push_cast
    rfl
  have hB : (soninUniversalSection t r hr).toLinearMap =
      ∑ i, (positiveEulerSoninCorner t (r i) (hr i)).toLinearMap := by
    rw [soninUniversalSection]
    push_cast
    rfl
  rw [soninOrderedPairSection, hA, hB, hkey]

/-! ## The tensor-free one-particle replacement -/

/-- The reciprocal-root weighted adjoint corner `p^{-1/2} L_p^*`. -/
def soninAdjointWeightedCorner (t r : ℝ) (hr : 1 < r) : SoninL2 →L[ℂ] SoninL2 :=
  ((Real.sqrt r : ℂ)⁻¹) •
    ContinuousLinearMap.adjoint
      (crossBoundary (centralSoninProjection t) (dilationSum r hr) : SoninL2 →L[ℂ] SoninL2)

/-- The reciprocal-root weighted corner `p^{-1/2} L_p`. -/
def soninWeightedCorner (t r : ℝ) (hr : 1 < r) : SoninL2 →L[ℂ] SoninL2 :=
  ((Real.sqrt r : ℂ)⁻¹) •
    (crossBoundary (centralSoninProjection t) (dilationSum r hr) : SoninL2 →L[ℂ] SoninL2)

/-- `(8a)`: the one-particle zero-diagonal Gram coboundary. -/
def soninPrimeGramCoboundary {n : ℕ} (t : ℝ) (r : Fin n → ℝ) (hr : ∀ i, 1 < r i)
    (a : Fin n → ℂ) : SoninL2 →L[ℂ] SoninL2 :=
  ∑ i, ∑ j, (a i - a j) •
    (soninAdjointWeightedCorner t (r i) (hr i) * soninWeightedCorner t (r j) (hr j))

/-- **`(8g)`: the one-particle Gram coboundary is an exterior combination of the universal and the
two Schwarz-related weighted sections.**  No tensor product occurs. -/
theorem soninPrimeGramCoboundary_eq_exterior {n : ℕ} (t : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 1 < r i) (a : Fin n → ℂ) :
    soninPrimeGramCoboundary t r hr a =
      (∑ i, a i • soninAdjointWeightedCorner t (r i) (hr i)) *
          (∑ j, soninWeightedCorner t (r j) (hr j)) -
        (∑ i, soninAdjointWeightedCorner t (r i) (hr i)) *
          (∑ j, a j • soninWeightedCorner t (r j) (hr j)) :=
  HTGeometry.sum_sub_smul_mul (R := ℂ) (A := SoninL2 →L[ℂ] SoninL2) a
    (fun i => soninAdjointWeightedCorner t (r i) (hr i))
    (fun j => soninWeightedCorner t (r j) (hr j))

/-- The coefficient of `L_p^* L_q` in `(8a)` is exactly `(a_p − a_q)/√(pq)`. -/
theorem soninPrimeGramCoboundary_coefficient {n : ℕ} (t : ℝ) (r : Fin n → ℝ)
    (hr : ∀ i, 1 < r i) (a : Fin n → ℂ) (i j : Fin n) :
    (a i - a j) •
        (soninAdjointWeightedCorner t (r i) (hr i) * soninWeightedCorner t (r j) (hr j)) =
      ((a i - a j) / ((Real.sqrt (r i) : ℂ) * (Real.sqrt (r j) : ℂ))) •
        (ContinuousLinearMap.adjoint
            (crossBoundary (centralSoninProjection t) (dilationSum (r i) (hr i)) :
              SoninL2 →L[ℂ] SoninL2) *
          (crossBoundary (centralSoninProjection t) (dilationSum (r j) (hr j)) :
            SoninL2 →L[ℂ] SoninL2)) := by
  rw [soninAdjointWeightedCorner, soninWeightedCorner, smul_mul_assoc, mul_smul_comm,
    smul_smul, smul_smul]
  congr 1
  field_simp

end

end RHTower
