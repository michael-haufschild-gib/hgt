import GaloisForLFunctions.HTGeometry.SeibergWitten.SpinC

/-!
# Flat Euclidean chiral Clifford multiplication

This module supplies the closed pointwise Clifford representation omitted by the generic
`PointwiseSpinCCliffordData` interface.  Explicit Pauli-type matrices define maps between two
copies of `ℂ²` for every vector in Euclidean four-space.  Both chiral anticommutation identities
are proved against the actual Euclidean inner product.

It is a pointwise flat model.  Integrating this representation to a `Spinᶜ(4)` group action and
identifying that action with the principal-torsor association layer remain separate work.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.SeibergWitten

/-- Positive or negative chiral spinor in the flat Euclidean model. -/
abbrev FlatChiralSpinor := Fin 2 → ℂ

/-- Real coordinate in the canonical Euclidean four-space model. -/
def flatFourCoordinate (v : FourSpace) (i : Fin 4) : ℝ :=
  (EuclideanSpace.equiv (Fin 4) ℝ v) i

/-- Positive-to-negative flat chiral Clifford multiplication. -/
def flatCliffordPlus (v : FourSpace) : FlatChiralSpinor →ₗ[ℂ] FlatChiralSpinor where
  toFun := fun psi => ![
    ((flatFourCoordinate v 0 : ℝ) : ℂ) * psi 0 +
      ((flatFourCoordinate v 1 : ℝ) : ℂ) * Complex.I * psi 0 +
      ((flatFourCoordinate v 2 : ℝ) : ℂ) * psi 1 +
      ((flatFourCoordinate v 3 : ℝ) : ℂ) * Complex.I * psi 1,
    -((flatFourCoordinate v 2 : ℝ) : ℂ) * psi 0 +
      ((flatFourCoordinate v 3 : ℝ) : ℂ) * Complex.I * psi 0 +
      ((flatFourCoordinate v 0 : ℝ) : ℂ) * psi 1 -
      ((flatFourCoordinate v 1 : ℝ) : ℂ) * Complex.I * psi 1]
  map_add' := by
    intro psi chi
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c psi
    ext i
    fin_cases i <;> simp <;> ring

/-- Negative-to-positive flat chiral Clifford multiplication. -/
def flatCliffordMinus (v : FourSpace) : FlatChiralSpinor →ₗ[ℂ] FlatChiralSpinor where
  toFun := fun psi => ![
    -((flatFourCoordinate v 0 : ℝ) : ℂ) * psi 0 +
      ((flatFourCoordinate v 1 : ℝ) : ℂ) * Complex.I * psi 0 +
      ((flatFourCoordinate v 2 : ℝ) : ℂ) * psi 1 +
      ((flatFourCoordinate v 3 : ℝ) : ℂ) * Complex.I * psi 1,
    -((flatFourCoordinate v 2 : ℝ) : ℂ) * psi 0 +
      ((flatFourCoordinate v 3 : ℝ) : ℂ) * Complex.I * psi 0 -
      ((flatFourCoordinate v 0 : ℝ) : ℂ) * psi 1 -
      ((flatFourCoordinate v 1 : ℝ) : ℂ) * Complex.I * psi 1]
  map_add' := by
    intro psi chi
    ext i
    fin_cases i <;> simp <;> ring
  map_smul' := by
    intro c psi
    ext i
    fin_cases i <;> simp <;> ring

/-- Coordinate expansion of the Euclidean four-dimensional inner product. -/
theorem flatFourCoordinate_inner (v w : FourSpace) :
    inner ℝ v w =
      flatFourCoordinate v 0 * flatFourCoordinate w 0 +
      flatFourCoordinate v 1 * flatFourCoordinate w 1 +
      flatFourCoordinate v 2 * flatFourCoordinate w 2 +
      flatFourCoordinate v 3 * flatFourCoordinate w 3 := by
  simp [flatFourCoordinate, EuclideanSpace.inner_eq_star_dotProduct, dotProduct,
    Fin.sum_univ_succ]
  ring

/-- The positive chiral Clifford relation in flat Euclidean signature. -/
theorem flatClifford_positive_relation (v w : FourSpace) :
    (flatCliffordMinus v).comp (flatCliffordPlus w) +
        (flatCliffordMinus w).comp (flatCliffordPlus v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id := by
  ext psi i
  fin_cases i
  · simp [flatCliffordMinus, flatCliffordPlus, flatFourCoordinate_inner]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp [flatCliffordMinus, flatCliffordPlus, flatFourCoordinate_inner]
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- The negative chiral Clifford relation in flat Euclidean signature. -/
theorem flatClifford_negative_relation (v w : FourSpace) :
    (flatCliffordPlus v).comp (flatCliffordMinus w) +
        (flatCliffordPlus w).comp (flatCliffordMinus v) =
      ((-2 * inner ℝ v w : ℝ) : ℂ) • LinearMap.id := by
  ext psi i
  fin_cases i
  · simp [flatCliffordMinus, flatCliffordPlus, flatFourCoordinate_inner]
    ring_nf
    simp only [Complex.I_sq]
    ring
  · simp [flatCliffordMinus, flatCliffordPlus, flatFourCoordinate_inner]
    ring_nf
    simp only [Complex.I_sq]
    ring

/-- Closed pointwise `Spinᶜ` Clifford data on the flat Euclidean spinor fibers. -/
def flatPointwiseSpinCCliffordData :
    PointwiseSpinCCliffordData FourSpace
      (fun _ => FlatChiralSpinor) (fun _ => FlatChiralSpinor) where
  cliffordPlus := fun _ => flatCliffordPlus
  cliffordMinus := fun _ => flatCliffordMinus
  positiveClifford := by
    intro x v w
    exact flatClifford_positive_relation v w
  negativeClifford := by
    intro x v w
    exact flatClifford_negative_relation v w

end GaloisForLFunctions.HTGeometry.SeibergWitten
