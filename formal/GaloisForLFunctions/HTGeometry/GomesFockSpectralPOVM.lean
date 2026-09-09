import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowSupport
import GaloisForLFunctions.HTGeometry.GomesFockSpectralWindowGauge
import Mathlib.MeasureTheory.VectorMeasure.Basic

/-! Countably additive spectral measurements from arbitrary completed Fock data.
This extends the corpus applications of the reconstruction and internal-frame
viewpoints in Gomes, arXiv:2607.24901v1 and arXiv:2404.10461. Scalar spectral
measures polarize to a normalized positive matrix-valued measure. As required
by Mathlib's VectorMeasure interface, nonmeasurable sets receive zero; on every
Borel set the value is the previously constructed spectral-window matrix.
No mathematical input hypotheses are supplied to the construction. -/

open scoped Matrix Classical ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- The full countably additive, matrix-valued spectral measure of arbitrary completed data. -/
def gomesFockSpectralPOVM {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    VectorMeasure ℝ (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) where
  measureOf' S := if MeasurableSet S then gomesFockWindowMatrix B S else 0
  empty' := by simp [gomesFockWindowMatrix_empty]
  not_measurable' _ hS := by simp only [if_neg hS]
  m_iUnion' f hf hd := by
    have hU : MeasurableSet (⋃ n, f n) := MeasurableSet.iUnion hf
    have hq : ∀ x : Fin (d+1) → ℂ,
        HasSum (fun n => gomesFockWindowMass B (f n) x)
          (gomesFockWindowMass B (⋃ n, f n) x) := by
      intro x
      have h := (gomesFockSpectralMeasure B x).toSignedMeasure.m_iUnion hf hd
      simpa only [Measure.toSignedMeasure_apply,hf,hU,if_true,measureReal_def,
        gomesFockWindowMass] using h
    have hp : ∀ x y : Fin (d+1) → ℂ,
        HasSum (fun n => (realQuadraticPolarization (gomesFockWindowMass B (f n)) x y : ℂ))
          (realQuadraticPolarization (gomesFockWindowMass B (⋃ n, f n)) x y : ℂ) := by
      intro x y
      exact Complex.hasSum_ofReal.mpr (((hq (x+y)).sub (hq (x-y))).div_const 4)
    simp only [hf,hU,if_true]
    apply Pi.hasSum.mpr
    intro i
    apply Pi.hasSum.mpr
    intro j
    exact (hp (freeFockInternalBasis i) (freeFockInternalBasis j)).sub
      ((hp (freeFockInternalBasis i) (Complex.I • freeFockInternalBasis j)).mul_left Complex.I)

/-- Exact total interface, including Mathlib's convention on nonmeasurable sets. -/
theorem gomesFockSpectralPOVM_apply {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    gomesFockSpectralPOVM B S = if MeasurableSet S then gomesFockWindowMatrix B S else 0 := rfl

/-- Every effect is positive, including the zero value outside the Borel sets. -/
theorem gomesFockSpectralPOVM_posSemidef {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (gomesFockSpectralPOVM B S).PosSemidef := by
  rw [gomesFockSpectralPOVM_apply]
  split_ifs
  · exact gomesFockWindowMatrix_posSemidef B S
  · exact Matrix.PosSemidef.zero

/-- The full spectral measurement is normalized to the identity operator. -/
theorem gomesFockSpectralPOVM_univ {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockSpectralPOVM B Set.univ = 1 := by
  simp [gomesFockSpectralPOVM_apply,gomesFockWindowMatrix_univ]

/-- All effects are contractions in the positive-operator order. -/
theorem gomesFockSpectralPOVM_complement_posSemidef {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) :
    (1-gomesFockSpectralPOVM B S).PosSemidef := by
  rw [gomesFockSpectralPOVM_apply]
  split_ifs
  · exact gomesFockWindowMatrix_complement_posSemidef B S
  · simpa using (Matrix.PosSemidef.one : (1 : Matrix (Fin (d+1)) (Fin (d+1)) ℂ).PosSemidef)

/-- Quadratic evaluation recovers the original scalar spectral measure as a signed measure. -/
theorem gomesFockSpectralPOVM_quadratic {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (S : Set ℝ) (x : Fin (d+1) → ℂ) :
    star x ⬝ᵥ (gomesFockSpectralPOVM B S *ᵥ x) =
      ((gomesFockSpectralMeasure B x).toSignedMeasure S : ℂ) := by
  rw [gomesFockSpectralPOVM_apply,Measure.toSignedMeasure_apply]
  split_ifs
  · exact gomesFockWindowMatrix_quadratic B S x
  · simp

/-- The spectral atom interface agrees exactly with the previous window construction. -/
theorem gomesFockSpectralPOVM_singleton {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (a : ℝ) :
    gomesFockSpectralPOVM B {a} = gomesFockWindowMatrix B {a} := by
  simp [gomesFockSpectralPOVM_apply]

/-- Lower spectral half-lines recover the original effects. -/
theorem gomesFockSpectralPOVM_Iic {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (a : ℝ) :
    gomesFockSpectralPOVM B (Set.Iic a) = gomesFockWindowMatrix B (Set.Iic a) := by
  simp [gomesFockSpectralPOVM_apply]

/-- Upper spectral half-lines recover the original effects. -/
theorem gomesFockSpectralPOVM_Ioi {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (a : ℝ) :
    gomesFockSpectralPOVM B (Set.Ioi a) = gomesFockWindowMatrix B (Set.Ioi a) := by
  simp [gomesFockSpectralPOVM_apply]

/-- Bounded half-open spectral intervals recover the original effects. -/
theorem gomesFockSpectralPOVM_Ioc {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (a b : ℝ) :
    gomesFockSpectralPOVM B (Set.Ioc a b) = gomesFockWindowMatrix B (Set.Ioc a b) := by
  simp [gomesFockSpectralPOVM_apply]

end GaloisForLFunctions.HTGeometry
