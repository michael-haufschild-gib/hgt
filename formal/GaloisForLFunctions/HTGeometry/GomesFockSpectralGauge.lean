import GaloisForLFunctions.HTGeometry.GomesFockSpectralMeasure

/-!
Exact scalar and unitary reconstruction from complete spectral measures. This
applies the invariant-menu and internal-frame viewpoints of Gomes,
arXiv:2607.24901v1 and arXiv:2404.10461, to actual finite Fock spectral measures.
The previous moment classifications survive passage to the full measure, with
all positivity and compact determinacy proved for the concrete data interface.
-/
open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- Rescaling an observing vector multiplies its complete spectral measure by squared amplitude. -/
theorem gomesFockSpectralMeasure_smul {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c : ℂ) :
    gomesFockSpectralMeasure B (c • x) = ENNReal.ofReal (Complex.normSq c) • gomesFockSpectralMeasure B x :=
  freeFockVectorSpectralMeasure_smul _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B) c x

/-- Full spectral measures distinguish exactly scalar squared amplitude, except at the zero state. -/
theorem gomesFockSpectralMeasure_scalar_eq_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockSpectralMeasure B (c • x) = gomesFockSpectralMeasure B (e • x) ↔
      Complex.normSq c = Complex.normSq e ∨ x = 0 := by
  rw [gomesFockSpectralMeasure_eq_iff]
  exact gomesFockScalar_moments_eq_iff _ x c e

/-- The entire spectral measure has exactly the unit-circle scalar stabilizer at nonzero states. -/
theorem gomesFockSpectralMeasure_scalar_stabilizer {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c : ℂ) :
    gomesFockSpectralMeasure B (c • x) = gomesFockSpectralMeasure B x ↔
      Complex.normSq c = 1 ∨ x = 0 := by
  rw [gomesFockSpectralMeasure_eq_iff]
  exact gomesFockScalar_moment_stabilizer _ x c

/-- All vector-state spectral measures reconstruct precisely the unit-circle scalar subgroup. -/
theorem gomesFockSpectralMeasure_global_scalar_stabilizer {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (c : ℂ) :
    (∀ x, gomesFockSpectralMeasure B (c • x) = gomesFockSpectralMeasure B x) ↔
      Complex.normSq c = 1 := by
  simp only [gomesFockSpectralMeasure_eq_iff]
  exact gomesFockScalar_global_stabilizer _ c

/-- Joint generator/state transport preserves every full spectral measure exactly for unitary internal changes. -/
theorem gomesFockSpectralMeasure_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x,
      gomesFockSpectralMeasure (gomesFockConjugatedData U B) (U*ᵥx) = gomesFockSpectralMeasure B x) ↔
      Uᴴ*U = 1 := by
  simp only [gomesFockSpectralMeasure_eq_iff]
  exact gomesFock_vector_gauge_iff U

end GaloisForLFunctions.HTGeometry
