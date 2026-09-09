import GaloisForLFunctions.HTGeometry.GomesFockQubitGauge

/-!
Complete spectral observations of the data-only Fock source. This applies the
reconstruction viewpoint of Gomes, arXiv:2607.24901v1 and arXiv:2509.25276v7, by
lifting moment equality to equality of actual compact spectral measures. Source
mass is retained. Different matrix dimensions and different support bounds are
allowed; compact determinacy supplies the exact inverse without proof premises.
-/
open scoped Matrix BigOperators
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory _root_.HTGeometry

/-- Actual spectral measure of arbitrary completed matrix data and observing vector. -/
def gomesFockSpectralMeasure {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) : Measure ℝ :=
  freeFockVectorSpectralMeasure (gomesCompletedFockGenerators B)
    (gomesCompletedFockGenerators_hermitian B) (gomesCompletedFockGenerators_commonKernel B) x

/-- Every concrete vector-state spectral measure has finite total mass. -/
instance gomesFockSpectralMeasure_isFinite {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    IsFiniteMeasure (gomesFockSpectralMeasure B x) := by
  unfold gomesFockSpectralMeasure
  infer_instance

/-- Every moment of the exact spectral measure is the existing Fock source moment. -/
theorem gomesFockSpectralMeasure_hasMoments {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    HasHamburgerMoments (freeFockVectorMoment (gomesCompletedFockGenerators B) x)
      (gomesFockSpectralMeasure B x) :=
  freeFockVectorSpectralMeasure_hasMoments _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B) x

/-- The exact spectral measure is carried by its existing explicit compact source bound. -/
theorem gomesFockSpectralMeasure_carried {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    gomesFockSpectralMeasure B x
      (Set.Icc (-freeFockMatrixSpectralRadius (gomesCompletedFockGenerators B))
        (freeFockMatrixSpectralRadius (gomesCompletedFockGenerators B)))ᶜ = 0 :=
  freeFockVectorSpectralMeasure_carried _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B) x

/-- Total spectral mass is exactly the original zeroth Fock moment. -/
theorem gomesFockSpectralMeasure_totalMass {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    (gomesFockSpectralMeasure B x Set.univ).toReal =
      freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 := by
  rw [freeFockVectorMoment_zero]
  exact freeFockVectorSpectralMeasure_totalMass _ (gomesCompletedFockGenerators_hermitian B)
    (gomesCompletedFockGenerators_commonKernel B) x

/-- Complete moment records reconstruct spectral measures exactly, even across different internal dimensions. -/
theorem gomesFockSpectralMeasure_eq_iff {d k e l : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ)
    (x : Fin (d+1) → ℂ) (y : Fin (e+1) → ℂ) :
    gomesFockSpectralMeasure B x = gomesFockSpectralMeasure C y ↔
      ∀ n, freeFockVectorMoment (gomesCompletedFockGenerators B) x n =
        freeFockVectorMoment (gomesCompletedFockGenerators C) y n := by
  have hB := gomesFockSpectralMeasure_hasMoments B x
  have hC := gomesFockSpectralMeasure_hasMoments C y
  constructor
  · intro h n
    calc
      freeFockVectorMoment (gomesCompletedFockGenerators B) x n =
          ∫ t : ℝ, t^n ∂gomesFockSpectralMeasure B x := (hB n).2.symm
      _ = ∫ t : ℝ, t^n ∂gomesFockSpectralMeasure C y := by rw [h]
      _ = freeFockVectorMoment (gomesCompletedFockGenerators C) y n := (hC n).2
  · intro h
    let R := max (freeFockMatrixSpectralRadius (gomesCompletedFockGenerators B))
      (freeFockMatrixSpectralRadius (gomesCompletedFockGenerators C))
    have hRB : freeFockMatrixSpectralRadius (gomesCompletedFockGenerators B) ≤ R := le_max_left _ _
    have hRC : freeFockMatrixSpectralRadius (gomesCompletedFockGenerators C) ≤ R := le_max_right _ _
    have hBs : gomesFockSpectralMeasure B x (Set.Icc (-R) R)ᶜ = 0 :=
      measure_mono_null (by
        intro t ht ho
        exact ht ⟨(neg_le_neg hRB).trans ho.1,ho.2.trans hRB⟩)
        (gomesFockSpectralMeasure_carried B x)
    have hCs : gomesFockSpectralMeasure C y (Set.Icc (-R) R)ᶜ = 0 :=
      measure_mono_null (by
        intro t ht ho
        exact ht ⟨(neg_le_neg hRC).trans ho.1,ho.2.trans hRC⟩)
        (gomesFockSpectralMeasure_carried C y)
    exact measure_eq_of_moments_eq_of_carried hBs hCs
      (fun n => (hB n).2.symm) (fun n => (hB n).1)
      (fun n => (h n).trans (hC n).2.symm) (fun n => (hC n).1)

/-- A spectral observation vanishes exactly for the zero observing vector. -/
theorem gomesFockSpectralMeasure_zero_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    gomesFockSpectralMeasure B x = 0 ↔ x = 0 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_zero_iff (gomesCompletedFockGenerators B) x).mp
    rw [← gomesFockSpectralMeasure_totalMass,h]
    simp
  · rintro rfl
    apply Measure.measure_univ_eq_zero.mp
    have h : (gomesFockSpectralMeasure B 0 Set.univ).toReal = 0 := by
      rw [gomesFockSpectralMeasure_totalMass,gomesFock_zeroVector_moment]
    exact ((ENNReal.toReal_eq_zero_iff _).mp h).resolve_right (measure_ne_top _ _)

end GaloisForLFunctions.HTGeometry
