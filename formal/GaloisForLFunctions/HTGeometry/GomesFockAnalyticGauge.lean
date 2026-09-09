import GaloisForLFunctions.HTGeometry.GomesFockSpectralGauge
import GaloisForLFunctions.HTGeometry.FreeFockMatrixFullFourierDecay

/-! Transport of actual spectral observations through internal frames. This applies
Gomes's reconstruction viewpoint (arXiv:2607.24901v1) and the internal-frame viewpoint
of arXiv:2404.10461 to the corpus's existing Fock measures and transforms. These are
corpus applications, not transcriptions of numbered paper statements. All data are
arbitrary: completion discharges generator conditions, and the iff theorems classify
exactly which transformations preserve the full observation menu. -/

open scoped Matrix
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory _root_.HTGeometry

/-- Real spectral observations, including every polynomial moment. -/
def gomesFockSpectralObservable {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ)
    (f : ℝ → ℝ) : ℝ := ∫ t, f t ∂gomesFockSpectralMeasure B x

/-- Polynomial observations recover the original Fock source sequence. -/
theorem gomesFockSpectralObservable_monomial {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (n : ℕ) :
    gomesFockSpectralObservable B x (fun t => t^n) =
      freeFockVectorMoment (gomesCompletedFockGenerators B) x n :=
  (gomesFockSpectralMeasure_hasMoments B x n).2

/-- The full real observation menu determines the compact spectral measure, even across dimensions. -/
theorem gomesFockSpectralObservable_eq_iff {d e k l : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (C : Fin l → Matrix (Fin (e+1)) (Fin (e+1)) ℂ)
    (x : Fin (d+1) → ℂ) (y : Fin (e+1) → ℂ) :
    (∀ f, gomesFockSpectralObservable B x f = gomesFockSpectralObservable C y f) ↔
      gomesFockSpectralMeasure B x = gomesFockSpectralMeasure C y := by
  constructor
  · intro h
    apply (gomesFockSpectralMeasure_eq_iff B C x y).mpr
    intro n
    simpa only [gomesFockSpectralObservable_monomial] using h (fun t => t^n)
  · intro h f
    unfold gomesFockSpectralObservable
    rw [h]

/-- Arbitrary real spectral observations retain precisely scalar modulus. -/
theorem gomesFockSpectralObservable_scalar_eq_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    (∀ f, gomesFockSpectralObservable B (c • x) f = gomesFockSpectralObservable B (e • x) f) ↔
      Complex.normSq c = Complex.normSq e ∨ x = 0 := by
  rw [gomesFockSpectralObservable_eq_iff,gomesFockSpectralMeasure_scalar_eq_iff]

/-- Preservation of every real spectral observation characterizes unitary internal changes. -/
theorem gomesFockSpectralObservable_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x f,
      gomesFockSpectralObservable (gomesFockConjugatedData U B) (Matrix.mulVec U x) f =
        gomesFockSpectralObservable B x f) ↔ Uᴴ*U = 1 := by
  simp only [gomesFockSpectralObservable_eq_iff]
  exact gomesFockSpectralMeasure_unitary_gauge_iff U

/-- Along a scalar orbit, total mass already determines the entire spectral measure. -/
theorem gomesFockSpectralMeasure_scalar_eq_iff_mass_eq {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockSpectralMeasure B (c • x) = gomesFockSpectralMeasure B (e • x) ↔
      freeFockVectorMoment (gomesCompletedFockGenerators B) (c • x) 0 =
        freeFockVectorMoment (gomesCompletedFockGenerators B) (e • x) 0 := by
  rw [gomesFockSpectralMeasure_eq_iff]
  exact gomesFockScalar_record_eq_iff_mass_eq _ x c e

/-- The existing Fourier amplitude with all generator obligations discharged. -/
def gomesFockFourier {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (t : ℝ) : ℂ :=
  freeFockVectorFourierAmplitude (gomesCompletedFockGenerators B)
    (gomesCompletedFockGenerators_hermitian B) (gomesCompletedFockGenerators_commonKernel B) x t

/-- The existing compact generating-function observation. -/
def gomesFockMGF {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (u : ℂ) : ℂ :=
  compactMomentGeneratingFunction (gomesFockSpectralMeasure B x) u

/-- The existing Stieltjes observation with all generator obligations discharged. -/
def gomesFockStieltjes {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (z : ℂ) : ℂ :=
  freeFockVectorStieltjes (gomesCompletedFockGenerators B)
    (gomesCompletedFockGenerators_hermitian B) (gomesCompletedFockGenerators_commonKernel B) x z

/-- Zero frequency records exactly the initial source mass. -/
theorem gomesFockFourier_zero {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    gomesFockFourier B x 0 = (freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 : ℂ) := by
  change (∫ a : ℝ, Complex.exp (-((0*a : ℝ) : ℂ)*Complex.I) ∂gomesFockSpectralMeasure B x) = _
  simp [integral_const, measureReal_def, Complex.real_smul, gomesFockSpectralMeasure_totalMass]

/-- The generating function at the origin also records exactly the initial source mass. -/
theorem gomesFockMGF_zero {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    gomesFockMGF B x 0 = (freeFockVectorMoment (gomesCompletedFockGenerators B) x 0 : ℂ) := by
  unfold gomesFockMGF compactMomentGeneratingFunction
  simp [integral_const, measureReal_def, Complex.real_smul, gomesFockSpectralMeasure_totalMass]

/-- Fourier observations at all times have exactly the unitary internal gauge group. -/
theorem gomesFockFourier_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x t,
      gomesFockFourier (gomesFockConjugatedData U B) (Matrix.mulVec U x) t = gomesFockFourier B x t) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff
      (gomesCompletedFockGenerators (0 : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) U).mp
    intro x
    have h0 := congrArg Complex.re (h 0 x 0)
    simpa only [gomesFockFourier_zero,Complex.ofReal_re,freeFockVectorMoment_zero] using h0
  · intro hu B x t
    have h := (gomesFockSpectralMeasure_unitary_gauge_iff U).mpr hu B x
    change (∫ a : ℝ, Complex.exp (-((t*a : ℝ) : ℂ)*Complex.I) ∂gomesFockSpectralMeasure _ _) =
      ∫ a : ℝ, Complex.exp (-((t*a : ℝ) : ℂ)*Complex.I) ∂gomesFockSpectralMeasure B x
    rw [h]

/-- Generating-function observations have the same exact internal gauge group. -/
theorem gomesFockMGF_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x u,
      gomesFockMGF (gomesFockConjugatedData U B) (Matrix.mulVec U x) u = gomesFockMGF B x u) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff
      (gomesCompletedFockGenerators (0 : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ)) U).mp
    intro x
    have h0 := congrArg Complex.re (h 0 x 0)
    simpa only [gomesFockMGF_zero,Complex.ofReal_re,freeFockVectorMoment_zero] using h0
  · intro hu B x u
    unfold gomesFockMGF
    rw [(gomesFockSpectralMeasure_unitary_gauge_iff U).mpr hu B x]

/-- The joint Fourier, generating-function, and Stieltjes menu of a vector state. -/
def gomesFockAnalyticMenu {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) :
    (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) :=
  (gomesFockFourier B x, gomesFockMGF B x, gomesFockStieltjes B x)

/-- The entire analytic menu is preserved exactly by unitary internal changes. -/
theorem gomesFockAnalyticMenu_unitary_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ, ∀ x,
      gomesFockAnalyticMenu (gomesFockConjugatedData U B) (Matrix.mulVec U x) =
        gomesFockAnalyticMenu B x) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockFourier_unitary_gauge_iff U).mp
    intro B x t
    exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.1 t) (h B x)
  · intro hu B x
    have h := (gomesFockSpectralMeasure_unitary_gauge_iff U).mpr hu B x
    unfold gomesFockAnalyticMenu gomesFockFourier gomesFockMGF gomesFockStieltjes
      freeFockVectorFourierAmplitude freeFockVectorStieltjes
    change (fun t => ∫ a : ℝ, Complex.exp (-((t*a : ℝ) : ℂ)*Complex.I) ∂gomesFockSpectralMeasure _ _,
      compactMomentGeneratingFunction (gomesFockSpectralMeasure _ _),
      fun z => ∫ a : ℝ, ((a : ℂ)-z)⁻¹ ∂gomesFockSpectralMeasure _ _) = _
    simp only [h]
    rfl

/-- All three analytic transforms together still retain only modulus on a scalar orbit. -/
theorem gomesFockAnalyticMenu_scalar_eq_iff {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (x : Fin (d+1) → ℂ) (c e : ℂ) :
    gomesFockAnalyticMenu B (c • x) = gomesFockAnalyticMenu B (e • x) ↔
      Complex.normSq c = Complex.normSq e ∨ x = 0 := by
  constructor
  · intro h
    have h0 := congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => (p.1 0).re) h
    change (gomesFockFourier B (c • x) 0).re = (gomesFockFourier B (e • x) 0).re at h0
    simp only [gomesFockFourier_zero,Complex.ofReal_re] at h0
    exact (gomesFockSpectralMeasure_scalar_eq_iff B x c e).mp
      ((gomesFockSpectralMeasure_scalar_eq_iff_mass_eq B x c e).mpr h0)
  · intro hc
    have h := (gomesFockSpectralMeasure_scalar_eq_iff B x c e).mpr hc
    unfold gomesFockAnalyticMenu gomesFockFourier gomesFockMGF gomesFockStieltjes
      freeFockVectorFourierAmplitude freeFockVectorStieltjes
    change (fun t => ∫ a : ℝ, Complex.exp (-((t*a : ℝ) : ℂ)*Complex.I) ∂gomesFockSpectralMeasure B (c • x),
      compactMomentGeneratingFunction (gomesFockSpectralMeasure B (c • x)),
      fun z => ∫ a : ℝ, ((a : ℂ)-z)⁻¹ ∂gomesFockSpectralMeasure B (c • x)) = _
    simp only [h]
    rfl

end GaloisForLFunctions.HTGeometry
