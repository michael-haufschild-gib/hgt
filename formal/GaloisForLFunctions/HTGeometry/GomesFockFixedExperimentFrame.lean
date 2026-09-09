import GaloisForLFunctions.HTGeometry.GomesFockSpectralPOVMGauge
import GaloisForLFunctions.HTGeometry.GomesFockThresholdObservability
import GaloisForLFunctions.HTGeometry.GomesFockAnalyticGauge

/-! A fixed complete experiment already determines its internal frame group.
The generator data and threshold values need not vary: covariance of all observer
states, or of all effects of that one experiment, characterizes unitarity. This
strengthens the previous universal-data applications of Gomes's internal-frame
viewpoint (arXiv:2404.10461) using the normalization exposed by the reconstruction
viewpoint (arXiv:2607.24901v1). No observer-state or unitary hypotheses are assumed. -/

open scoped Matrix Classical
noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory

/-- Covariance of the operator-valued measure at any fixed generator data characterizes unitarity. -/
theorem gomesFockSpectralPOVM_fixed_data_covariance_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    gomesFockSpectralPOVM (gomesFockConjugatedData U B) = gomesFockConjugatedSpectralPOVM U B ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    have h0 := congrArg (fun μ : VectorMeasure ℝ (Matrix (Fin (d+1)) (Fin (d+1)) ℂ) => μ Set.univ) h
    simp only [gomesFockSpectralPOVM_univ,gomesFockConjugatedSpectralPOVM_univ] at h0
    exact mul_eq_one_comm.mp h0.symm
  · intro hu
    exact (gomesFockSpectralPOVM_unitary_covariance_iff U).mpr hu B

/-- A fixed vector-state spectral experiment over all input states characterizes unitary frames. -/
theorem gomesFockSpectralMeasure_fixed_data_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ x, gomesFockSpectralMeasure (gomesFockConjugatedData U B) (U*ᵥx) =
      gomesFockSpectralMeasure B x) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff (gomesCompletedFockGenerators B) U).mp
    intro x
    have h0 := congrArg (fun μ : Measure ℝ => (μ Set.univ).toReal) (h x)
    simpa only [gomesFockSpectralMeasure_totalMass,freeFockVectorMoment_zero] using h0
  · intro hu x
    exact (gomesFockSpectralMeasure_unitary_gauge_iff U).mpr hu B x

/-- Covariance of one complete finite threshold-effect menu already determines unitarity. -/
theorem gomesFockThresholdEffect_fixed_covariance_iff {d k n : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    (∀ bits, gomesFockThresholdEffect (gomesFockConjugatedData U B) cuts bits =
      gomesFockConjugate U (gomesFockThresholdEffect B cuts bits)) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    have hs : (∑ bits, gomesFockThresholdEffect (gomesFockConjugatedData U B) cuts bits) =
        ∑ bits, gomesFockConjugate U (gomesFockThresholdEffect B cuts bits) :=
      Finset.sum_congr rfl (fun bits _ => h bits)
    simp only [gomesFockConjugate,← Finset.sum_mul,← Matrix.mul_sum,
      gomesFockThresholdEffect_sum,Matrix.mul_one] at hs
    exact mul_eq_one_comm.mp hs.symm
  · intro hu bits
    rw [gomesFockThresholdEffect_eq_window,gomesFockThresholdEffect_eq_window]
    exact (gomesFockWindowMatrix_unitary_covariance_iff U).mpr hu B _

/-- One fixed threshold bank over all input states has exactly the unitary internal gauge group. -/
theorem gomesFockThresholdMass_fixed_gauge_iff {d k n : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    (∀ x bits, gomesFockWindowMass (gomesFockConjugatedData U B) (gomesFockThresholdCell cuts bits) (U*ᵥx) =
      gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff (gomesCompletedFockGenerators B) U).mp
    intro x
    have hs : (∑ bits, gomesFockWindowMass (gomesFockConjugatedData U B)
        (gomesFockThresholdCell cuts bits) (U*ᵥx)) =
        ∑ bits, gomesFockWindowMass B (gomesFockThresholdCell cuts bits) x :=
      Finset.sum_congr rfl (fun bits _ => h x bits)
    rw [gomesFockThresholdMass_sum,gomesFockThresholdMass_sum] at hs
    simpa only [freeFockVectorMoment_zero] using hs
  · intro hu x bits
    exact (gomesFockWindowMass_unitary_gauge_iff U).mpr hu B _ x

/-- Coherent references preserve the same exact frame group at fixed experimental data. -/
theorem gomesFockThresholdCoherent_fixed_gauge_iff {d k n : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    (∀ x c, gomesFockThresholdCoherentMenu (gomesFockConjugatedData U B) cuts (U*ᵥx) c =
      gomesFockThresholdCoherentMenu B cuts x c) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockThresholdMass_fixed_gauge_iff U B cuts).mp
    intro x bits
    have h0 := congrArg (fun f : (Fin n → Bool) → ℝ × ℝ × ℝ => (f bits).1) (h x 1)
    simpa only [gomesFockThresholdCoherentMenu,gomesFockWindowIntensityMenu,one_smul] using h0
  · intro hu x c
    funext bits
    simp only [gomesFockThresholdCoherentMenu,gomesFockWindowIntensityMenu,gomesFockWindowMass_smul]
    rw [(gomesFockThresholdMass_fixed_gauge_iff U B cuts).mpr hu x bits]

/-- Unreferenced scalar intensities also determine the exact frame group when every input state is tested. -/
theorem gomesFockThresholdIntensity_fixed_gauge_iff {d k n : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (cuts : Fin n → ℝ) :
    (∀ x c, gomesFockThresholdIntensityMenu (gomesFockConjugatedData U B) cuts (U*ᵥx) c =
      gomesFockThresholdIntensityMenu B cuts x c) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockThresholdMass_fixed_gauge_iff U B cuts).mp
    intro x bits
    simpa only [gomesFockThresholdIntensityMenu,one_smul] using congrFun (h x 1) bits
  · intro hu x c
    funext bits
    simp only [gomesFockThresholdIntensityMenu,gomesFockWindowMass_smul]
    rw [(gomesFockThresholdMass_fixed_gauge_iff U B cuts).mpr hu x bits]

/-- Fourier observations at fixed generator data, over every input state, characterize unitarity. -/
theorem gomesFockFourier_fixed_data_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ x t, gomesFockFourier (gomesFockConjugatedData U B) (U*ᵥx) t = gomesFockFourier B x t) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff (gomesCompletedFockGenerators B) U).mp
    intro x
    have h0 := congrArg Complex.re (h x 0)
    simpa only [gomesFockFourier_zero,Complex.ofReal_re,freeFockVectorMoment_zero] using h0
  · intro hu x t
    exact (gomesFockFourier_unitary_gauge_iff U).mpr hu B x t

/-- Generating-function observations have the same fixed-data frame classification. -/
theorem gomesFockMGF_fixed_data_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ x u, gomesFockMGF (gomesFockConjugatedData U B) (U*ᵥx) u = gomesFockMGF B x u) ↔
      Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockVector_mass_isometry_iff (gomesCompletedFockGenerators B) U).mp
    intro x
    have h0 := congrArg Complex.re (h x 0)
    simpa only [gomesFockMGF_zero,Complex.ofReal_re,freeFockVectorMoment_zero] using h0
  · intro hu x u
    exact (gomesFockMGF_unitary_gauge_iff U).mpr hu B x u

/-- The joint Fourier/MGF/Stieltjes menu needs only one fixed source family to determine its frame group. -/
theorem gomesFockAnalyticMenu_fixed_data_gauge_iff {d k : ℕ}
    (U : Matrix (Fin (d+1)) (Fin (d+1)) ℂ)
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) :
    (∀ x, gomesFockAnalyticMenu (gomesFockConjugatedData U B) (U*ᵥx) =
      gomesFockAnalyticMenu B x) ↔ Uᴴ*U = 1 := by
  constructor
  · intro h
    apply (gomesFockFourier_fixed_data_gauge_iff U B).mp
    intro x t
    exact congrArg (fun p : (ℝ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) => p.1 t) (h x)
  · intro hu x
    exact (gomesFockAnalyticMenu_unitary_gauge_iff U).mpr hu B x

end GaloisForLFunctions.HTGeometry
