import GaloisForLFunctions.HTGeometry.GomesFockCoherentReference
import GaloisForLFunctions.HTGeometry.GomesMomentMassTensorCovariance

/-!
Phase, amplitude, and tensor observations of actual free-Fock sources. Applying the
internal-frame and invariant-reconstruction viewpoints in Gomes, arXiv:2404.10461,
arXiv:2509.25276v7, and arXiv:2607.24901v1, separates three observational levels:
monic frames forget all scalar amplitude and phase; weighted tensors retain amplitude;
coherent reference observations recover the complex scalar itself.
-/
open scoped Matrix ComplexOrder
noncomputable section
namespace GaloisForLFunctions.HTGeometry

/-- Squared complex exponential amplitude is a positive real mass character. -/
theorem gomesFockExp_normSq (w : ℂ) :
    Complex.normSq (Complex.exp w) = Real.exp (2*w.re) := by
  rw [Complex.normSq_eq_norm_sq,Complex.norm_exp,two_mul,Real.exp_add,pow_two]

/-- Exact model of an exponentially rescaled actual Fock observing vector. -/
def gomesFockExponentialModel {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) : GomesMomentModel :=
  gomesMassScaledModel (gomesFockObservationModel B y) (2*w.re)

/-- The model represents the actual rescaled vector moment sequence, with its original amplitude. -/
theorem gomesFockExponentialModel_moments {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) :
    (gomesFockExponentialModel B y w).moments =
      freeFockVectorMoment (gomesCompletedFockGenerators B) (Complex.exp w • gomesFockObservationVector y) := by
  rw [gomesFockExponentialModel,gomesMassScaledModel_moments,gomesFockObservationModel_moments]
  funext n
  rw [freeFockVectorMoment_smul,gomesFockExp_normSq]
  rfl

/-- Entire complex frames forget every exponential scalar change of the observing vector. -/
theorem gomesFockExponential_frame {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentComplexFrame (gomesFockExponentialModel B y w) n z =
      gomesMomentComplexFrame (gomesFockObservationModel B y) n z :=
  gomesMassScaledModel_frame _ _ n z

/-- Projective quotients forget both phase and amplitude of the observing vector. -/
theorem gomesFockExponential_quotient {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentQuotient (gomesFockExponentialModel B y w) n z =
      gomesMomentQuotient (gomesFockObservationModel B y) n z :=
  gomesMassScaledModel_quotient _ _ n z

/-- Weighted observation tensors retain the inverse squared amplitude character. -/
theorem gomesFockExponential_gram {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentObservationGram (gomesFockExponentialModel B y w) n z =
      Real.exp (-(2*w.re)) • gomesMomentObservationGram (gomesFockObservationModel B y) n z :=
  gomesMassScaledModel_gram _ _ n z

/-- Flux tensors retain the inverse squared amplitude character. -/
theorem gomesFockExponential_flux {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux (gomesFockExponentialModel B y w) n z =
      Real.exp (-(2*w.re)) • gomesMomentNormalizedFlux (gomesFockObservationModel B y) n z :=
  gomesMassScaledModel_flux _ _ n z

/-- Full moment observations determine exactly exponential amplitude, leaving phase free. -/
theorem gomesFockExponential_source_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w t : ℂ) :
    (gomesFockExponentialModel B y w).moments = (gomesFockExponentialModel B y t).moments ↔ w.re = t.re := by
  change (gomesMassScaledModel _ _).moments = (gomesMassScaledModel _ _).moments ↔ _
  rw [gomesMassScaledModel_source_injective]
  constructor <;> intro h <;> linarith

/-- Every finite observation Gram has nonzero information, including the initial rank-one level. -/
theorem gomesMomentObservationGram_ne_zero (M : GomesMomentModel) (n : ℕ) (z : ℂ) :
    gomesMomentObservationGram M n z ≠ 0 := by
  intro h
  have he := gomesMomentObservationGram_quadratic M n z ![1,0]
  rw [h] at he
  have hz : gomesMomentWaveEnergy M ![1,0] n z = 0 := by
    simpa using he.symm
  exact (gomesMomentWaveEnergy_unit_pos M n z).ne' hz

/-- One full Gram tensor determines exponential amplitude at every point and observation depth. -/
theorem gomesFockExponential_gram_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w t : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentObservationGram (gomesFockExponentialModel B y w) n z =
      gomesMomentObservationGram (gomesFockExponentialModel B y t) n z ↔ w.re = t.re := by
  rw [gomesFockExponential_gram,gomesFockExponential_gram]
  constructor
  · intro h
    have he := (smul_left_injective ℝ (gomesMomentObservationGram_ne_zero _ n z)) h
    have hh := Real.exp_injective he
    linarith
  · intro h
    rw [h]

/-- A flux tensor determines amplitude precisely off the real boundary. -/
theorem gomesFockExponential_flux_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w t : ℂ) (n : ℕ) (z : ℂ) :
    gomesMomentNormalizedFlux (gomesFockExponentialModel B y w) n z =
      gomesMomentNormalizedFlux (gomesFockExponentialModel B y t) n z ↔ w.re = t.re ∨ z.im = 0 := by
  rw [gomesFockExponential_flux,gomesFockExponential_flux]
  constructor
  · intro h
    by_cases hz : z.im = 0
    · exact Or.inr hz
    · left
      have hd : gomesMomentNormalizedFlux (gomesFockObservationModel B y) n z ≠ 0 := by
        intro he
        exact hz ((gomesMomentNormalizedFlux_eq_zero_iff _ n z).mp he)
      have he := (smul_left_injective ℝ hd) h
      have hh := Real.exp_injective he
      linarith
  · rintro (h|hz)
    · rw [h]
    · rw [(gomesMomentNormalizedFlux_eq_zero_iff _ n z).mpr hz]
      simp

/-- Coherent references recover the whole complex exponential scalar, beyond the amplitude retained by tensors. -/
theorem gomesFockExponential_coherent_reconstruction {d k : ℕ}
    (B : Fin k → Matrix (Fin (d+1)) (Fin (d+1)) ℂ) (y : Fin d → ℂ) (w t : ℂ) :
    gomesFockCoherentMenu (gomesCompletedFockGenerators B) (gomesFockObservationVector y) 1 Complex.I (Complex.exp w) =
      gomesFockCoherentMenu (gomesCompletedFockGenerators B) (gomesFockObservationVector y) 1 Complex.I (Complex.exp t) ↔
        Complex.exp w = Complex.exp t :=
  gomesFockObservation_coherent_reconstruction B y _ _

end GaloisForLFunctions.HTGeometry
