import GaloisForLFunctions.HTGeometry.GammaOppositeShiftBoundary
import GaloisForLFunctions.HTGeometry.MeromorphicExponentialGaugeDA
import GaloisForLFunctions.HTGeometry.ExponentialObservationHypertranscendence
import GaloisForLFunctions.HTGeometry.UnivMeroFieldInstances

/-!
# Thermal-CFT reflected Gamma response boundary

The exact Fourier transform of a two-dimensional thermal CFT light-cone factor contains

`Gamma(h + z) * Gamma(h - z)`,

with the physical frequency slice `z = i*kappa/(2*pi)`.  Euler reflection turns this product
into a nonzero differentially algebraic sine gauge times the translated Gamma ratio with channel
separation `1-2*h`.  The existing Veneziano ratio theorem therefore gives the exact boundary:
the kernel is differentially algebraic precisely when `1-2*h` is integral, and it is
hypertranscendental otherwise.

The primary physics formula is equation (7.8) of A. Manenti, *Thermal CFTs in momentum space*,
arXiv:1905.01355.  The same paper identifies the thermal cylinder as the holographic AdS
black-hole phase.  The physical identification is external to Lean; the meromorphic Gamma
kernel, classification, exceptional half-weight collapse, and finite-sector source theorem are
internal.
-/

open Filter Set Topology Function Complex
open scoped Differential

namespace GaloisForLFunctions

open Bottcher Polynomial

noncomputable section

open scoped UnivMeroFieldInstances

/-- The complexified frequency kernel `Gamma(h+z) * Gamma(h-z)` of a thermal CFT response. -/
def gammaReflectionProductMero (h : ℂ) : meroField Set.univ :=
  gammaShiftMero h * gammaNegativeShiftMero h

/-- Euler reflection factors the thermal kernel into a DA sine gauge and the translated Gamma
ratio whose channel separation is `1-2*h`. -/
theorem gammaReflectionProductMero_eq_gauge_mul_reducedVeneziano (h : ℂ) :
    gammaReflectionProductMero h =
      gammaReflectionGaugeMero h *
        reducedVenezianoAmplitudeMero h (1 - 2 * h) := by
  simpa [gammaReflectionProductMero, gammaOppositeShiftProductMero,
    show 1 - h - h = 1 - 2 * h by ring] using
      gammaOppositeShiftProductMero_eq_gauge_mul_reducedVeneziano h h

/-- **Exact thermal-response boundary.**  The reflected Gamma product is differentially
algebraic exactly at integral `1-2*h`, equivalently at integral twice-weight. -/
theorem differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight
    (h : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ) (gammaReflectionProductMero h) ↔
      ∃ k : ℤ, 1 - 2 * h = (k : ℂ) := by
  simpa [gammaReflectionProductMero, gammaOppositeShiftProductMero,
    show 1 - h - h = 1 - 2 * h by ring] using
      differentialAlgebraicOver_gammaOppositeShiftProductMero_iff_integerSeparation h h

/-- Generic conformal weight gives a hypertranscendental thermal frequency kernel; precisely the
half-integral/integral weight lattice is exceptional. -/
theorem hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight
    (h : ℂ) :
    HypertranscendentalOver (RatFunc ℂ) (gammaReflectionProductMero h) ↔
      ∀ k : ℤ, 1 - 2 * h ≠ (k : ℂ) := by
  rw [HypertranscendentalOver,
    differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight]
  push Not
  rfl

/-- The frequency-dependent part of the complete thermal response, including its elementary
exponential clock readout.  Frequency-independent nonzero constants do not affect the boundary.
For the two signs in Manenti's equation (7.8), the physical slice
`z = i*kappa/(2*pi)` has `lambda = -pi*i` or `lambda = pi*i`. -/
def thermalCFTFrequencyResponseMero (h lambda : ℂ) : meroField Set.univ :=
  gammaReflectionProductMero h * physicalExponentialMero lambda

/-- Actual-function reflected Gamma core of the thermal response. -/
def gammaReflectionProductValue (h z : ℂ) : ℂ :=
  Complex.Gamma (h + z) * Complex.Gamma (h - z)

/-- Actual-function exponential-dressed thermal response, up to a frequency-independent
constant. -/
def thermalCFTFrequencyResponseValue (h lambda z : ℂ) : ℂ :=
  gammaReflectionProductValue h z * Complex.exp (lambda * z)

/-- The Gamma core is even in the complexified frequency coordinate. -/
theorem gammaReflectionProductValue_neg (h z : ℂ) :
    gammaReflectionProductValue h (-z) = gammaReflectionProductValue h z := by
  simp [gammaReflectionProductValue, sub_eq_add_neg]
  ring

/-- **Exponential detailed-balance law.**  Reflecting the observed frequency cancels the entire
Gamma source; the orientation asymmetry is exactly the elementary exponential gauge. -/
theorem thermalCFTFrequencyResponseValue_neg (h lambda z : ℂ) :
    thermalCFTFrequencyResponseValue h lambda (-z) =
      Complex.exp ((-2 * lambda) * z) *
        thermalCFTFrequencyResponseValue h lambda z := by
  have hexp : Complex.exp (lambda * (-z)) =
      Complex.exp ((-2 * lambda) * z) * Complex.exp (lambda * z) := by
    rw [← Complex.exp_add]
    congr 1
    ring
  rw [thermalCFTFrequencyResponseValue, gammaReflectionProductValue_neg, hexp,
    thermalCFTFrequencyResponseValue]
  ring

/-- The positive-orientation physical slice of Manenti's thermal response. -/
def thermalCFTKMSResponseValue (h kappa : ℂ) : ℂ :=
  thermalCFTFrequencyResponseValue h (-Real.pi * Complex.I)
    (Complex.I * kappa / (2 * Real.pi))

/-- **Exact KMS detailed balance on the physical slice.**  The reflected-frequency ratio is the
universal Boltzmann factor; all reflected-Gamma content is orientation-even. -/
theorem thermalCFTKMSResponseValue_neg (h kappa : ℂ) :
    thermalCFTKMSResponseValue h (-kappa) =
      Complex.exp (-kappa) * thermalCFTKMSResponseValue h kappa := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hz : Complex.I * (-kappa) / (2 * Real.pi) =
      -(Complex.I * kappa / (2 * Real.pi)) := by ring
  have harg : (-2 * (-Real.pi * Complex.I)) *
      (Complex.I * kappa / (2 * Real.pi)) = -kappa := by
    field_simp [hpi]
    rw [pow_two, Complex.I_mul_I]
    ring
  rw [thermalCFTKMSResponseValue, hz,
    thermalCFTFrequencyResponseValue_neg, harg]
  rfl

/-- The exponential readout does not alter the exact thermal-response boundary. -/
theorem differentialAlgebraicOver_thermalCFTFrequencyResponseMero_iff_integerWeight
    (h lambda : ℂ) :
    DifferentialAlgebraicOver (RatFunc ℂ)
        (thermalCFTFrequencyResponseMero h lambda) ↔
      ∃ k : ℤ, 1 - 2 * h = (k : ℂ) := by
  have hexpDA := differentialAlgebraicOver_physicalExponentialMero lambda
  have hexp0 := physicalExponentialMero_ne_zero lambda
  constructor
  · intro hresponse
    have hrecover := HTGeometry.differentialAlgebraicOver_mul hresponse
      (HTGeometry.differentialAlgebraicOver_inv hexpDA)
    have hgamma : DifferentialAlgebraicOver (RatFunc ℂ)
        (gammaReflectionProductMero h) := by
      simpa [thermalCFTFrequencyResponseMero, mul_assoc, hexp0] using hrecover
    exact (differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight h).1
      hgamma
  · intro hweight
    exact HTGeometry.differentialAlgebraicOver_mul
      ((differentialAlgebraicOver_gammaReflectionProductMero_iff_integerWeight h).2
        hweight)
      hexpDA

/-- Generic conformal weight remains hypertranscendental after the exact thermal exponential
readout is restored.  Hypertranscendence is therefore a property of the observable's Gamma clock
structure, not of frequency evolution. -/
theorem hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight
    (h lambda : ℂ) :
    HypertranscendentalOver (RatFunc ℂ)
        (thermalCFTFrequencyResponseMero h lambda) ↔
      ∀ k : ℤ, 1 - 2 * h ≠ (k : ℂ) := by
  rw [thermalCFTFrequencyResponseMero,
    HTGeometry.hypertranscendentalOver_mul_differentialAlgebraic_iff
      (differentialAlgebraicOver_physicalExponentialMero lambda)
      (physicalExponentialMero_ne_zero lambda),
    hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight]

/-- At conformal weight `h=1/2`, the Gamma content cancels exactly to the Euler-reflection gauge.
This is the meromorphic reason the paper's frequency response simplifies to a hyperbolic function. -/
theorem gammaReflectionProductMero_half :
    gammaReflectionProductMero (1 / 2 : ℂ) =
      gammaReflectionGaugeMero (1 / 2 : ℂ) := by
  rw [gammaReflectionProductMero, gammaNegativeShiftMero_reflection]
  have harg : (1 : ℂ) - 1 / 2 = 1 / 2 := by ring
  rw [harg]
  have hg : gammaShiftMero (1 / 2 : ℂ) ≠ 0 :=
    gammaShiftMero_ne_zero (1 / 2 : ℂ)
  calc
    gammaShiftMero (1 / 2 : ℂ) *
          (gammaReflectionGaugeMero (1 / 2 : ℂ) *
            (gammaShiftMero (1 / 2 : ℂ))⁻¹) =
        gammaReflectionGaugeMero (1 / 2 : ℂ) *
          (gammaShiftMero (1 / 2 : ℂ) *
            (gammaShiftMero (1 / 2 : ℂ))⁻¹) := by ring
    _ = gammaReflectionGaugeMero (1 / 2 : ℂ) := by
      rw [mul_inv_cancel₀ hg, mul_one]

/-- **Finite-sector source localization.**  If a finite product of thermal CFT Gamma kernels is
hypertranscendental, at least one sector has a nonintegral `1-2*h`; an all-half-integral weight
packet is necessarily differentially algebraic. -/
theorem exists_nonintegerWeight_of_hypertranscendental_finset_product
    {ι : Type*} {s : Finset ι} (weight : ι → ℂ)
    (hHT : HypertranscendentalOver (RatFunc ℂ)
      (∏ i ∈ s, gammaReflectionProductMero (weight i))) :
    ∃ i ∈ s, ∀ k : ℤ, 1 - 2 * weight i ≠ (k : ℂ) := by
  obtain ⟨i, hi, hfactor⟩ :=
    HTGeometry.exists_hypertranscendental_factor_of_finset_prod hHT
  exact ⟨i, hi,
    (hypertranscendentalOver_gammaReflectionProductMero_iff_nonintegerWeight
      (weight i)).1 hfactor⟩

/-- Finite-sector source localization also holds for the complete exponential-dressed thermal
responses: an HT packet has at least one non-half-integral weight sector. -/
theorem exists_nonintegerWeight_of_hypertranscendental_finset_response_product
    {ι : Type*} {s : Finset ι} (weight lambda : ι → ℂ)
    (hHT : HypertranscendentalOver (RatFunc ℂ)
      (∏ i ∈ s, thermalCFTFrequencyResponseMero (weight i) (lambda i))) :
    ∃ i ∈ s, ∀ k : ℤ, 1 - 2 * weight i ≠ (k : ℂ) := by
  obtain ⟨i, hi, hfactor⟩ :=
    HTGeometry.exists_hypertranscendental_factor_of_finset_prod hHT
  exact ⟨i, hi,
    (hypertranscendentalOver_thermalCFTFrequencyResponseMero_iff_nonintegerWeight
      (weight i) (lambda i)).1 hfactor⟩

end

end GaloisForLFunctions
