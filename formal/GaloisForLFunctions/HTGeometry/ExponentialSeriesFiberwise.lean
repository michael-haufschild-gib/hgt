import GaloisForLFunctions.HTGeometry.ExponentialSeriesAlgebra
import GaloisForLFunctions.HTGeometry.BohrExponentialSeriesCoefficient

/-!
# Reading an exponential series frequency by frequency

A monomial in the jets of a carrier is an exponential series indexed by tuples, and different tuples
can share a frequency.  Regrouping by the fibres of the frequency map turns it into a series indexed
by the frequencies themselves, whose frequency map is the identity and therefore injective.

The Bohr coefficient at a frequency is then exactly the sum of the amplitudes over that fibre.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

variable {J : Type*}

/-- The amplitude carried by one frequency: the sum over its fibre. -/
def fiberAmplitude (B : J → ℂ) (Omega : J → ℝ) (nu : ℝ) : ℂ :=
  ∑' j : {j : J // Omega j = nu}, B (j : J)

theorem summable_norm_fiberAmplitude {B : J → ℂ} {Omega : J → ℝ}
    (hB : Summable fun j => ‖B j‖) :
    Summable fun nu : ℝ => ‖fiberAmplitude B Omega nu‖ := by
  have hsig : Summable fun p : Σ nu : ℝ, {j : J // Omega j = nu} => ‖B (p.2 : J)‖ :=
    ((Equiv.sigmaFiberEquiv Omega).summable_iff (f := fun j => ‖B j‖)).2 hB
  have hnorm : Summable fun nu : ℝ => ∑' j : {j : J // Omega j = nu}, ‖B (j : J)‖ :=
    hsig.sigma
  refine Summable.of_nonneg_of_le (fun nu => norm_nonneg _) (fun nu => ?_) hnorm
  exact norm_tsum_le_tsum_norm (hsig.sigma_factor nu)

/-- **Regrouping an exponential series by frequency.** -/
theorem expSeriesCarrier_fiberwise (B : J → ℂ) (Omega : J → ℝ)
    (hB : Summable fun j => ‖B j‖) (t : ℝ) :
    expSeriesCarrier B Omega t = expSeriesCarrier (fiberAmplitude B Omega) id t := by
  have hsum : Summable fun j => B j * expChar (Omega j) t := by
    refine Summable.of_norm ?_
    simpa [norm_mul] using hB
  have hsig : Summable fun p : Σ nu : ℝ, {j : J // Omega j = nu} =>
      B (p.2 : J) * expChar (Omega (p.2 : J)) t :=
    ((Equiv.sigmaFiberEquiv Omega).summable_iff
      (f := fun j => B j * expChar (Omega j) t)).2 hsum
  have hstep : expSeriesCarrier B Omega t
      = ∑' nu : ℝ, ∑' j : {j : J // Omega j = nu},
        B (j : J) * expChar (Omega (j : J)) t := by
    rw [expSeriesCarrier, ← hsig.tsum_sigma]
    exact ((Equiv.sigmaFiberEquiv Omega).tsum_eq
      (fun j => B j * expChar (Omega j) t)).symm
  rw [hstep, expSeriesCarrier]
  refine tsum_congr fun nu => ?_
  have hchar : ∀ j : {j : J // Omega j = nu},
      B (j : J) * expChar (Omega (j : J)) t = B (j : J) * expChar nu t := by
    intro j
    rw [j.2]
  rw [tsum_congr hchar, tsum_mul_right]
  rfl

/-- **The Bohr coefficient of an exponential series at a frequency is its fibre sum.** -/
theorem bohrCoefficient_expSeriesCarrier_fiber (B : J → ℂ) (Omega : J → ℝ)
    (hB : Summable fun j => ‖B j‖) (nu : ℝ) :
    bohrCoefficient (expSeriesCarrier B Omega) nu = fiberAmplitude B Omega nu := by
  have hfun : expSeriesCarrier B Omega = expSeriesCarrier (fiberAmplitude B Omega) id :=
    funext fun t => expSeriesCarrier_fiberwise B Omega hB t
  rw [hfun]
  exact bohrCoefficient_expSeriesCarrier (summable_norm_fiberAmplitude hB)
    Function.injective_id nu

/-! ## Vanishing series -/

theorem bohrCoefficient_zero (lam : ℝ) :
    bohrCoefficient (fun _ : ℝ => (0 : ℂ)) lam = 0 := by
  have hval : (fun t : ℝ => (0 : ℂ) * bohrChar lam t) = fun _ : ℝ => (0 : ℂ) := by
    funext t
    ring
  rw [bohrCoefficient, hval]
  exact bohrMean_zero

/-- **A vanishing exponential series has vanishing amplitudes, frequency by frequency.** -/
theorem fiberAmplitude_eq_zero_of_expSeriesCarrier_eq_zero (B : J → ℂ) (Omega : J → ℝ)
    (hB : Summable fun j => ‖B j‖) (hzero : ∀ t : ℝ, expSeriesCarrier B Omega t = 0) (nu : ℝ) :
    fiberAmplitude B Omega nu = 0 := by
  have hfun : expSeriesCarrier B Omega = fun _ : ℝ => (0 : ℂ) := funext hzero
  have hcoef := bohrCoefficient_expSeriesCarrier_fiber B Omega hB nu
  rw [hfun, bohrCoefficient_zero] at hcoef
  exact hcoef.symm

end

end GaloisForLFunctions
