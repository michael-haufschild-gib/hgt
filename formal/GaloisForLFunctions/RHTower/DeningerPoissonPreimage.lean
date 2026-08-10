import GaloisForLFunctions.RHTower.DeningerPoissonSource
import GaloisForLFunctions.RHTower.DeningerPoissonMoebius
import GaloisForLFunctions.RHTower.DeningerPoissonFourierReflection
import GaloisForLFunctions.RHTower.DeningerCollarExchange
import GaloisForLFunctions.RHTower.DeningerMobiusPreimage

/-!
# The canonical preimage of a Poisson boundary

On a Poisson boundary the canonical Möbius preimage is the boundary function itself: the pullback
of `Z f` along the logarithm is the Poisson sum of `f`, and the corpus's Möbius inversion of the
Poisson sum says exactly that the Möbius-weighted dilation sum recovers `f`.

The collar exchange acts on a Poisson boundary by the Fourier transform of the boundary: the
Poisson operator intertwines Fourier with multiplicative inversion, and `J` *is* multiplicative
inversion in the logarithmic coordinate.

* `deningerMobiusPreimage_poissonSource` : **`f_{Zf} = f` on the ray.**
* `deningerCollarExchange_poissonSource` : **`J(Zf) = Z(ℱf)`.**
-/

namespace RHTower

open SchwartzMap ArithmeticFunction GaloisForLFunctions

noncomputable section

/-- The pullback of a Poisson boundary is the Poisson sum. -/
theorem deningerLogPull_poissonSource (h : DeningerMeyerCap) {x : ℝ} (hx : 0 < x) :
    deningerLogPull ((deningerPoissonSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x
      = deningerPoissonValue ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x := by
  rw [deningerLogPull_apply, deningerPoissonSource_apply, deningerPoissonLog_eq,
    Real.exp_log hx]

/-- **The canonical Möbius preimage of a Poisson boundary is the boundary itself.** -/
theorem deningerMobiusPreimage_poissonSource (h : DeningerMeyerCap) {x : ℝ} (hx : 0 < x) :
    deningerMobiusPreimage ((deningerPoissonSource h : DeningerExpSchwartz) : 𝓢(ℝ, ℂ)) x
      = ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) x := by
  have hinv := deningerMoebius_poissonValue ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
    (deningerMeyerCap_zero h.2) hx
  rw [deningerMoebiusValue] at hinv
  rw [deningerMobiusPreimage, ← hinv]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have hnx : (0 : ℝ) < (n : ℝ) * x := by
      have hnr : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      exact mul_pos hnr hx
    rw [deningerLogPull_poissonSource h hnx]

/-- Meyer's space is stable under the Fourier transform. -/
def deningerMeyerFourier (h : DeningerMeyerCap) : DeningerMeyerCap :=
  ⟨fourierSCLM ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)), deningerMeyerCap_fourierSCLM h.2⟩

@[simp]
theorem deningerMeyerFourier_coe (h : DeningerMeyerCap) :
    ((deningerMeyerFourier h : DeningerMeyerCap) : 𝓢(ℝ, ℂ))
      = fourierSCLM ((h : DeningerMeyerCap) : 𝓢(ℝ, ℂ)) := rfl

/-- **The collar exchange of a Poisson boundary is the Poisson boundary of the Fourier
transform.**  The Poisson operator carries the Fourier involution to multiplicative inversion, and
in the logarithmic coordinate multiplicative inversion is exactly `J`. -/
theorem deningerCollarExchange_poissonSource (h : DeningerMeyerCap) :
    deningerCollarExchange (deningerPoissonSource h)
      = deningerPoissonSource (deningerMeyerFourier h) := by
  refine Subtype.ext (SchwartzMap.ext fun t => ?_)
  rw [deningerCollarExchange_apply, deningerPoissonSource_apply, deningerPoissonSource_apply,
    deningerMeyerFourier_coe, deningerPoissonLog_eq, deningerPoissonLog_eq]
  have hrefl := deningerPoissonValue_fourier_reflection h.2 (Real.exp_pos (-t))
  have hinv : (Real.exp (-t))⁻¹ = Real.exp t := by
    rw [Real.exp_neg, inv_inv]
  rw [hrefl, hinv, ← mul_assoc, ← Complex.ofReal_mul, ← Real.exp_add, neg_add_cancel,
    Real.exp_zero, Complex.ofReal_one, one_mul]

end

end RHTower
