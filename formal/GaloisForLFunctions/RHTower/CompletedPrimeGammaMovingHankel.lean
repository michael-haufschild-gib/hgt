import GaloisForLFunctions.RHTower.PrimeArchHankelDeterminantCriterion
import GaloisForLFunctions.RHTower.SeamFluxCompletion

/-!
# Moving completed prime--Gamma Hankel determinants

This file constructs the source-defined moving determinant family used by the
far-right anchor route.  At a base point `sigma`, translate the completed
logarithmic derivative along the centered spectral direction, subtract its
base value, and apply the same normalized divided difference used at the
functional-equation center.

At `sigma = 1/2` this moving germ is locally the existing normalized continued
prime--Gamma source germ.  Consequently its finite Hankel matrices and
determinants are exactly the matrices already proved equivalent to RH.  No
positivity or zero-location assertion is made here.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The completed logarithmic derivative vanishes at the functional-equation center. -/
theorem logDeriv_xi_one_half : logDeriv xi (1 / 2) = 0 := by
  have h := logDeriv_xi_reciprocity (1 / 2)
  norm_num at h
  have hsum : logDeriv xi (1 / 2) + logDeriv xi (1 / 2) = 0 :=
    eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 : ℂ) * logDeriv xi (1 / 2) = 0 := by
    simpa [two_mul] using hsum
  exact (mul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Completed relative trace translated to an arbitrary base point `sigma`. -/
def completedMovingRelativeTrace (sigma z : ℂ) : ℂ :=
  Complex.I * (logDeriv xi (sigma + z * Complex.I) - logDeriv xi sigma)

/-- Normalized moving trace-moment germ at `sigma`. -/
def completedMovingMomentGerm (sigma : ℂ) : ℂ → ℂ :=
  normalizedTraceMomentGerm (completedMovingRelativeTrace sigma)

/-- Finite moving completed-source Hankel matrix. -/
def completedMovingHankelMatrix (n : ℕ) (sigma : ℂ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => analyticTraceMoments (completedMovingMomentGerm sigma)
    ((i : ℕ) + (j : ℕ))

/-- Leading determinant of the moving completed-source Hankel matrix. -/
def completedMovingHankelDet (n : ℕ) (sigma : ℂ) : ℝ :=
  (completedMovingHankelMatrix n sigma).det

/-- At the center, the moving relative trace is exactly the centered Xi logarithmic trace. -/
theorem completedMovingRelativeTrace_one_half (z : ℂ) :
    completedMovingRelativeTrace (1 / 2) z = logDeriv XiC z := by
  rw [completedMovingRelativeTrace, logDeriv_XiC_eq_mul_I_logDeriv_xi,
    logDeriv_xi_one_half, sub_zero]

/-- Normalized divided difference preserves equality of analytic germs. -/
theorem normalizedTraceMomentGerm_eventuallyEq_of_eventuallyEq
    {f g : ℂ → ℂ} (h : f =ᶠ[nhds 0] g) :
    normalizedTraceMomentGerm f =ᶠ[nhds 0] normalizedTraceMomentGerm g := by
  have h0 : f 0 = g 0 := h.eq_of_nhds
  have hd : deriv f 0 = deriv g 0 := h.deriv_eq
  filter_upwards [h] with z hz
  rw [normalizedTraceMomentGerm, normalizedTraceMomentGerm]
  by_cases hz0 : z = 0
  · subst z
    rw [dslope_same, dslope_same, hd]
  · rw [dslope_of_ne _ hz0, dslope_of_ne _ hz0,
      slope_def_module, slope_def_module, hz, h0]

/-- The moving center germ and the existing normalized prime--Gamma germ are the same germ. -/
theorem completedMovingMomentGerm_one_half_eventuallyEq :
    completedMovingMomentGerm (1 / 2) =ᶠ[nhds 0] normalizedPrimeArchMomentGerm := by
  have hmove : completedMovingRelativeTrace (1 / 2) = logDeriv XiC := by
    funext z
    exact completedMovingRelativeTrace_one_half z
  rw [completedMovingMomentGerm, hmove, normalizedPrimeArchMomentGerm]
  exact normalizedTraceMomentGerm_eventuallyEq_of_eventuallyEq
    continuedPrimeArchSourceRelativeTrace_eventuallyEq_logDeriv_XiC.symm

/-- The moving completed-source matrix at `1/2` is the established central prime--Gamma matrix. -/
theorem completedMovingHankelMatrix_one_half (n : ℕ) :
    completedMovingHankelMatrix n (1 / 2) =
      primeArchSourceMomentHankelMatrix n := by
  ext i j
  rw [completedMovingHankelMatrix, primeArchSourceMomentHankelMatrix]
  unfold analyticTraceMoments
  rw [(completedMovingMomentGerm_one_half_eventuallyEq.iteratedDeriv_eq
    (2 * ((i : ℕ) + (j : ℕ))))]
  rfl

/-- The moving determinant at `1/2` is the central source determinant consumed by the RH gate. -/
theorem completedMovingHankelDet_one_half (n : ℕ) :
    completedMovingHankelDet n (1 / 2) =
      (primeArchSourceMomentHankelMatrix n).det := by
  rw [completedMovingHankelDet, completedMovingHankelMatrix_one_half]

/-! ## Euler-half-plane source-value realization -/

/-- The centered spectral coordinate corresponding to a completed `s`-coordinate. -/
def completedCenteredCoordinate (s : ℂ) : ℂ :=
  -(s - 1 / 2) * Complex.I

theorem one_half_add_completedCenteredCoordinate_mul_I (s : ℂ) :
    1 / 2 + completedCenteredCoordinate s * Complex.I = s := by
  rw [completedCenteredCoordinate]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- On the Euler half-plane, one prime--Gamma source value is exactly the completed logarithmic
derivative at the corresponding `s`-coordinate. -/
theorem primeArchSourceRelativeTrace_completedCenteredCoordinate
    {s : ℂ} (hs : 1 < s.re) :
    primeArchSourceRelativeTrace (completedCenteredCoordinate s) =
      Complex.I * logDeriv xi s := by
  rw [primeArchSourceRelativeTrace,
    one_half_add_completedCenteredCoordinate_mul_I]
  rw [← infinitePrimeFlux_eq_vonMangoldtLSeries hs,
    ← seamFluxCochain_eq_prime_add_archimedean_of_one_lt_re hs,
    seamFluxCochain]
  ring

theorem completedCenteredCoordinate_add_spectral (s z : ℂ) :
    completedCenteredCoordinate (s + z * Complex.I) =
      completedCenteredCoordinate s + z := by
  rw [completedCenteredCoordinate, completedCenteredCoordinate]
  ring_nf
  rw [Complex.I_sq]
  ring

/-- **Two-value source law.** The moving completed trace is literally the difference of two
values of the fixed prime--Gamma source after the centered coordinate change. -/
theorem completedMovingRelativeTrace_eq_primeArchSource_value_sub
    {s z : ℂ} (hs : 1 < s.re) (hsz : 1 < (s + z * Complex.I).re) :
    completedMovingRelativeTrace s z =
      primeArchSourceRelativeTrace (completedCenteredCoordinate s + z) -
        primeArchSourceRelativeTrace (completedCenteredCoordinate s) := by
  rw [← completedCenteredCoordinate_add_spectral]
  rw [primeArchSourceRelativeTrace_completedCenteredCoordinate hsz,
    primeArchSourceRelativeTrace_completedCenteredCoordinate hs,
    completedMovingRelativeTrace]
  ring

/-- The two-point prime--Gamma value difference that determines the moving trace. -/
def primeArchSourceValueDifference (s z : ℂ) : ℂ :=
  primeArchSourceRelativeTrace (completedCenteredCoordinate s + z) -
    primeArchSourceRelativeTrace (completedCenteredCoordinate s)

/-- Normalized germ constructed solely from two values of the fixed prime--Gamma source. -/
def primeArchSourceValueMomentGerm (s : ℂ) : ℂ → ℂ :=
  normalizedTraceMomentGerm (primeArchSourceValueDifference s)

/-- Moving source Hankel matrix written entirely in the prime--Gamma value language. -/
def primeArchSourceValueHankelMatrix (n : ℕ) (s : ℂ) :
    Matrix (Fin n) (Fin n) ℝ :=
  fun i j => analyticTraceMoments (primeArchSourceValueMomentGerm s)
    ((i : ℕ) + (j : ℕ))

/-- The pointwise two-value law holds as a germ around every Euler-half-plane base point. -/
theorem completedMovingRelativeTrace_eventuallyEq_primeArchSourceValueDifference
    {s : ℂ} (hs : 1 < s.re) :
    completedMovingRelativeTrace s =ᶠ[nhds 0]
      primeArchSourceValueDifference s := by
  have hcont : ContinuousAt (fun z : ℂ => (s + z * Complex.I).re) 0 := by
    fun_prop
  have hev : ∀ᶠ z : ℂ in nhds 0, 1 < (s + z * Complex.I).re := by
    exact hcont.eventually_const_lt (by simpa using hs)
  filter_upwards [hev] with z hsz
  exact completedMovingRelativeTrace_eq_primeArchSource_value_sub hs hsz

/-- The moving normalized germ is fixed by the two-point prime--Gamma value germ. -/
theorem completedMovingMomentGerm_eventuallyEq_primeArchSourceValueMomentGerm
    {s : ℂ} (hs : 1 < s.re) :
    completedMovingMomentGerm s =ᶠ[nhds 0]
      primeArchSourceValueMomentGerm s := by
  rw [completedMovingMomentGerm, primeArchSourceValueMomentGerm]
  exact normalizedTraceMomentGerm_eventuallyEq_of_eventuallyEq
    (completedMovingRelativeTrace_eventuallyEq_primeArchSourceValueDifference hs)

/-- Every finite moving Hankel matrix on the Euler half-plane is determined by static values of
the fixed prime--Gamma source. -/
theorem completedMovingHankelMatrix_eq_primeArchSourceValueHankelMatrix
    (n : ℕ) {s : ℂ} (hs : 1 < s.re) :
    completedMovingHankelMatrix n s = primeArchSourceValueHankelMatrix n s := by
  ext i j
  rw [completedMovingHankelMatrix, primeArchSourceValueHankelMatrix]
  unfold analyticTraceMoments
  rw [(completedMovingMomentGerm_eventuallyEq_primeArchSourceValueMomentGerm hs).iteratedDeriv_eq]

end

end RHTower
