import GaloisForLFunctions.RHTower.SuzukiCriticalEntryWallQuarterShiftGreenLaw
import GaloisForLFunctions.RHTower.SuzukiCausalHingeBoundaryTailGreenLaw

/-!
# Suzuki critical wall-field square-root weld

The observer factor in the critical quarter-shift atom is not part of Suzuki's restricted-Weil
endpoint trace: observer aperture is an independent variable.  Removing that factor exposes one
source-defined wall field.  Its bilinear square is exactly the far delayed-hinge numerator, while
its linear degree is exactly the bare entry third jet.  Observer innovation acts only afterwards.

This is an exact source classification.  It uses neither RH nor positivity, estimates, numerical
computation, or zero data.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Observer-free wall field -/

/-- Critical Gamma boundary amplitude before pairing with any observer aperture. -/
def suzukiCriticalEntryWallBareAmplitude
    (p : Nat.Primes) (e : ℕ) : ℝ :=
  Real.sqrt
    (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, e) : ℝ) *
      Real.exp ((1 / 2 : ℝ) *
        Real.log (xiGammaEulerValuationNat (p, e) : ℝ)))

/-- Conjugated critical Gamma-height feature: the causal prime-power wall field. -/
def suzukiCriticalWallField
    (t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  star (xiGammaEulerHeightBoundaryFeature (-1 / 2) t (p, e))

/-- The critical wall field is observer-free amplitude times the causal entry-wall phase. -/
theorem suzukiCriticalWallField_eq_bareAmplitude_mul_kernel
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField t p e =
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) := by
  simp only [suzukiCriticalWallField, xiGammaEulerHeightBoundaryFeature,
    suzukiCriticalEntryWallBareAmplitude]
  simp only [show -(-1 / 2 : ℝ) = 1 / 2 by norm_num]
  rw [star_mul]
  change
    conj (Complex.exp
      (-(((t * Real.log (xiGammaEulerValuationNat (p, e) : ℝ) / 2 : ℝ) : ℂ) * I))) *
        conj ((Real.sqrt
          (Real.log (p : ℝ) / (xiGammaEulerValuationNat (p, e) : ℝ) *
            Real.exp ((1 / 2 : ℝ) *
              Real.log (xiGammaEulerValuationNat (p, e) : ℝ))) : ℂ)) = _
  rw [← Complex.exp_conj, Complex.conj_ofReal]
  simp only [map_neg, map_mul, Complex.conj_ofReal, Complex.conj_I]
  rw [suzukiOscillatoryKernel_primePowerEntryWall_eq_criticalPhase]
  push_cast
  ring_nf

/-! ## Exact symmetric-square weld -/

/-- Squaring the bare critical amplitude gives the exact von-Mangoldt far-hinge weight. -/
theorem sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallBareAmplitude p e ^ 2 =
      ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
        Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) := by
  let n := xiGammaEulerValuationNat (p, e)
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast (pow_pos p.property.pos (e + 1))
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hn
  have hexp :
      Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) = Real.sqrt (n : ℝ) := by
    rw [show (1 / 2 : ℝ) * Real.log (n : ℝ) = Real.log (n : ℝ) / 2 by ring,
      ← Real.log_sqrt hn.le, Real.exp_log hsqrt]
  have hvm : ArithmeticFunction.vonMangoldt n = Real.log (p : ℝ) := by
    simpa only [n, xiGammaEulerValuationNat] using
      vonMangoldt_prime_pow_succ_eq_log (p, e)
  rw [suzukiCriticalEntryWallBareAmplitude, Real.sq_sqrt, hvm]
  · change Real.log (p : ℝ) / (n : ℝ) *
      Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)) =
        Real.log (p : ℝ) / Real.sqrt (n : ℝ)
    rw [hexp]
    field_simp [hn.ne', hsqrt.ne']
    nlinarith [Real.mul_self_sqrt hn.le]
  · exact mul_nonneg (div_nonneg hlogp.le hn.le) (Real.exp_nonneg _)

/-- Prime-power far-hinge weight is strictly positive. -/
theorem suzukiCriticalFarHingeWeight_pos
    (p : Nat.Primes) (e : ℕ) :
    0 < ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
      Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) := by
  have hn : 0 < (xiGammaEulerValuationNat (p, e) : ℝ) := by
    exact_mod_cast (pow_pos p.property.pos (e + 1))
  have hvm :
      ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) =
        Real.log (p : ℝ) := by
    simpa only [xiGammaEulerValuationNat] using
      vonMangoldt_prime_pow_succ_eq_log (p, e)
  rw [hvm]
  exact div_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))
    (Real.sqrt_pos.mpr hn)

/-- Squaring the entry-wall kernel doubles its half-log delay to the full prime-power delay. -/
theorem sq_suzukiOscillatoryKernel_primePowerEntryWall
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiOscillatoryKernel (t : ℂ)
          (suzukiPrimePowerEntryWallAperture p e) ^ 2 =
      suzukiOscillatoryKernel (t : ℂ)
        (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
  simp only [suzukiOscillatoryKernel, pow_two, ← Complex.exp_add]
  congr 1
  rw [← two_mul_suzukiPrimePowerEntryWallAperture p e]
  push_cast
  ring

/-- **Square-root weld.**  The complex bilinear square of the wall field is exactly the
von-Mangoldt far-hinge numerator, including its full delay phase. -/
theorem sq_suzukiCriticalWallField_eq_farHingeNumerator
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallField t p e ^ 2 =
      (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ) : ℂ) *
        suzukiOscillatoryKernel (t : ℂ)
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) := by
  rw [suzukiCriticalWallField_eq_bareAmplitude_mul_kernel, mul_pow,
    ← ofReal_pow, sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt,
    sq_suzukiOscillatoryKernel_primePowerEntryWall]
  push_cast
  ring_nf

/-- The Xi-real far delayed-hinge atom is `-I` times the wall-field square divided by `t^2`. -/
theorem suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq_div
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalDelayedHingeJumpAtom
        (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
          Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
        (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ) =
      -I * suzukiCriticalWallField t p e ^ 2 / (t : ℂ) ^ 2 := by
  rw [suzukiCriticalDelayedHingeJumpAtom,
    sq_suzukiCriticalWallField_eq_farHingeNumerator]
  simp only [suzukiOscillatoryKernel]
  push_cast
  ring_nf

/-- Off the spectral center, matching denominators exposes the exact symmetric-square source. -/
theorem sq_mul_suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq
    (t : ℝ) (p : Nat.Primes) (e : ℕ) (ht : t ≠ 0) :
    (t : ℂ) ^ 2 *
        suzukiCriticalDelayedHingeJumpAtom
          (ArithmeticFunction.vonMangoldt (xiGammaEulerValuationNat (p, e)) /
            Real.sqrt (xiGammaEulerValuationNat (p, e) : ℝ))
          (Real.log (xiGammaEulerValuationNat (p, e) : ℝ)) (t : ℂ) =
      -I * suzukiCriticalWallField t p e ^ 2 := by
  rw [suzukiCriticalDelayedHingeJumpAtom_eq_neg_I_mul_wallField_sq_div]
  field_simp [Complex.ofReal_ne_zero.mpr ht]

/-! ## Linear entry degree and observer separation -/

/-- Bare third-jet entry forcing before observer pairing. -/
def suzukiCriticalEntryWallBareThirdJetAtom
    (t : ℝ) (p : Nat.Primes) (e : ℕ) : ℂ :=
  (t : ℂ) ^ 2 * suzukiCriticalWallField t p e

/-- Inserting the bare Gamma amplitude at the prime-power wall gives the wall field's linear
third-jet degree. -/
theorem suzukiDelayedHingeCompletedJet3_entryWall_eq_bareThirdJetAtom
    (t : ℝ) (p : Nat.Primes) (e : ℕ) (wholeMoment : ℂ) :
    suzukiDelayedHingeNearCompletedJet3
          (suzukiPrimePowerEntryWallAperture p e)
          (2 * suzukiPrimePowerEntryWallAperture p e)
          wholeMoment (suzukiCriticalEntryWallBareAmplitude p e : ℂ) (t : ℂ) -
        suzukiDelayedHingeFarCompletedJet3
          (2 * suzukiPrimePowerEntryWallAperture p e) wholeMoment (t : ℂ) =
      suzukiCriticalEntryWallBareThirdJetAtom t p e := by
  rw [suzukiDelayedHingeCompletedJet3_entryWall_sub,
    suzukiCriticalEntryWallBareThirdJetAtom,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  ring

/-- Existing critical entry forcing is bare third jet followed by observer innovation. -/
theorem suzukiCriticalEntryWallThirdJetAtom_eq_bare_mul_innovation
    (h b t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallThirdJetAtom h b t p e =
      suzukiCriticalEntryWallBareThirdJetAtom t p e *
        (xiMobiusCubicNormalizedInnovationFeature h b (p, e) : ℂ) := by
  rw [suzukiCriticalEntryWallThirdJetAtom,
    suzukiCriticalApertureBoundaryAtom_eq_entryWallAmplitude_mul_kernel,
    suzukiCriticalEntryWallBareThirdJetAtom,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  simp only [suzukiCriticalEntryWallEndpointAmplitude,
    suzukiCriticalEntryWallBareAmplitude]
  push_cast
  ring

/-- The old `EndpointAmplitude` declaration is an observed amplitude: bare wall amplitude followed
by the independently chosen aperture innovation. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_eq_bare_mul_innovation
    (h b : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallEndpointAmplitude h b p e =
      suzukiCriticalEntryWallBareAmplitude p e *
        xiMobiusCubicNormalizedInnovationFeature h b (p, e) := by
  rfl

/-- **Observer-separation no-go.**  At depth zero, the old observed amplitude is injective in
positive observer aperture.  It therefore cannot equal one observer-independent deficiency
endpoint trace at two distinct apertures. -/
theorem suzukiCriticalEntryWallEndpointAmplitude_zero_injective
    {h b₁ b₂ : ℝ} (hh : 0 < h) (hb₁ : 0 < b₁) (hb₂ : 0 < b₂)
    (p : Nat.Primes)
    (heq : suzukiCriticalEntryWallEndpointAmplitude h b₁ p 0 =
      suzukiCriticalEntryWallEndpointAmplitude h b₂ p 0) :
    b₁ = b₂ := by
  unfold suzukiCriticalEntryWallEndpointAmplitude at heq
  unfold xiMobiusCubicNormalizedInnovationFeature at heq
  unfold xiMobiusContinuousApertureDyadicInnovationFeature at heq
  unfold xiMobiusPrimeContinuousApertureDyadicInnovationFeature at heq
  simp only [pow_zero, mul_one] at heq
  let n := xiGammaEulerValuationNat (p, 0)
  let B := Real.sqrt
    (Real.log (p : ℝ) / (n : ℝ) *
      Real.exp ((1 / 2 : ℝ) * Real.log (n : ℝ)))
  let C := (h * Real.sqrt h)⁻¹
  let q := xiTransversePrimeApertureDiskNode 1 p
  let r₁ := xiMobiusContinuousApertureDiskNode (h / 2 * b₁) p
  let r₂ := xiMobiusContinuousApertureDiskNode (h / 2 * b₂) p
  have hn : 0 < (n : ℝ) := by
    exact_mod_cast (pow_pos p.property.pos (0 + 1))
  have hlogp : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have hB : 0 < B := Real.sqrt_pos.mpr
    (mul_pos (div_pos hlogp hn) (Real.exp_pos _))
  have hC : 0 < C := inv_pos.mpr (mul_pos hh (Real.sqrt_pos.mpr hh))
  have hq : 0 < q := xiTransversePrimeApertureDiskNode_pos 1 p
  have hqratio : 0 < q / (1 + q) := div_pos hq (by linarith)
  have hK : 0 < B * C * (q / (1 + q)) := by positivity
  change B * (C * (q / (1 + q) * (1 - r₁) ^ 2)) =
    B * (C * (q / (1 + q) * (1 - r₂) ^ 2)) at heq
  have hsquares : (1 - r₁) ^ 2 = (1 - r₂) ^ 2 := by
    nlinarith [heq]
  have hr₁lt : r₁ < 1 :=
    xiMobiusContinuousApertureDiskNode_lt_one (by positivity) p
  have hr₂lt : r₂ < 1 :=
    xiMobiusContinuousApertureDiskNode_lt_one (by positivity) p
  have hr : r₁ = r₂ := by nlinarith
  have haperture : h / 2 * b₁ = h / 2 * b₂ :=
    xiMobiusContinuousApertureDiskNode_injective p hr
  nlinarith

end

end RHTower
