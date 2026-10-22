import GaloisForLFunctions.RHTower.Deninger.DeningerTraceBound

/-!
# Orthogonality of the Poisson extension to zero-trace fillings

The energy pairing of a zero-trace filling with the Poisson extension vanishes.  The pairing of the
two profiles is a total derivative whose boundary value is the product of the traces, so it
integrates to zero when one trace vanishes; the radial and transverse contributions to the energy
pairing then cancel, because the Poisson profile satisfies the first-order equation.

This is the orthogonality behind the Dirichlet decomposition: the energy splits as the zero-trace
part plus the Poisson part.

* `deningerConjPairing_hasDerivAt` : the derivative of the real pairing.
* `deningerPairing_integral_eq` : integrating the derivative recovers minus the boundary value.
* `deningerDirichlet_orthogonal` : the energy cross term vanishes.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

section DirichletOrthogonal

variable {w v p q : ℝ → ℂ}

/-- **The derivative of the real pairing** of two differentiable paths. -/
theorem deningerConjPairing_hasDerivAt {r : ℝ} (hw : HasDerivAt w (v r) r)
    (hp : HasDerivAt p (q r) r) :
    HasDerivAt (fun s => ((starRingEnd ℂ) (w s) * p s).re)
      (((starRingEnd ℂ) (v r) * p r).re + ((starRingEnd ℂ) (w r) * q r).re) r := by
  have hconj : HasDerivAt (fun s => (starRingEnd ℂ) (w s)) ((starRingEnd ℂ) (v r)) r :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt r hw
  have hmul := hconj.mul hp
  have hre : HasDerivAt (fun s => ((starRingEnd ℂ) (w s) * p s).re)
      (((starRingEnd ℂ) (v r) * p r + (starRingEnd ℂ) (w r) * q r).re) r :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt r hmul
  rwa [Complex.add_re] at hre

/-- **Integrating the derivative of the pairing** recovers minus its boundary value. -/
theorem deningerPairing_integral_eq
    (hderivw : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt w (v r) r)
    (hderivp : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt p (q r) r)
    (hcont : ContinuousWithinAt (fun s => ((starRingEnd ℂ) (w s) * p s).re) (Ici (0 : ℝ)) 0)
    (hlim : Tendsto (fun s => ((starRingEnd ℂ) (w s) * p s).re) atTop (𝓝 0))
    (hint : IntegrableOn (fun r => ((starRingEnd ℂ) (v r) * p r).re
      + ((starRingEnd ℂ) (w r) * q r).re) (Ioi (0 : ℝ))) :
    (∫ r in Ioi (0 : ℝ), (((starRingEnd ℂ) (v r) * p r).re
        + ((starRingEnd ℂ) (w r) * q r).re))
      = -((starRingEnd ℂ) (w 0) * p 0).re := by
  have hderiv : ∀ r ∈ Ioi (0 : ℝ),
      HasDerivAt (fun s => ((starRingEnd ℂ) (w s) * p s).re)
        (((starRingEnd ℂ) (v r) * p r).re + ((starRingEnd ℂ) (w r) * q r).re) r :=
    fun r hr => deningerConjPairing_hasDerivAt (hderivw r hr) (hderivp r hr)
  have h := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto hcont hderiv hint hlim
  rw [h, zero_sub]

/-- **The energy cross term vanishes.**  For a zero-trace filling the pairing integral vanishes, and
the Poisson profile's first-order equation makes the radial and transverse contributions cancel. -/
theorem deningerDirichlet_orthogonal {m : ℝ}
    (hderivw : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt w (v r) r)
    (hderivp : ∀ r ∈ Ioi (0 : ℝ), HasDerivAt p (q r) r)
    (hfirst : ∀ r : ℝ, q r = -(m : ℂ) * p r)
    (hw0 : w 0 = 0)
    (hcont : ContinuousWithinAt (fun s => ((starRingEnd ℂ) (w s) * p s).re) (Ici (0 : ℝ)) 0)
    (hlim : Tendsto (fun s => ((starRingEnd ℂ) (w s) * p s).re) atTop (𝓝 0))
    (hint : IntegrableOn (fun r => ((starRingEnd ℂ) (v r) * p r).re
      + ((starRingEnd ℂ) (w r) * q r).re) (Ioi (0 : ℝ)))
    (hintv : IntegrableOn (fun r => ((starRingEnd ℂ) (v r) * p r).re) (Ioi (0 : ℝ)))
    (hintw : IntegrableOn (fun r => ((starRingEnd ℂ) (w r) * p r).re) (Ioi (0 : ℝ))) :
    (∫ r in Ioi (0 : ℝ), ((starRingEnd ℂ) (v r) * q r).re)
      + m ^ (2 : ℕ) * ∫ r in Ioi (0 : ℝ), ((starRingEnd ℂ) (w r) * p r).re = 0 := by
  have hpair := deningerPairing_integral_eq hderivw hderivp hcont hlim hint
  rw [hw0] at hpair
  simp only [map_zero, zero_mul, Complex.zero_re, neg_zero] at hpair
  have hq : ∀ r : ℝ, ((starRingEnd ℂ) (w r) * q r).re
      = -(m * ((starRingEnd ℂ) (w r) * p r).re) := by
    intro r
    rw [hfirst r]
    have hexp : (starRingEnd ℂ) (w r) * (-(m : ℂ) * p r)
        = -((m : ℂ) * ((starRingEnd ℂ) (w r) * p r)) := by ring
    rw [hexp, Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hv : ∀ r : ℝ, ((starRingEnd ℂ) (v r) * q r).re
      = -(m * ((starRingEnd ℂ) (v r) * p r).re) := by
    intro r
    rw [hfirst r]
    have hexp : (starRingEnd ℂ) (v r) * (-(m : ℂ) * p r)
        = -((m : ℂ) * ((starRingEnd ℂ) (v r) * p r)) := by ring
    rw [hexp, Complex.neg_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hintq : IntegrableOn (fun r => ((starRingEnd ℂ) (w r) * q r).re) (Ioi (0 : ℝ)) := by
    have hfun : (fun r => ((starRingEnd ℂ) (w r) * q r).re)
        = fun r => (-m) * ((starRingEnd ℂ) (w r) * p r).re := by
      funext r
      rw [hq r]
      ring
    rw [hfun]
    exact hintw.const_mul _
  rw [integral_add hintv hintq,
    MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => hq r,
    integral_neg, integral_const_mul] at hpair
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun r _ => hv r,
    integral_neg, integral_const_mul]
  have hkey : (∫ r in Ioi (0 : ℝ), ((starRingEnd ℂ) (v r) * p r).re)
      = m * ∫ r in Ioi (0 : ℝ), ((starRingEnd ℂ) (w r) * p r).re := by
    linarith [hpair]
  rw [hkey]
  ring

end DirichletOrthogonal

end RHTower
