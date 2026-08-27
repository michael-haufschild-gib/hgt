import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicSchwarzPolarization

/-!
# BM second-harmonic polarized Green identity

The independent `--` second-harmonic fibre at conjugate momentum is the Schwarz partner of the
existing `++` fibre. This module upgrades that algebraic statement to the exact finite-radius
Lagrange identity for their forced Birmingham--Mokhtari hypergeometric equations.

The complex integrating factor is

`p(z) = exp(c * log z) * sqrt(1-z)`

and its weight is `w(z)=p(z)/(z(1-z))`. The resulting polarized current obeys

`J'(z) = w(z) * (conj(v(z))*f(z) - conj(g(z))*y(z))`.

This is a compact-interval radial identity. It does not assert singular endpoint limits, augmented
Einstein boundary terms, retarded/advanced incidence, or flux positivity.
-/

open Complex Real
open scoped Interval

namespace RHTower

noncomputable section

/-- Hypergeometric differential expression on the `++` second-harmonic jet. -/
def d4BMPlusPlusHypergeometricJet
    (n : ℕ) (chi : ℂ) (z : ℝ) (y dy ddy : ℂ) : ℂ :=
  ((z * (1 - z) : ℝ) : ℂ) * ddy +
    (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
      (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
        d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1) *
        (z : ℂ)) * dy -
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
      d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi * y

/-- Hypergeometric differential expression on the `--` second-harmonic jet. -/
def d4BMMinusMinusHypergeometricJet
    (n : ℕ) (chi : ℂ) (z : ℝ) (y dy ddy : ℂ) : ℂ :=
  ((z * (1 - z) : ℝ) : ℂ) * ddy +
    (d4BMCausalRadialC (d4BMCausalMinusMinusFrequency n chi) -
      (d4BMCausalHypergeometricA (d4BMCausalMinusMinusFrequency n chi) chi +
        d4BMCausalHypergeometricB (d4BMCausalMinusMinusFrequency n chi) chi + 1) *
        (z : ℂ)) * dy -
    d4BMCausalHypergeometricA (d4BMCausalMinusMinusFrequency n chi) chi *
      d4BMCausalHypergeometricB (d4BMCausalMinusMinusFrequency n chi) chi * y

/-- Universal BM hypergeometric exponent balance on the `++` second harmonic. -/
theorem d4BMPlusPlusHypergeometric_exponentBalance
    (n : ℕ) (chi : ℂ) :
    d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
        d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi -
        d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) + 1 =
      1 / 2 := by
  simp [d4BMCausalHypergeometricA, d4BMCausalHypergeometricB,
    d4BMCausalRadialA, d4BMCausalRadialB, d4BMCausalRadialC]
  ring

/-- Conjugating the `--` jet at conjugate momentum gives the `++` jet. -/
theorem d4BMMinusMinusHypergeometricJet_schwarz
    (n : ℕ) (chi : ℂ) (z : ℝ) (y dy ddy : ℂ) :
    (starRingEnd ℂ)
        (d4BMMinusMinusHypergeometricJet n ((starRingEnd ℂ) chi) z y dy ddy) =
      d4BMPlusPlusHypergeometricJet n chi z
        ((starRingEnd ℂ) y) ((starRingEnd ℂ) dy) ((starRingEnd ℂ) ddy) := by
  simp only [d4BMMinusMinusHypergeometricJet, d4BMPlusPlusHypergeometricJet,
    map_sub, map_add, map_mul,
    d4BMCausalRadialC_minusMinus_schwarz,
    d4BMCausalHypergeometricA_minusMinus_schwarz,
    d4BMCausalHypergeometricB_minusMinus_schwarz,
    map_one, Complex.conj_ofReal, Complex.conj_conj]
  ring

/-- Complex BM integrating factor on the radial interior. -/
def d4BMPlusPlusIntegratingFactor
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  Complex.exp
      (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) *
        (Real.log z : ℂ)) *
    (Real.sqrt (1 - z) : ℂ)

/-- BM integrating weight `p(z)/(z(1-z))`. -/
def d4BMPlusPlusIntegratingWeight
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMPlusPlusIntegratingFactor n chi z /
    ((z : ℂ) * (1 - z : ℂ))

/-- First-derivative coefficient of the `++` hypergeometric equation. -/
def d4BMPlusPlusHypergeometricDrift
    (n : ℕ) (chi : ℂ) (z : ℝ) : ℂ :=
  d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
    (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
      d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1) *
      (z : ℂ)

/-- Exponent balance reduces the drift to `c(1-z)-z/2`. -/
theorem d4BMPlusPlusHypergeometricDrift_eq
    (n : ℕ) (chi : ℂ) (z : ℝ) :
    d4BMPlusPlusHypergeometricDrift n chi z =
      d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) * (1 - z : ℂ) -
        (z : ℂ) / 2 := by
  have h := d4BMPlusPlusHypergeometric_exponentBalance n chi
  rw [d4BMPlusPlusHypergeometricDrift]
  have hab :
      d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
          d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi + 1 =
        d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) + 1 / 2 := by
    linear_combination h
  rw [hab]
  ring

/-- Integrating factor solves `p'=w*drift` throughout `0<z<1`. -/
theorem hasDerivAt_d4BMPlusPlusIntegratingFactor
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1) :
    HasDerivAt (d4BMPlusPlusIntegratingFactor n chi)
      (d4BMPlusPlusIntegratingWeight n chi z *
        d4BMPlusPlusHypergeometricDrift n chi z) z := by
  let c := d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi)
  have hz : z ≠ 0 := ne_of_gt hz0
  have h1z : 1 - z ≠ 0 := ne_of_gt (sub_pos.mpr hz1)
  have hsqrt0 : Real.sqrt (1 - z) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr hz1))
  have hlogR : HasDerivAt Real.log z⁻¹ z := Real.hasDerivAt_log hz
  have hlogC : HasDerivAt (fun x : ℝ => (Real.log x : ℂ))
      ((z⁻¹ : ℝ) : ℂ) z := hlogR.ofReal_comp
  have hpow : HasDerivAt
      (fun x : ℝ => Complex.exp (c * (Real.log x : ℂ)))
      (Complex.exp (c * (Real.log z : ℂ)) * (c * ((z⁻¹ : ℝ) : ℂ))) z := by
    exact (hlogC.const_mul c).cexp
  have hinner : HasDerivAt (fun x : ℝ => 1 - x) (-1) z := by
    simpa using (hasDerivAt_id z).const_sub (1 : ℝ)
  have hsqrtR := (Real.hasDerivAt_sqrt h1z).comp z hinner
  have hsqrtC : HasDerivAt (fun x : ℝ => (Real.sqrt (1 - x) : ℂ))
      ((1 / (2 * Real.sqrt (1 - z)) * -1 : ℝ) : ℂ) z :=
    hsqrtR.ofReal_comp
  refine (hpow.mul hsqrtC).congr_deriv ?_
  rw [d4BMPlusPlusIntegratingWeight, d4BMPlusPlusIntegratingFactor,
    d4BMPlusPlusHypergeometricDrift_eq]
  change Complex.exp (c * (Real.log z : ℂ)) * (c * ((z⁻¹ : ℝ) : ℂ)) *
        (Real.sqrt (1 - z) : ℂ) +
      Complex.exp (c * (Real.log z : ℂ)) *
        ((1 / (2 * Real.sqrt (1 - z)) * -1 : ℝ) : ℂ) = _
  have hsquare : Real.sqrt (1 - z) ^ 2 = 1 - z :=
    Real.sq_sqrt (sub_nonneg.mpr (le_of_lt hz1))
  have hsquareC : (Real.sqrt (1 - z) : ℂ) ^ 2 = (1 - z : ℝ) := by
    exact_mod_cast hsquare
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast hz
  have h1zC : (1 - z : ℂ) ≠ 0 := by exact_mod_cast h1z
  have hsqrt0C : (Real.sqrt (1 - z) : ℂ) ≠ 0 := by exact_mod_cast hsqrt0
  push_cast
  field_simp [hz, h1z, hsqrt0, hzC, h1zC, hsqrt0C]
  rw [hsquareC]
  dsimp [c]
  push_cast
  ring_nf

/-- Product `a*b` in the `++` hypergeometric potential. -/
def d4BMPlusPlusHypergeometricPotential (n : ℕ) (chi : ℂ) : ℂ :=
  d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
    d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi

/-- Integrating factor puts the `++` equation in complex Sturm divergence form. -/
theorem d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (y dy ddy : ℂ) :
    d4BMPlusPlusIntegratingWeight n chi z *
        d4BMPlusPlusHypergeometricJet n chi z y dy ddy =
      (d4BMPlusPlusIntegratingWeight n chi z *
          d4BMPlusPlusHypergeometricDrift n chi z) * dy +
        d4BMPlusPlusIntegratingFactor n chi z * ddy -
        (d4BMPlusPlusIntegratingWeight n chi z *
          d4BMPlusPlusHypergeometricPotential n chi) * y := by
  have hzC : (z : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hz0
  have h1zC : (1 - z : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (sub_pos.mpr hz1)
  have hweight :
      d4BMPlusPlusIntegratingWeight n chi z *
          (((z * (1 - z) : ℝ) : ℂ)) =
        d4BMPlusPlusIntegratingFactor n chi z := by
    rw [d4BMPlusPlusIntegratingWeight]
    push_cast
    field_simp
  rw [d4BMPlusPlusHypergeometricJet,
    d4BMPlusPlusHypergeometricDrift,
    d4BMPlusPlusHypergeometricPotential]
  calc
    d4BMPlusPlusIntegratingWeight n chi z *
        (((z * (1 - z) : ℝ) : ℂ) * ddy +
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
            (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
                d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi +
                1) * (z : ℂ)) * dy -
          d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
            d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi * y) =
      (d4BMPlusPlusIntegratingWeight n chi z *
          (((z * (1 - z) : ℝ) : ℂ))) * ddy +
        (d4BMPlusPlusIntegratingWeight n chi z *
          (d4BMCausalRadialC (d4BMCausalPlusPlusFrequency n chi) -
            (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi +
                d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi +
                1) * (z : ℂ))) * dy -
        (d4BMPlusPlusIntegratingWeight n chi z *
          (d4BMCausalHypergeometricA (d4BMCausalPlusPlusFrequency n chi) chi *
            d4BMCausalHypergeometricB (d4BMCausalPlusPlusFrequency n chi) chi)) * y := by
        ring
    _ = _ := by rw [hweight]; ring

/-- Jet derivative of the polarized BM radial concomitant. -/
def d4BMSecondHarmonicPolarizedCurrentDerivativeJet
    (n : ℕ) (chi : ℂ) (z : ℝ)
    (y dy ddy v dv ddv : ℂ) : ℂ :=
  (d4BMPlusPlusIntegratingWeight n chi z *
      d4BMPlusPlusHypergeometricDrift n chi z) *
      ((starRingEnd ℂ v) * dy - (starRingEnd ℂ dv) * y) +
    d4BMPlusPlusIntegratingFactor n chi z *
      (((starRingEnd ℂ dv) * dy + (starRingEnd ℂ v) * ddy) -
        ((starRingEnd ℂ ddv) * y + (starRingEnd ℂ dv) * dy))

/-- Local polarized source identity; full hypergeometric potential cancels. -/
theorem d4BMSecondHarmonicPolarizedCurrentDerivativeJet_eq_source
    (n : ℕ) (chi : ℂ) {z : ℝ} (hz0 : 0 < z) (hz1 : z < 1)
    (y dy ddy v dv ddv forcingY forcingV : ℂ)
    (hY : d4BMPlusPlusHypergeometricJet n chi z y dy ddy = forcingY)
    (hV : d4BMMinusMinusHypergeometricJet n ((starRingEnd ℂ) chi)
      z v dv ddv = forcingV) :
    d4BMSecondHarmonicPolarizedCurrentDerivativeJet
        n chi z y dy ddy v dv ddv =
      d4BMPlusPlusIntegratingWeight n chi z *
        ((starRingEnd ℂ v) * forcingY -
          (starRingEnd ℂ forcingV) * y) := by
  have hVstar := congrArg (starRingEnd ℂ) hV
  rw [d4BMMinusMinusHypergeometricJet_schwarz] at hVstar
  have hYsturm := d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
    n chi hz0 hz1 y dy ddy
  rw [hY] at hYsturm
  have hVsturm := d4BMPlusPlusHypergeometricJet_integratingFactorDecomposition
    n chi hz0 hz1 ((starRingEnd ℂ) v) ((starRingEnd ℂ) dv)
      ((starRingEnd ℂ) ddv)
  rw [hVstar] at hVsturm
  rw [d4BMSecondHarmonicPolarizedCurrentDerivativeJet]
  linear_combination
    -((starRingEnd ℂ) v) * hYsturm + y * hVsturm

/-- Polarized second-harmonic radial concomitant. -/
def d4BMSecondHarmonicPolarizedCurrent
    (n : ℕ) (chi : ℂ) (y dy v dv : ℝ → ℂ) : ℝ → ℂ :=
  d4BMPlusPlusIntegratingFactor n chi *
    fun z => (starRingEnd ℂ) (v z) * dy z -
      (starRingEnd ℂ) (dv z) * y z

/-- Derivative of the polarized concomitant from two solution jets. -/
theorem hasDerivAt_d4BMSecondHarmonicPolarizedCurrent
    (n : ℕ) (chi : ℂ) (y dy v dv : ℝ → ℂ) (z : ℝ)
    (ddy ddv : ℂ) (hz0 : 0 < z) (hz1 : z < 1)
    (hy : HasDerivAt y (dy z) z)
    (hdy : HasDerivAt dy ddy z)
    (hv : HasDerivAt v (dv z) z)
    (hdv : HasDerivAt dv ddv z) :
    HasDerivAt (d4BMSecondHarmonicPolarizedCurrent n chi y dy v dv)
      (d4BMSecondHarmonicPolarizedCurrentDerivativeJet
        n chi z (y z) (dy z) ddy (v z) (dv z) ddv) z := by
  have hstarv : HasDerivAt (fun x : ℝ => (starRingEnd ℂ) (v x))
      ((starRingEnd ℂ) (dv z)) z :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z hv
  have hstardv : HasDerivAt (fun x : ℝ => (starRingEnd ℂ) (dv x))
      ((starRingEnd ℂ) ddv) z :=
    Complex.conjCLE.hasFDerivAt.comp_hasDerivAt z hdv
  have hpair : HasDerivAt
      (fun x : ℝ => (starRingEnd ℂ) (v x) * dy x -
        (starRingEnd ℂ) (dv x) * y x)
      (((starRingEnd ℂ) (dv z) * dy z +
          (starRingEnd ℂ) (v z) * ddy) -
        ((starRingEnd ℂ) ddv * y z +
          (starRingEnd ℂ) (dv z) * dy z)) z :=
    (hstarv.mul hdy).sub (hstardv.mul hy)
  have hp := hasDerivAt_d4BMPlusPlusIntegratingFactor n chi hz0 hz1
  simpa [d4BMSecondHarmonicPolarizedCurrent,
    d4BMSecondHarmonicPolarizedCurrentDerivativeJet] using hp.mul hpair

/-- Integrated polarized BM Green identity on every compact radial subinterval. -/
theorem d4BMSecondHarmonicIntegratedPolarizedGreenIdentity
    (n : ℕ) (chi : ℂ) (a b : ℝ)
    (ha0 : 0 < a) (hab : a ≤ b) (hb1 : b < 1)
    (y dy ddy v dv ddv forcingY forcingV : ℝ → ℂ)
    (hy : ∀ z ∈ Set.uIcc a b, HasDerivAt y (dy z) z)
    (hdy : ∀ z ∈ Set.uIcc a b, HasDerivAt dy (ddy z) z)
    (hv : ∀ z ∈ Set.uIcc a b, HasDerivAt v (dv z) z)
    (hdv : ∀ z ∈ Set.uIcc a b, HasDerivAt dv (ddv z) z)
    (hforcingY : ∀ z ∈ Set.uIcc a b,
      d4BMPlusPlusHypergeometricJet n chi z
        (y z) (dy z) (ddy z) = forcingY z)
    (hforcingV : ∀ z ∈ Set.uIcc a b,
      d4BMMinusMinusHypergeometricJet n ((starRingEnd ℂ) chi) z
        (v z) (dv z) (ddv z) = forcingV z)
    (hint : IntervalIntegrable
      (fun z : ℝ => d4BMPlusPlusIntegratingWeight n chi z *
        ((starRingEnd ℂ) (v z) * forcingY z -
          (starRingEnd ℂ) (forcingV z) * y z))
      MeasureTheory.volume a b) :
    (∫ z in a..b, d4BMPlusPlusIntegratingWeight n chi z *
        ((starRingEnd ℂ) (v z) * forcingY z -
          (starRingEnd ℂ) (forcingV z) * y z)) =
      d4BMSecondHarmonicPolarizedCurrent n chi y dy v dv b -
        d4BMSecondHarmonicPolarizedCurrent n chi y dy v dv a := by
  have hz0 : ∀ z ∈ Set.uIcc a b, 0 < z := by
    intro z hz
    rw [Set.uIcc_of_le hab] at hz
    exact lt_of_lt_of_le ha0 hz.1
  have hz1 : ∀ z ∈ Set.uIcc a b, z < 1 := by
    intro z hz
    rw [Set.uIcc_of_le hab] at hz
    exact lt_of_le_of_lt hz.2 hb1
  have hcurrent : ∀ z ∈ Set.uIcc a b,
      HasDerivAt (d4BMSecondHarmonicPolarizedCurrent n chi y dy v dv)
        (d4BMPlusPlusIntegratingWeight n chi z *
          ((starRingEnd ℂ) (v z) * forcingY z -
            (starRingEnd ℂ) (forcingV z) * y z)) z := by
    intro z hz
    apply (hasDerivAt_d4BMSecondHarmonicPolarizedCurrent
      n chi y dy v dv z (ddy z) (ddv z) (hz0 z hz) (hz1 z hz)
      (hy z hz) (hdy z hz) (hv z hz) (hdv z hz)).congr_deriv
    exact d4BMSecondHarmonicPolarizedCurrentDerivativeJet_eq_source
      n chi (hz0 z hz) (hz1 z hz)
      (y z) (dy z) (ddy z) (v z) (dv z) (ddv z)
      (forcingY z) (forcingV z) (hforcingY z hz) (hforcingV z hz)
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hcurrent hint

end

end RHTower
