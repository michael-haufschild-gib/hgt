import GaloisForLFunctions.RHTower.RoutePPrimitiveBurnolDeningerSquaredCauchyGraphIncidence
import GaloisForLFunctions.RHTower.XiQuotientRealDecay

/-!
# Prime--Gamma mixed-secant graph incidence (W-H203)

P-G200 identifies every primitive generated reporter with a forced negative square of one
Deninger source Cauchy evaluation.  The missing finite source carrier is not an additional
postulate: it is the mixed secant of Deninger's source-only prime--Gamma cup kernel.

For lower source nodes `z0,z1` and upper nodes `w0,w1`, form the four-corner quotient

`(K(z1,w1)-K(z1,w0)-K(z0,w1)+K(z0,w0)) /
  ((z1-z0)(conj(w1)-conj(w0)))`.

This module proves that it is exactly the Weil polarization of the corresponding left and right
Cauchy secants.  Its divisor expansion is therefore the product of two secant columns, and every
secant factors as a product of two ordinary Cauchy resolvents.  On the reflected source graph the
complete form is an absolutely convergent sum of bilinear squares.

This closes construction of the finite coefficient-faithful pre-divisor graph carrier and its
coalescent algebra.  It also classifies the remaining sign seam: reflection produces complex
symmetric squares, not Hermitian norm squares.  A successful cubic trace comparison must add the
Schwarz/opposite-radial shorting that converts this exact source cup into positive zero energy
without losing the primitive trace budget.
-/

open Complex

namespace RHTower

noncomputable section

/-- Lower Cauchy secant in Deninger's strict absolute-Euler source sector. -/
def xiWardCubicPrimeGammaLowerSecantTest
    (z0 z1 : DeningerPrimeGammaLowerPoint) : ℂ → ℂ :=
  fun a =>
    (xiWeilCauchyTest (z1 : ℂ) a - xiWeilCauchyTest (z0 : ℂ) a) /
      ((z1 : ℂ) - z0)

/-- Upper Cauchy secant; Weil sharp conjugates its scalar denominator. -/
def xiWardCubicPrimeGammaUpperSecantTest
    (w0 w1 : DeningerPrimeGammaUpperPoint) : ℂ → ℂ :=
  fun a =>
    (xiWeilCauchyTest (w1 : ℂ) a - xiWeilCauchyTest (w0 : ℂ) a) /
      ((w1 : ℂ) - w0)

/-- Source-only four-corner mixed secant of Deninger's prime--Gamma cup kernel. -/
def xiWardCubicPrimeGammaSourceMixedSecant
    (z0 z1 : DeningerPrimeGammaLowerPoint)
    (w0 w1 : DeningerPrimeGammaUpperPoint) : ℂ :=
  (deningerPrimeGammaSourceKernel z1 w1 -
      deningerPrimeGammaSourceKernel z1 w0 -
      deningerPrimeGammaSourceKernel z0 w1 +
      deningerPrimeGammaSourceKernel z0 w0) /
    (((z1 : ℂ) - z0) *
      ((starRingEnd ℂ) (w1 : ℂ) - (starRingEnd ℂ) (w0 : ℂ)))

/-- **W-H203 finite source graph incidence.**  The literal prime--Gamma four-cup secant is exactly
the Weil polarization of the two Cauchy secants. -/
theorem xiWardCubicPrimeGammaSourceMixedSecant_eq_polarization
    (z0 z1 : DeningerPrimeGammaLowerPoint)
    (w0 w1 : DeningerPrimeGammaUpperPoint) :
    xiWardCubicPrimeGammaSourceMixedSecant z0 z1 w0 w1 =
      xiWeilPolarization (xiWardCubicPrimeGammaLowerSecantTest z0 z1)
        (xiWardCubicPrimeGammaUpperSecantTest w0 w1) := by
  let F0 := xiWeilCauchyTest (z0 : ℂ)
  let F1 := xiWeilCauchyTest (z1 : ℂ)
  let G0 := xiWeilCauchyTest (w0 : ℂ)
  let G1 := xiWeilCauchyTest (w1 : ℂ)
  let dz : ℂ := (z1 : ℂ) - z0
  let dw : ℂ := (w1 : ℂ) - w0
  have hF0 : XiWeilSquareSummable F0 := XiWeilSquareSummable_cauchy _
  have hF1 : XiWeilSquareSummable F1 := XiWeilSquareSummable_cauchy _
  have hG0 : XiWeilSquareSummable G0 := XiWeilSquareSummable_cauchy _
  have hG1 : XiWeilSquareSummable G1 := XiWeilSquareSummable_cauchy _
  have hnegF0 := hF0.const_smul (-1)
  have hnegG0 := hG0.const_smul (-1)
  have hFdiff := hF1.add hnegF0
  have hGdiff := hG1.add hnegG0
  have hleft : xiWardCubicPrimeGammaLowerSecantTest z0 z1 =
      fun a => dz⁻¹ * (F1 a + (-1 : ℂ) * F0 a) := by
    funext a
    simp [xiWardCubicPrimeGammaLowerSecantTest, F0, F1, dz,
      div_eq_mul_inv]
    ring
  have hright : xiWardCubicPrimeGammaUpperSecantTest w0 w1 =
      fun a => dw⁻¹ * (G1 a + (-1 : ℂ) * G0 a) := by
    funext a
    simp [xiWardCubicPrimeGammaUpperSecantTest, G0, G1, dw,
      div_eq_mul_inv]
    ring
  rw [hleft, hright,
    xiWeilPolarization_const_smul_left,
    xiWeilPolarization_const_smul_right]
  have hFfun : (fun a => F1 a + (-1 : ℂ) * F0 a) =
      F1 + fun a => (-1 : ℂ) * F0 a := by rfl
  have hGfun : (fun a => G1 a + (-1 : ℂ) * G0 a) =
      G1 + fun a => (-1 : ℂ) * G0 a := by rfl
  rw [hFfun, hGfun]
  rw [xiWeilPolarization_add_left hF1 hnegF0 hGdiff,
    xiWeilPolarization_add_right hF1 hG1 hnegG0,
    xiWeilPolarization_add_right hnegF0 hG1 hnegG0]
  rw [xiWeilPolarization_const_smul_left,
    xiWeilPolarization_const_smul_right,
    xiWeilPolarization_const_smul_right,
    xiWeilPolarization_const_smul_left]
  simp only [map_inv₀, map_neg, map_one]
  rw [show (starRingEnd ℂ) dw =
      (starRingEnd ℂ) (w1 : ℂ) - (starRingEnd ℂ) (w0 : ℂ) by
        dsimp only [dw]
        exact map_sub (starRingEnd ℂ) _ _]
  rw [xiWardCubicPrimeGammaSourceMixedSecant,
    deningerPrimeGammaSourceKernel_eq_xiWeilPolarization,
    deningerPrimeGammaSourceKernel_eq_xiWeilPolarization,
    deningerPrimeGammaSourceKernel_eq_xiWeilPolarization,
    deningerPrimeGammaSourceKernel_eq_xiWeilPolarization]
  dsimp only [F0, F1, G0, G1, dz, dw]
  rw [div_eq_mul_inv, mul_inv]
  ring

/-- Explicit sharp of the upper secant, now expressed in the independent conjugate chamber. -/
def xiWardCubicPrimeGammaUpperSharpSecant
    (w0 w1 : DeningerPrimeGammaUpperPoint) : ℂ → ℂ :=
  fun a =>
    (xiWeilCauchyTest ((starRingEnd ℂ) (w1 : ℂ)) a -
      xiWeilCauchyTest ((starRingEnd ℂ) (w0 : ℂ)) a) /
        ((starRingEnd ℂ) (w1 : ℂ) - (starRingEnd ℂ) (w0 : ℂ))

theorem xiWeilSharp_xiWardCubicPrimeGammaUpperSecantTest
    (w0 w1 : DeningerPrimeGammaUpperPoint) :
    xiWeilSharp (xiWardCubicPrimeGammaUpperSecantTest w0 w1) =
      xiWardCubicPrimeGammaUpperSharpSecant w0 w1 := by
  funext a
  simp [xiWardCubicPrimeGammaUpperSecantTest,
    xiWardCubicPrimeGammaUpperSharpSecant,
    xiWeilSharp, xiWeilCauchyTest]

/-- Multiplicity-exact all-zero expansion of the finite source graph carrier. -/
theorem xiWardCubicPrimeGammaSourceMixedSecant_eq_xiZeroCopy_tsum
    (z0 z1 : DeningerPrimeGammaLowerPoint)
    (w0 w1 : DeningerPrimeGammaUpperPoint) :
    xiWardCubicPrimeGammaSourceMixedSecant z0 z1 w0 w1 =
      ∑' q : XiZeroCopy,
        xiWardCubicPrimeGammaLowerSecantTest z0 z1 (xiSpectralPoint q) *
          xiWardCubicPrimeGammaUpperSharpSecant w0 w1
            (xiSpectralPoint q) := by
  rw [xiWardCubicPrimeGammaSourceMixedSecant_eq_polarization,
    xiWeilPolarization,
    xiWeilSharp_xiWardCubicPrimeGammaUpperSecantTest]

/-- Reflected finite source graph: each upper node is the canonical conjugate of its lower mate. -/
def xiWardCubicPrimeGammaReflectedSourceMixedSecant
    (z0 z1 : DeningerPrimeGammaLowerPoint) : ℂ :=
  xiWardCubicPrimeGammaSourceMixedSecant z0 z1
    (deningerPrimeGammaPointConjEquiv z0)
    (deningerPrimeGammaPointConjEquiv z1)

theorem xiWardCubicPrimeGammaUpperSharpSecant_reflected_eq_lower
    (z0 z1 : DeningerPrimeGammaLowerPoint) :
    xiWardCubicPrimeGammaUpperSharpSecant
        (deningerPrimeGammaPointConjEquiv z0)
        (deningerPrimeGammaPointConjEquiv z1) =
      xiWardCubicPrimeGammaLowerSecantTest z0 z1 := by
  funext a
  simp [xiWardCubicPrimeGammaUpperSharpSecant,
    xiWardCubicPrimeGammaLowerSecantTest,
    deningerPrimeGammaPointConjEquiv]

/-- **W-H203 reflected sign classification.**  The finite reflected prime--Gamma graph form is a
sum of complex bilinear squares.  No positivity or RH premise is used. -/
theorem xiWardCubicPrimeGammaReflectedSourceMixedSecant_eq_tsum_sq
    (z0 z1 : DeningerPrimeGammaLowerPoint) :
    xiWardCubicPrimeGammaReflectedSourceMixedSecant z0 z1 =
      ∑' q : XiZeroCopy,
        xiWardCubicPrimeGammaLowerSecantTest z0 z1 (xiSpectralPoint q) ^ (2 : ℕ) := by
  rw [xiWardCubicPrimeGammaReflectedSourceMixedSecant,
    xiWardCubicPrimeGammaSourceMixedSecant_eq_xiZeroCopy_tsum,
    xiWardCubicPrimeGammaUpperSharpSecant_reflected_eq_lower]
  apply tsum_congr
  intro q
  ring

/-- Every finite Cauchy secant is exactly a product of its endpoint resolvents. -/
theorem xiWardCubicPrimeGammaLowerSecantTest_factorization
    {z0 z1 : DeningerPrimeGammaLowerPoint} (hz : z0 ≠ z1)
    {a : ℂ} (ha0 : a ≠ (z0 : ℂ)) (ha1 : a ≠ (z1 : ℂ)) :
    xiWardCubicPrimeGammaLowerSecantTest z0 z1 a =
      (a - (z1 : ℂ))⁻¹ * (a - (z0 : ℂ))⁻¹ := by
  rw [xiWardCubicPrimeGammaLowerSecantTest,
    xiWeilCauchyTest, xiWeilCauchyTest]
  have hz' : (z1 : ℂ) - z0 ≠ 0 := sub_ne_zero.mpr (by
    intro h
    apply hz
    exact Subtype.ext h.symm)
  field_simp [hz', sub_ne_zero.mpr ha0, sub_ne_zero.mpr ha1]
  ring

end

end RHTower
