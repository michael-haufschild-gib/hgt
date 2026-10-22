import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeGammaReflectedDiagonal

/-!
# Absolute Euler sectors do not supply the Hodge diagonal

Prime--Gamma packet cohomology has a source-defined pairing between lower and upper Cauchy
sectors.  This file proves that the two strict absolute-convergence sectors are disjoint and that
canonical conjugation changes the pole of a nonzero Cauchy atom.  Therefore the source pairing
cannot become Deninger's positive diagonal Hodge metric merely by identifying these sectors.

No Xi-zero enumeration, positivity hypothesis, or RH premise is used.
-/

open Complex

namespace RHTower

noncomputable section

/-- Lower absolute-Euler parameters lie strictly below imaginary height `-1 / 2`. -/
theorem deningerPrimeGammaLowerPoint_im_lt
    (z : DeningerPrimeGammaLowerPoint) :
    (z : ℂ).im < -(1 / 2 : ℝ) := by
  have hz := z.property
  norm_num [Complex.mul_re] at hz ⊢
  linarith

/-- Upper absolute-Euler parameters lie strictly above imaginary height `1 / 2`. -/
theorem deningerPrimeGammaUpperPoint_im_gt
    (w : DeningerPrimeGammaUpperPoint) :
    (1 / 2 : ℝ) < (w : ℂ).im := by
  have hw := w.property
  norm_num [Complex.mul_re] at hw ⊢
  linarith

/-- The lower and upper strict absolute-convergence sectors are disjoint. -/
theorem deningerPrimeGammaLower_coe_ne_upper_coe
    (z : DeningerPrimeGammaLowerPoint)
    (w : DeningerPrimeGammaUpperPoint) :
    (z : ℂ) ≠ (w : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  have hz := deningerPrimeGammaLowerPoint_im_lt z
  have hw := deningerPrimeGammaUpperPoint_im_gt w
  linarith

/-- A lower parameter is not fixed by the conjugation equivalence into the upper sector. -/
theorem deningerPrimeGammaLower_ne_conj
    (z : DeningerPrimeGammaLowerPoint) :
    (z : ℂ) ≠ (starRingEnd ℂ) (z : ℂ) := by
  simpa [deningerPrimeGammaPointConjEquiv] using
    deningerPrimeGammaLower_coe_ne_upper_coe z
      (deningerPrimeGammaPointConjEquiv z)

@[simp]
theorem deningerPrimeGammaLowerCauchyTest_single
    (z : DeningerPrimeGammaLowerPoint) (c a : ℂ) :
    deningerPrimeGammaLowerCauchyTest (Finsupp.single z c) a =
      c * xiWeilCauchyTest (z : ℂ) a := by
  simp [deningerPrimeGammaLowerCauchyTest]

@[simp]
theorem deningerPrimeGammaUpperCauchyTest_single
    (w : DeningerPrimeGammaUpperPoint) (d a : ℂ) :
    deningerPrimeGammaUpperCauchyTest (Finsupp.single w d) a =
      (starRingEnd ℂ) d * xiWeilCauchyTest (w : ℂ) a := by
  simp [deningerPrimeGammaUpperCauchyTest,
    deningerPrimeGammaUpperSharpCauchyTest, xiWeilSharp,
    xiWeilCauchyTest]

/--
Conjugating a lower atom into the upper sector changes its Cauchy pole from `z` to `conj z`.
-/
theorem deningerPrimeGammaUpperCauchyTest_conjugateAtom
    (z : DeningerPrimeGammaLowerPoint) (c a : ℂ) :
    deningerPrimeGammaUpperCauchyTest
        (Finsupp.single (deningerPrimeGammaPointConjEquiv z)
          ((starRingEnd ℂ) c)) a =
      c * xiWeilCauchyTest ((starRingEnd ℂ) (z : ℂ)) a := by
  simp [deningerPrimeGammaPointConjEquiv]

/--
For a nonzero coefficient, the canonical conjugate upper atom is not the same Weil test as the
original lower atom.  Thus absolute-Euler packet conjugation cannot itself be the Hodge diagonal.
-/
theorem deningerPrimeGammaLowerCauchyTest_ne_conjugateUpperAtom
    (z : DeningerPrimeGammaLowerPoint) {c : ℂ} (hc : c ≠ 0) :
    deningerPrimeGammaLowerCauchyTest (Finsupp.single z c) ≠
      deningerPrimeGammaUpperCauchyTest
        (Finsupp.single (deningerPrimeGammaPointConjEquiv z)
          ((starRingEnd ℂ) c)) := by
  intro hfun
  have h := congrFun hfun (z : ℂ)
  rw [deningerPrimeGammaLowerCauchyTest_single,
    deningerPrimeGammaUpperCauchyTest_conjugateAtom] at h
  unfold xiWeilCauchyTest at h
  rw [sub_self, inv_zero, mul_zero] at h
  have hsub :
      (z : ℂ) - (starRingEnd ℂ) (z : ℂ) ≠ 0 :=
    sub_ne_zero.mpr (deningerPrimeGammaLower_ne_conj z)
  exact (mul_ne_zero hc (inv_ne_zero hsub)) h.symm

end

end RHTower
