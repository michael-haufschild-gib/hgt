import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureKernel
import GaloisForLFunctions.RHTower.Deninger.DeningerPrimeGammaEulerSectorObstruction
import GaloisForLFunctions.RHTower.XiGuinandWeilSymmetricContour

/-!
# Prime--Gamma Cauchy decomposition of the critical feature kernel

The Hedenmalm critical reproducing kernel splits into two one-sided Hardy resolvents, with poles
at `t-i` and `t+i`.  These poles lie in the strict lower and upper absolute-Euler sectors used by
Deninger's prime--Gamma packet cohomology.  Cross pairings are exact source cups.  Functional-
equation oddness folds the two same-orientation pairings back to lower absolute-Euler source
values.  Consequently the full critical-feature Weil polarization has an exact four-term
prime--Gamma formula with no continued or zero-enumerated source value.

This closes source realization of the pointwise critical kernel.  It does not prove the remaining
height-local four-leg arithmetic upper bound for the five-shift energy current.
-/

open Complex

namespace RHTower

noncomputable section

open HedenmalmThetaSource

/-- Lower absolute-Euler pole of the real-centered critical feature. -/
def criticalHardyLowerPoint (t : ℝ) : DeningerPrimeGammaLowerPoint :=
  ⟨(t : ℂ) - I, by
    simp [Complex.mul_re]⟩

/-- Upper absolute-Euler pole, canonically conjugate to the lower pole. -/
def criticalHardyUpperPoint (t : ℝ) : DeningerPrimeGammaUpperPoint :=
  deningerPrimeGammaPointConjEquiv (criticalHardyLowerPoint t)

@[simp]
theorem criticalHardyLowerPoint_coe (t : ℝ) :
    (criticalHardyLowerPoint t : ℂ) = (t : ℂ) - I := rfl

@[simp]
theorem criticalHardyUpperPoint_coe (t : ℝ) :
    (criticalHardyUpperPoint t : ℂ) = (t : ℂ) + I := by
  simp [criticalHardyUpperPoint, criticalHardyLowerPoint,
    deningerPrimeGammaPointConjEquiv]

/-- Lower one-sided Hardy resolvent, normalized to its positive-time Laplace value. -/
def criticalHardyLowerCauchyTest (t : ℝ) (z : ℂ) : ℂ :=
  I * xiWeilCauchyTest (criticalHardyLowerPoint t : ℂ) z

/-- Upper one-sided Hardy resolvent.  It is the Weil sharp of the lower resolvent. -/
def criticalHardyUpperCauchyTest (t : ℝ) (z : ℂ) : ℂ :=
  -I * xiWeilCauchyTest (criticalHardyUpperPoint t : ℂ) z

theorem xiWeilSharp_criticalHardyLowerCauchyTest (t : ℝ) :
    xiWeilSharp (criticalHardyLowerCauchyTest t) =
      criticalHardyUpperCauchyTest t := by
  funext z
  simp [criticalHardyLowerCauchyTest, criticalHardyUpperCauchyTest,
    xiWeilSharp, xiWeilCauchyTest]

/-- Partial fractions split the symmetric critical kernel into its lower and upper Hardy atoms. -/
theorem criticalKernel_eq_hardyCauchySum
    {t : ℝ} {z : ℂ}
    (hl : z ≠ (t : ℂ) - I) (hu : z ≠ (t : ℂ) + I) :
    2 / (1 + (z - (t : ℂ)) ^ (2 : ℕ)) =
      criticalHardyLowerCauchyTest t z +
        criticalHardyUpperCauchyTest t z := by
  simp only [criticalHardyLowerCauchyTest, criticalHardyUpperCauchyTest,
    criticalHardyLowerPoint_coe, criticalHardyUpperPoint_coe,
    xiWeilCauchyTest]
  have hdl : z - ((t : ℂ) - I) ≠ 0 := sub_ne_zero.mpr hl
  have hdu : z - ((t : ℂ) + I) ≠ 0 := sub_ne_zero.mpr hu
  have hden : 1 + (z - (t : ℂ)) ^ (2 : ℕ) ≠ 0 := by
    intro h
    have hfactor :
        1 + (z - (t : ℂ)) ^ (2 : ℕ) =
          (z - ((t : ℂ) - I)) * (z - ((t : ℂ) + I)) := by
      ring_nf
      norm_num [Complex.I_sq]
      ring
    rw [hfactor] at h
    exact (mul_ne_zero hdl hdu) h
  field_simp [hdl, hdu, hden]
  ring_nf
  norm_num [Complex.I_sq]

private theorem criticalStrip_ne_lowerPole
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    z ≠ (t : ℂ) - I := by
  intro h
  have him := congrArg Complex.im h
  rcases abs_lt.mp hz with ⟨hz0, _⟩
  simp at him
  linarith

private theorem criticalStrip_ne_upperPole
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    z ≠ (t : ℂ) + I := by
  intro h
  have him := congrArg Complex.im h
  rcases abs_lt.mp hz with ⟨_, hz1⟩
  simp at him
  linarith

/-- Exact two-orientation Cauchy formula for a real-centered critical feature evaluation. -/
theorem criticalEvaluation_realCriticalFeature_eq_hardyCauchySum
    (t : ℝ) {z : ℂ} (hz : |z.im| < 1 / 2) :
    criticalEvaluation z hz
        (criticalFeature (t : ℂ) (by norm_num)) =
      criticalHardyLowerCauchyTest t z +
        criticalHardyUpperCauchyTest t z := by
  rw [criticalEvaluation_criticalFeature_eq (by norm_num) hz]
  rw [Complex.conj_ofReal]
  exact criticalKernel_eq_hardyCauchySum
    (criticalStrip_ne_lowerPole t hz) (criticalStrip_ne_upperPole t hz)

/-- The complete real-centered critical Cauchy kernel as a divisor test. -/
def criticalFeatureCauchyKernelTest (t : ℝ) (z : ℂ) : ℂ :=
  criticalHardyLowerCauchyTest t z + criticalHardyUpperCauchyTest t z

/-- Atomic lower/upper Hardy pairing defined entirely by the prime--Gamma source cup. -/
def criticalHardyPrimeGammaSourceCup (t s : ℝ) : ℂ :=
  deningerPrimeGammaSourceCup
    (Finsupp.single (criticalHardyLowerPoint t) I)
    (Finsupp.single (criticalHardyUpperPoint s) I)

/-- Functional-equation fold of the lower/lower Cauchy correlation into two absolute-Euler
source values below the Xi strip. -/
def criticalHardyLowerLowerPrimeArchSource (t s : ℝ) : ℂ :=
  let z := (criticalHardyLowerPoint t : ℂ)
  let v := (criticalHardyLowerPoint (-s) : ℂ)
  (-primeArchSourceRelativeTrace v - primeArchSourceRelativeTrace z) / (z + v)

/-- Functional-equation fold of the upper/upper Cauchy correlation into two absolute-Euler
source values below the Xi strip. -/
def criticalHardyUpperUpperPrimeArchSource (t s : ℝ) : ℂ :=
  let z := (criticalHardyLowerPoint s : ℂ)
  let v := (criticalHardyLowerPoint (-t) : ℂ)
  (primeArchSourceRelativeTrace z + primeArchSourceRelativeTrace v) /
    ((criticalHardyUpperPoint t : ℂ) - z)

private theorem xiRelativeResolventTrace_neg_of_lowerPoint (t : ℝ) :
    xiRelativeResolventTrace (-(criticalHardyLowerPoint t : ℂ)) =
      -xiRelativeResolventTrace (criticalHardyLowerPoint t : ℂ) := by
  have hbase : XiC (criticalHardyLowerPoint t : ℂ) ≠ 0 :=
    XiC_ne_zero_of_one_lt_centered_re (criticalHardyLowerPoint t).property
  have hneg : XiC (-(criticalHardyLowerPoint t : ℂ)) ≠ 0 := by
    rw [XiC_even]
    exact hbase
  rw [← logDeriv_XiC_eq_relativeResolventTrace hneg,
    logDeriv_XiC_neg,
    logDeriv_XiC_eq_relativeResolventTrace hbase]

/-- The same-orientation lower Hardy correlation is already an absolute-Euler prime--Gamma
divided difference after folding its upper evaluation through the functional equation. -/
theorem xiWeilPolarization_criticalHardyLower_eq_primeArchSource
    (t s : ℝ) :
    xiWeilPolarization
        (criticalHardyLowerCauchyTest t)
        (criticalHardyLowerCauchyTest s) =
      criticalHardyLowerLowerPrimeArchSource t s := by
  let z : ℂ := criticalHardyLowerPoint t
  let w : ℂ := criticalHardyLowerPoint s
  let v : ℂ := criticalHardyLowerPoint (-s)
  have hz : XiC z ≠ 0 :=
    XiC_ne_zero_of_one_lt_centered_re (criticalHardyLowerPoint t).property
  have hw : XiC ((starRingEnd ℂ) w) ≠ 0 := by
    apply XiC_ne_zero_of_half_le_abs_im
    simp [w]
    norm_num
  have hsep : z ≠ (starRingEnd ℂ) w := by
    intro h
    have him := congrArg Complex.im h
    simp [z, w] at him
    norm_num at him
  have hconj : (starRingEnd ℂ) w = -v := by
    dsimp [w, v]
    simp
    ring
  have hbase := xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference
    hz hw hsep
  have hzSource := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (criticalHardyLowerPoint t).property
  have hvSource := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (criticalHardyLowerPoint (-s)).property
  change xiWeilPolarization
    (fun a => I * xiWeilCauchyTest z a)
    (fun a => I * xiWeilCauchyTest w a) = _
  rw [xiWeilPolarization_const_smul_left,
    xiWeilPolarization_const_smul_right]
  have hscale :
      I * ((starRingEnd ℂ) I *
        xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w)) =
      xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) := by
    rw [conj_I]
    ring_nf
    norm_num [Complex.I_sq]
  rw [hscale]
  rw [hbase, hconj, xiRelativeResolventTrace_neg_of_lowerPoint (-s),
    ← hzSource, ← hvSource]
  simp [criticalHardyLowerLowerPrimeArchSource, z, v]
  congr 1
  ring

/-- The same-orientation upper Hardy correlation is likewise an absolute-Euler source divided
difference, using the opposite real center under functional-equation reflection. -/
theorem xiWeilPolarization_criticalHardyUpper_eq_primeArchSource
    (t s : ℝ) :
    xiWeilPolarization
        (criticalHardyUpperCauchyTest t)
        (criticalHardyUpperCauchyTest s) =
      criticalHardyUpperUpperPrimeArchSource t s := by
  let z : ℂ := criticalHardyUpperPoint t
  let w : ℂ := criticalHardyUpperPoint s
  let u : ℂ := criticalHardyLowerPoint s
  let v : ℂ := criticalHardyLowerPoint (-t)
  have hz : XiC z ≠ 0 := by
    apply XiC_ne_zero_of_half_le_abs_im
    simp [z]
    norm_num
  have hconj : (starRingEnd ℂ) w = u := by
    dsimp [w, u]
    simp
    ring
  have hw : XiC ((starRingEnd ℂ) w) ≠ 0 := by
    rw [hconj]
    exact XiC_ne_zero_of_one_lt_centered_re (criticalHardyLowerPoint s).property
  have hsep : z ≠ (starRingEnd ℂ) w := by
    intro h
    have him := congrArg Complex.im h
    simp [z, w] at him
    norm_num at him
  have hreflect : z = -v := by
    dsimp [z, v]
    simp
    ring
  have hbase := xiWeilPolarization_cauchy_eq_relativeResolvent_dividedDifference
    hz hw hsep
  have huSource := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (criticalHardyLowerPoint s).property
  have hvSource := primeArchSourceRelativeTrace_eq_xiRelativeResolventTrace
    (criticalHardyLowerPoint (-t)).property
  change xiWeilPolarization
    (fun a => -I * xiWeilCauchyTest z a)
    (fun a => -I * xiWeilCauchyTest w a) = _
  rw [xiWeilPolarization_const_smul_left,
    xiWeilPolarization_const_smul_right]
  have hscale :
      -I * ((starRingEnd ℂ) (-I) *
        xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w)) =
      xiWeilPolarization (xiWeilCauchyTest z) (xiWeilCauchyTest w) := by
    simp only [map_neg, conj_I]
    ring_nf
    norm_num [Complex.I_sq]
  rw [hscale]
  rw [hbase, hconj, hreflect,
    xiRelativeResolventTrace_neg_of_lowerPoint (-t),
    ← huSource, ← hvSource]
  simp [criticalHardyUpperUpperPrimeArchSource, u, v]
  congr 1
  ring

/-- The atomic Hardy source cup is exactly the corresponding multiplicity-exact Xi Weil
polarization. -/
theorem criticalHardyPrimeGammaSourceCup_eq_xiWeilPolarization
    (t s : ℝ) :
    criticalHardyPrimeGammaSourceCup t s =
      xiWeilPolarization
        (criticalHardyLowerCauchyTest t)
        (criticalHardyUpperCauchyTest s) := by
  rw [criticalHardyPrimeGammaSourceCup,
    deningerPrimeGammaSourceCup_eq_xiWeilPolarization]
  congr 1
  · funext z
    simp [criticalHardyLowerCauchyTest]
  · funext z
    simp [criticalHardyUpperCauchyTest]

/-- Exact four-term source anatomy of the full critical-feature polarization.  The two cross
orientations are literal prime--Gamma cups.  The remaining lower/lower and upper/upper terms are
the same-orientation correlations that a completed four-leg source trace must supply. -/
theorem xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceCups_add_sameOrientation
    (t s : ℝ) :
    xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest s) =
      xiWeilPolarization
          (criticalHardyLowerCauchyTest t)
          (criticalHardyLowerCauchyTest s) +
        criticalHardyPrimeGammaSourceCup t s +
        (starRingEnd ℂ) (criticalHardyPrimeGammaSourceCup s t) +
        xiWeilPolarization
          (criticalHardyUpperCauchyTest t)
          (criticalHardyUpperCauchyTest s) := by
  let Lt : ℂ → ℂ := criticalHardyLowerCauchyTest t
  let Ut : ℂ → ℂ := criticalHardyUpperCauchyTest t
  let Ls : ℂ → ℂ := criticalHardyLowerCauchyTest s
  let Us : ℂ → ℂ := criticalHardyUpperCauchyTest s
  have hLt : XiWeilSquareSummable Lt :=
    (XiWeilSquareSummable_cauchy (criticalHardyLowerPoint t : ℂ)).const_smul I
  have hUt : XiWeilSquareSummable Ut :=
    (XiWeilSquareSummable_cauchy (criticalHardyUpperPoint t : ℂ)).const_smul (-I)
  have hLs : XiWeilSquareSummable Ls :=
    (XiWeilSquareSummable_cauchy (criticalHardyLowerPoint s : ℂ)).const_smul I
  have hUs : XiWeilSquareSummable Us :=
    (XiWeilSquareSummable_cauchy (criticalHardyUpperPoint s : ℂ)).const_smul (-I)
  have hcrossTS :
      criticalHardyPrimeGammaSourceCup t s = xiWeilPolarization Lt Us := by
    simpa [Lt, Us] using
      criticalHardyPrimeGammaSourceCup_eq_xiWeilPolarization t s
  have hcrossST :
      (starRingEnd ℂ) (criticalHardyPrimeGammaSourceCup s t) =
        xiWeilPolarization Ut Ls := by
    rw [criticalHardyPrimeGammaSourceCup_eq_xiWeilPolarization,
      ← xiWeilPolarization_conj_symm]
  change xiWeilPolarization (Lt + Ut) (Ls + Us) = _
  rw [xiWeilPolarization_add_left hLt hUt (hLs.add hUs),
    xiWeilPolarization_add_right hLt hLs hUs,
    xiWeilPolarization_add_right hUt hLs hUs,
    ← hcrossTS, ← hcrossST]
  ring

/-- Complete absolute-Euler prime--Gamma realization of the critical-feature polarization.  Both
same-orientation terms have been folded through the functional equation and both cross terms are
literal Deninger source cups. -/
theorem xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_primeGammaSource
    (t s : ℝ) :
    xiWeilPolarization
        (criticalFeatureCauchyKernelTest t)
        (criticalFeatureCauchyKernelTest s) =
      criticalHardyLowerLowerPrimeArchSource t s +
        criticalHardyPrimeGammaSourceCup t s +
        (starRingEnd ℂ) (criticalHardyPrimeGammaSourceCup s t) +
        criticalHardyUpperUpperPrimeArchSource t s := by
  rw [
    xiWeilPolarization_criticalFeatureCauchyKernelTest_eq_sourceCups_add_sameOrientation,
    xiWeilPolarization_criticalHardyLower_eq_primeArchSource,
    xiWeilPolarization_criticalHardyUpper_eq_primeArchSource]

end

end RHTower
