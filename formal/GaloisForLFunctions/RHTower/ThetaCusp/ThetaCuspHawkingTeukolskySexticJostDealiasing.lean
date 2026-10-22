import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyChargeDecayResonanceLadder
import GaloisForLFunctions.HTGeometry.DigammaGammaFactorialBlowUp

/-!
# Sextic Hawking--Teukolsky Jost dealiasing

Evaluate each nonlinear charge-decay frequency against the complete negative
Birmingham--Mokhtari Jost divisor, rather than one preselected overtone.  At
rung `k`, the reciprocal-Gamma argument is

`-(5k+3) + 2(k+1) Im(z)`.

For the first, sextic rung the open Xi strip sends this argument into
`(-4,-2)`.  Its only reciprocal-Gamma zero is `-3`, so any negative-branch
Jost incidence is exactly the critical-line equation.  Every higher rung has
an off-axis alias: `Im(z)=1/(2(k+1))` hits overtone `5k+2` inside the strip.
Thus the sextic rung is the unique alias-free member of this nonlinear ladder.

These theorems classify source-frequency incidence.  They do not prove that
the sixth-order Einstein--Teukolsky source coefficient is nonzero or that full
dynamics forces its frequency onto the Jost divisor.

**[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED]**
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Negative-helicity Jost value evaluated at nonlinear charge-decay frequency. -/
def d4ThetaHawkingChargeDecayNegativeJost (k : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricJostMinus
    (d4ThetaHawkingChargeDecayInputFrequency k z)
    (d4ThetaCuspHawkingQuadraticDealiasedLift z)

/-- Reciprocal-Gamma coordinate of nonlinear charge-decay frequency. -/
theorem d4ThetaHawkingChargeDecayInput_radialB (k : ℕ) (z : ℂ) :
    thetaCuspHawkingHypergeometricRadialB
        (d4ThetaHawkingChargeDecayInputFrequency k z)
        (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
      -(d4ThetaHawkingChargeDecayTargetOvertone k : ℂ) +
        2 * ((k + 1 : ℕ) : ℂ) * (z.im : ℂ) := by
  let omega0 := thetaCuspHawkingTopologicalBlackHoleQNMMinus
    (d4ThetaHawkingChargeDecayTargetOvertone k)
    (d4ThetaCuspHawkingQuadraticDealiasedLift z)
  calc
    thetaCuspHawkingHypergeometricRadialB
        (d4ThetaHawkingChargeDecayInputFrequency k z)
        (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
      thetaCuspHawkingHypergeometricRadialB omega0
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) -
        Complex.I / 2 *
          (d4ThetaHawkingChargeDecayInputFrequency k z - omega0) := by
            unfold thetaCuspHawkingHypergeometricRadialB
            ring
    _ = _ := by
      rw [show thetaCuspHawkingHypergeometricRadialB omega0
          (d4ThetaCuspHawkingQuadraticDealiasedLift z) =
            -(d4ThetaHawkingChargeDecayTargetOvertone k : ℂ) by
        exact thetaCuspHawkingHypergeometricRadialB_qnmMinus _ _]
      rw [show d4ThetaHawkingChargeDecayInputFrequency k z - omega0 =
          (4 * (k + 1) : ℂ) * Complex.I * (z.im : ℂ) by
        exact d4ThetaHawkingChargeDecayInputFrequency_sub_qnmMinus k z]
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring

/-- Exact reciprocal-Gamma value of first, sextic charge-decay source. -/
theorem d4ThetaHawkingSexticNegativeJost_eq (z : ℂ) :
    d4ThetaHawkingChargeDecayNegativeJost 0 z =
      GaloisForLFunctions.reciprocalGammaEntire
        (-3 + 2 * (z.im : ℂ)) := by
  unfold d4ThetaHawkingChargeDecayNegativeJost
    thetaCuspHawkingHypergeometricJostMinus
  rw [d4ThetaHawkingChargeDecayInput_radialB]
  norm_num [d4ThetaHawkingChargeDecayTargetOvertone]

private lemma reciprocalGammaEntire_ne_zero_of_real_mem_neg_one_one_ne_zero
    (x : ℝ) (hxlo : -1 < x) (hx0 : x ≠ 0) :
    GaloisForLFunctions.reciprocalGammaEntire (x : ℂ) ≠ 0 := by
  apply inv_ne_zero
  apply Complex.Gamma_ne_zero
  intro m hm
  have hre := congrArg Complex.re hm
  simp only [Complex.ofReal_re, Complex.neg_re, Complex.natCast_re] at hre
  by_cases hm0 : m = 0
  · subst m
    norm_num at hre
    exact hx0 hre
  · have hm1 : (1 : ℝ) ≤ (m : ℝ) := by
      exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hm0)
    linarith

/-- Inside open Xi strip, sextic source hits negative Jost divisor only on axis. -/
theorem d4ThetaHawkingSexticNegativeJost_eq_zero_iff
    (z : ℂ) (hzlo : -1 / 2 < z.im) (hzhi : z.im < 1 / 2) :
    d4ThetaHawkingChargeDecayNegativeJost 0 z = 0 ↔ z.im = 0 := by
  rw [d4ThetaHawkingSexticNegativeJost_eq]
  let delta : ℂ := (2 * z.im : ℝ)
  have hdlo : (-1 : ℝ) < delta.re := by simp [delta]; linarith
  have hdhi : delta.re < (1 : ℝ) := by simp [delta]; linarith
  rw [show (-3 : ℂ) + 2 * (z.im : ℂ) = -(3 : ℂ) + delta by
    simp [delta]]
  have hrec :=
    GaloisForLFunctions.reciprocalGammaEntire_neg_nat_add 3 delta
  norm_num at hrec
  rw [hrec]
  have hprod :
      GaloisForLFunctions.reciprocalGammaBackwardProduct 3 delta ≠ 0 := by
    unfold GaloisForLFunctions.reciprocalGammaBackwardProduct
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    apply sub_ne_zero.mpr
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.natCast_re] at hre
    push_cast at hre
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  rw [mul_eq_zero]
  simp only [hprod, false_or]
  constructor
  · intro hzero
    by_contra hz0
    apply (reciprocalGammaEntire_ne_zero_of_real_mem_neg_one_one_ne_zero
      (2 * z.im) (by simpa [delta] using hdlo)
      (mul_ne_zero (by norm_num) hz0))
    simpa [delta] using hzero
  · intro hz0
    simp [delta, hz0, GaloisForLFunctions.reciprocalGammaEntire]

lemma xiSpectralPoint_im_mem_open_half (q : XiZeroCopy) :
    -1 / 2 < (xiSpectralPoint q).im ∧ (xiSpectralPoint q).im < 1 / 2 := by
  rw [xiSpectralPoint_im_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith

/-- Divisor-wise sextic Jost incidence is exactly critical-line placement. -/
theorem d4ThetaHawkingSexticNegativeJost_xi_eq_zero_iff (q : XiZeroCopy) :
    d4ThetaHawkingChargeDecayNegativeJost 0 (xiSpectralPoint q) = 0 ↔
      (q.1 : ℂ).re = 1 / 2 := by
  have hstrip := xiSpectralPoint_im_mem_open_half q
  rw [d4ThetaHawkingSexticNegativeJost_eq_zero_iff _ hstrip.1 hstrip.2,
    xiSpectralPoint_im_eq]
  constructor <;> intro h <;> linarith

/-- Every divisor-labelled sextic source frequency lies on negative Jost divisor. -/
def D4ThetaHawkingSexticSourceOnNegativeJostDivisor : Prop :=
  ∀ q : XiZeroCopy,
    d4ThetaHawkingChargeDecayNegativeJost 0 (xiSpectralPoint q) = 0

/-- Global sextic source-to-negative-Jost incidence is equivalent to RH. -/
theorem riemannHypothesis_iff_d4ThetaHawkingSexticSourceOnNegativeJostDivisor :
    RiemannHypothesis ↔ D4ThetaHawkingSexticSourceOnNegativeJostDivisor := by
  constructor
  · intro hRH q
    apply (d4ThetaHawkingSexticNegativeJost_xi_eq_zero_iff q).2
    have him := xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q
    rw [xiSpectralPoint_im_eq] at him
    linarith
  · intro hJost
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hre :=
      (d4ThetaHawkingSexticNegativeJost_xi_eq_zero_iff q).1 (hJost q)
    have him : (xiSpectralPoint q).im = 0 := by
      rw [xiSpectralPoint_im_eq]
      linarith
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [him]

/-- First positive reciprocal-Gamma alias displacement at rung `k`. -/
def d4ThetaHawkingChargeDecayFirstPositiveAliasTilt (k : ℕ) : ℝ :=
  1 / (2 * ((k + 1 : ℕ) : ℝ))

/-- Alias point with arbitrary physical height coordinate. -/
def d4ThetaHawkingChargeDecayFirstPositiveAliasPoint (k : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) + Complex.I *
    (d4ThetaHawkingChargeDecayFirstPositiveAliasTilt k : ℂ)

lemma d4ThetaHawkingChargeDecayFirstPositiveAliasPoint_im (k : ℕ) (x : ℝ) :
    (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x).im =
      1 / (2 * ((k + 1 : ℕ) : ℝ)) := by
  simp only [d4ThetaHawkingChargeDecayFirstPositiveAliasPoint,
    Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
    Complex.I_im, zero_mul, one_mul, zero_add, Complex.ofReal_re]
  rfl

/-- First positive alias lands one overtone below nominal ladder target. -/
theorem d4ThetaHawkingChargeDecayFirstPositiveAlias_frequency_eq
    (k : ℕ) (x : ℝ) :
    d4ThetaHawkingChargeDecayInputFrequency k
        (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus
        (d4ThetaHawkingChargeDecayTargetOvertone k - 1)
        (d4ThetaCuspHawkingQuadraticDealiasedLift
          (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x)) := by
  rw [← sub_eq_zero]
  change d4ThetaHawkingChargeMinusTwoFundamentalFrequency
      (d4ThetaHawkingChargeDecayDirectMultiplicity k)
      (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x) - _ = 0
  rw [d4ThetaHawkingChargeMinusTwoFundamentalFrequency_sub_qnmMinus]
  rw [d4ThetaHawkingChargeDecayFirstPositiveAliasPoint_im]
  simp [d4ThetaHawkingChargeDecayDirectMultiplicity,
    d4ThetaHawkingChargeDecayTargetOvertone]
  have hk : (k : ℂ) + 1 ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero k
  field_simp [hk]
  ring

/-- For every higher rung, first positive alias lies strictly inside Xi strip. -/
theorem d4ThetaHawkingChargeDecayFirstPositiveAlias_mem_strip
    {k : ℕ} (hk : 1 ≤ k) (x : ℝ) :
    0 < (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x).im ∧
      (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x).im < 1 / 2 := by
  rw [d4ThetaHawkingChargeDecayFirstPositiveAliasPoint_im]
  constructor
  · positivity
  · have hkR : (1 : ℝ) < (k + 1 : ℕ) := by
      exact_mod_cast (by omega : 1 < k + 1)
    have hpos : (0 : ℝ) < 2 * ((k + 1 : ℕ) : ℝ) := by positivity
    rw [div_lt_iff₀ hpos]
    have heq : (1 / 2 : ℝ) * (2 * ((k + 1 : ℕ) : ℝ)) =
        ((k + 1 : ℕ) : ℝ) := by ring
    rw [heq]
    exact hkR

/-- Every first positive alias is an actual negative-helicity Jost zero. -/
theorem d4ThetaHawkingChargeDecayFirstPositiveAlias_jost_eq_zero
    (k : ℕ) (x : ℝ) :
    d4ThetaHawkingChargeDecayNegativeJost k
        (d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k x) = 0 := by
  unfold d4ThetaHawkingChargeDecayNegativeJost
  rw [d4ThetaHawkingChargeDecayFirstPositiveAlias_frequency_eq]
  exact thetaCuspHawkingHypergeometricJostMinus_qnm_zero _ _

/-- Every higher rung has an off-axis negative-Jost alias in open Xi strip. -/
theorem exists_d4ThetaHawkingChargeDecay_offAxisJostAlias
    (k : ℕ) (hk : 1 ≤ k) :
    ∃ z : ℂ, 0 < z.im ∧ z.im < 1 / 2 ∧
      d4ThetaHawkingChargeDecayNegativeJost k z = 0 := by
  let z := d4ThetaHawkingChargeDecayFirstPositiveAliasPoint k 0
  have hstrip := d4ThetaHawkingChargeDecayFirstPositiveAlias_mem_strip hk 0
  exact ⟨z, hstrip.1, hstrip.2,
    d4ThetaHawkingChargeDecayFirstPositiveAlias_jost_eq_zero k 0⟩

end

end RHTower
