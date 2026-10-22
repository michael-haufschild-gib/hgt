import GaloisForLFunctions.RHTower.XiHorizontalCollisionGaussHodgePrimeCurrent
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmSquarefreeFirstTraceExponentialContinuation

/-!
# Gamma-six curvature / continued first-prime-trace weld

The raw Gamma-six curvature is not the valuation-one prime-log current itself: the two objects
have different Mellin order, and at neutral grade the curvature vanishes while the prime-log atom
does not.  This module gives the exact source-derived identification.  Twice Mellin-integrate each
valuation-one prime-log atom, take the central difference at the two retained grades `±t`, and
apply the already source-selected Gauss-residue/Fisher Hadamard weight.  The result is literally
the Gamma-six suspension determinant current at every Xi multiplicity copy and prime label.

The second-derivative theorem and the Euler-chamber `tsum` theorem certify that the primitive is
the one belonging to the existing meromorphic valuation-one continuation, rather than an
unrelated exponential fitted to the curvature formula.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- One coefficient of the valuation-one prime-log current. -/
def xiValuationOnePrimeLogAtom (p : Nat.Primes) (s : ℂ) : ℂ :=
  (Real.log (p : ℝ) : ℂ) * coronaPrimeEigenvalue s p

/-- Canonical twice-Mellin-primitive of one valuation-one prime-log coefficient. -/
def xiValuationOneSecondMellinPrimitiveAtom (p : Nat.Primes) (s : ℂ) : ℂ :=
  Complex.exp (-((Real.log (p : ℝ) : ℂ) * s)) /
    (Real.log (p : ℝ) : ℂ)

theorem deriv_xiValuationOneSecondMellinPrimitiveAtom
    (p : Nat.Primes) (s : ℂ) :
    deriv (xiValuationOneSecondMellinPrimitiveAtom p) s =
      -Complex.exp (-((Real.log (p : ℝ) : ℂ) * s)) := by
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  have hlin : HasDerivAt
      (fun w : ℂ => -((Real.log (p : ℝ) : ℂ) * w))
      (-(Real.log (p : ℝ) : ℂ)) s := by
    simpa only [id_eq, mul_one, neg_mul] using
      (hasDerivAt_id s).const_mul (-(Real.log (p : ℝ) : ℂ))
  have h := hlin.cexp.div_const (Real.log (p : ℝ) : ℂ)
  rw [show xiValuationOneSecondMellinPrimitiveAtom p =
      fun w : ℂ => Complex.exp (-((Real.log (p : ℝ) : ℂ) * w)) /
        (Real.log (p : ℝ) : ℂ) by rfl,
    h.deriv]
  field_simp

/-- The primitive has exactly the valuation-one prime-log atom as its second Mellin derivative. -/
theorem secondDeriv_xiValuationOneSecondMellinPrimitiveAtom
    (p : Nat.Primes) (s : ℂ) :
    deriv (fun w : ℂ =>
      deriv (xiValuationOneSecondMellinPrimitiveAtom p) w) s =
      xiValuationOnePrimeLogAtom p s := by
  have hfun : (fun w : ℂ =>
      deriv (xiValuationOneSecondMellinPrimitiveAtom p) w) =
      fun w : ℂ => -Complex.exp (-((Real.log (p : ℝ) : ℂ) * w)) := by
    funext w
    exact deriv_xiValuationOneSecondMellinPrimitiveAtom p w
  rw [hfun]
  have hlin : HasDerivAt
      (fun w : ℂ => -((Real.log (p : ℝ) : ℂ) * w))
      (-(Real.log (p : ℝ) : ℂ)) s := by
    simpa only [id_eq, mul_one, neg_mul] using
      (hasDerivAt_id s).const_mul (-(Real.log (p : ℝ) : ℂ))
  change deriv (-fun w : ℂ =>
      Complex.exp (-((Real.log (p : ℝ) : ℂ) * w))) s = _
  rw [(hlin.cexp.neg).deriv]
  rw [xiValuationOnePrimeLogAtom, coronaPrimeEigenvalue]
  have hp0 : ((p : ℂ)) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.natCast_log]
  ring

/-- Existing Gauss residue/Fisher channel, before its Mellin primitive contributes `1/log p`. -/
def gammaSixPrimeTraceHadamardWeight (m : ℕ) (p : Nat.Primes) : ℝ :=
  Real.log 2 / 2 * gaussChannelResidueCurrent m p *
    primeActivationOccupancyFisherDensity p

/-- Source-side filtered central second difference of the twice-Mellin-primitive prime trace. -/
def gammaSixFilteredPrimeTraceSecondDifference
    (m : ℕ) (p : Nat.Primes) (t : ℝ) : ℂ :=
  (gammaSixPrimeTraceHadamardWeight m p : ℂ) *
    (xiValuationOneSecondMellinPrimitiveAtom p (-t) +
      xiValuationOneSecondMellinPrimitiveAtom p t -
      2 * xiValuationOneSecondMellinPrimitiveAtom p 0)

theorem gammaSixFilteredPrimeTraceSecondDifference_eq_splitEnergy
    (m : ℕ) (p : Nat.Primes) (t : ℝ) :
    gammaSixFilteredPrimeTraceSecondDifference m p t =
      (gaussReciprocalCharacterWeight m p : ℂ) *
        reciprocalCharacterComplexEnergy 1 (Real.log (p : ℝ)) t := by
  have hlog : (Real.log (p : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.log_pos (by exact_mod_cast p.prop.one_lt)).ne'
  rw [gammaSixFilteredPrimeTraceSecondDifference,
    gammaSixPrimeTraceHadamardWeight,
    xiValuationOneSecondMellinPrimitiveAtom,
    xiValuationOneSecondMellinPrimitiveAtom,
    xiValuationOneSecondMellinPrimitiveAtom,
    gaussReciprocalCharacterWeight,
    reciprocalCharacterComplexEnergy]
  simp only [mul_zero, neg_zero, Complex.exp_zero]
  push_cast
  field_simp

/-- **Coefficient-faithful curvature/trace weld.**  For every retained Xi multiplicity copy and
ordinary-prime label, raw Gamma-six determinant curvature is exactly the Gauss/Fisher-filtered
central two-orientation difference of the canonical second Mellin primitive of the valuation-one
prime-log current. -/
theorem gammaSixSuspensionDeterminantPrimeCurrent_eq_filteredPrimeTrace
    (m : ℕ) (q : XiZeroCopy) (p : Nat.Primes) :
    (gammaSixSuspensionDeterminantPrimeCurrent m q p : ℂ) =
      gammaSixFilteredPrimeTraceSecondDifference m p
        (primeDepthBVWoldXiCenteredRate q.1) := by
  rw [gammaSixFilteredPrimeTraceSecondDifference_eq_splitEnergy]
  rw [reciprocalCharacterComplexEnergy_ofReal]
  norm_cast
  rw [gammaSixSuspensionDeterminantPrimeCurrent,
    gaussGammaSixSuspensionTraceEnergy_eq_pairedBoundaryEnergy,
    gaussGammaSixPairedBoundaryEnergy_eq_splitEnergy]
  simp only [reciprocalCharacterSplitEnergy]
  ring

/-- On the Euler half-plane, the existing meromorphic valuation-one continuation is the sum of
the second derivatives of the very same primitive atoms used in the curvature weld. -/
theorem xiPrimeLogDirichletContinuation_eq_tsum_secondMellinPrimitive_secondDeriv
    {s : ℂ} (hs : 1 < s.re) :
    xiPrimeLogDirichletContinuation s =
      ∑' p : Nat.Primes,
        deriv (fun w : ℂ =>
          deriv (xiValuationOneSecondMellinPrimitiveAtom p) w) s := by
  rw [xiPrimeLogDirichletContinuation_eq hs,
    xiPrimeLogDirichlet_eq_tsum_primeLog_div_cpow hs]
  apply tsum_congr
  intro p
  rw [secondDeriv_xiValuationOneSecondMellinPrimitiveAtom,
    xiValuationOnePrimeLogAtom, coronaPrimeEigenvalue]
  have hp0 : ((p : ℂ)) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  rw [Complex.cpow_neg, div_eq_mul_inv]

/-- Explicit completed prime--Gamma form of the source identity: after removing the higher-prime-
power and archimedean regular terms, the completed flux is the sum of the second derivatives of
the same primitive atoms whose filtered central difference is Gamma-six curvature. -/
theorem completedPrimeGammaFlux_sub_regular_eq_tsum_secondMellinPrimitive_secondDeriv
    {s : ℂ} (hs : 1 < s.re) :
    completedPrimeGammaFlux s - xiPrimeLogHigherValuation s + logDeriv archFactor s =
      ∑' p : Nat.Primes,
        deriv (fun w : ℂ =>
          deriv (xiValuationOneSecondMellinPrimitiveAtom p) w) s := by
  rw [← xiPrimeLogDirichletContinuation_eq_tsum_secondMellinPrimitive_secondDeriv hs,
    completedPrimeGammaFlux_eq_firstTrace_add_regular,
    squarefreeFirstTraceContinuedCurrent]
  ring

end

end RHTower
