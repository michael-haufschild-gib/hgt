import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspLikelihoodAtomicNondivisibility
import GaloisForLFunctions.RHTower.XiCTaylorThetaTailProductFiberCenteredSeam

/-!
# Theta likelihood gaps are exact oriented Eisenstein mass shells

For the atomic theta likelihood gap `tₙ = n² - 1`, a two-particle pair obeys

`(tₙ + 1) (tₘ + 1) = (nm)²`.

Thus fixed products `nm = k`, which are the divisor packets governing the Wigner--Eisenstein
expansion, are exactly integral mass shells in shifted likelihood-gap coordinates.  Their Lorentz
form is

`(tₙ + tₘ + 2)² - (tₙ - tₘ)² = 4 (nm)²`.

The rapidity coordinate also agrees exactly: the centered divisor displacement is one quarter of
the shifted-gap logarithmic ratio.  Consequently the complete likelihood mass-shell phase is the
already formalized product-fibre/divisor phase, and inherits its strict negative upper-half-plane
current for every nontrivial shell.

This closes an exact connector between the positive theta likelihood measure and the
Wigner--Bessel--Eisenstein arithmetic carrier.  It does not sign the later positive-half-line seam;
that coupling remains the RH-relevant open step.
-/

open Complex Real Finset

namespace RHTower
noncomputable section

/-- Shifted theta-likelihood gaps attached to a zero-based positive factor pair. -/
def thetaCuspLikelihoodAtomicGapPair (q : ℕ × ℕ) : ℝ × ℝ :=
  (thetaCuspLikelihoodGap (q.1 + 1), thetaCuspLikelihoodGap (q.2 + 1))

/-- Adding back the ground-state shift recovers the square index exactly. -/
theorem thetaCuspLikelihoodGap_add_one (n : ℕ) :
    thetaCuspLikelihoodGap n + 1 = (n : ℝ) ^ (2 : ℕ) := by
  unfold thetaCuspLikelihoodGap
  ring

/-- The product coordinate of a likelihood-gap pair is the square of its arithmetic mode. -/
theorem thetaCuspLikelihoodAtomicGapPair_massSq (q : ℕ × ℕ) :
    ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) *
      ((thetaCuspLikelihoodAtomicGapPair q).2 + 1) =
      ((thetaPositivePairProduct q : ℕ) : ℝ) ^ (2 : ℕ) := by
  simp only [thetaCuspLikelihoodAtomicGapPair, thetaCuspLikelihoodGap_add_one,
    thetaPositivePairProduct]
  push_cast
  ring

/-- Energy and displacement coordinates put every atomic pair on an exact Lorentz mass shell. -/
theorem thetaCuspLikelihoodAtomicGapPair_lorentz_massShell (q : ℕ × ℕ) :
    ((thetaCuspLikelihoodAtomicGapPair q).1 +
        (thetaCuspLikelihoodAtomicGapPair q).2 + 2) ^ (2 : ℕ) -
      ((thetaCuspLikelihoodAtomicGapPair q).1 -
        (thetaCuspLikelihoodAtomicGapPair q).2) ^ (2 : ℕ) =
      4 * ((thetaPositivePairProduct q : ℕ) : ℝ) ^ (2 : ℕ) := by
  calc
    _ = 4 * (((thetaCuspLikelihoodAtomicGapPair q).1 + 1) *
        ((thetaCuspLikelihoodAtomicGapPair q).2 + 1)) := by ring
    _ = 4 * ((thetaPositivePairProduct q : ℕ) : ℝ) ^ (2 : ℕ) := by
      rw [thetaCuspLikelihoodAtomicGapPair_massSq]

/-- The shifted-gap shell equation detects the arithmetic product mode without loss. -/
theorem thetaCuspLikelihoodAtomicGapPair_massShell_iff
    (q : ℕ × ℕ) (k : ℕ) :
    ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) *
        ((thetaCuspLikelihoodAtomicGapPair q).2 + 1) = (k : ℝ) ^ (2 : ℕ) ↔
      thetaPositivePairProduct q = k := by
  constructor
  · intro h
    rw [thetaCuspLikelihoodAtomicGapPair_massSq] at h
    have hp : 0 ≤ ((thetaPositivePairProduct q : ℕ) : ℝ) := by positivity
    have hk : 0 ≤ (k : ℝ) := by positivity
    have heq : ((thetaPositivePairProduct q : ℕ) : ℝ) = (k : ℝ) := by
      nlinarith
    exact_mod_cast heq
  · intro h
    rw [thetaCuspLikelihoodAtomicGapPair_massSq, h]

/-- Every positive factor packet lies on its corresponding likelihood mass shell. -/
theorem thetaCuspLikelihoodAtomicGapPair_mem_massShell
    {k : ℕ} {q : ℕ × ℕ} (hq : q ∈ thetaPositiveFactorPairs k) :
    ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) *
      ((thetaCuspLikelihoodAtomicGapPair q).2 + 1) = (k : ℝ) ^ (2 : ℕ) := by
  rw [thetaCuspLikelihoodAtomicGapPair_massSq]
  congr 1
  exact_mod_cast (Finset.mem_filter.mp hq).2

/-- Divisor rapidity is precisely the shifted likelihood-gap log-ratio. -/
theorem thetaFactorPairLogDisplacement_eq_gapPair (q : ℕ × ℕ) :
    thetaFactorPairLogDisplacement q =
      (Real.log ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) -
        Real.log ((thetaCuspLikelihoodAtomicGapPair q).2 + 1)) / 4 := by
  simp only [thetaCuspLikelihoodAtomicGapPair, thetaCuspLikelihoodGap_add_one,
    thetaFactorPairLogDisplacement]
  have h1 : ((q.1 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((q.2 + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [show ((q.1 + 1 : ℕ) : ℝ) ^ (2 : ℕ) =
      ((q.1 + 1 : ℕ) : ℝ) * ((q.1 + 1 : ℕ) : ℝ) by ring,
    show ((q.2 + 1 : ℕ) : ℝ) ^ (2 : ℕ) =
      ((q.2 + 1 : ℕ) : ℝ) * ((q.2 + 1 : ℕ) : ℝ) by ring,
    Real.log_mul h1 h1, Real.log_mul h2 h2]
  ring

/-- The first self-convolution atom born at total gap `6` is the central `(2,2)` divisor pair on
mode `4`.  Its rapidity is zero, so it is current-neutral in isolation; orientation belongs to
the completed shell rather than to this new atom alone. -/
theorem thetaCuspLikelihood_selfConv_birth_is_mode_four_zeroRapidity :
    thetaCuspLikelihoodAtomicGapPair (1, 1) = (3, 3) ∧
      thetaPositivePairProduct (1, 1) = 4 ∧
      thetaFactorPairLogDisplacement (1, 1) = 0 := by
  norm_num [thetaCuspLikelihoodAtomicGapPair, thetaCuspLikelihoodGap,
    thetaPositivePairProduct, thetaFactorPairLogDisplacement]

/-- Complete centered phase of one arithmetic likelihood mass shell. -/
def thetaCuspLikelihoodMassShellPhase (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    Complex.exp
      (I * (((Real.log ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) -
        Real.log ((thetaCuspLikelihoodAtomicGapPair q).2 + 1)) / 4 : ℝ) : ℂ) * z)

/-- Explicit spectral derivative of the complete likelihood mass-shell phase. -/
def thetaCuspLikelihoodMassShellPhaseDerivative (k : ℕ) (z : ℂ) : ℂ :=
  ∑ q ∈ thetaPositiveFactorPairs k,
    (I * (((Real.log ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) -
      Real.log ((thetaCuspLikelihoodAtomicGapPair q).2 + 1)) / 4 : ℝ) : ℂ)) *
      Complex.exp
        (I * (((Real.log ((thetaCuspLikelihoodAtomicGapPair q).1 + 1) -
          Real.log ((thetaCuspLikelihoodAtomicGapPair q).2 + 1)) / 4 : ℝ) : ℂ) * z)

/-- Likelihood mass-shell phase is exactly the theta product-fibre/divisor phase. -/
theorem thetaCuspLikelihoodMassShellPhase_eq_productFiber
    (k : ℕ) (z : ℂ) :
    thetaCuspLikelihoodMassShellPhase k z =
      thetaProductFiberCenteredPhase k z := by
  unfold thetaCuspLikelihoodMassShellPhase thetaProductFiberCenteredPhase
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaFactorPairLogDisplacement_eq_gapPair]

/-- The likelihood mass-shell derivative is the existing product-fibre derivative. -/
theorem thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber
    (k : ℕ) (z : ℂ) :
    thetaCuspLikelihoodMassShellPhaseDerivative k z =
      thetaProductFiberCenteredPhaseDerivative k z := by
  unfold thetaCuspLikelihoodMassShellPhaseDerivative
    thetaProductFiberCenteredPhaseDerivative
  apply Finset.sum_congr rfl
  intro q _hq
  rw [thetaFactorPairLogDisplacement_eq_gapPair]

/-- Coherent current of one likelihood mass shell with a common radial tail. -/
def thetaCuspLikelihoodMassShellCoherentBaseCurrent
    (k : ℕ) (z F : ℂ) : ℝ :=
  Complex.normSq F *
    (thetaCuspLikelihoodMassShellPhaseDerivative k z *
      (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im

/-- The likelihood-shell base is exactly the coherent product-fibre base in the theta current. -/
theorem thetaCuspLikelihoodMassShellCoherentBaseCurrent_eq_productFiber
    (k : ℕ) (z F : ℂ) :
    thetaCuspLikelihoodMassShellCoherentBaseCurrent k z F =
      xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent k z F := by
  unfold thetaCuspLikelihoodMassShellCoherentBaseCurrent
    xiCTaylorThetaTailCoreProductFiberCoherentPhaseBaseCurrent
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber,
    thetaCuspLikelihoodMassShellPhase_eq_productFiber]

/-- **Oriented likelihood mass-shell theorem.** Every nontrivial complete arithmetic shell has
strict negative upper-half-plane current before coupling to the positive-half-line seam. -/
theorem thetaCuspLikelihoodMassShellPhase_current_lt_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    (thetaCuspLikelihoodMassShellPhaseDerivative k z *
      (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase k z)).im < 0 := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber,
    thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  exact thetaProductFiberCenteredPhase_current_lt_zero hk hz

/-- A nonzero common radial tail preserves strict likelihood-shell orientation. -/
theorem thetaCuspLikelihoodMassShellCoherentBaseCurrent_lt_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im)
    {F : ℂ} (hF : F ≠ 0) :
    thetaCuspLikelihoodMassShellCoherentBaseCurrent k z F < 0 := by
  unfold thetaCuspLikelihoodMassShellCoherentBaseCurrent
  exact mul_neg_of_pos_of_neg (Complex.normSq_pos.mpr hF)
    (thetaCuspLikelihoodMassShellPhase_current_lt_zero hk hz)

/-- **Exact likelihood-shell/current bridge.** The actual untruncated theta phase current on one
shell is its strictly oriented likelihood base plus the complete Hermitian-polarization and
positive-half-line window seam. -/
theorem thetaProductFiberActualPhaseCurrent_eq_likelihoodMassShellBase_add_correctedSeam
    (k : ℕ) {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : 0 ≤ z.im) :
    thetaProductFiberActualPhaseCurrent k z =
      thetaCuspLikelihoodMassShellCoherentBaseCurrent k z
          (thetaCuspTailSecondDensityAtomOnePhaseTail c z) +
        thetaProductFiberCenteredCorrectedPhaseSeamCurrent k c z := by
  rw [thetaCuspLikelihoodMassShellCoherentBaseCurrent_eq_productFiber]
  exact thetaProductFiberActualPhaseCurrent_eq_coherentBase_add_correctedCenteredSeam
    k hc hz

/-- On the first nontrivial likelihood shell, Hermitian convolution reverses the coherent shell
sign at an explicit upper-half-plane point even before endpoint windows are introduced. -/
theorem thetaCuspLikelihoodMassShell_two_hermitian_sign_reversal :
    (thetaCuspLikelihoodMassShellPhaseDerivative 2
          thetaProductFiberHermitianSignReversalPoint *
        (starRingEnd ℂ) (thetaCuspLikelihoodMassShellPhase 2
          thetaProductFiberHermitianSignReversalPoint)).im < 0 ∧
      0 < thetaProductFiberCommonTailHermitianCurrent 2
        thetaProductFiberHermitianSignReversalPoint 1 0 := by
  rw [thetaCuspLikelihoodMassShellPhaseDerivative_eq_productFiber,
    thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  exact thetaProductFiberHermitianPolarization_sign_reversal

/-- Nontrivial likelihood mass shells have no upper-half-plane phase zero. -/
theorem thetaCuspLikelihoodMassShellPhase_ne_zero
    {k : ℕ} (hk : 1 < k) {z : ℂ} (hz : 0 < z.im) :
    thetaCuspLikelihoodMassShellPhase k z ≠ 0 := by
  rw [thetaCuspLikelihoodMassShellPhase_eq_productFiber]
  exact thetaProductFiberCenteredPhase_ne_zero hk hz

end
end RHTower
