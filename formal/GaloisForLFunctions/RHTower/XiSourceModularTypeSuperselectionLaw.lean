import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression
import GaloisForLFunctions.RHTower.XiBVResidueHurwitzPhaseEnergyUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw
import GaloisForLFunctions.RHTower.AsymptoticTypeSuperselection
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration
import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction
import GaloisForLFunctions.RHTower.XiDepthMobiusGammaOuterInnerWeld
import GaloisForLFunctions.RHTower.XiPrimeSeamCoherenceCollapse
import GaloisForLFunctions.RHTower.XiEulerContractionResiduePairing
import GaloisForLFunctions.RHTower.CriticalActivationReesSourceLaw
import GaloisForLFunctions.RHTower.HypertranscendentalDivisorInformationLocalizationLaw
import GaloisForLFunctions.RHTower.HedenmalmThetaNullTemperedDenseRadicalUniversalityLaw
import GaloisForLFunctions.RHTower.XiPrimeSeamCalkinUniversalityLaw
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardEulerEdgeCompleteness
import GaloisForLFunctions.RHTower.XiDyadicDescentLevelUniversalityLaw
import GaloisForLFunctions.RHTower.XiDefectPersistentLocalLoopUniversalityLaw
import GaloisForLFunctions.RHTower.XiSpectralApertureConservationUniversalityLaw
import GaloisForLFunctions.RHTower.XiThetaHeatNodeObstruction
import GaloisForLFunctions.RHTower.ArithmeticJuliaNormalConeUniversalityLaw
import GaloisForLFunctions.RHTower.XiHurwitzOrientationEnergy
import GaloisForLFunctions.RHTower.XiRamifiedDifferentialOrientationLaw
import GaloisForLFunctions.RHTower.CCMFiniteRamifiedBoundaryNoGo
import GaloisForLFunctions.RHTower.XiFiniteLocalSpectralFrameObstruction
import GaloisForLFunctions.RHTower.XiLogDerivFiniteReporterBlindness
import GaloisForLFunctions.RHTower.XiMassGradedTraceZeroFreeDistortionUniversalityLaw
import GaloisForLFunctions.RHTower.PositiveEulerFiniteQuartetOrientationLaw
import GaloisForLFunctions.RHTower.SourceHorizonEscapeConservationLaw
import GaloisForLFunctions.RHTower.SuzukiKreinSchurBlockCongruence
import GaloisForLFunctions.RHTower.LocalGlobalRHTomography
import GaloisForLFunctions.RHTower.XiApertureCollisionRelativeKOneSimplicityTomographyUniversalityLaw
import GaloisForLFunctions.RHTower.XiPairwiseValuationBaseUniversalityLaw
import GaloisForLFunctions.RHTower.XiRootedStarIncidenceValuationMetricFusionUniversalityLaw
import GaloisForLFunctions.RHTower.XiCofiniteExactBlindDataProcessingUniversalityLaw
import GaloisForLFunctions.RHTower.XiEvaluationReporterSourceDiscriminationUniversalityLaw
import GaloisForLFunctions.RHTower.CCMCriticalClockDivisorBlindness
import GaloisForLFunctions.RHTower.XiSquaredEulerDiagonalCorrelationUniversalityLaw
import GaloisForLFunctions.RHTower.XiThermalOffLineChargeSelfCubicBound
import GaloisForLFunctions.RHTower.XiWardInteriorSourceBudgetDivergence
import GaloisForLFunctions.RHTower.ConePositivstellensatzFailure
import GaloisForLFunctions.RHTower.XiWeilCriterionConverse
import GaloisForLFunctions.HTGeometry.BifilteredScalarizationNoGo
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationInteractionSuperselection
import GaloisForLFunctions.HTGeometry.PrimeValuationCoordinateFusionCompletion
import GaloisForLFunctions.HTGeometry.PrimeDirichletDifferentialField
import GaloisForLFunctions.HTGeometry.PrimeDirichletTailGroupoid
import GaloisForLFunctions.HTGeometry.PrimeDirichletPositiveDefinite

/-!
# Xi source-modular type superselection

Every right-half Xi divisor copy has one positive centered charge.  This file
identifies that charge in four independently constructed charts:

* the residue of the source-normal-cone exceptional current;
* the cofinal entropy of the positive high-exponent shell;
* the principal phase of Hurwitz monodromy;
* the forward/inverse residue phase of every noncensoring compact-BV prime
  window.

The same charge parametrizes the reflected prime-valuation sectors.  Their
asymptotic types are not two finite grades: the positive sector is flat beyond
every Wold Rees order, whereas the reflected sector is finite/half-normal.
Consequently no finite-Rees-moderate operator can sew them, and every exact
sewing operator has norm beyond every inverse Rees power.
-/

open Complex Filter Asymptotics MeasureTheory Set
open scoped Topology ComplexOrder Differential UpperEndDifferentialInstances BigOperators
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open HTGeometry Module

namespace RHTower

noncomputable section

/-- Positive centered charge of a right-half Xi divisor copy. -/
def xiRightSourceModularCharge (q : XiRightZeroCopy) : ℝ :=
  (q.1.1 : ℂ).re - 1 / 2

/-- Every right-half Xi divisor charge is strictly positive. -/
theorem xiRightSourceModularCharge_pos
    (q : XiRightZeroCopy) :
    0 < xiRightSourceModularCharge q := by
  rw [xiRightSourceModularCharge]
  have h := xiRightCenteredZero_re_pos q
  rw [xiRightCenteredZero_eq_support_sub_half,
    Complex.sub_re] at h
  norm_num at h ⊢
  exact h

/-- Every right-half Xi divisor charge lies below the strip half-width. -/
theorem xiRightSourceModularCharge_lt_half
    (q : XiRightZeroCopy) :
    xiRightSourceModularCharge q < 1 / 2 := by
  rw [xiRightSourceModularCharge]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1.1
  linarith

/-- A genuine right-half Xi divisor copy cannot have a coherent canonical
prime-seam family. -/
theorem xiRightPrimeSeamCharges_not_coherent
    (q : XiRightZeroCopy) :
    ¬ OrbitwisePrimeSeamChargesCoherent (q.1.1 : ℂ) := by
  intro hcoh
  have hstrip := xi_divisor_support_re_mem_open_unit q.1.1
  have hre :=
    (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      hstrip).mp hcoh
  have hpos := xiRightSourceModularCharge_pos q
  rw [xiRightSourceModularCharge] at hpos
  linarith

/-- The cofinal shell entropy is the negative of the right modular charge. -/
theorem shellTransferEntropy_eq_neg_xiRightSourceModularCharge
    (q : XiRightZeroCopy) :
    shellTransferEntropy (q.1.1 : ℂ) =
      -xiRightSourceModularCharge q := by
  rw [shellTransferEntropy_eq, xiRightSourceModularCharge]
  ring

/-- The local source-normal-cone residue carries multiplicity times the same
signed modular charge. -/
theorem tendsto_re_xiExceptionalAffineDivisorCurrent_eq_neg_modularCharge
    (q : XiRightZeroCopy) {n : ℤ}
    (horder : meromorphicOrderAt xi (q.1.1 : ℂ) = n) :
    Tendsto
      (fun s =>
        ((s - (q.1.1 : ℂ)) *
          xiExceptionalAffineDivisorCurrent s).re)
      (nhdsWithin (q.1.1 : ℂ) ({(q.1.1 : ℂ)}ᶜ))
      (nhds (-((n : ℝ) * xiRightSourceModularCharge q))) := by
  have h :=
    tendsto_re_xiExceptionalAffineDivisorCurrent_eq_transferEntropy
      horder
  rw [shellTransferEntropy_eq_neg_xiRightSourceModularCharge] at h
  simpa only [mul_neg] using h

/-- Hurwitz monodromy has the same principal modular charge. -/
theorem xiRightSourceModularCharge_eq_hurwitzPrincipalPhase
    (q : XiRightZeroCopy) :
    xiRightSourceModularCharge q =
      xiHurwitzRightPrincipalPhase q := by
  rw [xiRightSourceModularCharge,
    xiHurwitzRightPrincipalPhase_eq_transverse,
    xiRightCenteredZero_eq_support_sub_half, Complex.sub_re]
  norm_num

/-- Every noncensoring compact-BV prime window recovers the same charge from
its forward/inverse dilation residues. -/
theorem xiBVResiduePhaseCoordinate_eq_sourceModularCharge
    (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r)
    (q : XiRightZeroCopy)
    (hres : W.continuedSourceResidueValue (q.1.1 : ℂ) ≠ 0) :
    xiBVResiduePhaseCoordinate W r hr q =
      xiRightSourceModularCharge q := by
  have hcert :=
    xiBVResidue_hurwitzPhaseEnergyUniversality W hr q hres
  rw [hcert.phaseReconstruction,
    xiRightSourceModularCharge_eq_hurwitzPrincipalPhase]

/-- Exact source-side certificate for the positive completion surviving the
finite-Rees no-go.  The depth-one activation atoms are Fisher-damped Gamma
valuation coordinates.  Gamma sewing is a boundedly invertible localization
on every positive aperture, so it preserves prime summability exactly, while
its principal symbols have arbitrarily large exact finite-prime Rees rank. -/
structure GammaSewnActivationReesResolutionCertificate : Prop where
  fisherDampedAtoms :
    ∀ (p : Nat.Primes) (e : ℕ),
      diagonalActivationPositiveValuationMass
          (xiTransversePrimeApertureDiskNode 1 p) e =
        xiMobiusPrimeSchurValuationDamping p *
          xiTransversePrimeHalfShiftedValuationCoordinate p e
  dampingIsFisher :
    ∀ p : Nat.Primes,
      xiMobiusPrimeSchurValuationDamping p ^ 2 =
        diagonalActivationOccupancyFisher
          (xiTransversePrimeApertureDiskNode 1 p)
  noFreeHilbertization :
    ∀ {x : ℝ}, 0 < x → ∀ (a : Nat.Primes → ℝ),
      (∀ p, 0 ≤ a p) →
        (Summable (fun p =>
          gammaSewnMobiusValuationContractionMultiplier x p ^ 2 * a p) ↔
          Summable a)
  unboundedExactReesRank :
    ∀ {N : ℕ} {p : Fin N → Nat.Primes}, Function.Injective p →
      (gammaSewnMobiusReesPrincipalSymbolMatrix p).det ≠ 0

/-- **Gamma-sewn activation--Rees resolution law.**  Fisher whitening and
Gamma sewing do not provide a missing bounded cutoff.  They preserve source
summability, but the complete prime information survives in an unbounded
tower of exact Rees symbols. -/
theorem gammaSewnActivationReesResolution_law :
    GammaSewnActivationReesResolutionCertificate where
  fisherDampedAtoms :=
    diagonalActivationPrimeMass_eq_fisherDampedGammaValuation
  dampingIsFisher :=
    xiMobiusPrimeSchurValuationDamping_sq_eq_activationOccupancyFisher
  noFreeHilbertization :=
    fun {_x} hx a ha =>
      summable_gammaSewnMobiusMultiplier_sq_mul_iff hx a ha
  unboundedExactReesRank :=
    fun hp =>
      gammaSewnMobiusReesPrincipalSymbolMatrix_det_ne_zero hp

/-- Exact certificate that the corrected singular squarefree source graph is
the outer balanced Xi connection and that its divisor residue is the first
outer coefficient of the two-endpoint depth nearby cycle. -/
structure XiDepthGraphOuterInnerWeldCertificate : Prop where
  sourceGraphOuterConnection :
    ∀ {sigma epsilon u : ℂ},
      1 < sigma.re →
      1 < (sigma + u * epsilon).re →
      epsilon ≠ 0 →
      xiExceptionalAffineDivisorCurrent (sigma + u * epsilon) =
        ((sigma + u * epsilon - 1 / 2) / 2) *
          (squarefreeMobiusGammaCurrentTransportV sigma epsilon
              (squarefreeFisherScore sigma epsilon) u +
            4 * infinitePrimeFlux (2 * (sigma + u * epsilon)))
  innerOuterChargeWeld :
    ∀ rho : ℂ,
      let m := (analyticOrderAt xi rho).toNat
      Tendsto
          (fun w : ℂ =>
            w⁻¹ *
              (depthSuccessorNearbyCycle (rho - 1 / 2) m w⁻¹ - 1))
          (𝓝[≠] 0)
          (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
        Tendsto
          (fun s : ℂ =>
            (s - rho) * xiExceptionalAffineDivisorCurrent s)
          (𝓝[≠] rho)
          (𝓝 (-((rho - 1 / 2) * (m : ℂ))))

/-- **Xi depth-graph outer/inner weld.** The actual squarefree
Möbius--Gamma graph, including its doubled-zeta correction, is the outer
balanced Xi connection. Its divisor charge is exactly the first outer
coefficient of the rational two-endpoint depth nearby cycle. -/
theorem xiDepthGraphOuterInnerWeld_law :
    XiDepthGraphOuterInnerWeldCertificate where
  sourceGraphOuterConnection :=
    fun hsigma hshift hepsilon =>
      xiExceptionalAffineDivisorCurrent_eq_scaled_mobiusGammaGraph
        hsigma hshift hepsilon
  innerOuterChargeWeld :=
    xiDepthNearby_outerCharge_and_affineResidue_match

/-- Additive normal-layer mismatch between source-inverse and
analytic-adjoint nearby poles. -/
def xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) : ℂ :=
  depthSuccessorNearbyPole (-(rho - 1 / 2)) -
    depthSuccessorNearbyPole (starRingEnd ℂ (rho - 1 / 2))

/-- The nearby-pole duality--adjunction fracture is exactly twice the
horizontal centered displacement. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_two_re
    (rho : ℂ) :
    xiNearbyPoleDualityAdjunctionFracture rho =
      ((2 * (rho.re - 1 / 2) : ℝ) : ℂ) := by
  apply Complex.ext
  · simp [xiNearbyPoleDualityAdjunctionFracture,
      depthSuccessorNearbyPole]
    ring
  · simp [xiNearbyPoleDualityAdjunctionFracture,
      depthSuccessorNearbyPole]

/-- The additive fracture vanishes exactly on the critical line. -/
theorem xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
    (rho : ℂ) :
    xiNearbyPoleDualityAdjunctionFracture rho = 0 ↔
      rho.re = 1 / 2 := by
  constructor
  · intro h
    have hre := congrArg Complex.re h
    simp [xiNearbyPoleDualityAdjunctionFracture,
      depthSuccessorNearbyPole] at hre
    linarith
  · intro h
    apply Complex.ext
    · simp [xiNearbyPoleDualityAdjunctionFracture,
        depthSuccessorNearbyPole, h]
    · simp [xiNearbyPoleDualityAdjunctionFracture,
        depthSuccessorNearbyPole]

/-- Every prime-clock duality--adjunction fracture is the exponential image
of the same two nearby-pole branches. -/
theorem primeCpowDualityAdjunctionFracture_eq_nearbyPoleExponentials
    (p : ℕ) (rho : ℂ) :
    primeCpowDualityAdjunctionFracture p rho =
      (p : ℂ) ^
          depthSuccessorNearbyPole (-(rho - 1 / 2)) -
        (p : ℂ) ^
          depthSuccessorNearbyPole
            (starRingEnd ℂ (rho - 1 / 2)) := by
  rw [show depthSuccessorNearbyPole (-(rho - 1 / 2)) =
      rho - 1 / 2 by simp [depthSuccessorNearbyPole]]
  rw [show depthSuccessorNearbyPole
      (starRingEnd ℂ (rho - 1 / 2)) =
        1 / 2 - starRingEnd ℂ rho by
    apply Complex.ext
    · simp [depthSuccessorNearbyPole]
    · simp [depthSuccessorNearbyPole]]
  rfl

/-- Exact additive/multiplicative equalizer certificate for the oriented
boundary character. -/
structure XiBoundaryCharacterFractureCertificate : Prop where
  additiveFracture :
    ∀ rho : ℂ,
      xiNearbyPoleDualityAdjunctionFracture rho =
        ((2 * (rho.re - 1 / 2) : ℝ) : ℂ)
  additiveEqualizer :
    ∀ rho : ℂ,
      xiNearbyPoleDualityAdjunctionFracture rho = 0 ↔
        rho.re = 1 / 2
  primeExponentiation :
    ∀ (p : ℕ) (rho : ℂ),
      primeCpowDualityAdjunctionFracture p rho =
        (p : ℂ) ^
            depthSuccessorNearbyPole (-(rho - 1 / 2)) -
          (p : ℂ) ^
            depthSuccessorNearbyPole
              (starRingEnd ℂ (rho - 1 / 2))
  primeCoherenceEqualizer :
    ∀ {rho : ℂ}, 0 < rho.re ∧ rho.re < 1 →
      (OrbitwisePrimeSeamChargesCoherent rho ↔
        rho.re = 1 / 2)

/-- **Boundary-character duality--adjunction law.** The additive mismatch of
the two inner nearby-pole branches is twice horizontal displacement. Prime
clocks exponentiate the same branches, and their canonical seam family is
coherent exactly on the additive equalizer. -/
theorem xiBoundaryCharacterFracture_law :
    XiBoundaryCharacterFractureCertificate where
  additiveFracture :=
    xiNearbyPoleDualityAdjunctionFracture_eq_two_re
  additiveEqualizer :=
    xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
  primeExponentiation :=
    primeCpowDualityAdjunctionFracture_eq_nearbyPoleExponentials
  primeCoherenceEqualizer :=
    fun {rho} hstrip =>
      orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
        (rho := rho) hstrip

/-- A norm-conservative real-linear action cannot have a nonzero positive
real eigenvector with eigenvalue other than one. -/
theorem normConservative_realEigenvector_eigenvalue_eq_one
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →ₗ[ℝ] E) (x : E) (hx : x ≠ 0) (lam : ℝ)
    (hlam : 0 ≤ lam)
    (hconservative : ∀ y : E, ‖S y‖ = ‖y‖)
    (heigen : S x = lam • x) :
    lam = 1 := by
  have hxnorm : 0 < ‖x‖ := norm_pos_iff.mpr hx
  have hnorm := hconservative x
  rw [heigen, norm_smul, Real.norm_eq_abs, abs_of_nonneg hlam] at hnorm
  nlinarith

/-- A nonzero exponential character in a norm-conservative representation
has zero real rate. -/
theorem normConservative_expCharacter_forces_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : E →ₗ[ℝ] E) (x : E) (hx : x ≠ 0) (nu : ℝ)
    (hconservative : ∀ y : E, ‖S y‖ = ‖y‖)
    (heigen : S x = Real.exp nu • x) :
    nu = 0 := by
  have hone : Real.exp nu = 1 :=
    normConservative_realEigenvector_eigenvalue_eq_one
      S x hx (Real.exp nu) (Real.exp_nonneg nu) hconservative heigen
  apply Real.exp_injective
  simpa using hone

/-- **Conservative character-descent law.** If an equivariant map does not
erase an exponential source eigenvector, descent into a norm-conservative
target forces its real character rate to vanish. -/
theorem normConservative_equivariantDescent_forces_zero
    {E F : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (U : E →ₗ[ℝ] E) (V : F →ₗ[ℝ] F) (T : E →ₗ[ℝ] F)
    (x : E) (hx : T x ≠ 0) (nu : ℝ)
    (hsource : U x = Real.exp nu • x)
    (hintertwine : ∀ y : E, V (T y) = T (U y))
    (hconservative : ∀ y : F, ‖V y‖ = ‖y‖) :
    nu = 0 := by
  apply normConservative_expCharacter_forces_zero
    V (T x) hx nu hconservative
  rw [hintertwine, hsource, map_smul]

/-- Critical-line reflection sends the real-ray modular character to its
conjugate inverse, not merely to a reciprocal norm. -/
theorem centeredComplexModularCharacter_reflection_real
    (rho : ℂ) (t : ℝ) :
    centeredComplexModularCharacter
        (criticalLineReflectionPoint rho) (t : ℂ) =
      (starRingEnd ℂ
        (centeredComplexModularCharacter rho (t : ℂ)))⁻¹ := by
  rw [centeredComplexModularCharacter, centeredComplexModularCharacter]
  rw [← Complex.exp_conj, ← Complex.exp_neg]
  congr 1
  apply Complex.ext
  all_goals
    simp [criticalLineReflectionPoint, mul_re, mul_im] <;> ring

/-- At any nonzero real time, unitarity of the centered modular character is
exactly the critical-line equalizer. -/
theorem norm_centeredComplexModularCharacter_eq_one_iff
    (rho : ℂ) {t : ℝ} (ht : t ≠ 0) :
    ‖centeredComplexModularCharacter rho (t : ℂ)‖ = 1 ↔
      rho.re = 1 / 2 := by
  rw [norm_centeredComplexModularCharacter_ofReal, ← Real.exp_zero,
    Real.exp_eq_exp]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with htzero | hweight
    · exact absurd htzero ht
    · linarith
  · intro h
    rw [h]
    ring

/-! ## Reflected-character conservative geometry -/

/-- The real two-channel action carried by a reflected pair of centered
characters with rates `q` and `-q`. -/
def reflectedRealCharacterAction
    (q t : ℝ) (v : ℝ × ℝ) : ℝ × ℝ :=
  (Real.exp (q * t) * v.1, Real.exp (-(q * t)) * v.2)

/-- A general real symmetric quadratic form on the reflected character
pair. -/
def reflectedRealCharacterQuadraticForm
    (a b c : ℝ) (v : ℝ × ℝ) : ℝ :=
  a * v.1 ^ 2 + 2 * b * v.1 * v.2 + c * v.2 ^ 2

private theorem exp_sq_ne_one_of_ne_zero
    {q : ℝ} (hq : q ≠ 0) :
    Real.exp q ^ 2 ≠ 1 := by
  intro hsq
  have hpos := Real.exp_pos q
  have heq : Real.exp q = 1 := by nlinarith
  exact hq ((Real.exp_eq_one_iff q).mp heq)

/-- **Hyperbolic uniqueness law.** For a nonzero real character rate,
the invariant symmetric quadratic forms are exactly the multiples of the
cross pairing `2xy`. -/
theorem reflectedRealCharacter_invariantQuadratic_iff
    {q a b c : ℝ} (hq : q ≠ 0) :
    (∀ t : ℝ, ∀ v : ℝ × ℝ,
      reflectedRealCharacterQuadraticForm a b c
          (reflectedRealCharacterAction q t v) =
        reflectedRealCharacterQuadraticForm a b c v) ↔
      a = 0 ∧ c = 0 := by
  constructor
  · intro hinv
    have haInv := hinv 1 (1, 0)
    have hcInv := hinv 1 (0, 1)
    have hqa : Real.exp q ^ 2 ≠ 1 :=
      exp_sq_ne_one_of_ne_zero hq
    have hnq : -q ≠ 0 := neg_ne_zero.mpr hq
    have hqc : Real.exp (-q) ^ 2 ≠ 1 :=
      exp_sq_ne_one_of_ne_zero hnq
    have haEq : a * Real.exp q ^ 2 = a := by
      simpa [reflectedRealCharacterAction,
        reflectedRealCharacterQuadraticForm] using haInv
    have hcEq : c * Real.exp (-q) ^ 2 = c := by
      simpa [reflectedRealCharacterAction,
        reflectedRealCharacterQuadraticForm] using hcInv
    have haMul : a * (Real.exp q ^ 2 - 1) = 0 := by
      nlinarith [haEq]
    have hcMul : c * (Real.exp (-q) ^ 2 - 1) = 0 := by
      nlinarith [hcEq]
    refine
      ⟨(mul_eq_zero.mp haMul).resolve_right (sub_ne_zero.mpr hqa), ?_⟩
    exact
      (mul_eq_zero.mp hcMul).resolve_right (sub_ne_zero.mpr hqc)
  · rintro ⟨rfl, rfl⟩ t v
    have hcancel :
        Real.exp (q * t) * Real.exp (-(q * t)) = 1 := by
      rw [← Real.exp_add]
      simp
    have hp :
        (Real.exp (q * t) * v.1) *
            (Real.exp (-(q * t)) * v.2) =
          v.1 * v.2 := by
      calc
        (Real.exp (q * t) * v.1) *
              (Real.exp (-(q * t)) * v.2) =
            (Real.exp (q * t) * Real.exp (-(q * t))) *
              (v.1 * v.2) := by ring
        _ = v.1 * v.2 := by rw [hcancel]; ring
    simp only [reflectedRealCharacterAction,
      reflectedRealCharacterQuadraticForm, zero_mul, zero_add, add_zero]
    simpa only [mul_assoc] using
      congrArg (fun z : ℝ => 2 * b * z) hp

/-- A nonzero reflected character pair has both positive and negative
directions for its canonical invariant cross pairing. -/
theorem reflectedRealCharacter_hyperbolic_witness :
    0 < reflectedRealCharacterQuadraticForm 0 1 0 (1, 1) ∧
      reflectedRealCharacterQuadraticForm 0 1 0 (1, -1) < 0 := by
  norm_num [reflectedRealCharacterQuadraticForm]

/-- **Positive conservative metric no-go.** A nonzero reflected real
character has no nonzero positive-semidefinite invariant quadratic form.
Exact conservation exists only in the hyperbolic cross pairing. -/
theorem reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic
    {q a b c : ℝ} (hq : q ≠ 0)
    (hinv : ∀ t : ℝ, ∀ v : ℝ × ℝ,
      reflectedRealCharacterQuadraticForm a b c
          (reflectedRealCharacterAction q t v) =
        reflectedRealCharacterQuadraticForm a b c v)
    (hpos : ∀ v : ℝ × ℝ,
      0 ≤ reflectedRealCharacterQuadraticForm a b c v) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have hac :=
    (reflectedRealCharacter_invariantQuadratic_iff hq).mp hinv
  rcases hac with ⟨rfl, rfl⟩
  have hp := hpos (1, 1)
  have hn := hpos (1, -1)
  simp [reflectedRealCharacterQuadraticForm] at hp hn
  exact ⟨rfl, by linarith, rfl⟩

/-- The reflected-character geometry, its exact finite-packet charge
conversion, its sharp positive-completion tax, and its nonlocal
prime--Gamma tomography form one completion law. -/
structure XiReflectionCharacterCompletionCertificate : Prop where
  invariantQuadraticClassification :
    ∀ {q a b c : ℝ}, q ≠ 0 →
      ((∀ t : ℝ, ∀ v : ℝ × ℝ,
        reflectedRealCharacterQuadraticForm a b c
            (reflectedRealCharacterAction q t v) =
          reflectedRealCharacterQuadraticForm a b c v) ↔
        a = 0 ∧ c = 0)
  noPositiveConservativeMetric :
    ∀ {q a b c : ℝ}, q ≠ 0 →
      (∀ t : ℝ, ∀ v : ℝ × ℝ,
        reflectedRealCharacterQuadraticForm a b c
            (reflectedRealCharacterAction q t v) =
          reflectedRealCharacterQuadraticForm a b c v) →
      (∀ v : ℝ × ℝ,
        0 ≤ reflectedRealCharacterQuadraticForm a b c v) →
      a = 0 ∧ b = 0 ∧ c = 0
  finitePacketChargeConversion :
    ∀ n : ℕ,
      finiteQuartetPoleExcess (Fin n) =
          finiteQuartetWeilBlockIndex (Fin n) ∧
      finiteQuartetWardCharge (Fin n) =
        (4 * Real.pi) * finiteQuartetWeilBlockIndex (Fin n)
  sharpScalarCompletionTax :
    ∀ (a b c n : ℝ), 0 < a →
      ((∀ x y : ℝ,
          0 ≤ suzukiTwoChannelKreinCompletionForm a b c n x y) ↔
        n + b ^ 2 / a ≤ c)
  sourceHorizonResolution :
    SourceHorizonEscapeConservationCertificate
  fixedWidthGlobalTomography :
    ∀ {L : ℝ}, 0 < L → ∀ {N : ℕ},
      (∀ n : ℕ, N ≤ n →
        1 ≤ n ∧ L ≤ Real.log n / 2) →
      (RiemannHypothesis ↔
        ∀ s : ℂ, 1 < s.re →
          AnalyticAt ℂ
            (xiRectangularPrimeGammaTailContinuation L N) s)

/-- **Reflected-character completion law.** Off-axis reflected characters
are exactly conservative in a hyperbolic plane, never in a nonzero positive
metric. Their finite packet charge is simultaneously Euler pole excess,
Weil negative index, and Ward charge divided by `4π`; positive Krein
completion pays the exact Schur tax; inverse-drift source time and a
nonlocal fixed-width prime--Gamma tail provide the two faithful positive
resolutions. -/
theorem xiReflectionCharacterCompletion_law :
    XiReflectionCharacterCompletionCertificate where
  invariantQuadraticClassification :=
    fun hq => reflectedRealCharacter_invariantQuadratic_iff hq
  noPositiveConservativeMetric :=
    fun hq hinv hpos =>
      reflectedRealCharacter_no_nonzero_positiveInvariantQuadratic
        hq hinv hpos
  finitePacketChargeConversion :=
    fun n => finiteQuartet_eulerWardWeil_index_law (Fin n)
  sharpScalarCompletionTax :=
    fun _ _ _ _ ha =>
      suzukiTwoChannelKreinCompletionForm_nonneg_iff_schurDebt ha
  sourceHorizonResolution :=
    sourceHorizonEscapeConservation_law
  fixedWidthGlobalTomography :=
    fun {_L} hL {_N} hN =>
      riemannHypothesis_iff_primeGammaTailContinuation_analytic_rightOne
        hL hN

/-- The canonical positive Xi--Hurwitz energy is exactly the quadratic
compression of the continuous divisor characters: it vanishes precisely
when every actual divisor character is unitary on the real unit step. -/
theorem xiHurwitzOrientationEnergy_eq_zero_iff_unitaryCenteredCharacters :
    xiHurwitzOrientationEnergy = 0 ↔
      ∀ rho : XiDivisorSupport,
        ‖centeredComplexModularCharacter (rho : ℂ) (1 : ℂ)‖ = 1 := by
  constructor
  · intro henergy rho
    have hterm :
        xiHurwitzOrientationEnergyTerm rho = 0 :=
      xiHurwitzOrientationEnergy_eq_zero_iff_terms.mp henergy rho
    have hdefect :
        xiHurwitzOrientationDefect rho = 0 :=
      (xiHurwitzOrientationEnergyTerm_eq_zero_iff rho).mp hterm
    have hre :
        (rho : ℂ).re = 1 / 2 :=
      (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half rho).mp hdefect
    exact
      (norm_centeredComplexModularCharacter_eq_one_iff
        (rho : ℂ) (t := 1) one_ne_zero).2 hre
  · intro hunitary
    apply xiHurwitzOrientationEnergy_eq_zero_iff_terms.mpr
    intro rho
    apply (xiHurwitzOrientationEnergyTerm_eq_zero_iff rho).mpr
    apply (xiHurwitzOrientationDefect_eq_zero_iff_re_eq_half rho).mpr
    exact
      (norm_centeredComplexModularCharacter_eq_one_iff
        (rho : ℂ) (t := 1) one_ne_zero).1 (hunitary rho)

/-- **Odd source-orientation transgression.** The pointed Fisher--Ward
scalar is odd in the unsquared source tangent, and for an orthogonal cutoff
it is exactly the trace pairing of that tangent connection with double
cutoff curvature. -/
theorem pointedFisherWard_orientationTransgression
    {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (e T : H →L[ℂ] H) (psi chi : H)
    (he : ContinuousLinearMap.adjoint e = e) :
    HTGeometry.pointedCutoffWardTrace e T psi (-chi) =
        -HTGeometry.pointedCutoffWardTrace e T psi chi ∧
      HTGeometry.pointedCutoffWardTrace e T psi chi =
        ContinuousLinearMap.opTrace
          (HTGeometry.pointedFisherConnection psi chi *
            HTGeometry.cutoffWardCurvature e T) := by
  exact ⟨
    HTGeometry.pointedCutoffWardTrace_neg_tangent e T psi chi,
    HTGeometry.pointedCutoffWardTrace_eq_opTrace_curvature
      e T psi chi he⟩

/-- The completed-Xi square retains the complete logarithmic-current
differential field, while the source-selected Cayley coordinate retains the
odd reflection lift and vanishes on the divisor. -/
structure XiDifferentialParityResolvedCertificate : Prop where
  squareHypertranscendental :
    HypertranscendentalOver upperEndRationalCoordinateField
      (xiRotatedUpperEndCarrier ^ 2)
  squareRetainsLogCurrent :
    differentialAdjoin upperEndRationalCoordinateField
        ({Differential.logDeriv (xiRotatedUpperEndCarrier ^ 2)} :
          Set upperEndMeroField) =
      differentialAdjoin upperEndRationalCoordinateField
        ({Differential.logDeriv xiRotatedUpperEndCarrier} :
          Set upperEndMeroField)
  oddCoordinateSharp :
    ∀ {z : ℂ}, |z.im| < 1 →
      (starRingEnd ℂ)
          (thetaCuspTailSecondDensityReflectionOddCoordinate
            ((starRingEnd ℂ) z)) =
        -thetaCuspTailSecondDensityReflectionOddCoordinate z
  oddCoordinateVanishesOnDivisor :
    ∀ {z : ℂ}, 0 < z.im → z.im < 1 → XiC z = 0 →
      thetaCuspTailSecondDensityReflectionOddCoordinate z = 0

/-- **Even-current/odd-orientation splitting.** Squaring retains the
hypertranscendental logarithmic current, but reflection orientation lives in
the odd Cayley lift. -/
theorem xiDifferentialParityResolved_law :
    XiDifferentialParityResolvedCertificate where
  squareHypertranscendental :=
    xiRotatedUpperEndCarrier_sq_hypertranscendentalOver
  squareRetainsLogCurrent :=
    differentialAdjoin_logDeriv_xiRotatedUpperEndCarrier_sq_eq
  oddCoordinateSharp :=
    fun hz => thetaCuspTailSecondDensityReflectionOddCoordinate_sharp hz
  oddCoordinateVanishesOnDivisor :=
    fun hz hz1 hXi =>
      thetaCuspTailSecondDensityReflectionOddCoordinate_eq_zero_at_XiC_zero
        hz hz1 hXi

/-- Exact continuous and ramified character data attached to one Xi divisor
point. The complex character retains the centered point, while the dyadic
deck tower retains the two-adic divisibility profile of its multiplicity. -/
structure XiRamifiedDivisorCharacterCertificate (rho : ℂ) : Prop where
  additiveCharacter :
    ∀ z w : ℂ,
      centeredComplexModularCharacter rho (z + w) =
        centeredComplexModularCharacter rho z *
          centeredComplexModularCharacter rho w
  realRayNorm :
    ∀ t : ℝ,
      ‖centeredComplexModularCharacter rho (t : ℂ)‖ =
        Real.exp (t * (rho.re - 1 / 2))
  reflectedConjugateInverse :
    ∀ t : ℝ,
      centeredComplexModularCharacter
          (criticalLineReflectionPoint rho) (t : ℂ) =
        (starRingEnd ℂ
          (centeredComplexModularCharacter rho (t : ℂ)))⁻¹
  unitaryEqualizer :
    ∀ {t : ℝ}, t ≠ 0 →
      (‖centeredComplexModularCharacter rho (t : ℂ)‖ = 1 ↔
        rho.re = 1 / 2)
  dyadicRootOfUnity :
    ∀ k : ℕ, xiDeckCharge k rho ^ (2 ^ k) = 1
  dyadicTrivialityReadsMultiplicity :
    ∀ k : ℕ,
      xiDeckCharge k rho = 1 ↔
        2 ^ k ∣ (analyticOrderAt xi rho).toNat
  innerOuterInfinitesimalCharge :
    let m := (analyticOrderAt xi rho).toNat
    Tendsto
        (fun w : ℂ =>
          w⁻¹ *
            (depthSuccessorNearbyCycle (rho - 1 / 2) m w⁻¹ - 1))
        (𝓝[≠] 0)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ)))) ∧
      Tendsto
        (fun s : ℂ =>
          (s - rho) * xiExceptionalAffineDivisorCurrent s)
        (𝓝[≠] rho)
        (𝓝 (-((rho - 1 / 2) * (m : ℂ))))

/-- **Ramified divisor-character law.** Every Xi divisor point carries one
complex reflection character and one coherent dyadic ramification tower.
Their common infinitesimal coupling is the multiplicity-weighted centered
residue of the source-generated Xi connection. -/
theorem xiRamifiedDivisorCharacter_law (rho : ℂ) :
    XiRamifiedDivisorCharacterCertificate rho where
  additiveCharacter :=
    centeredComplexModularCharacter_add rho
  realRayNorm :=
    norm_centeredComplexModularCharacter_ofReal rho
  reflectedConjugateInverse :=
    centeredComplexModularCharacter_reflection_real rho
  unitaryEqualizer :=
    norm_centeredComplexModularCharacter_eq_one_iff rho
  dyadicRootOfUnity :=
    fun k => xiDeckCharge_pow k rho
  dyadicTrivialityReadsMultiplicity :=
    fun k => xiDeckCharge_eq_one_iff_toNat_dvd k rho
  innerOuterInfinitesimalCharge :=
    xiDepthNearby_outerCharge_and_affineResidue_match rho

/-- Global neutrality of the inner duality--adjunction boundary character. -/
def XiBoundaryCharacterNeutral : Prop :=
  ∀ rho : XiDivisorSupport,
    xiNearbyPoleDualityAdjunctionFracture (rho : ℂ) = 0

/-- Global independent-quadrant regularity of the Wold-depth/Poisson-time
character carried by every Xi divisor fibre. -/
def XiWoldPoissonQuadrantRegular : Prop :=
  ∀ rho : XiDivisorSupport,
    ConjugateTwoClockQuadrantBounded
      (sourceCayleyTransverseRate 1 (rho : ℂ))

/-- The Wold--Poisson rate is the real form of the same inner boundary
fracture. Hence independent-quadrant boundedness is exactly its equalizer. -/
theorem conjugateTwoClockQuadrantBounded_xiSourceRate_iff_boundaryFracture_zero
    (rho : ℂ) :
    ConjugateTwoClockQuadrantBounded
        (sourceCayleyTransverseRate 1 rho) ↔
      xiNearbyPoleDualityAdjunctionFracture rho = 0 := by
  rw [conjugateTwoClockQuadrantBounded_iff,
    sourceCayleyTransverseRate_eq_zero_iff,
    xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff]
  norm_num

/-- Global Wold--Poisson independent-quadrant regularity is exactly global
boundary-character neutrality. -/
theorem xiBoundaryCharacterNeutral_iff_woldPoissonQuadrantRegular :
    XiBoundaryCharacterNeutral ↔ XiWoldPoissonQuadrantRegular := by
  constructor
  · intro hneutral rho
    exact
      (conjugateTwoClockQuadrantBounded_xiSourceRate_iff_boundaryFracture_zero
        (rho : ℂ)).2 (hneutral rho)
  · intro hregular rho
    exact
      (conjugateTwoClockQuadrantBounded_xiSourceRate_iff_boundaryFracture_zero
        (rho : ℂ)).1 (hregular rho)

/-- Boundary-character neutrality is the divisor-level form of RH. -/
theorem xiBoundaryCharacterNeutral_iff_riemannHypothesis :
    XiBoundaryCharacterNeutral ↔ RiemannHypothesis := by
  rw [← xiPrimeSeamChargesCoherent_iff_riemannHypothesis]
  constructor
  · intro hneutral rho
    apply (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).2
    exact
      (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
        (rho : ℂ)).1 (hneutral rho)
  · intro hcoherent rho
    apply (xiNearbyPoleDualityAdjunctionFracture_eq_zero_iff
      (rho : ℂ)).2
    exact (orbitwisePrimeSeamChargesCoherent_iff_re_eq_half
      (xi_divisor_support_re_mem_open_unit rho)).1 (hcoherent rho)

/-- The global boundary equalizer is simultaneously the Wold--Poisson,
Sonin--Calkin, and fixed-edge Ward regularity phase. -/
theorem xiBoundaryCharacterNeutral_iff_regularBoundaryConsumers :
    XiBoundaryCharacterNeutral ↔
      XiWoldPoissonQuadrantRegular ∧
      XiPrimeSeamAllScaleCalkinCertificate ∧
      ContinuedXiWardEulerEdgeBoundaryGramLaw := by
  constructor
  · intro hneutral
    have hRH :=
      xiBoundaryCharacterNeutral_iff_riemannHypothesis.mp hneutral
    exact ⟨
      xiBoundaryCharacterNeutral_iff_woldPoissonQuadrantRegular.mp hneutral,
      xiPrimeSeamAllScaleCalkinCertificate_iff_riemannHypothesis.mpr hRH,
      continuedXiWardEulerEdgeBoundaryGramLaw_of_riemannHypothesis hRH⟩
  · rintro ⟨hwold, _hcalkin, _hward⟩
    exact xiBoundaryCharacterNeutral_iff_woldPoissonQuadrantRegular.mpr hwold

/-- One strict-right upper Xi divisor fibre makes every regular horizontal
consumer fail: its two-clock character is quadrant-unbounded, its prime-seam
Calkin phase is noncompact, and its adapted Ward boundary Gram is not
positive. -/
structure XiRightUpperHorizontalFailureCertificate
    (q : XiRightUpperZeroCopy) : Prop where
  sourceRatePositive :
    0 < sourceCayleyTransverseRate 1 (q.1.1.1 : ℂ)
  woldPoissonNotQuadrantRegular :
    ¬ ConjugateTwoClockQuadrantBounded
      (sourceCayleyTransverseRate 1 (q.1.1.1 : ℂ))
  primeSeamNotCoherent :
    ¬ OrbitwisePrimeSeamChargesCoherent (q.1.1.1 : ℂ)
  soninCalkinNotCompact :
    ∀ a : ℝ, 0 < a →
      ¬ OrbitwisePrimeSeamCalkinGramCompact a (q.1.1.1 : ℂ)
  wardFourUnitViolation :
    4 <
      Complex.normSq
        (continuedXiAntiCausalWardResponse
          (xiWardEulerEdgeAdaptedNode q))
  wardBoundaryGramNotPositive :
    ¬ (continuedXiWardFourUnitBoundaryGram
      (fun _ : Fin 1 => xiWardEulerEdgeAdaptedNode q)).PosSemidef

/-- **Strict-right horizontal failure law.** All regular consumer failures
are forced by one positive boundary-character rate on the same divisor
fibre. -/
theorem xiRightUpperHorizontalFailure_law
    (q : XiRightUpperZeroCopy) :
    XiRightUpperHorizontalFailureCertificate q := by
  have hrate :
      0 < sourceCayleyTransverseRate 1 (q.1.1.1 : ℂ) := by
    have hpos := xiRightSourceModularCharge_pos q.1
    rw [xiRightSourceModularCharge] at hpos
    rw [sourceCayleyTransverseRate]
    simp only [Complex.sub_re, Complex.one_re]
    linarith
  exact {
    sourceRatePositive := hrate
    woldPoissonNotQuadrantRegular := by
      intro hbounded
      have hzero :=
        (conjugateTwoClockQuadrantBounded_iff
          (sourceCayleyTransverseRate 1 (q.1.1.1 : ℂ))).mp hbounded
      linarith
    primeSeamNotCoherent :=
      xiRightPrimeSeamCharges_not_coherent q.1
    soninCalkinNotCompact := by
      intro a ha hcompact
      have hre :=
        (orbitwisePrimeSeamCalkinGramCompact_iff_re_eq_half
          a (q.1.1.1 : ℂ) ha
          (xi_divisor_support_re_mem_open_unit q.1.1.1)).mp hcompact
      have hpos := xiRightSourceModularCharge_pos q.1
      rw [xiRightSourceModularCharge] at hpos
      linarith
    wardFourUnitViolation :=
      normSq_continuedXiAntiCausalWardResponse_at_eulerEdge_gt_four q
    wardBoundaryGramNotPositive :=
      continuedXiWardFourUnitBoundaryGram_eulerEdge_adapted_not_posSemidef q
  }

/-- Exact two-axis certificate for the Riemann boundary. Vertically, every
nonzero positive theta-null divisor detector is singular through ordinary
`L²`; horizontally, regular Wold--Poisson, Sonin--Calkin, and Ward descent is
exactly the boundary-character equalizer. -/
structure XiSingularEqualizerBoundaryCertificate : Prop where
  verticalThetaClosureClassification :
    ∀ (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm),
      Q.MomentumSymmetric →
      Q.IsNonnegative →
      Q xiThetaSchwartzSource xiThetaSchwartzSource = 0 →
      (Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2 ↔
        ∀ u v : SchwartzMap ℝ ℂ, Q u v = 0)
  verticalThetaDenseRadical :
    ∀ (Q : SchwartzMap.ContinuousSchwartzSesquilinearForm),
      Q.MomentumSymmetric →
      Q.IsNonnegative →
      Q xiThetaSchwartzSource xiThetaSchwartzSource = 0 →
      (∃ u v : SchwartzMap ℝ ℂ, Q u v ≠ 0) →
      Dense (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
        ¬ IsClosed (xiThetaL2RadicalImage Q : Set XiThetaL2) ∧
        ¬ Q.IsSequentiallyClosableThrough xiThetaSchwartzToL2
  horizontalRegularityEqualizer :
    XiBoundaryCharacterNeutral ↔
      XiWoldPoissonQuadrantRegular ∧
      XiPrimeSeamAllScaleCalkinCertificate ∧
      ContinuedXiWardEulerEdgeBoundaryGramLaw

/-- **Singular-equalizer boundary law.** Divisor detection and orientation
selection occupy different completion axes: the former forces a singular
vertical rigging even at the neutral boundary, while every regular
horizontal consumer factors through the same character equalizer. -/
theorem xiSingularEqualizerBoundary_law :
    XiSingularEqualizerBoundaryCertificate where
  verticalThetaClosureClassification :=
    universalPositiveForm_thetaNull_sequentiallyL2Closable_iff_zero
  verticalThetaDenseRadical := by
    intro Q hQ hQnonneg hnull hNonzero
    have h :=
      universalPositiveForm_nonzero_thetaNull_temperedDenseRadicalLaw
        Q hQ hQnonneg hnull hNonzero
    exact ⟨h.2.1, h.2.2.1, h.2.2.2.2⟩
  horizontalRegularityEqualizer :=
    xiBoundaryCharacterNeutral_iff_regularBoundaryConsumers

/-- Exact finite-source separation beneath the singular character boundary.
Every finite positive realization of a collision-free Xi source packet is a
representation of the same pointed incidence matroid.  The matroid is
unchanged by adjoining all scalar valuation layers, and the full metric
package collapses to literal nonzero label injectivity.  This source
faithfulness does not imply logarithmic-current faithfulness: one and the same
cofinite evaluation reporter is positive definite on the Xi jet carrier but
has an exact nonzero blind packet for the logarithmic current, even after
isometric encoding. -/
structure XiFiniteSourceObservableSeparationCertificate : Prop where
  pairwiseMatroidValuationInvariant :
    ∀ {V E : Type} [Fintype V] [Fintype E]
        [DecidableEq V] [DecidableEq E]
        (root : V) (shift : V → ℕ) (_hroot : shift root = 0)
        (_hinj : Function.Injective shift) (tail head : E → V),
      differentialFamilyMatroid
          (F := upperEndRationalCoordinateField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head) =
        differentialFamilyMatroid
          (F := analyticScalarValuationLayerDifferentialField)
          (xiTransverseShiftPairDifferenceUpperEndCarrier shift tail head)
  finitePositiveMetricFusion :
    ∀ {d : ℕ} (grade : Fin d → ℕ) (embed : ℕ → ℕ),
      Function.Injective embed → embed 0 = 0 →
      ∀ (p : Nat.Primes) (m : ℕ),
        XiEvenShiftRawLogDerivDefectCofiniteHilbertReconstruction grade ↔
          XiRootedStarIncidenceValuationExactMetricFusionCertificate
            grade embed p m
  carrierCurrentSeparation :
    ∀ N : ℕ,
      ∃ points : Fin N → ℂ,
        Function.Injective points ∧
        (finiteDerivativeReporterGram N xi
          (finiteEvaluationReporter points)).PosDef ∧
        ∃ k : ℕ, k ≤ N ∧
          finiteDerivativeReporterConditionalInformation k (logDeriv xi)
              (finiteEvaluationReporter points) = 0 ∧
          finiteEvaluationReporter points (iteratedDeriv k (logDeriv xi)) ∈
            finiteDerivativeReporterPreviousSpace k (logDeriv xi)
              (finiteEvaluationReporter points) ∧
          iteratedDeriv k (logDeriv xi) ∉ Submodule.span ℂ
            (Set.range fun i : Fin k =>
              iteratedDeriv (i : ℕ) (logDeriv xi))

/-- **Finite positivity / current-separation law.**  Valuation completion and
all finite positive Hilbert realizations preserve only the pointed source
incidence matroid.  Faithfulness of that carrier is strictly weaker than
faithfulness of its logarithmic current. -/
theorem xiFiniteSourceObservableSeparation_law :
    XiFiniteSourceObservableSeparationCertificate where
  pairwiseMatroidValuationInvariant :=
    fun root shift hroot hinj tail head =>
      xiTransverseShiftPairDifferenceUpperEndCarrier_differentialMatroid_base_eq_allValuation
        root shift hroot hinj tail head
  finitePositiveMetricFusion :=
    fun grade embed hinj hzero p m =>
      xiRootedStar_incidenceValuationExactMetricFusion_reparam_iff
        grade embed hinj hzero p m
  carrierCurrentSeparation :=
    exists_injective_xiEvaluationReporter_faithfulXi_blindLogDeriv

/-- Positive Euler orientation is a source-level pointing above, rather than
an invariant of, the projective differential-field quotient.  The complete
signed-prime shift field remembers an orientation only modulo finite changes
and global sign; every such fibre is dense; positive definiteness of the
vertical trace nevertheless singles out the literal all-positive source. -/
structure PrimeProjectiveTailPositivePointingCertificate : Prop where
  projectiveFieldClassification :
    ∀ epsilon delta : Nat.Primes → Bool,
      differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (signedPrimeNaturalShiftPalette epsilon)) =
        differentialAdjoin finitePrimeRationalCoefficientField
          (Set.range (signedPrimeNaturalShiftPalette delta)) ↔
        PrimeOrientationsEventuallyEqual epsilon delta ∨
          PrimeOrientationsEventuallyOpposite epsilon delta
  projectiveTailFibresDense :
    ∀ epsilon : ℕ → Bool,
      Dense
        (booleanProjectiveTailClass ⁻¹'
          {booleanProjectiveTailClass epsilon})
  uniquePositiveSourcePointing :
    ∀ (epsilon : Nat.Primes → Bool) {sigma : ℝ}, 1 < sigma →
      (PositiveDefiniteOnReal (signedPrimeVerticalTrace epsilon sigma) ↔
        PrimeOrientationAllPositive epsilon)

/-- **Projective-tail positive-pointing law.** Differential-field type loses
global source sign and has dense nonseparated fibres, whereas positivity
selects one literal Euler representative and therefore cannot descend to that
field quotient. -/
theorem primeProjectiveTailPositivePointing_law :
    PrimeProjectiveTailPositivePointingCertificate where
  projectiveFieldClassification :=
    signedPrimeNaturalShiftPalette_differentialAdjoin_eq_iff
  projectiveTailFibresDense :=
    booleanProjectiveTailClass_fiber_dense
  uniquePositiveSourcePointing :=
    signedPrimeVerticalTrace_positiveDefinite_iff_allPositive

/-- Positive information occurs at strictly different observable levels.
The critical clock is blind to a prescribed off-line divisor, finite source
Grams see the collision matroid, an off-line atom separates diagonal Hilbert
response from transverse charge, and the full resolvent Weil form detects the
off-axis divisor.  The endpoint source still gives a sharp unconditional
cubic budget for the total transverse defect. -/
structure XiPositiveObservableHierarchyCertificate : Prop where
  criticalClockDivisorBlindness :
    ∀ {theta a : ℝ}, 1 / 2 < theta → theta < 1 → 0 < a →
      ∃ m L : ℝ, 0 < m ∧ 0 < L ∧
        (∀ sigma : ℝ, 1 < sigma →
          blindWitnessMellinReal m L sigma =
            ∫ x, x ^ (-sigma) ∂(blindWitnessMeasure m L)) ∧
        Tendsto
          (fun sigma : ℝ =>
            (sigma - 1) * blindWitnessMellinReal m L sigma)
          (𝓝[>] 1) (𝓝 1) ∧
        (∀ u : ℝ, 0 ≤ u →
          Tendsto
            (criticalClockLaplace (blindWitnessMellinReal m L) u)
            (𝓝[>] 1) (𝓝 (1 / (1 + u)))) ∧
        blindWitnessMellin m L ((theta : ℂ) + (a : ℂ) * I) = 0 ∧
        blindWitnessMellin m L ((theta : ℂ) - (a : ℂ) * I) = 0 ∧
        8 < schwarzPairCauchyEnergy
          ((theta - 1 / 2 : ℝ) + (a : ℝ) * I)
  unconditionalCubicDefectBudget :
    0 ≤ xiThermalOrientationEnergy ∧
      xiThermalOrientationEnergy ≤
        xiThermalOffLineChargeCubicBudget ∧
      xiThermalOffLineChargeCubicBudget ≤
        xiThermalExactCubicEndpointBudget ∧
      xiThermalExactCubicEndpointBudget < 1 / 150000
  cubicBudgetExactZeroLocus :
    [xiEndpointOffLineCharge = 0,
      xiThermalOffLineChargeCubicBudget = 0,
      xiThermalOrientationEnergy = 0,
      RiemannHypothesis].TFAE
  offLineAtomDiagonalSeparation :
    ∀ (q : XiZeroCopy), (q.1 : ℂ).re ≠ 1 / 2 →
      ∃ p : Polynomial ℝ,
        p.natDegree ≤ 1 ∧
        xiSquaredEulerApertureHilbertTerm p q = 0 ∧
        0 < xiSquaredEulerApertureTransverseTerm p q
  orbitwiseDiagonalControlExactBoundary :
    XiSquaredEulerApertureOrbitwiseBoundedCharge ↔
      RiemannHypothesis
  mixedReflectionConePositive :
    ∀ u : ℝ, 0 ≤ coneObstruction u
  mixedReflectionConeNotSumOfSquares :
    ∀ {n : ℕ} (q : Fin n → ℝ → ℝ → ℂ),
      (∀ s phi, cylinderLift s phi =
        ∑ k, ‖q k s phi‖ ^ 2) → False
  sourceMajorantDiverges :
    ∀ {h : ℝ}, 1 / 2 < h →
      Tendsto
        (fun t : ℝ =>
          xiWardInteriorSourceArithmeticBound
            ((h : ℂ) + I * (t : ℂ)))
        atTop atTop
  rankOneGlobalWeilDetection :
    ∀ {pt : ℂ}, XiC pt = 0 → pt.im ≠ 0 → pt ≠ 0 →
      ∃ z : ℂ,
        XiC z ≠ 0 ∧ XiC ((starRingEnd ℂ) z) ≠ 0 ∧
        z ≠ 0 ∧ z.im ≠ 0 ∧
        (xiWeilPolarization (xiCauchyRegularizedKernel z)
          (xiCauchyRegularizedKernel z)).re < 0

/-- **Positive-observable hierarchy law.**  Source-clock positivity, finite
source-Gram positivity, atomwise diagonal response, mixed reflection-cone
positivity, and global resolvent positivity are not interchangeable
certificates.  The exact failure witnesses and the unconditional cubic defect
budget coexist in one theorem. -/
theorem xiPositiveObservableHierarchy_law :
    XiPositiveObservableHierarchyCertificate where
  criticalClockDivisorBlindness :=
    ccm_criticalClock_divisor_blindness
  unconditionalCubicDefectBudget :=
    ⟨xiThermalOrientationEnergy_nonneg,
      xiThermalOrientationEnergy_le_offLineChargeCubicBudget,
      xiThermalOffLineChargeCubicBudget_le_exactCubicEndpointBudget,
      xiThermalExactCubicEndpointBudget_lt_one_over_oneHundredFiftyThousand⟩
  cubicBudgetExactZeroLocus :=
    xiThermal_offLineCharge_budget_energy_zero_tfae
  offLineAtomDiagonalSeparation :=
    exists_xiSquaredEulerAperture_atom_charge_without_hilbert
  orbitwiseDiagonalControlExactBoundary :=
    xiSquaredEulerApertureOrbitwiseBoundedCharge_iff_riemannHypothesis
  mixedReflectionConePositive :=
    coneObstruction_nonneg
  mixedReflectionConeNotSumOfSquares :=
    cylinderLift_not_sum_of_squares
  sourceMajorantDiverges :=
    xiWardInteriorSourceArithmeticBound_vertical_tendsto_atTop
  rankOneGlobalWeilDetection :=
    exists_neg_weilDiagonal_of_offAxis_zero

/-- Complete boundary architecture after restoring the independent source
bigrading and the divisor's ramification coordinate. -/
structure XiRamifiedSingularBoundaryCertificate : Prop where
  singularEqualizer :
    XiSingularEqualizerBoundaryCertificate
  noFaithfulAdditiveSourceScalarization :
    ∀ w : (ℕ × ℕ) →+ ℕ, ¬ Function.Injective w
  pairedSourceScalarizationFaithful :
    Function.Injective transverseScalarDegrees
  noEntireHeatNodeDeltaReader :
    ∀ (F : ℂ → ℂ), Differentiable ℂ F →
      ∀ {n : ℕ}, 1 ≤ n →
        F (thetaHeatNode n) = 1 →
        (∀ m : ℕ, 1 ≤ m → m ≠ n →
          F (thetaHeatNode m) = 0) →
        False
  arithmeticJuliaOrientedAcquisition :
    ArithmeticJuliaHardySingularCompletion ∧
      ArithmeticJuliaCellwiseMinimality ∧
      ArithmeticJuliaMellinKolchinCompletion
  differentialParityResolution :
    XiDifferentialParityResolvedCertificate
  noFiniteLocalOrientationFrame :
    ∀ {a : ℝ}, 0 < a → ¬ XiFiniteLocalPolynomialSpectralFrame a
  ramifiedDivisorCharacter :
    ∀ rho : ℂ, XiRamifiedDivisorCharacterCertificate rho
  quadraticCharacterCompression :
    0 ≤ xiHurwitzOrientationEnergy ∧
      (xiHurwitzOrientationEnergy = 0 ↔
        ∀ rho : XiDivisorSupport,
          ‖centeredComplexModularCharacter (rho : ℂ) (1 : ℂ)‖ = 1)
  reflectionCharacterCompletion :
    XiReflectionCharacterCompletionCertificate
  finiteSourceObservableSeparation :
    XiFiniteSourceObservableSeparationCertificate
  sourceProjectiveTailPositivePointing :
    PrimeProjectiveTailPositivePointingCertificate
  positiveObservableHierarchy :
    XiPositiveObservableHierarchyCertificate
  ramificationMultiplicityTomography :
    ∀ rho : XiDivisorSupport,
      xiCompletedApertureRegularizedResonantTwoPointDet rho 0 = -4 ↔
        XiLocalJordanNormal rho ∧
        localDivisorJetInfinitesimalUnit ℂ
            (xiSupportMultiplicity rho) = 1 ∧
        localDivisorJetLogUnit (xiSupportMultiplicity rho) = 0
  dyadicLevelwiseDescent :
    ∀ k : ℕ,
      RHLadder k ↔ XiDyadicDescentLevelUniversalCertificate k
  allDyadicLevels :
    RiemannHypothesis ↔
      ∀ k : ℕ, XiDyadicDescentLevelUniversalCertificate k
  persistentOddDefectLoops :
    ∀ rho : ℂ,
      XiDefect rho ↔
        rho.re ∈ Set.Ioo (1 / 2 : ℝ) 1 ∧
        xi rho = 0 ∧
        PersistentXiDefectLoop rho ∧
        Odd (analyticOrderAt xi rho).toNat
  fullApertureSpectrum :
    ∀ {tau L : ℝ}, 0 < tau → 0 < L →
      ∀ {N : ℕ},
        (∀ n : ℕ, N ≤ n →
          1 ≤ n ∧ L ≤ Real.log n / 2) →
        XiSpectralApertureSpectrum tau L N =
          Set.Ici xiProjectiveReflectionRadius
  massTraceDistortion :
    ∀ {a lam : ℝ}, (ha : 1 / 2 ≤ a) → 0 ≤ lam →
      ((∀ q : XiZeroCopy,
          |(xiSpectralPoint q).im| ≤ lam) →
        xiMassTraceLineGrowth (a := a) ha lam) ∧
      (xiMassTraceLineGrowth (a := a) ha lam →
        ∀ q : XiZeroCopy,
          9 * (xiSpectralPoint q).im ^ 2 ≤
            (9 + a ^ 2) * lam ^ 2)

/-- **Bifiltered ramified-character boundary law.** The Riemann source
cannot be faithfully reduced to one additive grading or one analytic
heat-node reader. Its exact divisor output is the ramified character pair:
the continuous modular character controls horizontal aperture and
conservative descent, while the deck-character tower controls multiplicity
divisibility and local root descent. -/
theorem xiRamifiedSingularBoundary_law :
    XiRamifiedSingularBoundaryCertificate where
  singularEqualizer :=
    xiSingularEqualizerBoundary_law
  noFaithfulAdditiveSourceScalarization :=
    natProd_addMonoidHom_not_injective
  pairedSourceScalarizationFaithful :=
    transverseScalarDegrees_injective
  noEntireHeatNodeDeltaReader :=
    fun F hF {_n} hn hself hother =>
      no_entire_thetaHeatNode_delta F hF hn hself hother
  arithmeticJuliaOrientedAcquisition :=
    ⟨arithmeticJuliaNormalConeUniversality.1,
      arithmeticJuliaNormalConeUniversality.2.1,
      arithmeticJuliaNormalConeUniversality.2.2.1⟩
  differentialParityResolution :=
    xiDifferentialParityResolved_law
  noFiniteLocalOrientationFrame :=
    fun ha => not_XiFiniteLocalPolynomialSpectralFrame_of_pos ha
  ramifiedDivisorCharacter :=
    xiRamifiedDivisorCharacter_law
  quadraticCharacterCompression :=
    ⟨xiHurwitzOrientationEnergy_nonneg,
      xiHurwitzOrientationEnergy_eq_zero_iff_unitaryCenteredCharacters⟩
  reflectionCharacterCompletion :=
    xiReflectionCharacterCompletion_law
  finiteSourceObservableSeparation :=
    xiFiniteSourceObservableSeparation_law
  sourceProjectiveTailPositivePointing :=
    primeProjectiveTailPositivePointing_law
  positiveObservableHierarchy :=
    xiPositiveObservableHierarchy_law
  ramificationMultiplicityTomography :=
    xiCompletedApertureCollision_neg_four_iff_completeLocalSimplicity
  dyadicLevelwiseDescent :=
    rhLadder_iff_dyadicDescentLevelUniversalCertificate
  allDyadicLevels :=
    riemannHypothesis_iff_forall_dyadicDescentLevelUniversalCertificate
  persistentOddDefectLoops :=
    xiDefect_persistentLoop_openStrip_oddOrderUniversality
  fullApertureSpectrum := by
    intro tau L htau hL N hN
    exact
      xiSpectralApertureSpectrum_eq_Ici_projectiveReflectionRadius
        htau hL hN
  massTraceDistortion := by
    intro a lam ha hlam
    exact xiMass_gradedTrace_zeroFreeDistortionUniversality ha hlam

/-- Critical activation certificate showing why its divisor transport cannot
be compressed into a finite recurrence or bounded positive Gram completion. -/
structure CriticalActivationSingularResolutionCertificate : Prop where
  occupancyNotSummable :
    ¬ Summable criticalActivationOccupancyMass
  fixedHigherDepthSummable :
    ∀ {m : ℕ}, 2 ≤ m →
      Summable (criticalActivationValuationTailMass m)
  gammaFibreNotSummable :
    ¬ Summable criticalActivationGammaFibreMass
  reciprocalPrimeNodesHaveNoFiniteRecurrence :
    ∀ (S : Set Nat.Primes), S.Infinite →
      ∀ Q : Polynomial ℝ,
        (∀ p ∈ S,
          Polynomial.eval
            (xiTransversePrimeApertureDiskNode 1 p) Q = 0) →
        Q = 0
  divisorDifferentiationDropsOneGrade :
    ∀ {d : ℕ}, 0 < d → ∀ {t : ℝ}, t ≠ 0 →
      monomialDivisorFisherNumerator d t ^ 2 /
          monomialDivisorOverlap d t ^ 2 =
        (d : ℝ) ^ 2 / t ^ 2
  noBoundedPositiveDivisorCompletion :
    ∀ {d : ℕ}, 0 < d → ∀ M : ℝ,
      ∃ t : ℝ, 0 < t ∧ ∀ C : ℝ, C ≤ M →
        ¬ (divisorReesGram
            (monomialDivisorOverlap d t)
            (monomialDivisorFisherNumerator d t) C).PosSemidef

/-- **Critical activation singular-resolution law.** Radical occupancy and
Fisher-whitened Gamma mass remain prime-harmonic, every fixed higher depth is
summable, reciprocal-prime nodes admit no finite recurrence, and divisor
differentiation forces inverse-square Gram blow-up. -/
theorem criticalActivationSingularResolution_law :
    CriticalActivationSingularResolutionCertificate where
  occupancyNotSummable :=
    not_summable_criticalActivationOccupancyMass
  fixedHigherDepthSummable :=
    summable_criticalActivationValuationTailMass
  gammaFibreNotSummable :=
    not_summable_criticalActivationGammaFibreMass
  reciprocalPrimeNodesHaveNoFiniteRecurrence :=
    polynomial_eq_zero_of_vanishes_on_infinite_prime_nodes
  divisorDifferentiationDropsOneGrade :=
    monomialDivisorFisher_ratio
  noBoundedPositiveDivisorCompletion :=
    no_bounded_positive_divisorReesGram

/-- A finite-Rees-moderate operator cannot sew the reflected valuation
sectors selected by an actual right Xi divisor charge. -/
theorem no_finiteReesOperator_sews_xiRightModularSectors
    (q : XiRightZeroCopy)
    (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : ReesOperatorGradeAtMost atTop
      primeWoldBoundaryVolumeBelow K R) :
    (fun N =>
      R N
        (primeValuationSquaredHellingerBelow
          (xiRightSourceModularCharge q) N)) ≠
      primeValuationSquaredHellingerBelow
        (-xiRightSourceModularCharge q) := by
  exact no_finiteReesOperator_sews_reflected_Hellinger_sectors
    (xiRightSourceModularCharge_pos q)
    (xiRightSourceModularCharge_lt_half q) K R hR

/-- Every exact sewing at an actual right Xi divisor charge has essential
operator norm: it dominates every inverse Wold Rees power. -/
theorem xiRightModularSewingOperatorNorm_beyondEveryReesOrder
    (q : XiRightZeroCopy)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N =>
        R N
          (primeValuationSquaredHellingerBelow
            (xiRightSourceModularCharge q) N)) =
        primeValuationSquaredHellingerBelow
          (-xiRightSourceModularCharge q))
    (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N => ‖R N‖) := by
  exact reflectedHellingerSewingOperatorNorm_beyondEveryReesOrder
    (xiRightSourceModularCharge_pos q)
    (xiRightSourceModularCharge_lt_half q) R hsew K

/-- The unsquared reflected affinities themselves cannot be sewn by a
finite-Rees-moderate operator. -/
theorem no_finiteReesOperator_sews_xiRightModularAffinities
    (q : XiRightZeroCopy)
    (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hR : ReesOperatorGradeAtMost atTop
      primeWoldBoundaryVolumeBelow K R) :
    (fun N =>
      R N
        (primeValuationHellingerBelow
          (xiRightSourceModularCharge q) N)) ≠
      primeValuationHellingerBelow
        (-xiRightSourceModularCharge q) := by
  intro hsew
  have hscale :
      ∀ᶠ N : ℕ in atTop, primeWoldBoundaryVolumeBelow N ≠ 0 :=
    Filter.Eventually.of_forall fun N =>
      (primeWoldBoundaryVolumeBelow_pos N).ne'
  have hflat :
      ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (fun N =>
          R N (primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N)) :=
    reesAllOrdersFlat_apply_reesOperatorGradeAtMost
      atTop primeWoldBoundaryVolumeBelow K R
      (primeValuationHellingerBelow
        (xiRightSourceModularCharge q))
      hscale hR
      (primeValuationHellingerBelow_reesAllOrdersFlat_of_pos
        (xiRightSourceModularCharge_pos q)
        (xiRightSourceModularCharge_lt_half q))
  have hreflectedNonflat :
      ¬ ReesAllOrdersFlat atTop primeWoldBoundaryVolumeBelow
        (primeValuationHellingerBelow
          (-xiRightSourceModularCharge q)) :=
    primeValuationHellingerBelow_not_reesAllOrdersFlat_of_nonpos
      (by linarith [xiRightSourceModularCharge_pos q])
  apply hreflectedNonflat
  simpa only [hsew] using hflat

/-- The scalar sewing cost between the unsquared affinities also dominates
every inverse Wold Rees power. -/
theorem xiRightModularAffinitySewingCost_beyondEveryReesOrder
    (q : XiRightZeroCopy) (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N =>
        primeValuationHellingerBelow
            (-xiRightSourceModularCharge q) N /
          primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N) := by
  have hsq :=
    reflectedHellingerSewingCost_beyondEveryReesOrder
      (xiRightSourceModularCharge_pos q)
      (xiRightSourceModularCharge_lt_half q) (2 * K)
  have hpow :
      (fun N => ((primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) ^ 2) =o[atTop]
        (fun N =>
          (primeValuationHellingerBelow
              (-xiRightSourceModularCharge q) N /
            primeValuationHellingerBelow
              (xiRightSourceModularCharge q) N) ^ 2) := by
    apply hsq.congr'
    · filter_upwards [] with N
      rw [← pow_mul, Nat.mul_comm K 2]
    · filter_upwards [] with N
      rw [div_pow,
        primeValuationHellingerBelow_sq
          (by linarith [xiRightSourceModularCharge_pos q]),
        primeValuationHellingerBelow_sq
          (xiRightSourceModularCharge_lt_half q).le]
  exact hpow.of_pow (by norm_num)

/-- Every exact sewing of the unsquared affinities has essential operator
norm. -/
theorem xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder
    (q : XiRightZeroCopy)
    (R : ℕ → (ℝ →L[ℝ] ℝ))
    (hsew :
      (fun N =>
        R N
          (primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N)) =
        primeValuationHellingerBelow
          (-xiRightSourceModularCharge q))
    (K : ℕ) :
    (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
      (fun N => ‖R N‖) := by
  have hcost :=
    xiRightModularAffinitySewingCost_beyondEveryReesOrder q K
  have hratio :
      (fun N =>
        primeValuationHellingerBelow
            (-xiRightSourceModularCharge q) N /
          primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N) =O[atTop]
        (fun N => ‖R N‖) := by
    apply IsBigO.of_bound 1
    filter_upwards [] with N
    have hfpos :
        0 < primeValuationHellingerBelow
          (xiRightSourceModularCharge q) N := by
      rw [primeValuationHellingerBelow]
      exact Real.sqrt_pos.2
        (primeValuationSquaredHellingerBelow_pos
          (xiRightSourceModularCharge_lt_half q) N)
    have hgnonneg :
        0 ≤ primeValuationHellingerBelow
          (-xiRightSourceModularCharge q) N :=
      Real.sqrt_nonneg _
    have hop := (R N).le_opNorm
      (primeValuationHellingerBelow
        (xiRightSourceModularCharge q) N)
    rw [congrFun hsew N] at hop
    have hdiv :
        primeValuationHellingerBelow
              (-xiRightSourceModularCharge q) N /
            primeValuationHellingerBelow
              (xiRightSourceModularCharge q) N ≤
          ‖R N‖ :=
      (div_le_iff₀ hfpos).2 (by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hgnonneg,
          abs_of_pos hfpos, mul_comm] using hop)
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg hgnonneg hfpos.le),
      abs_norm, one_mul] using hdiv
  exact hcost.trans_isBigO hratio

/-- Exact cross-chart certificate attached to one right-half Xi divisor
copy. -/
structure XiRightSourceModularTypeSuperselectionCertificate
    (q : XiRightZeroCopy) : Prop where
  chargePositive :
    0 < xiRightSourceModularCharge q
  chargeBelowHalf :
    xiRightSourceModularCharge q < 1 / 2
  primeSeamNotCoherent :
    ¬ OrbitwisePrimeSeamChargesCoherent (q.1.1 : ℂ)
  shellTransgression :
    shellTransferEntropy (q.1.1 : ℂ) =
      -xiRightSourceModularCharge q
  normalConeResidue :
    ∀ {n : ℤ}, meromorphicOrderAt xi (q.1.1 : ℂ) = n →
      Tendsto
        (fun s =>
          ((s - (q.1.1 : ℂ)) *
            xiExceptionalAffineDivisorCurrent s).re)
        (nhdsWithin (q.1.1 : ℂ) ({(q.1.1 : ℂ)}ᶜ))
        (nhds (-((n : ℝ) * xiRightSourceModularCharge q)))
  hurwitzPhase :
    xiRightSourceModularCharge q =
      xiHurwitzRightPrincipalPhase q
  primeWindowPhase :
    ∀ (W : CompactBVPrimeWindow) {r : ℝ} (hr : 1 < r),
      W.continuedSourceResidueValue (q.1.1 : ℂ) ≠ 0 →
        xiBVResiduePhaseCoordinate W r hr q =
          xiRightSourceModularCharge q
  gammaReesResolution :
    GammaSewnActivationReesResolutionCertificate
  depthGraphOuterInnerWeld :
    XiDepthGraphOuterInnerWeldCertificate
  boundaryCharacterFracture :
    XiBoundaryCharacterFractureCertificate
  criticalActivationSingularResolution :
    CriticalActivationSingularResolutionCertificate
  finiteReesNoSewing :
    ∀ (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ)),
      ReesOperatorGradeAtMost atTop
        primeWoldBoundaryVolumeBelow K R →
      (fun N =>
        R N
          (primeValuationSquaredHellingerBelow
            (xiRightSourceModularCharge q) N)) ≠
        primeValuationSquaredHellingerBelow
          (-xiRightSourceModularCharge q)
  essentialSewingCost :
    ∀ (R : ℕ → (ℝ →L[ℝ] ℝ)),
      (fun N =>
        R N
          (primeValuationSquaredHellingerBelow
            (xiRightSourceModularCharge q) N)) =
          primeValuationSquaredHellingerBelow
            (-xiRightSourceModularCharge q) →
      ∀ K : ℕ,
        (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
          (fun N => ‖R N‖)
  affinityFiniteReesNoSewing :
    ∀ (K : ℕ) (R : ℕ → (ℝ →L[ℝ] ℝ)),
      ReesOperatorGradeAtMost atTop
        primeWoldBoundaryVolumeBelow K R →
      (fun N =>
        R N
          (primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N)) ≠
        primeValuationHellingerBelow
          (-xiRightSourceModularCharge q)
  affinityEssentialSewingCost :
    ∀ (R : ℕ → (ℝ →L[ℝ] ℝ)),
      (fun N =>
        R N
          (primeValuationHellingerBelow
            (xiRightSourceModularCharge q) N)) =
          primeValuationHellingerBelow
            (-xiRightSourceModularCharge q) →
      ∀ K : ℕ,
        (fun N => (primeWoldBoundaryVolumeBelow N)⁻¹ ^ K) =o[atTop]
          (fun N => ‖R N‖)

/-- **Xi source-modular type-superselection law.**  Every actual right Xi
divisor copy determines one positive charge common to the normal-cone,
hypertranscendental shell, Hurwitz, and compact prime-window charts.  In the
reflected prime-valuation realization, no finite-Rees operator can sew the
two sectors, and every exact sewing cost is essential. -/
theorem xiRightSourceModularTypeSuperselection_law
    (q : XiRightZeroCopy) :
    XiRightSourceModularTypeSuperselectionCertificate q where
  chargePositive := xiRightSourceModularCharge_pos q
  chargeBelowHalf := xiRightSourceModularCharge_lt_half q
  primeSeamNotCoherent :=
    xiRightPrimeSeamCharges_not_coherent q
  shellTransgression :=
    shellTransferEntropy_eq_neg_xiRightSourceModularCharge q
  normalConeResidue :=
    tendsto_re_xiExceptionalAffineDivisorCurrent_eq_neg_modularCharge q
  hurwitzPhase :=
    xiRightSourceModularCharge_eq_hurwitzPrincipalPhase q
  primeWindowPhase :=
    fun W {_r} hr hres =>
      xiBVResiduePhaseCoordinate_eq_sourceModularCharge
        W hr q hres
  gammaReesResolution :=
    gammaSewnActivationReesResolution_law
  depthGraphOuterInnerWeld :=
    xiDepthGraphOuterInnerWeld_law
  boundaryCharacterFracture :=
    xiBoundaryCharacterFracture_law
  criticalActivationSingularResolution :=
    criticalActivationSingularResolution_law
  finiteReesNoSewing :=
    fun K R hR =>
      no_finiteReesOperator_sews_xiRightModularSectors q K R hR
  essentialSewingCost :=
    fun R hsew K =>
      xiRightModularSewingOperatorNorm_beyondEveryReesOrder
        q R hsew K
  affinityFiniteReesNoSewing :=
    fun K R hR =>
      no_finiteReesOperator_sews_xiRightModularAffinities
        q K R hR
  affinityEssentialSewingCost :=
    fun R hsew K =>
      xiRightModularAffinitySewingOperatorNorm_beyondEveryReesOrder
        q R hsew K

end

end RHTower
