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
import GaloisForLFunctions.HTGeometry.BifilteredScalarizationNoGo
import GaloisForLFunctions.HTGeometry.PointedFisherCutoffWardTrace
import GaloisForLFunctions.HTGeometry.PrimeResidueValuationInteractionSuperselection
import GaloisForLFunctions.HTGeometry.PrimeValuationCoordinateFusionCompletion

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

open Complex Filter Asymptotics
open scoped Topology ComplexOrder
open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry

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
  ramifiedDivisorCharacter :
    ∀ rho : ℂ, XiRamifiedDivisorCharacterCertificate rho
  quadraticCharacterCompression :
    0 ≤ xiHurwitzOrientationEnergy ∧
      (xiHurwitzOrientationEnergy = 0 ↔
        ∀ rho : XiDivisorSupport,
          ‖centeredComplexModularCharacter (rho : ℂ) (1 : ℂ)‖ = 1)
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
  ramifiedDivisorCharacter :=
    xiRamifiedDivisorCharacter_law
  quadraticCharacterCompression :=
    ⟨xiHurwitzOrientationEnergy_nonneg,
      xiHurwitzOrientationEnergy_eq_zero_iff_unitaryCenteredCharacters⟩
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
