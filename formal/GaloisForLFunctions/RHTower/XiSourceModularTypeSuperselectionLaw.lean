import GaloisForLFunctions.RHTower.XiHypertranscendentalModularResidueTransgression
import GaloisForLFunctions.RHTower.XiBVResidueHurwitzPhaseEnergyUniversalityLaw
import GaloisForLFunctions.RHTower.PrimeValuationHellingerReesReflectionFracture
import GaloisForLFunctions.RHTower.RiemannComplexModularCharacterLaw
import GaloisForLFunctions.RHTower.AsymptoticTypeSuperselection
import GaloisForLFunctions.RHTower.EulerActivationSquarefreeDisintegration
import GaloisForLFunctions.RHTower.GammaSewnMobiusValuationContraction
import GaloisForLFunctions.RHTower.XiDepthMobiusGammaOuterInnerWeld

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
open scoped Topology
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
