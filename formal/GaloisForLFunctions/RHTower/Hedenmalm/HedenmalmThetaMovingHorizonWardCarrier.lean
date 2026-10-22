import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMovingHorizonBoundary
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmThetaMobiusPrimeNormalHalfDensityDomainNoGo
import GaloisForLFunctions.RHTower.CCM.CCMArchimedeanHankelTraceClass
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCenterMixedThreePoint

/-!
# Physical theta moving horizon as the Route P weak-Hilbert carrier

At prime aperture, Hadamard addition of the literal even and odd theta endpoint channels extracts
the common boundary atom.  After normalization by the nonzero theta value at the origin, this is
exactly `p^(-1/2)`, Route N's universal critical amplitude.

The oriented Möbius/Ward half-density on an Xi divisor copy differs from that physical source
amplitude by precisely the twisted channel `p^(-1/2-|a|)`.  Thus the difference is square summable
exactly away from neutral grade.  This is a coefficient-faithful identification on one physical
source carrier; it is not a postulated Hilbert realization or an RH premise.
-/

namespace RHTower.HedenmalmThetaSource

noncomputable section

open HedenmalmContinuousAperture

/-- Hadamard-sum extraction of the common theta boundary atom at prime aperture, normalized by
the strictly positive theta value at the origin. -/
def thetaMovingHorizonUniversalAmplitude (p : Nat.Primes) : ℝ :=
  (centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ))
        (-Real.log (p.1 : ℕ) / 2) +
      centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ))
        (-Real.log (p.1 : ℕ) / 2)) /
    (2 * thetaSource.k 0)

/-- **Physical principal-carrier identity.**  The literal moving-horizon theta doublet, rather
than an imposed prime weight, produces exactly Route N's universal `p^(-1/2)` amplitude. -/
theorem thetaMovingHorizonUniversalAmplitude_eq_routeN
    (p : Nat.Primes) :
    thetaMovingHorizonUniversalAmplitude p =
      routeNGammaSewnUniversalCriticalChannelAmplitude p := by
  rw [thetaMovingHorizonUniversalAmplitude,
    thetaApertureEvenEndpoint_leftHorizon,
    thetaApertureOddEndpoint_leftHorizon]
  have hk0 : thetaSource.k 0 ≠ 0 := (thetaSource.pos_k 0).ne'
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  have hsum :
      Real.exp (-Real.log (p.1 : ℕ) / 2) *
            (thetaSource.k 0 + thetaSource.k (Real.log (p.1 : ℕ))) +
          Real.exp (-Real.log (p.1 : ℕ) / 2) *
            (thetaSource.k 0 - thetaSource.k (Real.log (p.1 : ℕ))) =
        2 * thetaSource.k 0 * Real.exp (-Real.log (p.1 : ℕ) / 2) := by
    ring
  rw [hsum]
  rw [routeNGammaSewnUniversalCriticalChannelAmplitude,
    Real.rpow_def_of_pos hp0]
  field_simp [hk0]

/-- Hadamard-difference extraction of the decaying theta endpoint channel. -/
def thetaMovingHorizonHankelAmplitude (p : Nat.Primes) : ℝ :=
  (centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ))
        (-Real.log (p.1 : ℕ) / 2) -
      centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ))
        (-Real.log (p.1 : ℕ) / 2)) /
    (2 * thetaSource.k 0)

/-- The Hadamard difference is the universal carrier multiplied by the normalized theta tail. -/
theorem thetaMovingHorizonHankelAmplitude_eq
    (p : Nat.Primes) :
    thetaMovingHorizonHankelAmplitude p =
      thetaMovingHorizonUniversalAmplitude p *
        (thetaSource.k (Real.log (p.1 : ℕ)) / thetaSource.k 0) := by
  rw [thetaMovingHorizonHankelAmplitude, thetaMovingHorizonUniversalAmplitude,
    thetaApertureEvenEndpoint_leftHorizon,
    thetaApertureOddEndpoint_leftHorizon]
  have hk0 : thetaSource.k 0 ≠ 0 := (thetaSource.pos_k 0).ne'
  field_simp [hk0]
  ring

/-! ### Reflection swaps, rather than identifies, the two Hadamard channels -/

/-- Even aperture endpoint at the right moving horizon. -/
theorem thetaApertureEvenEndpoint_rightHorizon (L : ℝ) :
    centeredApertureEvenEndpoint thetaSource L (L / 2) =
      Real.exp (-L / 2) * (thetaSource.k L + thetaSource.k 0) := by
  rw [centeredApertureEvenEndpoint,
    show L / 2 + L / 2 = L by ring,
    show L / 2 - L / 2 = 0 by ring]

/-- Odd aperture endpoint at the right moving horizon. -/
theorem thetaApertureOddEndpoint_rightHorizon (L : ℝ) :
    centeredApertureOddEndpoint thetaSource L (L / 2) =
      Real.exp (-L / 2) * (thetaSource.k L - thetaSource.k 0) := by
  rw [centeredApertureOddEndpoint,
    show L / 2 + L / 2 = L by ring,
    show L / 2 - L / 2 = 0 by ring]

/-- Source reflection fixes the even endpoint. -/
theorem thetaApertureEvenEndpoint_right_eq_left (L : ℝ) :
    centeredApertureEvenEndpoint thetaSource L (L / 2) =
      centeredApertureEvenEndpoint thetaSource L (-L / 2) := by
  rw [thetaApertureEvenEndpoint_rightHorizon,
    thetaApertureEvenEndpoint_leftHorizon]
  ring

/-- Source reflection reverses the odd endpoint. -/
theorem thetaApertureOddEndpoint_right_eq_neg_left (L : ℝ) :
    centeredApertureOddEndpoint thetaSource L (L / 2) =
      -centeredApertureOddEndpoint thetaSource L (-L / 2) := by
  rw [thetaApertureOddEndpoint_rightHorizon,
    thetaApertureOddEndpoint_leftHorizon]
  ring

/-- At the reflected horizon, Hadamard addition is the CCM-visible theta tail. -/
theorem thetaMovingHorizon_right_sum_eq_hankel (p : Nat.Primes) :
    (centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ))
          (Real.log (p.1 : ℕ) / 2) +
        centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ))
          (Real.log (p.1 : ℕ) / 2)) /
        (2 * thetaSource.k 0) =
      thetaMovingHorizonHankelAmplitude p := by
  rw [thetaMovingHorizonHankelAmplitude,
    thetaApertureEvenEndpoint_right_eq_left,
    thetaApertureOddEndpoint_right_eq_neg_left]
  ring

/-- At the reflected horizon, Hadamard subtraction is the universal prime carrier. -/
theorem thetaMovingHorizon_right_sub_eq_universal (p : Nat.Primes) :
    (centeredApertureEvenEndpoint thetaSource (Real.log (p.1 : ℕ))
          (Real.log (p.1 : ℕ) / 2) -
        centeredApertureOddEndpoint thetaSource (Real.log (p.1 : ℕ))
          (Real.log (p.1 : ℕ) / 2)) /
        (2 * thetaSource.k 0) =
      thetaMovingHorizonUniversalAmplitude p := by
  rw [thetaMovingHorizonUniversalAmplitude,
    thetaApertureEvenEndpoint_right_eq_left,
    thetaApertureOddEndpoint_right_eq_neg_left]
  ring

/-- Strict source log-concavity makes the reflected tail atom smaller than the common boundary
atom at every prime aperture. -/
theorem thetaSource_k_log_prime_lt_k_zero (p : Nat.Primes) :
    thetaSource.k (Real.log (p.1 : ℕ)) < thetaSource.k 0 := by
  have hpR : (1 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.one_lt
  have hlog : 0 < Real.log (p.1 : ℕ) := Real.log_pos hpR
  have hproduct := strictAntiOn_thetaCuspFullSource_mul_reflect 0
    (show (0 : ℝ) ∈ Set.Ici 0 by simp)
    (show Real.log (p.1 : ℕ) ∈ Set.Ici (0 : ℝ) by exact hlog.le)
    hlog
  have hproduct' :
      thetaCuspFullSource (Real.log (p.1 : ℕ)) *
          thetaCuspFullSource (-Real.log (p.1 : ℕ)) <
        thetaCuspFullSource 0 * thetaCuspFullSource 0 := by
    simpa only [zero_add, zero_sub, neg_zero] using hproduct
  rw [thetaCuspFullSource_neg] at hproduct'
  rw [thetaSource_k, thetaSource_k]
  nlinarith [hproduct', thetaCuspFullSource_pos_all (Real.log (p.1 : ℕ)),
    thetaCuspFullSource_pos_all 0]

/-- **Strict channel-separation law.** Reflection cannot identify the two Hadamard channels:
the CCM-visible tail is strictly smaller than the universal boundary carrier at every prime. -/
theorem thetaMovingHorizonHankelAmplitude_lt_universal (p : Nat.Primes) :
    thetaMovingHorizonHankelAmplitude p <
      thetaMovingHorizonUniversalAmplitude p := by
  rw [thetaMovingHorizonHankelAmplitude_eq]
  have huniversal : 0 < thetaMovingHorizonUniversalAmplitude p := by
    rw [thetaMovingHorizonUniversalAmplitude_eq_routeN,
      routeNGammaSewnUniversalCriticalChannelAmplitude]
    exact Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  have hratio :
      thetaSource.k (Real.log (p.1 : ℕ)) / thetaSource.k 0 < 1 :=
    (div_lt_one (thetaSource.pos_k 0)).mpr (thetaSource_k_log_prime_lt_k_zero p)
  nlinarith

/-! ### Moving-horizon differentiation sees only the trace-class tail -/

/-- Physical theta aperture window followed along its left moving horizon. -/
def thetaLeftMovingHorizonWindow (L : ℝ) : ℝ :=
  centeredApertureWindow thetaSource L (-L / 2)

theorem thetaLeftMovingHorizonWindow_eq (L : ℝ) :
    thetaLeftMovingHorizonWindow L =
      Real.exp (-L / 2) *
        (thetaSource.mass * (thetaSource.cdfFun 0 - thetaSource.cdfFun (-L))) := by
  rw [thetaLeftMovingHorizonWindow, centeredApertureWindow,
    show -L / 2 + L / 2 = 0 by ring,
    show -L / 2 - L / 2 = -L by ring]

/-- The total moving-horizon derivative contains no `k(0)` boundary term.  Center motion cancels
that term from aperture motion, leaving only the translated theta tail. -/
theorem hasDerivAt_thetaLeftMovingHorizonWindow (L : ℝ) :
    SourceHasDerivAt thetaLeftMovingHorizonWindow
      ((-1 / 2) * thetaLeftMovingHorizonWindow L +
        Real.exp (-L / 2) * thetaSource.k L) L := by
  have hnegHalf : SourceHasDerivAt (fun M : ℝ => -M / 2) (-1 / 2) L := by
    simpa using (hasDerivAt_id L).neg.div_const 2
  have hexp : SourceHasDerivAt (fun M : ℝ => Real.exp (-M / 2))
      (Real.exp (-L / 2) * (-1 / 2)) L := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-L / 2)).comp L hnegHalf
  have hneg : SourceHasDerivAt (fun M : ℝ => -M) (-1) L := by
    have h := (hasDerivAt_const (x := L) (0 : ℝ)).sub (hasDerivAt_id L)
    refine (h.congr_deriv (by ring)).congr_of_eventuallyEq ?_
    filter_upwards with M
    simp
  have hcdf : SourceHasDerivAt (fun M : ℝ => thetaSource.cdfFun (-M))
      (thetaSource.normalized (-L) * (-1)) L := by
    simpa only [Function.comp_def] using
      (thetaSource.hasDerivAt_cdfFun (-L)).comp L hneg
  have hdiff : SourceHasDerivAt
      (fun M : ℝ => thetaSource.cdfFun 0 - thetaSource.cdfFun (-M))
      (0 - thetaSource.normalized (-L) * (-1)) L :=
    (hasDerivAt_const L (thetaSource.cdfFun 0)).sub hcdf
  have hmass := hdiff.const_mul thetaSource.mass
  have hproduct := hexp.mul hmass
  have hfun : thetaLeftMovingHorizonWindow =
      fun M : ℝ => Real.exp (-M / 2) *
        (thetaSource.mass * (thetaSource.cdfFun 0 - thetaSource.cdfFun (-M))) := by
    funext M
    exact thetaLeftMovingHorizonWindow_eq M
  rw [hfun]
  convert hproduct using 1
  · ext M
    rfl
  · rw [show thetaSource.normalized (-L) =
        thetaSource.k (-L) / thetaSource.mass from rfl,
      thetaSource_even]
    field_simp [thetaSource.mass_ne_zero]
    ring

/-- Covariant differentiation along the horizon is exactly the translated theta-tail endpoint. -/
theorem thetaLeftMovingHorizonCovariantDerivative_eq_tail (L : ℝ) :
    deriv thetaLeftMovingHorizonWindow L +
        (1 / 2) * thetaLeftMovingHorizonWindow L =
      Real.exp (-L / 2) * thetaSource.k L := by
  rw [(hasDerivAt_thetaLeftMovingHorizonWindow L).deriv]
  ring

/-- **Local-producer classification.** At every prime aperture, the normalized covariant
moving-horizon derivative is exactly the square-summable CCM/Hankel channel, not the universal
`p^(-1/2)` boundary carrier. -/
theorem thetaLeftMovingHorizonCovariantDerivative_prime_eq_hankel
    (p : Nat.Primes) :
    (deriv thetaLeftMovingHorizonWindow (Real.log (p.1 : ℕ)) +
          (1 / 2) * thetaLeftMovingHorizonWindow (Real.log (p.1 : ℕ))) /
        thetaSource.k 0 =
      thetaMovingHorizonHankelAmplitude p := by
  rw [thetaLeftMovingHorizonCovariantDerivative_eq_tail,
    thetaMovingHorizonHankelAmplitude,
    thetaApertureEvenEndpoint_leftHorizon,
    thetaApertureOddEndpoint_leftHorizon]
  ring

/-- Half-density connection along logarithmic aperture. -/
def thetaMovingHorizonConnection (f : ℝ → ℝ) (L : ℝ) : ℝ :=
  deriv f L + (1 / 2) * f L

/-- Common `k(0)` endpoint atom transported as a half-density in aperture. -/
def thetaMovingHorizonBoundaryMode (L : ℝ) : ℝ :=
  Real.exp (-L / 2) * thetaSource.k 0

theorem hasDerivAt_thetaMovingHorizonBoundaryMode (L : ℝ) :
    SourceHasDerivAt thetaMovingHorizonBoundaryMode
      ((-1 / 2) * thetaMovingHorizonBoundaryMode L) L := by
  have hnegHalf : SourceHasDerivAt (fun M : ℝ => -M / 2) (-1 / 2) L := by
    simpa using (hasDerivAt_id L).neg.div_const 2
  have hexp : SourceHasDerivAt (fun M : ℝ => Real.exp (-M / 2))
      (Real.exp (-L / 2) * (-1 / 2)) L := by
    simpa only [Function.comp_def] using
      (Real.hasDerivAt_exp (-L / 2)).comp L hnegHalf
  convert hexp.const_mul (thetaSource.k 0) using 1
  · funext y
    unfold thetaMovingHorizonBoundaryMode
    rw [show -y / 2 = y * (-1 / 2) by ring]
    ring
  · unfold thetaMovingHorizonBoundaryMode
    ring

/-- **Flat boundary law.** The entire nonsummable prime carrier lies in the kernel of the physical
half-density connection; local curvature and covariant-derivative receivers erase it exactly. -/
theorem thetaMovingHorizonConnection_boundaryMode_eq_zero (L : ℝ) :
    thetaMovingHorizonConnection thetaMovingHorizonBoundaryMode L = 0 := by
  rw [thetaMovingHorizonConnection,
    (hasDerivAt_thetaMovingHorizonBoundaryMode L).deriv]
  ring

/-- Prime sampling of the flat boundary mode recovers the coefficient-faithful universal carrier. -/
theorem thetaMovingHorizonBoundaryMode_prime_normalized_eq_universal
    (p : Nat.Primes) :
    thetaMovingHorizonBoundaryMode (Real.log (p.1 : ℕ)) /
        thetaSource.k 0 =
      thetaMovingHorizonUniversalAmplitude p := by
  rw [thetaMovingHorizonBoundaryMode,
    thetaMovingHorizonUniversalAmplitude_eq_routeN,
    routeNGammaSewnUniversalCriticalChannelAmplitude]
  have hk0 : thetaSource.k 0 ≠ 0 := (thetaSource.pos_k 0).ne'
  have hp0 : (0 : ℝ) < (p.1 : ℕ) := by exact_mod_cast p.2.pos
  rw [Real.rpow_def_of_pos hp0]
  field_simp [hk0]

/-- The same connection sends the physical moving window to the CCM-visible theta tail. -/
theorem thetaMovingHorizonConnection_leftWindow_eq_tail (L : ℝ) :
    thetaMovingHorizonConnection thetaLeftMovingHorizonWindow L =
      Real.exp (-L / 2) * thetaSource.k L := by
  exact thetaLeftMovingHorizonCovariantDerivative_eq_tail L

/-- Squared physical universal amplitude is exactly one reciprocal-prime mass atom. -/
theorem thetaMovingHorizonUniversalAmplitude_sq (p : Nat.Primes) :
    thetaMovingHorizonUniversalAmplitude p ^ 2 = 1 / (p.1 : ℝ) := by
  rw [thetaMovingHorizonUniversalAmplitude_eq_routeN,
    routeNGammaSewnUniversalCriticalChannelAmplitude_sq,
    routeNGammaSewnUniversalCriticalChannelMass,
    Real.rpow_neg_one]
  rw [one_div]

/-- The decaying Hadamard difference is exactly the diagonal value of CCM's factorized positive
Hankel kernel at the prime logarithmic horizon. -/
theorem ccmHankel_kernel_factorization_theta_prime (p : Nat.Primes) :
    (∫ t in Set.Ici (Real.log (p.1 : ℕ) / 2),
      (-(1 + t ^ 2 : ℂ) *
          deriv thetaCuspSchwartz (Real.log (p.1 : ℕ) / 2 + t)) *
        ((1 + t ^ 2)⁻¹ : ℂ)) =
      (thetaSource.k (Real.log (p.1 : ℕ)) : ℂ) := by
  simpa only [thetaCuspSchwartz_apply, thetaSource_k,
    show Real.log (p.1 : ℕ) / 2 + Real.log (p.1 : ℕ) / 2 =
      Real.log (p.1 : ℕ) by ring] using
    (ccmHankel_kernel_factorization thetaCuspSchwartz
      (Real.log (p.1 : ℕ) / 2) (Real.log (p.1 : ℕ) / 2))

/-- CCM-visible Hadamard-difference amplitudes are genuinely square summable over prime labels. -/
theorem summable_sq_thetaMovingHorizonHankelAmplitude :
    Summable (fun p : Nat.Primes => thetaMovingHorizonHankelAmplitude p ^ 2) := by
  have hk0 : thetaSource.k 0 ≠ 0 := (thetaSource.pos_k 0).ne'
  have hscaled := summable_thetaMovingHorizonResidual.mul_left
    ((2 * thetaSource.k 0 ^ 2)⁻¹)
  refine hscaled.congr (fun p => ?_)
  rw [thetaMovingHorizonHankelAmplitude_eq, mul_pow,
    thetaMovingHorizonUniversalAmplitude_sq]
  have hp0 : (p.1 : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp [hk0, hp0]

/-- **CCM block-separation obstruction.**  The square-summable Hankel crossblock channel cannot
absorb the universal moving-horizon principal carrier.  Any successful producer must rotate the
Hadamard sum into the trace-class crossblock before completion. -/
theorem not_summable_sq_thetaMovingHorizonUniversal_sub_hankel :
    ¬ Summable (fun p : Nat.Primes =>
      (thetaMovingHorizonUniversalAmplitude p -
        thetaMovingHorizonHankelAmplitude p) ^ 2) := by
  rw [show (fun p : Nat.Primes =>
      (thetaMovingHorizonUniversalAmplitude p -
        thetaMovingHorizonHankelAmplitude p) ^ 2) =
      fun p : Nat.Primes =>
        (routeNGammaSewnUniversalCriticalChannelAmplitude p -
          thetaMovingHorizonHankelAmplitude p) ^ 2 by
    funext p
    rw [thetaMovingHorizonUniversalAmplitude_eq_routeN]]
  exact not_summable_sq_sub_universal_of_summable_sq
    thetaMovingHorizonHankelAmplitude
    summable_sq_thetaMovingHorizonHankelAmplitude

/-- Orientation of the retained prime-normal horizontal class.  Neutral grade is assigned the
positive branch; the residual theorem below detects that this branch cannot be Hilbert-admitted. -/
def thetaWardHorizontalOrientation (q : XiZeroCopy) : ℝ :=
  if 0 ≤ primeDepthBVWoldXiCenteredRate q.1 then 1 else -1

/-- Difference between the physical Möbius/Ward half-density and the oriented literal theta
moving-horizon principal carrier. -/
def thetaWardMovingHorizonResidual
    (p : Nat.Primes) (q : XiZeroCopy) : ℝ :=
  thetaMobiusPrimeNormalProfileHalfDensityAmplitude p q -
    thetaWardHorizontalOrientation q * thetaMovingHorizonUniversalAmplitude p

/-- The same-carrier residual is exactly the signed twisted channel, coefficient by coefficient. -/
theorem thetaWardMovingHorizonResidual_eq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaWardMovingHorizonResidual p q =
      if 0 ≤ primeDepthBVWoldXiCenteredRate q.1 then
        -routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p
      else
        routeNGammaSewnTwistedCriticalChannelAmplitude
          (primeDepthBVWoldXiCenteredRate q.1) p := by
  rw [thetaWardMovingHorizonResidual,
    thetaWardHorizontalOrientation,
    thetaMovingHorizonUniversalAmplitude_eq_routeN,
    thetaMobiusPrimeNormalProfileHalfDensityAmplitude_eq_channelGap]
  split <;> ring

/-- Orientation disappears only after squaring the exact same-carrier residual. -/
theorem thetaWardMovingHorizonResidual_sq
    (p : Nat.Primes) (q : XiZeroCopy) :
    thetaWardMovingHorizonResidual p q ^ 2 =
      routeNGammaSewnTwistedCriticalChannelAmplitude
        (primeDepthBVWoldXiCenteredRate q.1) p ^ 2 := by
  rw [thetaWardMovingHorizonResidual_eq]
  split <;> ring

/-- **Weak-Hilbert wall law.**  The Ward half-density and oriented physical theta carrier differ
by an `ell^(2 : ℕ)` prime family exactly off the neutral wall. -/
theorem summable_sq_thetaWardMovingHorizonResidual_iff
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes => thetaWardMovingHorizonResidual p q ^ 2) ↔
      primeDepthBVWoldXiCenteredRate q.1 ≠ 0 := by
  let a := primeDepthBVWoldXiCenteredRate q.1
  rw [show (fun p : Nat.Primes => thetaWardMovingHorizonResidual p q ^ 2) =
      fun p : Nat.Primes => routeNGammaSewnTwistedCriticalChannelAmplitude a p ^ 2 by
    funext p
    exact thetaWardMovingHorizonResidual_sq p q]
  change Summable (fun p : Nat.Primes =>
    routeNGammaSewnTwistedCriticalChannelAmplitude a p ^ 2) ↔ a ≠ 0
  constructor
  · intro hsum ha
    rw [ha] at hsum
    apply not_summable_routeNGammaSewnUniversalCriticalChannelAmplitude_sq
    simpa [routeNGammaSewnTwistedCriticalChannelAmplitude,
      routeNGammaSewnUniversalCriticalChannelAmplitude] using hsum
  · exact summable_routeNGammaSewnTwistedCriticalChannelAmplitude_sq_of_ne a

/-- On an actual multiplicity-resolved Xi copy, square-summable same-carrier correction selects
nonzero theta boundary flux.  Its negation is the desired Route P/RH orientation. -/
theorem summable_sq_thetaWardMovingHorizonResidual_iff_boundaryFlux_ne_zero
    (q : XiZeroCopy) :
    Summable (fun p : Nat.Primes => thetaWardMovingHorizonResidual p q ^ 2) ↔
      thetaXiRankTwoBoundaryFlux q ≠ 0 := by
  rw [summable_sq_thetaWardMovingHorizonResidual_iff,
    thetaXiRankTwoBoundaryFlux_eq_neg_massEnergy_mul_centeredRate]
  have hmass : -(thetaSource.mass * thetaXiRootEnergy q) ≠ 0 :=
    neg_ne_zero.mpr (mul_pos thetaSource.mass_pos (thetaXiRootEnergy_pos q)).ne'
  constructor
  · exact fun hrate => mul_ne_zero hmass hrate
  · intro hproduct hrate
    apply hproduct
    rw [hrate, mul_zero]

/-- Away from the wall, functional-equation reflection reverses the physical principal
orientation. -/
theorem thetaWardHorizontalOrientation_copyReflect
    (q : XiZeroCopy) (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaWardHorizontalOrientation (xiZeroCopyReflectEquiv q) =
      -thetaWardHorizontalOrientation q := by
  rw [thetaWardHorizontalOrientation, thetaWardHorizontalOrientation,
    primeDepthBVWoldXiCenteredRate_copyReflect]
  by_cases hpos : 0 < primeDepthBVWoldXiCenteredRate q.1
  · have hleft : ¬ 0 ≤ -primeDepthBVWoldXiCenteredRate q.1 := by linarith
    simp [hpos.le, hleft]
  · have hneg : primeDepthBVWoldXiCenteredRate q.1 < 0 :=
      lt_of_le_of_ne (le_of_not_gt hpos) hq
    have hleft : 0 ≤ -primeDepthBVWoldXiCenteredRate q.1 := by linarith
    have hright : ¬ 0 ≤ primeDepthBVWoldXiCenteredRate q.1 := not_le.mpr hneg
    simp [hleft, hright]

/-- The two reflected physical principal carriers annihilate labelwise before scalarization. -/
theorem thetaWardReflectedPrincipalCarriers_add_eq_zero
    (p : Nat.Primes) (q : XiZeroCopy)
    (hq : primeDepthBVWoldXiCenteredRate q.1 ≠ 0) :
    thetaWardHorizontalOrientation q * thetaMovingHorizonUniversalAmplitude p +
        thetaWardHorizontalOrientation (xiZeroCopyReflectEquiv q) *
          thetaMovingHorizonUniversalAmplitude p = 0 := by
  rw [thetaWardHorizontalOrientation_copyReflect q hq]
  ring

end

end RHTower.HedenmalmThetaSource
