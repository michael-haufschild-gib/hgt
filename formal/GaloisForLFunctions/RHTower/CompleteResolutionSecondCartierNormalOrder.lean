import GaloisForLFunctions.RHTower.CompleteResolutionCofinalConditioningLaw
import GaloisForLFunctions.RHTower.SourceHorizontalSecondCartierOrbitCoercivity

/-!
# Complete-resolution normal order and the literal second-Cartier endpoint

The complete positive Riemann source has an internal two-prime normal reader.
This module identifies its prime-two coordinate with the literal Route-P
second-Cartier endpoint character, with exact conormal coefficient, endpoint
energy, and analytic multiplicity.

The resulting pre-divisor order predicate is classified exactly: it is the
critical-line condition, and its universal Xi admission is equivalent to RH.
This is a classification, not an unconditional proof of that admission.

The positive survivor is quantitative.  Across functional-equation
reflection, complete source vectors collapse in `ell^1`, while the endpoint
characters stay separated off line.  Hence every exact, possibly nonlinear,
coefficient-faithful extractor has Lipschitz sensitivity tending to infinity.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- The first complete-resolution normal clock is the prime-two bilateral
half-density character. -/
theorem shellTransferCharacter_eq_bilateralHalfDensityCharacter_two (s : ℂ) :
    shellTransferCharacter s = bilateralHalfDensityCharacter 2 s := by
  simp [shellTransferCharacter, bilateralHalfDensityCharacter]

/-- On an actual strict-right Xi copy, the complete source normal reader is
exactly the literal prime-two endpoint character. -/
theorem completeResolution_sourceNormalPrimeTwo_eq_actualXiEndpointCharacter
    (K : ℕ) (q : XiRightZeroCopy) :
    (completeResolutionSourceNormalReader K
      (completeResolutionSourceImagePoint K
        ⟨((q.1.1 : XiDivisorSupport) : ℂ), by
          have hcenter := xiRightCenteredZero_re_pos q
          rw [xiRightCenteredZero_eq_support_sub_half, Complex.sub_re] at hcenter
          norm_num at hcenter ⊢
          linarith⟩)).1 =
      sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
        (default : Nat.Primes) := by
  rw [completeResolutionSourceNormalReader_imagePoint]
  simp only [twoPrimeShellTransferSpectrum]
  simp [sourceHorizontalActualXiSecondCartierKreinPrimeCharacter,
    bilateralHalfDensityCharacter,
    GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter]
  rfl

/-- Off the critical line, reflected prime-two normal characters are
distinct. -/
theorem shellTransferCharacter_ne_reflection_of_re_ne_half
    (s : ℂ) (hoff : s.re ≠ 1 / 2) :
    shellTransferCharacter s ≠ shellTransferCharacter (1 - star s) := by
  intro heq
  have hpair := shellTransferCharacter_reflection_pair s
  rw [← heq] at hpair
  have hnorm := congrArg norm hpair
  simp only [norm_mul, norm_star, norm_one] at hnorm
  have hnonneg : 0 ≤ ‖shellTransferCharacter s‖ := norm_nonneg _
  have hone : ‖shellTransferCharacter s‖ = 1 := by nlinarith
  exact hoff ((norm_shellTransferCharacter_eq_one_iff s).mp hone)

/-- The order predicate is defined on the completed source image before any
divisor is selected. It retains the first source-normal clock as the literal
second-Cartier transfer character. -/
def CompleteResolutionPreDivisorSecondCartierOrderAt
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) : Prop :=
  SourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded
    (completeResolutionSourceNormalReader K
      (completeResolutionSourceImagePoint K s)).1 1

/-- Exact classification of the pre-divisor completed-source order: it is
neither weaker nor stronger than neutral horizontal grade. -/
theorem completeResolutionPreDivisorSecondCartierOrderAt_iff
    (K : ℕ) (s : CompleteResolutionRightHalfPlane) :
    CompleteResolutionPreDivisorSecondCartierOrderAt K s ↔
      s.1.re = 1 / 2 := by
  rw [CompleteResolutionPreDivisorSecondCartierOrderAt,
    sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff]
  · rw [completeResolutionSourceNormalReader_imagePoint]
    simpa [twoPrimeShellTransferSpectrum,
      shellTransferCharacter_eq_leastAtomTransferCharacter] using
        norm_shellTransferCharacter_eq_one_iff s.1
  · rw [completeResolutionSourceNormalReader_imagePoint]
    simp [twoPrimeShellTransferSpectrum,
      GaloisForLFunctions.HTGeometry.leastAtomTransferCharacter]
  · exact one_ne_zero

/-- Canonical completed-source point of an Xi divisor, with no right/left
choice and with its analytic multiplicity left untouched. -/
def completeResolutionXiSupportSourcePoint
    (rho : XiDivisorSupport) : CompleteResolutionRightHalfPlane :=
  ⟨(rho : ℂ), (xi_divisor_support_re_mem_open_unit rho).1⟩

/-- Global completed-source order demand. The observable is constructed
pre-divisor; this proposition only asks that every retained divisor land in
its ordered locus. -/
def CompleteResolutionXiPreDivisorSecondCartierOrderLaw : Prop :=
  ∀ rho : XiDivisorSupport,
    CompleteResolutionPreDivisorSecondCartierOrderAt 0
      (completeResolutionXiSupportSourcePoint rho)

/-- Hostile classification: unconditional construction of the global order
law is exactly RH, not a consequence of completed-source conservation alone. -/
theorem completeResolutionXiPreDivisorSecondCartierOrderLaw_iff_riemannHypothesis :
    CompleteResolutionXiPreDivisorSecondCartierOrderLaw ↔ RiemannHypothesis := by
  constructor
  · intro h
    apply riemannHypothesis_of_forall_xiDivisorSupport_re_eq_half
    intro rho
    exact (completeResolutionPreDivisorSecondCartierOrderAt_iff 0
      (completeResolutionXiSupportSourcePoint rho)).1 (h rho)
  · intro hRH rho
    exact (completeResolutionPreDivisorSecondCartierOrderAt_iff 0
      (completeResolutionXiSupportSourcePoint rho)).2
        (xi_divisor_support_re_eq_half_of_rh hRH rho)

/-- If the pre-divisor source order admitted one actual strict-right copy,
the already coefficient-faithful endpoint with the same copy and prime-two
label would be moderate. -/
theorem completeResolutionPreDivisorOrder_forces_actualXiEndpointModeration
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0) (hr : r ≠ 0)
    (N : ℕ) (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (horder : CompleteResolutionPreDivisorSecondCartierOrderAt 0
      (completeResolutionXiSupportSourcePoint q.1.1)) :
    bilateralModerate
      (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
        (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost) := by
  have hline : ((q.1.1 : XiDivisorSupport) : ℂ).re = 1 / 2 :=
    (completeResolutionPreDivisorSecondCartierOrderAt_iff 0
      (completeResolutionXiSupportSourcePoint q.1.1)).1 horder
  have hnorm :
      ‖sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
        (default : Nat.Primes)‖ = 1 := by
    have htwo : (((default : Nat.Primes) : ℕ)) = 2 := rfl
    have hpTwo : 2 ≤ (((default : Nat.Primes) : ℕ)) := by rw [htwo]
    exact (norm_bilateralHalfDensityCharacter_eq_one_iff hpTwo
      (q.1.1 : XiDivisorSupport)).2 hline
  have hbounded :
      SourceHorizontalActualXiSecondCartierKreinPolarizedGhostOrbitBounded
        x u q r N (default : Nat.Primes) := by
    exact (sourceHorizontalSecondCartierKreinPolarizedGhostOrbitBounded_iff
      (sourceHorizontalSecondCartierPointedKrein_actual_primeCharacter_ne_zero
        q (default : Nat.Primes))
      (sourceHorizontalSecondCartierPointedKrein_actual_scale_ne_zero
        q hkappa hr N hjet)).2 hnorm
  exact (sourceHorizontalActualXiSecondCartierKreinOrbitBounded_iff_endpointModerate
    q hkappa hr N hjet (default : Nat.Primes)).1 hbounded

/-- Exact completed-source-to-physical capstone. Prime-two character,
literal endpoint energy, and support-fibre analytic multiplicity survive in
one statement; no boundedness or RH premise is used. -/
theorem completeResolutionSourceNormal_actualXiLiteralEndpoint_coefficientMultiplicity
    (K : ℕ) (x u : ℝ) (q : XiRightZeroCopy) (r : ℝ) (N n : ℕ) :
    (completeResolutionSourceNormalReader K
      (completeResolutionSourceImagePoint K
        (completeResolutionXiSupportSourcePoint q.1.1))).1 =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) ∧
    sourceHorizontalSecondCartierKreinPositiveOrbitEnergy
        (sourceHorizontalSecondCartierKreinPolarizedGhostOrbit
          (completeResolutionSourceNormalReader K
            (completeResolutionSourceImagePoint K
              (completeResolutionXiSupportSourcePoint q.1.1))).1
          (sourceHorizontalActualXiSecondCartierKreinScale x u q r N) n) =
      ‖bilateralEigenFamily
          (sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
            (default : Nat.Primes)) (-(n : ℤ))‖ ^ 2 +
        4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
          (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost)
            (n : ℤ)‖ ^ 2 ∧
    (∑ s : XiRightSupportFiber q,
      sourceHorizontalActualXiSecondCartierKreinPolarizedGhost
        x u s.1 r N) =
      xiSupportMultiplicity q.1.1 •
        sourceHorizontalActualXiSecondCartierKreinPolarizedGhost
          x u q r N := by
  have hcharacter :
      (completeResolutionSourceNormalReader K
        (completeResolutionSourceImagePoint K
          (completeResolutionXiSupportSourcePoint q.1.1))).1 =
        sourceHorizontalActualXiSecondCartierKreinPrimeCharacter q
          (default : Nat.Primes) := by
    exact completeResolution_sourceNormalPrimeTwo_eq_actualXiEndpointCharacter K q
  refine ⟨hcharacter, ?_,
    sourceHorizontalActualXiSecondCartierKreinPolarizedGhost_fiber_sum
      x u q r N⟩
  rw [hcharacter]
  exact sourceHorizontalActualXiSecondCartierKreinOrbitEnergy_eq_literalEndpointEnergy
    x u q r N (default : Nat.Primes) n

/-- Any reflected endpoint-order estimate must pay a Lipschitz sensitivity
which diverges along the cofinal complete-source base. -/
theorem tendsto_completeResolutionReflectionEndpointSensitivity_atTop
    (s : CompleteResolutionOpenCriticalStrip)
    (hoff : s.1.re ≠ 1 / 2)
    (L : ℕ → ℝ)
    (horder : ∀ K : ℕ,
      dist (shellTransferCharacter s.1)
          (shellTransferCharacter (1 - star s.1)) ≤
        L K * ‖completeResolutionReflectionSourceDisplacement K s‖) :
    Tendsto L atTop atTop := by
  let δ : ℝ := dist (shellTransferCharacter s.1)
    (shellTransferCharacter (1 - star s.1))
  have hδ : 0 < δ := by
    exact dist_pos.mpr (shellTransferCharacter_ne_reflection_of_re_ne_half s.1 hoff)
  have hinv :=
    tendsto_inv_norm_completeResolutionReflectionSourceDisplacement_atTop s hoff
  have hlower : Tendsto
      (fun K : ℕ => δ * ‖completeResolutionReflectionSourceDisplacement K s‖⁻¹)
      atTop atTop :=
    hinv.const_mul_atTop hδ
  rw [tendsto_atTop]
  intro B
  filter_upwards [hlower.eventually_ge_atTop B] with K hK
  apply hK.trans
  have hpos : 0 < ‖completeResolutionReflectionSourceDisplacement K s‖ :=
    norm_pos_iff.mpr
      ((not_congr
        (completeResolutionReflectionSourceDisplacement_eq_zero_iff K s)).mpr hoff)
  have h := (div_le_iff₀ hpos).2 (horder K)
  simpa [δ, div_eq_mul_inv] using h

/-- Every exact nonlinear extractor of both reflected literal endpoint
characters has Lipschitz constants tending to infinity off the critical
line. -/
theorem tendsto_exactCompleteResolutionEndpointExtractor_lipschitz_atTop
    (s : CompleteResolutionOpenCriticalStrip)
    (hoff : s.1.re ≠ 1 / 2)
    (T : ℕ → CompleteResolutionSourceSpace → ℂ)
    (L : ℕ → ℝ)
    (hextract : ∀ K : ℕ,
      T K (completeResolutionSourceEmbedding K ⟨s.1, s.2.1⟩) =
        shellTransferCharacter s.1)
    (hextractReflection : ∀ K : ℕ,
      T K (completeResolutionSourceEmbedding K
        ⟨1 - star s.1, by
          have hstarRe : (star s.1).re = s.1.re := by simp
          simp only [sub_re, one_re]
          rw [hstarRe]
          linarith [s.2.2]⟩) =
        shellTransferCharacter (1 - star s.1))
    (hLip : ∀ K x y, dist (T K x) (T K y) ≤ L K * ‖x - y‖) :
    Tendsto L atTop atTop := by
  apply tendsto_completeResolutionReflectionEndpointSensitivity_atTop s hoff L
  intro K
  have h := hLip K
    (completeResolutionSourceEmbedding K ⟨s.1, s.2.1⟩)
    (completeResolutionSourceEmbedding K
      ⟨1 - star s.1, by
        have hstarRe : (star s.1).re = s.1.re := by simp
        simp only [sub_re, one_re]
        rw [hstarRe]
        linarith [s.2.2]⟩)
  rw [hextract K, hextractReflection K] at h
  simpa [completeResolutionReflectionSourceDisplacement] using h

end

end RHTower
