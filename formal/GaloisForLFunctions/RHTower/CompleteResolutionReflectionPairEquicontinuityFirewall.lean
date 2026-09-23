import GaloisForLFunctions.RHTower.CompleteResolutionSecondCartierNormalOrder
import GaloisForLFunctions.RHTower.SourceZeroHorizontalCarrier

/-!
# Reflection-pair equicontinuity firewall for the complete Riemann source

The complete source vectors of a point and its functional-equation reflection
converge to each other in the canonical `ell^(1 : ℕ)` topology.  Their literal
prime-two endpoint characters remain separated off the critical line.

This module strengthens the existing uniform-Lipschitz obstruction.  An exact
family of endpoint extractors cannot satisfy any common continuity modulus on
the reflected source pair off line.  Conversely, on the critical line a
constant extractor is exact.  Thus reflection-pair equicontinuous exact
extraction is classified exactly by the critical-line condition.

The final theorem connects this pre-divisor regularity criterion to the
literal Route-P endpoint while retaining its physical coefficient and Xi
multiplicity.  No finite measure, Toeplitz admission, or scalar short is used.
-/

open Complex Filter Topology

namespace RHTower

noncomputable section

/-- Exact reflected endpoint extraction with one common continuity modulus on
the two cofinally collapsing source points.  No linearity or global continuity
of the extractors is required. -/
def CompleteResolutionReflectionPairEndpointEquicontinuous
    (s : CompleteResolutionOpenCriticalStrip) : Prop :=
  ∃ T : ℕ → CompleteResolutionSourceSpace → ℂ,
    (∀ K : ℕ,
      T K (completeResolutionSourceEmbedding K
          (completeResolutionOpenCriticalStripToRightHalfPlane s)) =
        shellTransferCharacter s.1) ∧
    (∀ K : ℕ,
      T K (completeResolutionSourceEmbedding K
          (completeResolutionOpenCriticalStripToRightHalfPlane
            (completeResolutionOpenCriticalStripReflection s))) =
        shellTransferCharacter
          (completeResolutionOpenCriticalStripReflection s).1) ∧
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧ ∀ K : ℕ,
        dist
            (completeResolutionSourceEmbedding K
              (completeResolutionOpenCriticalStripToRightHalfPlane s))
            (completeResolutionSourceEmbedding K
              (completeResolutionOpenCriticalStripToRightHalfPlane
                (completeResolutionOpenCriticalStripReflection s))) < δ →
          dist
              (T K (completeResolutionSourceEmbedding K
                (completeResolutionOpenCriticalStripToRightHalfPlane s)))
              (T K (completeResolutionSourceEmbedding K
                (completeResolutionOpenCriticalStripToRightHalfPlane
                  (completeResolutionOpenCriticalStripReflection s)))) < ε

/-- Off the critical line, every exact reflected endpoint extractor violates
every common continuity modulus on the source pair. -/
theorem not_completeResolutionReflectionPairEndpointEquicontinuous_of_re_ne_half
    (s : CompleteResolutionOpenCriticalStrip)
    (hoff : s.1.re ≠ 1 / 2) :
    ¬ CompleteResolutionReflectionPairEndpointEquicontinuous s := by
  rintro ⟨T, hextract, hextractReflection, hequicontinuous⟩
  let gap : ℝ :=
    dist (shellTransferCharacter s.1)
      (shellTransferCharacter
        (completeResolutionOpenCriticalStripReflection s).1)
  have hcharactersNe :
      shellTransferCharacter s.1 ≠
        shellTransferCharacter
          (completeResolutionOpenCriticalStripReflection s).1 := by
    simpa [completeResolutionOpenCriticalStripReflection] using
      shellTransferCharacter_ne_reflection_of_re_ne_half s.1 hoff
  have hgap : 0 < gap := dist_pos.mpr hcharactersNe
  obtain ⟨δ, hδ, hmodulus⟩ :=
    hequicontinuous gap hgap
  have hcollapse :=
    tendsto_completeResolutionReflectionSourceDisplacement_zero s
  rw [Metric.tendsto_atTop] at hcollapse
  obtain ⟨K, hK⟩ := hcollapse δ hδ
  have hsmall := hK K le_rfl
  have hinput :
      dist
          (completeResolutionSourceEmbedding K
            (completeResolutionOpenCriticalStripToRightHalfPlane s))
          (completeResolutionSourceEmbedding K
            (completeResolutionOpenCriticalStripToRightHalfPlane
              (completeResolutionOpenCriticalStripReflection s))) < δ := by
    simpa [dist_eq_norm,
      completeResolutionReflectionSourceDisplacement_eq_orientedEdge] using hsmall
  have hout := hmodulus K hinput
  rw [hextract K, hextractReflection K] at hout
  exact (lt_irrefl gap) hout

/-- Reflection-pair equicontinuous exact extraction exists exactly at neutral
horizontal grade.  The reverse direction uses the constant exact extractor on
the fixed reflection pair. -/
theorem completeResolutionReflectionPairEndpointEquicontinuous_iff
    (s : CompleteResolutionOpenCriticalStrip) :
    CompleteResolutionReflectionPairEndpointEquicontinuous s ↔
      s.1.re = 1 / 2 := by
  constructor
  · intro h
    by_contra hoff
    exact
      (not_completeResolutionReflectionPairEndpointEquicontinuous_of_re_ne_half
        s hoff) h
  · intro hline
    have hreflection :
        completeResolutionOpenCriticalStripReflection s = s := by
      apply Subtype.ext
      apply Complex.ext
      · norm_num [completeResolutionOpenCriticalStripReflection, hline]
      · simp [completeResolutionOpenCriticalStripReflection]
    let T : ℕ → CompleteResolutionSourceSpace → ℂ :=
      fun _ _ => shellTransferCharacter s.1
    refine ⟨T, ?_, ?_, ?_⟩
    · intro K
      rfl
    · intro K
      rw [hreflection]
    · intro ε hε
      refine ⟨1, by norm_num, fun K hinput => ?_⟩
      rw [hreflection]
      exact dist_self _ |>.trans_lt hε

/-- Global reflection-pair regularity target on every multiplicity copy. -/
def EveryXiZeroCopyCompleteResolutionReflectionPairEndpointEquicontinuous : Prop :=
  ∀ q : XiZeroCopy,
    CompleteResolutionReflectionPairEndpointEquicontinuous
      (xiZeroCopyCompleteResolutionStripPoint q)

/-- The global regular exact-extraction target is precisely RH-strength. -/
theorem
    everyXiZeroCopyCompleteResolutionReflectionPairEndpointEquicontinuous_iff_riemannHypothesis :
    EveryXiZeroCopyCompleteResolutionReflectionPairEndpointEquicontinuous ↔
      RiemannHypothesis := by
  constructor
  · intro hregular
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    have hline : (q.1 : ℂ).re = 1 / 2 :=
      (completeResolutionReflectionPairEndpointEquicontinuous_iff
        (xiZeroCopyCompleteResolutionStripPoint q)).1 (hregular q)
    refine ⟨(q.1 : ℂ).im, ?_⟩
    apply Complex.ext
    · simp [xiSpectralPoint]
    · simp [xiSpectralPoint, hline]
  · intro hRH q
    apply (completeResolutionReflectionPairEndpointEquicontinuous_iff
      (xiZeroCopyCompleteResolutionStripPoint q)).2
    exact xi_divisor_support_re_eq_half_of_rh hRH q.1

/-- Coefficient-and-multiplicity faithful physical handoff.  Reflection-pair
regularity at one actual Xi copy forces pre-divisor order and literal endpoint
moderation; the prime-two character, radial energy, and support multiplicity
remain the existing literal ones. -/
theorem
    completeResolutionReflectionPairEndpointEquicontinuous_actualXi_capstone
    {x u r : ℝ} (q : XiRightZeroCopy)
    (hkappa : routePTwoPrimeJuliaWardNonlocalCoupling x u ≠ 0)
    (hr : r ≠ 0) (N : ℕ)
    (hjet : 0 < sourceHorizontalWoldBVGreenStokesEndpointThirdJet N)
    (hregular : CompleteResolutionReflectionPairEndpointEquicontinuous
      (xiZeroCopyCompleteResolutionStripPoint q.1)) :
    CompleteResolutionPreDivisorSecondCartierOrderAt 0
        (completeResolutionXiSupportSourcePoint q.1.1) ∧
      bilateralModerate
        (sourceHorizontalActualXiEndpointSecondJetHardyDescent x u q r N
          (default : Nat.Primes) sourceHorizontalBilateralSecondJetGhost) ∧
      ∀ K n : ℕ,
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
                (default : Nat.Primes)) (-(n : ℤ))‖ ^ (2 : ℕ) +
            4 * ‖(sourceHorizontalActualXiEndpointSecondJetHardyDescent
              x u q r N (default : Nat.Primes)
              sourceHorizontalBilateralSecondJetGhost) (n : ℤ)‖ ^ (2 : ℕ) ∧
        (∑ s : XiRightSupportFiber q,
          sourceHorizontalActualXiSecondCartierKreinPolarizedGhost
            x u s.1 r N) =
          xiSupportMultiplicity q.1.1 •
            sourceHorizontalActualXiSecondCartierKreinPolarizedGhost
              x u q r N := by
  have hline : ((q.1.1 : XiDivisorSupport) : ℂ).re = 1 / 2 :=
    (completeResolutionReflectionPairEndpointEquicontinuous_iff
      (xiZeroCopyCompleteResolutionStripPoint q.1)).1 hregular
  have horder :
      CompleteResolutionPreDivisorSecondCartierOrderAt 0
        (completeResolutionXiSupportSourcePoint q.1.1) :=
    (completeResolutionPreDivisorSecondCartierOrderAt_iff 0
      (completeResolutionXiSupportSourcePoint q.1.1)).2 hline
  refine ⟨horder,
    completeResolutionPreDivisorOrder_forces_actualXiEndpointModeration
      q hkappa hr N hjet horder, ?_⟩
  intro K n
  exact
    completeResolutionSourceNormal_actualXiLiteralEndpoint_coefficientMultiplicity
      K x u q r N n

end

end RHTower
