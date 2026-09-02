import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSecondHarmonicGaussSquareRootEndpoint
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMCanonicalLeftResponseWard

/-!
# Physical-Jost biorthogonal-normalization no-go for HB

The exact Gauss endpoint identifies the regular BM normalizable connection entry with the literal
Birmingham--Mokhtari decaying Gamma/Jost coefficient.  This module inserts that physical entry into
the canonical left-QNM covectors and proves that biorthogonal normalization erases it completely:
the matching dual response is the input horizon coordinate and the cross response is zero.

More generally, the two canonical dual rows recover the two input coordinates of every linear
combination of the exact regular and complementary connection columns.  Hence no coefficient of
the connection matrix--including the newly identified Gamma/Jost phase and modulus--can become the
missing HB source orientation after canonical dual normalization.  With a global nonzero input
coordinate, the resulting Peierls current is exactly the existing critical-wall/RH receiver.

The positive survivor is sharp: a genuine producer must place divisor-sensitive information in the
source-side horizon coordinates before dual normalization, or use a nonlinear/cross-channel/
renormalized pairing not reducible to inverse-row coordinate extraction.

`[NEW] [CLASSIFICATION] [NO-GO] [PAPER-PROVED] [LEAN-PROVED]`
-/

open Complex Real Set

namespace RHTower

noncomputable section

/-- Forbidden/source entry of a globally scaled physical regular BM connection mode. -/
def d4BMXiPhysicalJostRegularOuterSource
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  c * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
    (d4BMXiMixedHorizonAngularMomentum q)

/-- Normalizable entry written with the literal Birmingham--Mokhtari Gamma/Jost coefficient. -/
def d4BMXiPhysicalJostRegularOuterResponse
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  c * d4BMCausalDecayingBoundaryCoefficient
    (d4BMCausalPlusPlusFrequency n (d4BMXiMixedHorizonAngularMomentum q))
    (d4BMXiMixedHorizonAngularMomentum q)

/-- Canonical matching-channel left-QNM projection of the physical Jost outer mode. -/
def d4BMXiPhysicalJostRegularLeftResponse
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiPlusPlusRegularLeftConnectionCovector n q
    (d4BMXiPhysicalJostRegularOuterSource n c q)
    (d4BMXiPhysicalJostRegularOuterResponse n c q)

/-- Canonical cross-channel left-QNM projection of the physical regular Jost outer mode. -/
def d4BMXiPhysicalJostCrossLeftResponse
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
    (d4BMXiPhysicalJostRegularOuterSource n c q)
    (d4BMXiPhysicalJostRegularOuterResponse n c q)

/-- The physical Jost entry is exactly the Wronskian/Cramer normalizable entry. -/
theorem d4BMXiPhysicalJostRegularOuterResponse_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiPhysicalJostRegularOuterResponse n c q =
      c * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
        (d4BMXiMixedHorizonAngularMomentum q) := by
  rw [d4BMXiPhysicalJostRegularOuterResponse,
    d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient_eq n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMXiMixedHorizonAngularMomentum_re_ne_zero q)]

/-- Matching biorthogonal projection erases the complete physical Gamma/Jost coefficient. -/
theorem d4BMXiPhysicalJostRegularLeftResponse_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiPhysicalJostRegularLeftResponse n c q = c := by
  rw [d4BMXiPhysicalJostRegularLeftResponse,
    d4BMXiPhysicalJostRegularOuterSource,
    d4BMXiPhysicalJostRegularOuterResponse_eq]
  exact d4BMXiSecondHarmonicCanonicalRegularLeftResponse_eq n c q

/-- The opposite canonical dual row annihilates the physical regular Jost mode. -/
theorem d4BMXiPhysicalJostCrossLeftResponse_eq_zero
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiPhysicalJostCrossLeftResponse n c q = 0 := by
  rw [d4BMXiPhysicalJostCrossLeftResponse,
    d4BMXiPhysicalJostRegularOuterSource,
    d4BMXiPhysicalJostRegularOuterResponse_eq,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_scale,
    d4BMXiPlusPlusComplementaryLeftConnectionCovector_regular_eq_zero,
    mul_zero]

/-- Outer source coordinate of an arbitrary exact two-channel connection state. -/
def d4BMXiMixedConnectionOuterSource
    (n : ℕ) (cR cC : ℂ) (q : XiZeroCopy) : ℂ :=
  cR * d4BMPlusPlusRegularAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q) +
    cC * d4BMPlusPlusComplementaryAdSForbiddenConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q)

/-- Outer normalizable/response coordinate of an arbitrary exact two-channel connection state. -/
def d4BMXiMixedConnectionOuterResponse
    (n : ℕ) (cR cC : ℂ) (q : XiZeroCopy) : ℂ :=
  cR * d4BMPlusPlusRegularAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q) +
    cC * d4BMPlusPlusComplementaryAdSNormalizableConnectionCoefficient n
      (d4BMXiMixedHorizonAngularMomentum q)

/-- The regular dual row recovers exactly the regular input coordinate of every mixed state. -/
theorem d4BMXiRegularLeftConnectionCovector_mixed_eq
    (n : ℕ) (cR cC : ℂ) (q : XiZeroCopy) :
    d4BMXiPlusPlusRegularLeftConnectionCovector n q
        (d4BMXiMixedConnectionOuterSource n cR cC q)
        (d4BMXiMixedConnectionOuterResponse n cR cC q) = cR := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  unfold d4BMXiPlusPlusRegularLeftConnectionCovector
    d4BMXiMixedConnectionOuterSource d4BMXiMixedConnectionOuterResponse
  dsimp only
  apply (div_eq_iff hD).2
  ring

/-- The complementary dual row recovers exactly the complementary input coordinate. -/
theorem d4BMXiComplementaryLeftConnectionCovector_mixed_eq
    (n : ℕ) (cR cC : ℂ) (q : XiZeroCopy) :
    d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
        (d4BMXiMixedConnectionOuterSource n cR cC q)
        (d4BMXiMixedConnectionOuterResponse n cR cC q) = cC := by
  have hD := d4BMXiPlusPlusAdSConnectionDet_ne_zero n q
  unfold d4BMXiPlusPlusComplementaryLeftConnectionCovector
    d4BMXiMixedConnectionOuterSource d4BMXiMixedConnectionOuterResponse
  dsimp only
  apply (div_eq_iff hD).2
  ring

/-- Reflected Peierls current corrected by the canonical physical-Jost left response. -/
def d4BMXiPhysicalJostRegularLeftResponseCurrent
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) : ℂ :=
  d4BMXiSecondHarmonicPeierlsResponseCorrectedReflectionCurrent n
    (d4BMXiPhysicalJostRegularLeftResponse n c) q

/-- Physical-Jost left response is the divisor-independent scalar correction. -/
theorem d4BMXiPhysicalJostRegularLeftResponse_fun_eq
    (n : ℕ) (c : ℂ) :
    d4BMXiPhysicalJostRegularLeftResponse n c =
      d4BMXiSecondHarmonicSourceIndependentResponseCorrection c := by
  funext q
  rw [d4BMXiPhysicalJostRegularLeftResponse_eq]
  rfl

/-- The physical-Jost-corrected current is exactly the existing scalar-response current. -/
theorem d4BMXiPhysicalJostRegularLeftResponseCurrent_eq
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiPhysicalJostRegularLeftResponseCurrent n c q =
      d4BMXiSecondHarmonicSourceIndependentResponseCurrent n c q := by
  rw [d4BMXiPhysicalJostRegularLeftResponseCurrent,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent,
    d4BMXiPhysicalJostRegularLeftResponse_fun_eq]

/-- Local route classification: zero input is blind; nonzero input retains exactly the wall. -/
theorem d4BMXiPhysicalJostRegularLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) (q : XiZeroCopy) :
    d4BMXiPhysicalJostRegularLeftResponseCurrent n c q = 0 ↔
      c = 0 ∨ (q.1 : ℂ).re = 1 / 2 := by
  rw [d4BMXiPhysicalJostRegularLeftResponseCurrent_eq,
    d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff]

/-- Global route classification: nonzero physical-Jost response remains exactly the RH receiver. -/
theorem forall_d4BMXiPhysicalJostRegularLeftResponseCurrent_eq_zero_iff
    (n : ℕ) (c : ℂ) :
    (∀ q : XiZeroCopy,
      d4BMXiPhysicalJostRegularLeftResponseCurrent n c q = 0) ↔
      c = 0 ∨ RiemannHypothesis := by
  simpa only [d4BMXiPhysicalJostRegularLeftResponseCurrent_eq] using
    forall_d4BMXiSecondHarmonicSourceIndependentResponseCurrent_eq_zero_iff n c

/-- Closed route-class statement. Physical Gamma/Jost normalization and the full coefficient-linear
two-channel connection matrix disappear under canonical biorthogonal extraction; a nonzero global
input leaves precisely the existing wall/RH receiver. -/
def D4HBPhysicalJostBiorthogonalNormalizationRouteKilled : Prop :=
  (∀ (n : ℕ) (c : ℂ) (q : XiZeroCopy),
    d4BMXiPhysicalJostRegularLeftResponse n c q = c) ∧
  (∀ (n : ℕ) (c : ℂ) (q : XiZeroCopy),
    d4BMXiPhysicalJostCrossLeftResponse n c q = 0) ∧
  (∀ (n : ℕ) (cR cC : ℂ) (q : XiZeroCopy),
    d4BMXiPlusPlusRegularLeftConnectionCovector n q
        (d4BMXiMixedConnectionOuterSource n cR cC q)
        (d4BMXiMixedConnectionOuterResponse n cR cC q) = cR ∧
      d4BMXiPlusPlusComplementaryLeftConnectionCovector n q
        (d4BMXiMixedConnectionOuterSource n cR cC q)
        (d4BMXiMixedConnectionOuterResponse n cR cC q) = cC) ∧
  (∀ (n : ℕ) (c : ℂ) (q : XiZeroCopy),
    d4BMXiPhysicalJostRegularLeftResponseCurrent n c q = 0 ↔
      c = 0 ∨ (q.1 : ℂ).re = 1 / 2) ∧
  (∀ (n : ℕ) (c : ℂ),
    (∀ q : XiZeroCopy,
      d4BMXiPhysicalJostRegularLeftResponseCurrent n c q = 0) ↔
      c = 0 ∨ RiemannHypothesis)

/-- Premise-free HB physical-Jost biorthogonal-normalization route kill. -/
theorem d4HBPhysicalJostBiorthogonalNormalizationRouteKilled :
    D4HBPhysicalJostBiorthogonalNormalizationRouteKilled := by
  refine ⟨d4BMXiPhysicalJostRegularLeftResponse_eq,
    d4BMXiPhysicalJostCrossLeftResponse_eq_zero, ?_,
    d4BMXiPhysicalJostRegularLeftResponseCurrent_eq_zero_iff,
    forall_d4BMXiPhysicalJostRegularLeftResponseCurrent_eq_zero_iff⟩
  intro n cR cC q
  exact ⟨d4BMXiRegularLeftConnectionCovector_mixed_eq n cR cC q,
    d4BMXiComplementaryLeftConnectionCovector_mixed_eq n cR cC q⟩

end

end RHTower
