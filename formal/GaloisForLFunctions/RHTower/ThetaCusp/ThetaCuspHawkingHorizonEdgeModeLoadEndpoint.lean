import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBackreactionRecoveryChamberEndpoint

/-!
# Theta-Hawking horizon edge-mode load

Second-order gravitational backreaction on a stationary black-hole horizon does not only perturb
its total area.  The complete horizon constraint carries angle-dependent boost-supertranslation
charges and corresponding edge modes.  Their Hilbert-space covariance contribution must be
positive semidefinite.  See Klinger--Kudler-Flam--Satishchandran, arXiv:2601.07910.

That physical fact obstructs a tempting interpretation of the preceding canonical cubic
completion.  The Markov/Petz edge

`K_xz^* = K_xy K_yz / K_yy`

changes only the remote covariance while preserving all three diagonal responses.  A nonzero
positive additive edge-mode covariance cannot do this: positivity of its `x,z` principal minor
forces positive self-energy load at both endpoints whenever its remote entry is nonzero.

For the literal theta-cusp Hawking kernel, a negative raw cubic already proves
`K_xz != K_xz^*`.  Therefore every positive additive gravitational sector which reaches the
canonical completion must change both endpoint diagonals.  Off the critical line this load is
eventually forced at every sufficiently large Hawking rapidity, including in the source-reconstructed
causal Hardy scattering channel.

This is a no-go for identifying the long-edge-only Cayley/Petz completion with full nonlinear
black-hole backreaction.  It is also a positive survivor: genuine horizon dressing must renormalize
sector self-energies, not merely insert a remote edge.  Generic KMS, CCR, inverse, group, and Krein
identities do not supply this conclusion; the strict nonzero remote correction comes from the
theta-divisor negative cubic, while covariance positivity is the gravitational edge-mode input.
-/

namespace RHTower

noncomputable section

/-- Necessary `x,z` principal-minor condition for an additive horizon edge-mode covariance. -/
def HorizonEdgeModeTwoPointPositive
    (E : ℝ → ℝ → ℝ) (x z : ℝ) : Prop :=
  0 ≤ E x x ∧ 0 ≤ E z z ∧ 0 ≤ E x x * E z z - E x z ^ (2 : ℕ)

/-- A nonzero remote covariance in a positive additive edge sector forces strictly positive
self-energy load at both endpoints. -/
theorem horizonEdgeMode_remote_ne_zero_forces_endpointLoads_pos
    (E : ℝ → ℝ → ℝ) {x z : ℝ}
    (hE : HorizonEdgeModeTwoPointPositive E x z)
    (hremote : E x z ≠ 0) :
    0 < E x x ∧ 0 < E z z := by
  rcases hE with ⟨hxx, hzz, hminor⟩
  have hsquare : 0 < E x z ^ (2 : ℕ) := sq_pos_of_ne_zero hremote
  have hproduct : 0 < E x x * E z z := by
    nlinarith
  rcases (mul_pos_iff.mp hproduct) with hpositive | hnegative
  · exact hpositive
  · exact False.elim ((not_lt_of_ge hxx) hnegative.1)

/-- Consequently, a positive additive edge sector with even one zero endpoint load has zero remote
covariance. -/
theorem horizonEdgeMode_zero_leftEndpointLoad_forces_remote_zero
    (E : ℝ → ℝ → ℝ) {x z : ℝ}
    (hE : HorizonEdgeModeTwoPointPositive E x z)
    (hxx : E x x = 0) :
    E x z = 0 := by
  by_contra hremote
  have hloads :=
    horizonEdgeMode_remote_ne_zero_forces_endpointLoads_pos E hE hremote
  rw [hxx] at hloads
  exact (lt_irrefl 0) hloads.1

/-- Theta-specific load law.  Negative raw cubic makes the canonical remote correction nonzero;
positive gravitational covariance then forces both endpoint self-energies to change. -/
theorem thetaCuspHawking_negativeCubic_positiveEdgeMode_forces_endpointLoads_pos
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (E : ℝ → ℝ → ℝ)
    (hE : HorizonEdgeModeTwoPointPositive E x z)
    (hcompletion :
      thetaCuspHawkingSelectiveModularGainKernel q rapidity x z + E x z =
        thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) :
    0 < E x x ∧ 0 < E z z := by
  have hraw_ne :
      thetaCuspHawkingSelectiveModularGainKernel q rapidity x z ≠
        thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z :=
    thetaCuspHawking_negativeCubic_forces_backreaction_mixing
      q rapidity hx hxy hyz hnegative
  have hremote : E x z ≠ 0 := by
    intro hzero
    apply hraw_ne
    simpa [hzero] using hcompletion
  exact horizonEdgeMode_remote_ne_zero_forces_endpointLoads_pos E hE hremote

/-- No positive gravitational edge covariance can realize the theta canonical completion while
preserving both endpoint variances in a negative raw chamber. -/
theorem thetaCuspHawking_negativeCubic_no_diagonalPreserving_positiveEdgeCompletion
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (E : ℝ → ℝ → ℝ)
    (hE : HorizonEdgeModeTwoPointPositive E x z)
    (hcompletion :
      thetaCuspHawkingSelectiveModularGainKernel q rapidity x z + E x z =
        thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z) :
    ¬ (E x x = 0 ∧ E z z = 0) := by
  intro hzero
  have hloads :=
    thetaCuspHawking_negativeCubic_positiveEdgeMode_forces_endpointLoads_pos
      q rapidity hx hxy hyz hnegative E hE hcompletion
  rw [hzero.1] at hloads
  exact (lt_irrefl 0) hloads.1

/-- Source-reconstructed causal-Hardy specialization of the horizon load law. -/
theorem thetaCuspHawkingCausalHardy_negativeCubic_positiveEdgeMode_forces_endpointLoads_pos
    (q : XiZeroCopy)
    (mode : ThetaCuspHawkingBackreactionResonantMode)
    (hmode : 0 < mode.1.im)
    (horient : mode = thetaCuspHawkingXiOrbitResonantMode q ∨
      mode = thetaCuspHawkingBackreactionReflectedResonantMode
        (thetaCuspHawkingXiOrbitResonantMode q))
    (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity) x y z < 0)
    (E : ℝ → ℝ → ℝ)
    (hE : HorizonEdgeModeTwoPointPositive E x z)
    (hcompletion :
      thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity x z + E x z =
        thetaCuspHawkingCausalHardyPassiveBackreactionEdge
          mode hmode rapidity x y z) :
    0 < E x x ∧ 0 < E z z := by
  have hraw_ne :
      thetaCuspHawkingCausalHardyStimulatedKernel mode hmode rapidity x z ≠
        thetaCuspHawkingCausalHardyPassiveBackreactionEdge
          mode hmode rapidity x y z :=
    thetaCuspHawkingCausalHardy_negativeCubic_forces_backreaction_mixing
      q mode hmode horient rapidity hx hxy hyz hnegative
  have hremote : E x z ≠ 0 := by
    intro hzero
    apply hraw_ne
    simpa [hzero] using hcompletion
  exact horizonEdgeMode_remote_ne_zero_forces_endpointLoads_pos E hE hremote

/-- Every hypothetical off-line theta divisor eventually forces endpoint self-energy load in any
positive additive horizon sector which reaches the canonical completion. -/
theorem exists_thetaCuspHawking_eventually_everyPositiveEdgeCompletion_loadsEndpoints
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ rapidity : ℝ, R ≤ rapidity →
      ∀ E : ℝ → ℝ → ℝ,
        HorizonEdgeModeTwoPointPositive E x z →
        thetaCuspHawkingSelectiveModularGainKernel q rapidity x z + E x z =
          thetaCuspHawkingPassiveBackreactionEdge q rapidity x y z →
        0 < E x x ∧ 0 < E z z := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, fun rapidity hrapidity E hE hcompletion => ?_⟩
  exact thetaCuspHawking_negativeCubic_positiveEdgeMode_forces_endpointLoads_pos
    q rapidity hx hxy hyz (hR rapidity hrapidity) E hE hcompletion

end

end RHTower
