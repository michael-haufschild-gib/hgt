import GaloisForLFunctions.RHTower.ThetaCuspHawkingHorizonRedshiftPassivityEndpoint

/-!
# QNM branch-cut completion forced by a negative theta-Hawking resonance cubic

`[LITERATURE]` Black-hole QNM perturbation theory does not admit a complete pole-only spectral
expansion.  The Green-function contour decomposition contains both QNM residues and a continuous
branch-cut term; in the Pöschl--Teller model the isolated QNM sum for the first mode shift diverges.
See Lestingi--Sberna--Green, arXiv:2607.19492, Sec. IV and Sec. V.5.  The conserved Kerr QNM
bilinear form and its excitation-coefficient interpretation are due to
Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935.  Horizon absorption changes the
background at quadratic order and excites other QNMs at cubic order in the nonadiabatic regime;
see Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168.

`[FALSIFIED]` Consequently, the independent two-port Cayley blocks in
`ThetaCuspHawkingKMSCayleyScatteringMixingEndpoint` cannot by themselves be interpreted as the
full nonperturbative black-hole S-matrix.  They omit the continuum term required by the
Green-function contour and retain only discrete resonance data.

`[LEAN-PROVED]` This module proves the exact positive survivor.  Evaluate the selectively
stimulated theta resonance kernel on its canonical adjugate three-shell probe.  If its cubic is
negative, the pole-sector probe energy is strictly negative.  A full pole-plus-branch-cut
scattering output has energy

`E_full = E_pole + ‖A_cut‖²`.

Therefore full passivity forces

`‖A_cut‖² ≥ -E_pole > 0`.

Every off-critical Xi orbit eventually enters the negative chamber, so every passive full
scattering completion must then have nonzero branch-cut output on that orbit.  This proves the
"otherwise every tilted sector mixes" alternative without selecting the ad hoc Markov/Schur long
edge.  It does not assume that a QNM pole sum converges.

`[OPEN CORE]` The remaining Hawking-specific incidence theorem must derive, from the actual
Einstein--Klein--Gordon or Teukolsky Green function, that the theta three-shell pole energy is the
displayed resonance term and that its contour remainder has Hilbert norm `‖A_cut‖`.  Generic KMS,
CCR, group, inverse, or Krein laws do not identify that source coefficient.
-/

open Complex

noncomputable section

namespace RHTower

/-- Signed pole-sector energy of the source-reconstructed theta resonance on its canonical
adjugate three-shell probe. -/
def thetaCuspHawkingResonanceCanonicalProbeEnergy
    (q : XiZeroCopy) (rapidity x y z : ℝ) : ℝ :=
  let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
  symmetricThreePointLongEdgeEnergy K x y z (K x z)
    (threePointCanonicalEnergyProbeLeft K x y z)
    (threePointCanonicalEnergyProbeMiddle K x y z)
    (threePointCanonicalEnergyProbeRight K x y)

/-- Exact adjugate factorization of theta resonance probe energy. -/
theorem thetaCuspHawkingResonanceCanonicalProbeEnergy_eq_minor_mul_det
    (q : XiZeroCopy) (rapidity x y z : ℝ) :
    thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z =
      let K := thetaCuspHawkingSelectiveModularGainKernel q rapidity
      (K x x * K y y - K x y ^ 2) * symmetricThreePointDet K x y z := by
  exact symmetricThreePointLongEdgeEnergy_canonicalProbe_eq
    (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z

/-- A negative theta resonance cubic is a strictly negative pole-sector energy, before any
continuous Green-function contribution is restored. -/
theorem thetaCuspHawking_negativeCubic_forces_negativeResonanceProbeEnergy
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z < 0 := by
  exact thetaCuspHawking_negativeCubic_forces_negativeCanonicalEnergy
    q rapidity hx hxy hyz hnegative

/-- Full probe energy after restoring the continuous Green-function output.  `continuumOutput`
is deliberately a vector in an arbitrary normed additive group: no pole-basis completeness or
finite-dimensional truncation is assumed. -/
def thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
    {H : Type*} [Norm H]
    (q : XiZeroCopy) (rapidity x y z : ℝ) (continuumOutput : H) : ℝ :=
  thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z +
    ‖continuumOutput‖ ^ 2

/-- Exact optical lower bound: passive full scattering must pay at least the entire signed
pole-sector energy debt into the branch-cut channel. -/
theorem thetaCuspHawking_passiveFullScattering_branchCutNormSq_lower
    {H : Type*} [Norm H]
    (q : XiZeroCopy) (rapidity x y z : ℝ) (continuumOutput : H)
    (hpassive : 0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
      q rapidity x y z continuumOutput) :
    -thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z ≤
      ‖continuumOutput‖ ^ 2 := by
  unfold thetaCuspHawkingPoleBranchCutCompletedProbeEnergy at hpassive
  linarith

/-- Theta-specific passivity exclusion: a negative resonance cubic cannot be the whole passive
scattering output; the continuous channel has strictly positive energy on the canonical probe. -/
theorem thetaCuspHawking_negativeCubic_forces_positiveBranchCutEnergy
    {H : Type*} [Norm H]
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ} (continuumOutput : H)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (hpassive : 0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
      q rapidity x y z continuumOutput) :
    0 < ‖continuumOutput‖ ^ 2 := by
  have hresonance :=
    thetaCuspHawking_negativeCubic_forces_negativeResonanceProbeEnergy
      q rapidity hx hxy hyz hnegative
  unfold thetaCuspHawkingPoleBranchCutCompletedProbeEnergy at hpassive
  linarith

/-- A passive completion of a negative theta resonance cubic must genuinely mix with the
continuous channel. -/
theorem thetaCuspHawking_negativeCubic_forces_nonzeroBranchCutOutput
    {H : Type*} [NormedAddCommGroup H]
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ} (continuumOutput : H)
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0)
    (hpassive : 0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
      q rapidity x y z continuumOutput) :
    continuumOutput ≠ 0 := by
  have hcut := thetaCuspHawking_negativeCubic_forces_positiveBranchCutEnergy
    q rapidity continuumOutput hx hxy hyz hnegative hpassive
  intro hzero
  subst continuumOutput
  simp at hcut

/-- Pole-only Cayley completion is impossible in a negative cubic chamber: setting the continuum
output to zero contradicts passivity. -/
theorem thetaCuspHawking_negativeCubic_excludes_passivePoleOnlyCompletion
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    ¬ 0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
      q rapidity x y z (0 : ℂ) := by
  intro hpassive
  have hnonzero := thetaCuspHawking_negativeCubic_forces_nonzeroBranchCutOutput
    q rapidity (0 : ℂ) hx hxy hyz hnegative hpassive
  exact hnonzero rfl

/-- **All-tilted-sector branch-cut necessity.** Every off-critical Xi orbit eventually forces
nonzero continuum output in every passive full scattering completion, on every fixed ordered
positive three-shell probe. -/
theorem exists_eventually_thetaCuspHawking_offCritical_forces_branchCutMixing
    {H : Type*} [NormedAddCommGroup H]
    (q : XiZeroCopy) (hoff : (q.1 : ℂ).re ≠ 1 / 2)
    {x y z : ℝ} (hx : 0 < x) (hxy : x < y) (hyz : y < z) :
    ∃ R : ℝ, ∀ rapidity : ℝ, R ≤ rapidity →
      ∀ continuumOutput : H,
        0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
          q rapidity x y z continuumOutput →
        0 < ‖continuumOutput‖ ^ 2 ∧ continuumOutput ≠ 0 := by
  obtain ⟨R, hR⟩ :=
    exists_eventually_negative_thetaCuspHawkingSelectiveModularGainKernel_threePointDet
      q hoff hx hxy hyz
  refine ⟨R, ?_⟩
  intro rapidity hrapidity continuumOutput hpassive
  have hnegative := hR rapidity hrapidity
  exact ⟨
    thetaCuspHawking_negativeCubic_forces_positiveBranchCutEnergy
      q rapidity continuumOutput hx hxy hyz hnegative hpassive,
    thetaCuspHawking_negativeCubic_forces_nonzeroBranchCutOutput
      q rapidity continuumOutput hx hxy hyz hnegative hpassive⟩

end RHTower
