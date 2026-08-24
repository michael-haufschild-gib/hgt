import GaloisForLFunctions.RHTower.ThetaCuspHawkingHorizonRedshiftPassivityEndpoint

/-!
# QNM category wall and branch-cut completion forced by a negative theta-Hawking cubic

`[LITERATURE]` Black-hole QNM perturbation theory does not admit a complete pole-only spectral
expansion.  The Green-function contour decomposition contains both QNM residues and a continuous
branch-cut term; in the Pöschl--Teller model the isolated QNM sum for the first mode shift diverges.
See Lestingi--Sberna--Green, arXiv:2607.19492, Sec. IV and Sec. V.5.  The conserved Kerr QNM
bilinear form and its excitation-coefficient interpretation are due to
Green--Hollands--Sberna--Toomani--Zimmerman, arXiv:2210.15935.  Horizon absorption changes the
background at quadratic order and excites other QNMs at cubic order in the nonadiabatic regime;
see Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168.

`[CATEGORY WALL]` A zero of the theta moving-mirror Born numerator is a transmission/dark zero;
a black-hole QNM is a pole of a retarded Green function.  The cited QNM contour theory does not
identify these objects.  No theorem below calls an Xi zero a QNM pole.  Such an identification
would require a new Jost/Evans incidence theorem and cannot be imported by terminology.

`[FALSIFIED]` Independently of that category wall, the exact theta-mirror second-jet theorem in
`ThetaCuspHawkingFullMirrorCayleyNoGo` proves that independent two-port Cayley blocks cannot be the
full nonperturbative theta-mirror S-matrix: exact dynamics has a nonzero even coupling jet, while
the Cayley transition is odd.  Black-hole QNM contour theory supplies a separate reason that a
pole-only completion would also be incomplete in the genuine black-hole perturbation problem.

`[FALSIFIED PHYSICAL IDENTIFICATION]` This module evaluated the selectively stimulated theta
kernel on its canonical adjugate three-shell probe.  If its cubic is negative, that source-side
probe form is strictly negative.  It then *defined* a pole-plus-branch-cut ansatz

`E_full = E_pole + ‖A_cut‖²`.

Within that definition, nonnegativity algebraically forces

`‖A_cut‖² ≥ -E_pole > 0`.

That ansatz is not the Teukolsky optical energy.  QNM residues, the direct arc, and the branch-cut
tail are not positive orthogonal Hilbert channels; their quadratic energy contains interference
terms, and ordinary QNM profiles are not finite-energy vectors on standard slices.  Consequently
the theorems below are retained only as conditional algebra inside the displayed definition.  They
do not prove physical branch-cut mixing.

`[CATEGORY CLOSED NEGATIVELY]` `ThetaCuspHawkingSchwarzschildJostIncidenceNoGo` constructs the
actual real-axis Schwarzschild Jost normal form and proves the correct incidence.  The theta
divisor coordinate `w + i a` uses real physical frequency `w` and source tilt `a`; the homogeneous
Evans denominator is evaluated at `w`, where conserved flux makes it nonzero.  Xi vanishes in the
source numerator, so divisor points are scattering zeros, not QNM poles.  The actual optical
identity is the real-axis infinity-plus-horizon greybody split.  Generic KMS, CCR, group, inverse,
or Krein laws cannot turn this source zero into a pole or exclude it.
-/

open Complex

noncomputable section

namespace RHTower

/-- Signed candidate discrete-sector energy of the source-reconstructed theta response on its
canonical adjugate three-shell probe.  No QNM-pole interpretation is built into this definition. -/
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

/-- A negative theta cubic is a strictly negative candidate discrete-sector energy, before any
conditional continuous Green-function contribution is restored. -/
theorem thetaCuspHawking_negativeCubic_forces_negativeResonanceProbeEnergy
    (q : XiZeroCopy) (rapidity : ℝ) {x y z : ℝ}
    (hx : 0 < x) (hxy : x < y) (hyz : y < z)
    (hnegative : symmetricThreePointDet
      (thetaCuspHawkingSelectiveModularGainKernel q rapidity) x y z < 0) :
    thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z < 0 := by
  exact thetaCuspHawking_negativeCubic_forces_negativeCanonicalEnergy
    q rapidity hx hxy hyz hnegative

/-- Algebraic pole-plus-cut energy ansatz retained for compatibility.  This is not the energy of
the Teukolsky contour decomposition: it omits the direct arc and every interference term. -/
def thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
    {H : Type*} [Norm H]
    (q : XiZeroCopy) (rapidity x y z : ℝ) (continuumOutput : H) : ℝ :=
  thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z +
    ‖continuumOutput‖ ^ 2

/-- Conditional lower bound inside the preceding algebraic ansatz.  It is not a Teukolsky optical
theorem. -/
theorem thetaCuspHawking_passiveFullScattering_branchCutNormSq_lower
    {H : Type*} [Norm H]
    (q : XiZeroCopy) (rapidity x y z : ℝ) (continuumOutput : H)
    (hpassive : 0 ≤ thetaCuspHawkingPoleBranchCutCompletedProbeEnergy
      q rapidity x y z continuumOutput) :
    -thetaCuspHawkingResonanceCanonicalProbeEnergy q rapidity x y z ≤
      ‖continuumOutput‖ ^ 2 := by
  unfold thetaCuspHawkingPoleBranchCutCompletedProbeEnergy at hpassive
  linarith

/-- Conditional consequence of declaring the falsified ansatz nonnegative. -/
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

/-- Conditional nonvanishing inside the algebraic ansatz; no physical QNM/cut incidence is
asserted. -/
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

/-- Setting the auxiliary output to zero contradicts nonnegativity of the algebraic ansatz.  This
does not exclude a physical pole-only approximation. -/
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

/-- **Conditional all-sector statement.** Every off-critical orbit eventually forces nonzero
auxiliary output if the falsified pole-plus-cut ansatz is imposed on a fixed ordered probe. -/
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
