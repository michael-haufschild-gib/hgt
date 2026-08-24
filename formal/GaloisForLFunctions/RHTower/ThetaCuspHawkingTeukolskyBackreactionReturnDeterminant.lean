import GaloisForLFunctions.RHTower.ThetaCuspHawkingTopologicalBlackHoleHypergeometricJostIncidence
import GaloisForLFunctions.HTGeometry.InvolutiveProjectiveWedgeTransportLaw

/-!
# Nonlinear chiral Teukolsky backreaction return determinant

This module isolates the first source-specific gravitational producer beyond the scalar
topological-black-hole no-go.  It keeps four logically distinct layers separate.

## Exact gravitational input

Birmingham--Mokhtari, *Exact Gravitational Quasinormal Frequencies of Topological Black Holes*,
arXiv:hep-th/0609028, derive the Kodama--Ishibashi scalar and vector potentials and solve the
massless (`M=0`) problem hypergeometrically.  In `d=4` both gravitational parities have `beta=0`.
For a Hodge-paired scalar/coexact-vector harmonic on the curvature `-1` horizon,

`k_V^2 = k_S^2 + 1`, hence `Q_V = k_V^2-1 = k_S^2 = Q_S`.

Their forbidden-boundary coefficient is therefore exactly the preceding physical Gamma-product
Jost function.  Xi-divisor descendants are simple gravitational Jost zeros and inverse-Green
poles, not Jost poles.

Specializing their full potentials (Eqs. (10)--(13)) to `d=4`, writing
`x=omega_4 M/r`, `u=r^2/l^2`, and `Q=Q_S=Q_V`, gives the scalar numerator and vector bracket
formalized below.  Their first mass-coordinate split at `x=0` is

`d/dx (B_S-B_V)|_0 = 12/(Q+2)`.

On the physical theta/hyperbolic continuum `Q=1/4+xi^2`, this is strictly positive.  Multiplying
by normalized absorbed horizon flux `|A_H|^2` therefore excludes a negative radial cubic kernel
without KMS, CCR, Krein, or generic passivity.

## Helicity phase and its no-go

Sberna--Bosch--East--Green--Lehner, arXiv:2112.11168, use the analytically continued
Schwarzschild Teukolsky--Starobinsky constant

`C(M,E,omega)=E(E-2)+12 i M omega`.

On the two exact topological QNM branches its difference is `24 i M xi`: shadow odd, but nonzero
at every actual Xi divisor when `M != 0`.  Thus the bare helicity phase is not an RH selector.

## Genuine return determinant

Freeze frequency and let `J_0` be the branch-resolved ingoing/Dirichlet Jost factor.  For an exact
finite-backreacted returned Jost channel `J_ret` (or its infinitesimal mass jet), define

`R(z)=J_ret(z) J_0(tau z)-J_0(z) J_ret(tau z)`.

This determinant-line object is shadow odd.  At a plus-branch divisor QNM, `J_0(z)=0` and
`J_0(tau z) != 0`, so `R != 0` exactly when the returned channel is nonzero.  Writing
`J_ret = horizonPhase * J_0 + crossSource` proves that an arbitrary multiplicative horizon phase
cannot move the incidence: the additive cross-helicity source is the exact and only producer.

The Cayley completion `S=(1+R)/(1-R)` is fully nonperturbative and obeys
`S(tau z)=S(z)^{-1}`.  At every divisor it is nontrivial exactly when the cross source is nonzero.

## Remaining open dynamics

The actual `J_ret` must still be derived from the second-order Einstein/Teukolsky source and the
horizon-absorbed mass/spin history.  Green--Hollands--Sberna--Toomani--Zimmerman,
arXiv:2210.15935, identify the QNM residue normalization with `dW/domega` and a conserved complex
bilinear form; they do not prove a positive QNM completeness theorem.  AIME's AdS contour also
discards the direct large-frequency arc, while asymptotically flat Teukolsky Green functions have
a branch cut.  Consequently no discrete-plus-continuum optical-energy identity is assumed here.
Deriving that identity and proving its cross-helicity term is nonzero precisely in tilted sectors
is the remaining RH-bearing PDE statement.

**[LITERATURE-FORMALIZED] [PAPER-PROVED] [LEAN-PROVED]** Exact gravitational Jost incidence,
potential first variation, physical radial-kernel sign, Starobinsky phase no-go, determinant-line
incidence, and Cayley mirror law.

**[OPEN CORE]** Nonlinear Einstein/Teukolsky construction of `J_ret`, including direct/continuum
terms, and its theta-specific optical identity.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Birmingham--Mokhtari's `d=4` scalar-potential numerator after setting
`mu=Q+2`, `x=omega_4 M/r`, and `u=r^2/l^2`. -/
def d4ScalarU (Q x u : ℝ) : ℝ :=
  288 * u * x ^ 2 + 144 * x ^ 3 + 144 * (Q + 2) * x ^ 2 +
    48 * (Q + 2) ^ 2 * x + 16 * (Q + 2) ^ 2 * Q

/-- Dimensionless bracket in the exact `d=4` scalar gravitational potential. -/
def d4ScalarBracket (Q x u : ℝ) : ℝ :=
  d4ScalarU Q x u / (16 * ((Q + 2) + 3 * x) ^ 2)

/-- Dimensionless bracket in the exact `d=4` vector gravitational potential. -/
def d4VectorBracket (Q x : ℝ) : ℝ := Q - 3 * x

lemma d4ScalarBracket_zero {Q u : ℝ} (hQ : Q + 2 ≠ 0) :
    d4ScalarBracket Q 0 u = Q := by
  unfold d4ScalarBracket d4ScalarU
  field_simp [hQ]
  ring

lemma hasDerivAt_d4ScalarU_zero (Q u : ℝ) :
    HasDerivAt (fun x : ℝ => d4ScalarU Q x u) (48 * (Q + 2) ^ 2) 0 := by
  have h1 : HasDerivAt (fun x : ℝ => x) 1 0 := hasDerivAt_id 0
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2) 0 0 := by
    have h := h1.pow 2
    change HasDerivAt (fun x : ℝ => x ^ 2) (2 * 0 ^ (2 - 1) * 1) 0 at h
    norm_num at h
    exact h
  have h3 : HasDerivAt (fun x : ℝ => x ^ 3) 0 0 := by
    have h := h1.pow 3
    change HasDerivAt (fun x : ℝ => x ^ 3) (3 * 0 ^ (3 - 1) * 1) 0 at h
    norm_num at h
    exact h
  have h := (((((h2.const_mul (288 * u)).add (h3.const_mul 144)).add
      (h2.const_mul (144 * (Q + 2)))).add
      (h1.const_mul (48 * (Q + 2) ^ 2))).add
      (hasDerivAt_const (x := (0 : ℝ)) (16 * (Q + 2) ^ 2 * Q)))
  change HasDerivAt (fun x : ℝ => d4ScalarU Q x u) _ 0 at h
  convert h using 1
  all_goals ring

lemma hasDerivAt_d4ScalarBracket_zero {Q u : ℝ} (hQ : Q + 2 ≠ 0) :
    HasDerivAt (fun x : ℝ => d4ScalarBracket Q x u)
      (3 * (2 - Q) / (Q + 2)) 0 := by
  have hnum := hasDerivAt_d4ScalarU_zero Q u
  have hinner : HasDerivAt (fun x : ℝ => (Q + 2) + 3 * x) 3 0 := by
    have h := (hasDerivAt_const (x := (0 : ℝ)) (Q + 2)).add
      ((hasDerivAt_id (0 : ℝ)).const_mul 3)
    change HasDerivAt (fun x : ℝ => (Q + 2) + 3 * x) (0 + 3 * 1) 0 at h
    convert h using 1
    all_goals norm_num
  have hden : HasDerivAt (fun x : ℝ => 16 * ((Q + 2) + 3 * x) ^ 2)
      (96 * (Q + 2)) 0 := by
    have h := (hinner.pow 2).const_mul 16
    change HasDerivAt (fun x : ℝ => 16 * ((Q + 2) + 3 * x) ^ 2) _ 0 at h
    convert h using 1
    all_goals ring
  have hden0 : 16 * ((Q + 2) + 3 * (0 : ℝ)) ^ 2 ≠ 0 := by
    norm_num [hQ]
  have hquot := hnum.div hden hden0
  change HasDerivAt (fun x : ℝ => d4ScalarBracket Q x u) _ 0 at hquot
  convert hquot using 1
  simp only [d4ScalarU]
  field_simp [hQ]
  ring

lemma hasDerivAt_d4VectorBracket_zero (Q : ℝ) :
    HasDerivAt (fun x : ℝ => d4VectorBracket Q x) (-3) 0 := by
  unfold d4VectorBracket
  have h := (hasDerivAt_const (x := (0 : ℝ)) Q).sub
    ((hasDerivAt_id (0 : ℝ)).const_mul 3)
  change HasDerivAt (fun x : ℝ => Q - 3 * x) (0 - 3 * 1) 0 at h
  norm_num at h
  exact h

/-- Exact first mass-coordinate splitting of Hodge-paired scalar/vector potentials. -/
theorem hasDerivAt_d4ParitySplit_zero {Q u : ℝ} (hQ : Q + 2 ≠ 0) :
    HasDerivAt (fun x : ℝ => d4ScalarBracket Q x u - d4VectorBracket Q x)
      (12 / (Q + 2)) 0 := by
  have h := (hasDerivAt_d4ScalarBracket_zero (u := u) hQ).sub
    (hasDerivAt_d4VectorBracket_zero Q)
  change HasDerivAt
    (fun x : ℝ => d4ScalarBracket Q x u - d4VectorBracket Q x) _ 0 at h
  convert h using 1
  field_simp [hQ]
  ring

/-- Source-specific chiral first-variation kernel. -/
def d4BackreactionSplit (Q : ℝ) : ℝ := 12 / (Q + 2)

lemma d4BackreactionSplit_pos {Q : ℝ} (hQ : 0 ≤ Q) :
    0 < d4BackreactionSplit Q := by
  exact div_pos (by norm_num) (by linarith)

/-- Physical hyperbolic/theta-continuum angular eigenvalue. -/
def d4ThetaPhysicalAngularQ (xi : ℝ) : ℝ := 1 / 4 + xi ^ 2

lemma d4ThetaPhysicalAngularQ_nonneg (xi : ℝ) :
    0 ≤ d4ThetaPhysicalAngularQ xi := by
  unfold d4ThetaPhysicalAngularQ
  positivity

lemma d4ThetaBackreactionSplit_eq (xi : ℝ) :
    d4BackreactionSplit (d4ThetaPhysicalAngularQ xi) =
      48 / (9 + 4 * xi ^ 2) := by
  have hleft : 9 / 4 + xi ^ 2 ≠ 0 := by positivity
  have hright : 9 + 4 * xi ^ 2 ≠ 0 := by positivity
  unfold d4BackreactionSplit d4ThetaPhysicalAngularQ
  field_simp [hleft, hright]
  ring

lemma d4ThetaBackreactionSplit_pos (xi : ℝ) :
    0 < d4BackreactionSplit (d4ThetaPhysicalAngularQ xi) :=
  d4BackreactionSplit_pos (d4ThetaPhysicalAngularQ_nonneg xi)

/-- Normalized cubic radial kernel: quadratic horizon absorption times linear parity response. -/
def d4ThetaNormalizedAbsorptionCubicRadialKernel
    (xi horizonAmplitude : ℝ) : ℝ :=
  horizonAmplitude ^ 2 * d4BackreactionSplit (d4ThetaPhysicalAngularQ xi)

/-- Exact exclusion of the negative physical radial chamber. -/
theorem d4ThetaNormalizedAbsorptionCubicRadialKernel_nonneg
    (xi horizonAmplitude : ℝ) :
    0 ≤ d4ThetaNormalizedAbsorptionCubicRadialKernel xi horizonAmplitude := by
  exact mul_nonneg (sq_nonneg horizonAmplitude)
    (le_of_lt (d4ThetaBackreactionSplit_pos xi))

theorem d4ThetaNormalizedAbsorptionCubicRadialKernel_not_neg
    (xi horizonAmplitude : ℝ) :
    ¬d4ThetaNormalizedAbsorptionCubicRadialKernel xi horizonAmplitude < 0 :=
  not_lt_of_ge (d4ThetaNormalizedAbsorptionCubicRadialKernel_nonneg xi horizonAmplitude)

theorem d4ThetaNormalizedAbsorptionCubicRadialKernel_pos_iff
    (xi horizonAmplitude : ℝ) :
    0 < d4ThetaNormalizedAbsorptionCubicRadialKernel xi horizonAmplitude ↔
      horizonAmplitude ≠ 0 := by
  rw [d4ThetaNormalizedAbsorptionCubicRadialKernel, mul_pos_iff]
  constructor
  · rintro (hpos | hneg)
    · exact (sq_pos_iff).mp hpos.1
    · exact False.elim ((not_lt_of_ge (sq_nonneg horizonAmplitude)) hneg.1)
  · intro hamp
    exact Or.inl ⟨(sq_pos_iff).mpr hamp, d4ThetaBackreactionSplit_pos xi⟩

/-- For a Hodge-paired coexact vector harmonic on a curvature `-1` surface,
the rough vector-Laplacian eigenvalue is `k_V^2 = k_S^2 + 1`. -/
def d4HyperbolicHodgePairedVectorEigenvalue (scalarQ : ℂ) : ℂ := scalarQ + 1

lemma d4HyperbolicHodgePairedEffectiveQ_eq (scalarQ : ℂ) :
    d4HyperbolicHodgePairedVectorEigenvalue scalarQ - 1 = scalarQ := by
  unfold d4HyperbolicHodgePairedVectorEigenvalue
  ring

/-- Literal Birmingham--Mokhtari forbidden-boundary coefficient in the paired `d=4` sector. -/
def d4GravitationalHypergeometricBoundaryJost (omega z : ℂ) : ℂ :=
  thetaCuspHawkingHypergeometricPhysicalBoundaryJost omega z

def d4GravitationalHypergeometricBoundaryGreen (omega z : ℂ) : ℂ :=
  (d4GravitationalHypergeometricBoundaryJost omega z)⁻¹

/-- Divisor descendants are simple gravitational Jost zeros. -/
theorem d4GravitationalHypergeometricBoundaryJost_order_qnmPlus_xi
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) =
        (1 : ℤ) := by
  exact thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmPlus_xi n q

/-- Inverse Green functions have simple poles at those descendants. -/
theorem d4GravitationalHypergeometricBoundaryGreen_order_qnmPlus_xi
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  exact thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmPlus_xi n q

theorem d4GravitationalHypergeometricBoundaryJost_order_qnmMinus_xi
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => d4GravitationalHypergeometricBoundaryJost omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) =
        (1 : ℤ) := by
  exact thetaCuspHawkingHypergeometricPhysicalBoundaryJost_order_qnmMinus_xi n q

theorem d4GravitationalHypergeometricBoundaryGreen_order_qnmMinus_xi
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt
      (fun omega : ℂ => d4GravitationalHypergeometricBoundaryGreen omega (xiSpectralPoint q))
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q)) =
        ((-1 : ℤ) : WithTop ℤ) := by
  exact thetaCuspHawkingHypergeometricPhysicalBoundaryGreen_order_qnmMinus_xi n q

/-- Full linear gravitational determinant remains shadow even. -/
theorem d4GravitationalHypergeometricBoundaryJost_shadow (omega z : ℂ) :
    d4GravitationalHypergeometricBoundaryJost omega
        (thetaCuspHawkingOpticalCuspShadow z) =
      d4GravitationalHypergeometricBoundaryJost omega z :=
  thetaCuspHawkingHypergeometricPhysicalBoundaryJost_shadow omega z

/-- Analytically continued Schwarzschild Teukolsky--Starobinsky constant. -/
def teukolskyStarobinskyConstant (M E omega : ℂ) : ℂ :=
  E * (E - 2) + 12 * Complex.I * M * omega

/-- Helicity-normalization difference on exact opposing QNM branches. -/
def branchStarobinskyDifference (n : ℕ) (M E z : ℂ) : ℂ :=
  teukolskyStarobinskyConstant M E
      (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z) -
    teukolskyStarobinskyConstant M E
      (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z)

lemma branchStarobinskyDifference_eq (n : ℕ) (M E z : ℂ) :
    branchStarobinskyDifference n M E z =
      24 * Complex.I * M * thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold branchStarobinskyDifference teukolskyStarobinskyConstant
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  ring

lemma branchStarobinskyDifference_shadow (n : ℕ) (M E z : ℂ) :
    branchStarobinskyDifference n M E (thetaCuspHawkingOpticalCuspShadow z) =
      -branchStarobinskyDifference n M E z := by
  rw [branchStarobinskyDifference_eq, branchStarobinskyDifference_eq,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]
  ring

lemma angularMomentum_xiSpectralPoint_ne_zero (q : XiZeroCopy) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum (xiSpectralPoint q) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  simp [thetaCuspHawkingTopologicalBlackHoleAngularMomentum] at hre
  exact thetaCuspHawkingHypergeometricXiSpectralPoint_re_ne_zero q (by linarith)

/-- Bare Starobinsky branch phase is nonzero at every divisor and therefore cannot select RH. -/
theorem branchStarobinskyDifference_xi_ne_zero
    (n : ℕ) {M : ℂ} (hM : M ≠ 0) (E : ℂ) (q : XiZeroCopy) :
    branchStarobinskyDifference n M E (xiSpectralPoint q) ≠ 0 := by
  rw [branchStarobinskyDifference_eq]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) Complex.I_ne_zero) hM)
    (angularMomentum_xiSpectralPoint_ne_zero q)

/-- Chiral Evans determinant between the massless branch Jost line and a finite returned channel.
The second component may alternatively be its infinitesimal horizon-mass jet. -/
def teukolskyReturnDeterminant (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) : ℂ :=
  GaloisForLFunctions.HTGeometry.involutiveProjectiveWedge
    thetaCuspHawkingOpticalCuspShadow
    (fun p => thetaCuspHawkingHypergeometricJostPlus omega p) returnedJost z

/-- Return determinant is theta-shadow odd. -/
lemma teukolskyReturnDeterminant_shadow
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) :
    teukolskyReturnDeterminant omega returnedJost (thetaCuspHawkingOpticalCuspShadow z) =
      -teukolskyReturnDeterminant omega returnedJost z := by
  exact GaloisForLFunctions.HTGeometry.involutiveProjectiveWedge_apply_involution
    thetaCuspHawkingOpticalCuspShadow_involutive _ _ z

/-- At a plus QNM, determinant is returned channel times the nonzero companion Jost factor. -/
lemma teukolskyReturnDeterminant_qnmPlus (n : ℕ) (q : XiZeroCopy)
    (returnedJost : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) returnedJost
        (xiSpectralPoint q) =
      returnedJost (xiSpectralPoint q) *
        thetaCuspHawkingHypergeometricJostMinus
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          (xiSpectralPoint q) := by
  rw [teukolskyReturnDeterminant,
    GaloisForLFunctions.HTGeometry.involutiveProjectiveWedge,
    thetaCuspHawkingHypergeometricJostPlus_shadow,
    thetaCuspHawkingHypergeometricJostPlus_qnm_zero, zero_mul, sub_zero]

/-- Exact returned-channel incidence at every actual divisor. -/
lemma teukolskyReturnDeterminant_qnmPlus_ne_zero_iff (n : ℕ) (q : XiZeroCopy)
    (returnedJost : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) returnedJost
        (xiSpectralPoint q) ≠ 0 ↔
      returnedJost (xiSpectralPoint q) ≠ 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus]
  exact mul_ne_zero_iff_right
    (thetaCuspHawkingHypergeometricJostMinus_qnmPlus_ne_zero n q)

/-- Exact nonzero frequency derivative of the normalized branch Jost zero. -/
def teukolskyNormalizedJostOmegaDerivative (n : ℕ) : ℂ :=
  ((-1 : ℂ) ^ n * (n.factorial : ℂ)) * (-(Complex.I / 2))

/-- Implicit-function velocity of the QNM pole under a declared mass jet. -/
def teukolskyQNMPoleMassVelocity
    (n : ℕ) (q : XiZeroCopy) (massJet : ℂ → ℂ) : ℂ :=
  -massJet (xiSpectralPoint q) / teukolskyNormalizedJostOmegaDerivative n

lemma teukolskyNormalizedJostOmegaDerivative_ne_zero (n : ℕ) :
    teukolskyNormalizedJostOmegaDerivative n ≠ 0 :=
  thetaCuspHawkingHypergeometricJostDerivative_ne_zero n

lemma teukolskyQNMPoleMassVelocity_ne_zero_iff
    (n : ℕ) (q : XiZeroCopy) (massJet : ℂ → ℂ) :
    teukolskyQNMPoleMassVelocity n q massJet ≠ 0 ↔
      massJet (xiSpectralPoint q) ≠ 0 := by
  unfold teukolskyQNMPoleMassVelocity
  simp [teukolskyNormalizedJostOmegaDerivative_ne_zero]

/-- Determinant is the QNM pole velocity times `dJ/domega` and the companion factor. -/
theorem teukolskyReturnDeterminant_qnmPlus_eq_poleVelocity
    (n : ℕ) (q : XiZeroCopy) (massJet : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)) massJet
        (xiSpectralPoint q) =
      -teukolskyQNMPoleMassVelocity n q massJet *
        teukolskyNormalizedJostOmegaDerivative n *
        thetaCuspHawkingHypergeometricJostMinus
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          (xiSpectralPoint q) := by
  rw [teukolskyReturnDeterminant_qnmPlus]
  unfold teukolskyQNMPoleMassVelocity
  have hd := teukolskyNormalizedJostOmegaDerivative_ne_zero n
  field_simp [hd]

/-- Exact returned channel: arbitrary multiplicative horizon phase plus additive cross source. -/
def teukolskyReturnedJostWithHorizonPhase (omega : ℂ)
    (horizonPhase crossSource : ℂ → ℂ) (z : ℂ) : ℂ :=
  horizonPhase z * thetaCuspHawkingHypergeometricJostPlus omega z + crossSource z

lemma teukolskyReturnedJostWithHorizonPhase_qnmPlus
    (n : ℕ) (q : XiZeroCopy) (horizonPhase crossSource : ℂ → ℂ) :
    teukolskyReturnedJostWithHorizonPhase
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        horizonPhase crossSource (xiSpectralPoint q) = crossSource (xiSpectralPoint q) := by
  simp [teukolskyReturnedJostWithHorizonPhase,
    thetaCuspHawkingHypergeometricJostPlus_qnm_zero]

/-- Multiplicative horizon phase cancels at a Jost zero; cross-helicity source is sole producer. -/
theorem teukolskyCrossSource_is_exact_qnmPlus_return_producer
    (n : ℕ) (q : XiZeroCopy) (horizonPhase crossSource : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (teukolskyReturnedJostWithHorizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          horizonPhase crossSource)
        (xiSpectralPoint q) ≠ 0 ↔
      crossSource (xiSpectralPoint q) ≠ 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus_ne_zero_iff,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus]

/-- A fully nonlinear multiplicative horizon phase alone cannot lift the old QNM zero. -/
theorem teukolskyHorizonPhaseOnly_returnDeterminant_qnmPlus_eq_zero
    (n : ℕ) (q : XiZeroCopy) (horizonPhase : ℂ → ℂ) :
    teukolskyReturnDeterminant
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (teukolskyReturnedJostWithHorizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          horizonPhase (fun _ => 0))
        (xiSpectralPoint q) = 0 := by
  rw [teukolskyReturnDeterminant_qnmPlus,
    teukolskyReturnedJostWithHorizonPhase_qnmPlus]
  simp

/-- Projective numerator of the Cayley completion. -/
def teukolskyReturnCayleyNumerator
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 + teukolskyReturnDeterminant omega returnedJost z

/-- Projective denominator of the Cayley completion.  Its zeros are physical S-matrix poles. -/
def teukolskyReturnCayleyDenominator
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) : ℂ :=
  1 - teukolskyReturnDeterminant omega returnedJost z

/-- Shadow swaps projective S-matrix numerator with denominator. -/
theorem teukolskyReturnCayleyNumerator_shadow
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) :
    teukolskyReturnCayleyNumerator omega returnedJost
        (thetaCuspHawkingOpticalCuspShadow z) =
      teukolskyReturnCayleyDenominator omega returnedJost z := by
  rw [teukolskyReturnCayleyNumerator, teukolskyReturnCayleyDenominator,
    teukolskyReturnDeterminant_shadow]
  ring

/-- Shadow swaps projective S-matrix denominator with numerator. -/
theorem teukolskyReturnCayleyDenominator_shadow
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) :
    teukolskyReturnCayleyDenominator omega returnedJost
        (thetaCuspHawkingOpticalCuspShadow z) =
      teukolskyReturnCayleyNumerator omega returnedJost z := by
  rw [teukolskyReturnCayleyDenominator, teukolskyReturnCayleyNumerator,
    teukolskyReturnDeterminant_shadow]
  ring

/-- Canonical full nonperturbative Cayley completion of the chiral return determinant. -/
def teukolskyReturnCayleySMatrix
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) : ℂ :=
  teukolskyReturnCayleyNumerator omega returnedJost z /
    teukolskyReturnCayleyDenominator omega returnedJost z

/-- Exact theta-mirror S-matrix law. -/
theorem teukolskyReturnCayleySMatrix_shadow
    (omega : ℂ) (returnedJost : ℂ → ℂ) (z : ℂ) :
    teukolskyReturnCayleySMatrix omega returnedJost
        (thetaCuspHawkingOpticalCuspShadow z) =
      (teukolskyReturnCayleySMatrix omega returnedJost z)⁻¹ := by
  rw [teukolskyReturnCayleySMatrix, teukolskyReturnCayleySMatrix,
    teukolskyReturnCayleyNumerator_shadow,
    teukolskyReturnCayleyDenominator_shadow, inv_div]

private lemma cayley_eq_one_iff (r : ℂ) :
    (1 + r) / (1 - r) = 1 ↔ r = 0 := by
  by_cases h : 1 - r = 0
  · have hr : r = 1 := by linear_combination -h
    simp [hr]
  · rw [div_eq_one_iff_eq h]
    constructor <;> intro hEq
    · have h2r : (2 : ℂ) * r = 0 := by linear_combination hEq
      exact (mul_eq_zero.mp h2r).resolve_left (by norm_num)
    · simp [hEq]

/-- Cayley S-matrix is nontrivial at a divisor exactly when cross-helicity return is present. -/
theorem teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource
    (n : ℕ) (q : XiZeroCopy) (horizonPhase crossSource : ℂ → ℂ) :
    teukolskyReturnCayleySMatrix
        (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
        (teukolskyReturnedJostWithHorizonPhase
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          horizonPhase crossSource)
        (xiSpectralPoint q) ≠ 1 ↔
      crossSource (xiSpectralPoint q) ≠ 0 := by
  let omega := thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q)
  let returned := teukolskyReturnedJostWithHorizonPhase omega horizonPhase crossSource
  let r := teukolskyReturnDeterminant omega returned (xiSpectralPoint q)
  change ((1 + r) / (1 - r) ≠ 1) ↔ crossSource (xiSpectralPoint q) ≠ 0
  exact (not_congr (cayley_eq_one_iff r)).trans
    (teukolskyCrossSource_is_exact_qnmPlus_return_producer
      n q horizonPhase crossSource)

/-- Full-dynamics dichotomy in exact pointwise form: making the Cayley return nontrivial in every
Xi sector is equivalent to exciting the cross-helicity returned channel in every sector. -/
theorem teukolskyReturnCayleySMatrix_nontrivial_everyXi_iff_crossSource_everyXi
    (n : ℕ) (horizonPhase crossSource : ℂ → ℂ) :
    (∀ q : XiZeroCopy,
      teukolskyReturnCayleySMatrix
          (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
          (teukolskyReturnedJostWithHorizonPhase
            (thetaCuspHawkingTopologicalBlackHoleQNMPlus n (xiSpectralPoint q))
            horizonPhase crossSource)
          (xiSpectralPoint q) ≠ 1) ↔
      ∀ q : XiZeroCopy, crossSource (xiSpectralPoint q) ≠ 0 := by
  constructor
  · intro h q
    exact (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource
      n q horizonPhase crossSource).mp (h q)
  · intro h q
    exact (teukolskyReturnCayleySMatrix_qnmPlus_ne_one_iff_crossSource
      n q horizonPhase crossSource).mpr (h q)

end

end RHTower
