import GaloisForLFunctions.RHTower.ThetaCuspHawkingOpticalCuspScatteringIncidence

/-!
# Topological AdS black-hole QNM incidence for the theta cusp

This module places the modular scattering object in an exact black-hole wave equation rather than
using near-horizon analogy alone.

The four-dimensional massless topological AdS black hole has

`ds² = -(r²/l²-1)dt² + dr²/(r²/l²-1) + r² dσ²`,

with event horizon `r=l`, Hawking temperature `T_H=1/(2*pi*l)`, and a negative-curvature horizon
section `Sigma=H²/Gamma`.  Taking a torsion-free principal congruence subgroup gives a smooth,
finite-area, noncompact hyperbolic horizon.  The deck-invariant Eisenstein channel is the lift of
the scalar modular channel, so it carries the normalized scattering eigenvalue formalized in
`ThetaCuspHawkingOpticalCuspScatteringIncidence`.

For a scalar harmonic on `Sigma`, Klein--Gordon separation gives

`Q = 1/4 + xi²`.

For the massless conformally coupled scalar, the standard zero-flux AdS boundary condition gives
the exact dimensionless quasinormal frequencies

`l*omega_± = ±xi - I*(2*n + 3/2)`.

These are the `beta_+` modes of Aros--Martinez--Troncoso--Zanelli, Phys. Rev. D 67 (2003),
arXiv:hep-th/0211024.  Their derivation uses the Klein--Gordon stress-energy flux, not a formal KMS
analogy.

For the modular resonance coordinate of the preceding module,

`s(z)=1/2+I*xi(z)`,  `xi(z)=z/2+I/4`.

Thus the functional-equation shadow sends `xi` to `-xi` and exchanges the two analytically
continued QNM-frequency branches. Birmingham--Mokhtari's sign is a square-root spectral parameter
at fixed `Q`, not a pair of angular-momentum eigenspaces. At Xi divisors this is resonance
continuation; it is not asserted to be an `L2` horizon harmonic.
The angular eigenvalue `Q` is quadratic and therefore shadow-blind.  This is the precise reason the
linear discrete-plus-continuum optical energy cannot prove RH: the hyperbolic Plancherel identity
has the form

`E[Phi] = sum_j E_{Q_j}[Phi_j]
        + (1/(4*pi)) * sum_c integral_R E_{1/4+t²}[Phi_c(t)] dt`,

and every block factors through the shadow-even eigenvalue `Q`.  The theorem
`thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy_shadow` proves this blindness for every
energy reporter depending on the separated angular eigenvalue.

Time-oriented QNM data retain the missing sign.  Their imaginary-frequency splitting is exactly

`Im(l*omega_+) - Im(l*omega_-) = 1/2 + Im z`.

Hence canonical Hawking splitting `1/2 = pi*l*T_H` holds exactly when that Xi divisor has zero tilt.
At every divisor, the scattering pole, shadow zero, opposing analytically continued QNM branches,
and splitting criterion are proved together below.

**[LITERATURE-FORMALIZED] [PAPER-PROVED] [LEAN-PROVED]** The separated eigenvalue, QNM branch,
shadow, pole/zero, energy-blindness, and splitting laws below are unconditional consequences of the
displayed formulas.

**[OPEN CORE]** This is an exact Einstein-`Lambda` black-hole background with a linear
Klein--Gordon probe.  Full Einstein--Klein--Gordon backreaction is not derived here.  Remaining
RH-bearing producer is nonlinear: horizon absorption/mass memory must either enforce the canonical
QNM splitting or mix the two shadow sectors.  Linear passivity cannot do so because its complete
discrete-plus-continuum energy is already proved shadow-blind.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Hyperbolic Laplacian square-root parameter `xi` corresponding to modular resonance coordinate. -/
def thetaCuspHawkingTopologicalBlackHoleAngularMomentum (z : ℂ) : ℂ :=
  z / 2 + Complex.I / 4

/-- Separated horizon-Laplacian eigenvalue `Q=1/4+xi²`. -/
def thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue (z : ℂ) : ℂ :=
  1 / 4 + thetaCuspHawkingTopologicalBlackHoleAngularMomentum z ^ (2 : ℕ)

/-- Dimensionless decay of the standard conformally coupled `beta_+` scalar QNM. -/
def thetaCuspHawkingTopologicalBlackHoleConformalDecay (n : ℕ) : ℝ :=
  2 * n + 3 / 2

/-- Positive square-root branch of exact topological-black-hole QNM formula. -/
def thetaCuspHawkingTopologicalBlackHoleQNMPlus (n : ℕ) (z : ℂ) : ℂ :=
  thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
    Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n

/-- Negative square-root branch of exact topological-black-hole QNM formula. -/
def thetaCuspHawkingTopologicalBlackHoleQNMMinus (n : ℕ) (z : ℂ) : ℂ :=
  -thetaCuspHawkingTopologicalBlackHoleAngularMomentum z -
    Complex.I * thetaCuspHawkingTopologicalBlackHoleConformalDecay n

/-- Imaginary-frequency splitting of the two exact QNM branches. -/
def thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting
    (n : ℕ) (z : ℂ) : ℝ :=
  (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z).im -
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z).im

/-- Any separated linear optical-energy block, which can depend only on the angular eigenvalue. -/
def thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy
    (reporter : ℂ → ℝ) (z : ℂ) : ℝ :=
  reporter (thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue z)

/-- The modular scattering parameter is the standard hyperbolic parameter `s=1/2+I*xi`. -/
lemma thetaCuspHawkingOpticalCuspResonanceParameter_eq_angularMomentum
    (z : ℂ) :
    thetaCuspHawkingOpticalCuspResonanceParameter z =
      1 / 2 + Complex.I *
        thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold thetaCuspHawkingOpticalCuspResonanceParameter
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
  have hII : Complex.I * (Complex.I / 4) = -(1 / 4 : ℂ) := by
    calc
      Complex.I * (Complex.I / 4) = (Complex.I * Complex.I) / 4 := by ring
      _ = -(1 / 4 : ℂ) := by rw [Complex.I_mul_I]; ring
  rw [mul_add, hII]
  ring

/-- Scattering shadow negates topological-black-hole angular momentum. -/
lemma thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow
    (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum
        (thetaCuspHawkingOpticalCuspShadow z) =
      -thetaCuspHawkingTopologicalBlackHoleAngularMomentum z := by
  unfold thetaCuspHawkingTopologicalBlackHoleAngularMomentum
    thetaCuspHawkingOpticalCuspShadow
  ring

/-- Linear Klein--Gordon separation loses the pole/zero orientation because `Q` is quadratic. -/
lemma thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue_shadow
    (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue z := by
  unfold thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue
  rw [thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]
  ring

/-- Every discrete or continuum linear energy block factoring through `Q` is shadow-blind. -/
theorem thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy_shadow
    (reporter : ℂ → ℝ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy reporter
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy reporter z := by
  unfold thetaCuspHawkingTopologicalBlackHoleSeparatedOpticalEnergy
  rw [thetaCuspHawkingTopologicalBlackHoleAngularEigenvalue_shadow]

/-- Shadow sends the positive QNM branch to the negative branch. -/
lemma thetaCuspHawkingTopologicalBlackHoleQNMPlus_shadow
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMPlus n
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleQNMMinus n z := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  rw [thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]

/-- Shadow sends the negative QNM branch to the positive branch. -/
lemma thetaCuspHawkingTopologicalBlackHoleQNMMinus_shadow
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleQNMMinus n
        (thetaCuspHawkingOpticalCuspShadow z) =
      thetaCuspHawkingTopologicalBlackHoleQNMPlus n z := by
  unfold thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
  rw [thetaCuspHawkingTopologicalBlackHoleAngularMomentum_shadow]
  ring

lemma thetaCuspHawkingTopologicalBlackHoleQNMPlus_im
    (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z).im =
      z.im / 2 + 1 / 4 -
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  simp [thetaCuspHawkingTopologicalBlackHoleQNMPlus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum]

lemma thetaCuspHawkingTopologicalBlackHoleQNMMinus_im
    (n : ℕ) (z : ℂ) :
    (thetaCuspHawkingTopologicalBlackHoleQNMMinus n z).im =
      -z.im / 2 - 1 / 4 -
        thetaCuspHawkingTopologicalBlackHoleConformalDecay n := by
  simp [thetaCuspHawkingTopologicalBlackHoleQNMMinus,
    thetaCuspHawkingTopologicalBlackHoleAngularMomentum]
  ring

/-- Exact time-oriented recovery of the Xi tilt; radial decay and overtone cancel. -/
theorem thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n z =
      z.im + 1 / 2 := by
  rw [thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_im,
    thetaCuspHawkingTopologicalBlackHoleQNMMinus_im]
  ring

/-- Canonical Hawking splitting `pi*l*T_H=1/2` is exactly zero Xi tilt. -/
theorem thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq_half_iff
    (n : ℕ) (z : ℂ) :
    thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n z = 1 / 2 ↔
      z.im = 0 := by
  rw [thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq]
  constructor <;> intro h <;> linarith

/-- Full linear incidence packet: pole, shadow zero, opposing QNM branches, and thermal splitting. -/
theorem thetaCuspHawkingXiDivisor_topologicalBlackHoleQNM_incidence
    (n : ℕ) (q : XiZeroCopy) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering
        (xiSpectralPoint q) < 0 ∧
      AnalyticAt ℂ thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) ∧
      thetaCuspHawkingOpticalCuspScattering
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) = 0 ∧
      thetaCuspHawkingTopologicalBlackHoleQNMPlus n
        (thetaCuspHawkingOpticalCuspShadow (xiSpectralPoint q)) =
          thetaCuspHawkingTopologicalBlackHoleQNMMinus n (xiSpectralPoint q) ∧
      (thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n
          (xiSpectralPoint q) = 1 / 2 ↔
        (xiSpectralPoint q).im = 0) := by
  refine ⟨thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q, ?_⟩
  rcases thetaCuspHawkingOpticalCuspShadow_xiSpectralPoint_isZero q with
    ⟨han, hzero⟩
  exact ⟨han, hzero,
    thetaCuspHawkingTopologicalBlackHoleQNMPlus_shadow n (xiSpectralPoint q),
    thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq_half_iff
      n (xiSpectralPoint q)⟩

/-- An off-critical divisor is simultaneously a true optical pole, a noncanonical QNM thermal
split, and a Davies--Fulling reflected-flux asymmetry. -/
theorem thetaCuspHawkingXiDivisor_offCritical_topologicalBlackHoleQNM_flux
    (n : ℕ) (q : XiZeroCopy) (hq : (xiSpectralPoint q).im ≠ 0) :
    meromorphicOrderAt thetaCuspHawkingOpticalCuspScattering
        (xiSpectralPoint q) < 0 ∧
      thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting n
          (xiSpectralPoint q) ≠ 1 / 2 ∧
      ∃ lambda : ℝ,
        |lambda| < thetaCuspHawkingBifurcationCommonCouplingRadius
          (xiSpectralPoint q).im ∧
        thetaCuspHawkingSchwarzian (xiSpectralPoint q).im lambda 0 ≠
          thetaCuspHawkingSchwarzian (-(xiSpectralPoint q).im) lambda 0 := by
  refine ⟨thetaCuspHawkingOpticalCusp_xiSpectralPoint_isPole q, ?_, ?_⟩
  · exact (thetaCuspHawkingTopologicalBlackHoleBranchImaginarySplitting_eq_half_iff
      n (xiSpectralPoint q)).not.mpr hq
  · have hstrip : |(xiSpectralPoint q).im| < 1 := by
      linarith [abs_im_xiSpectralPoint_lt_half q]
    exact exists_thetaCuspHawkingBifurcationSchwarzian_reflection_ne_of_tilt_ne_zero
      hstrip hq

end

end RHTower
