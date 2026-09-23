import GaloisForLFunctions.RHTower.ProlateGaussianWindowLimit
import GaloisForLFunctions.RHTower.ProlateHermiteRescale
import GaloisForLFunctions.RHTower.SlepianKernelScaledFubini
import GaloisForLFunctions.RHTower.ProlateSecondMoment

/-!
# The rescaled prolate profile normalized at the centre

The window comparison against the Gaussian is stated for a solution of the rescaled prolate
equation normalized by `u(0) = 1`, `u′(0) = 0`.  For a genuine even prolate eigenfunction both
normalizations are available: the centre value is nonzero, and evenness kills the derivative there.

This module packages `ξ ↦ Φ(ξ/√c)/Φ(0)` together with its first two derivatives and checks the
three hypotheses of the window comparison — the global differentiability, the normal-form equation
on the window, and the initial phase vector.
-/

open Set Filter Topology GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

/-- The rescaled prolate profile normalized to value one at the centre. -/
def normalizedProlateProfile (c : ℝ) (Phi : ℝ → ℝ) (xi : ℝ) : ℝ :=
  prolateHermiteRescale c Phi xi / Phi 0

/-- Its first derivative. -/
def normalizedProlateDeriv (c : ℝ) (Phi : ℝ → ℝ) (xi : ℝ) : ℝ :=
  deriv (prolateHermiteRescale c Phi) xi / Phi 0

/-- Its second derivative. -/
def normalizedProlateDeriv2 (c : ℝ) (Phi : ℝ → ℝ) (xi : ℝ) : ℝ :=
  deriv (deriv (prolateHermiteRescale c Phi)) xi / Phi 0

theorem prolateHermiteRescale_zero (c : ℝ) (Phi : ℝ → ℝ) :
    prolateHermiteRescale c Phi 0 = Phi 0 := by
  simp [prolateHermiteRescale]

@[simp]
theorem normalizedProlateProfile_zero {Phi : ℝ → ℝ} (c : ℝ) (h0 : Phi 0 ≠ 0) :
    normalizedProlateProfile c Phi 0 = 1 := by
  rw [normalizedProlateProfile, prolateHermiteRescale_zero, div_self h0]

@[simp]
theorem normalizedProlateDeriv_zero {Phi : ℝ → ℝ} (c : ℝ) (heven : Function.Even Phi) :
    normalizedProlateDeriv c Phi 0 = 0 := by
  rw [normalizedProlateDeriv, deriv_zero_of_even (even_prolateHermiteRescale heven), zero_div]

theorem even_normalizedProlateProfile {c : ℝ} {Phi : ℝ → ℝ} (heven : Function.Even Phi) :
    Function.Even (normalizedProlateProfile c Phi) := by
  intro x
  rw [normalizedProlateProfile, normalizedProlateProfile, even_prolateHermiteRescale heven]

theorem hasDerivAt_normalizedProlateProfile {c : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi) (xi : ℝ) :
    HasDerivAt (normalizedProlateProfile c Phi) (normalizedProlateDeriv c Phi xi) xi := by
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateHermiteRescale c Phi) :=
    contDiff_prolateHermiteRescale hsm
  have hd : Differentiable ℝ (prolateHermiteRescale c Phi) :=
    (contDiff_infty_iff_deriv.mp hw).1
  exact ((hd xi).hasDerivAt).div_const (Phi 0)

theorem hasDerivAt_normalizedProlateDeriv {c : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi) (xi : ℝ) :
    HasDerivAt (normalizedProlateDeriv c Phi) (normalizedProlateDeriv2 c Phi xi) xi := by
  have hw : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateHermiteRescale c Phi) :=
    contDiff_prolateHermiteRescale hsm
  have hw' : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (deriv (prolateHermiteRescale c Phi)) :=
    (contDiff_infty_iff_deriv.mp hw).2
  have hd : Differentiable ℝ (deriv (prolateHermiteRescale c Phi)) :=
    (contDiff_infty_iff_deriv.mp hw').1
  exact ((hd xi).hasDerivAt).div_const (Phi 0)

theorem continuous_normalizedProlateProfile {c : ℝ} {Phi : ℝ → ℝ}
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi) :
    Continuous (normalizedProlateProfile c Phi) :=
  Differentiable.continuous fun x => (hasDerivAt_normalizedProlateProfile hsm x).differentiableAt

/-- **Normal form.**  On a window where the bandwidth dominates, the normalized rescaled profile
solves the rescaled prolate equation with separation parameter `μ = c·s`. -/
theorem normalizedProlate_ode {c chi K : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    ∀ xi ∈ Icc (0 : ℝ) K,
      normalizedProlateDeriv2 c Phi xi
        = rescaledProlateP c (c * radialSeparationRatio c chi) xi * normalizedProlateProfile c Phi xi
          + rescaledProlateQ c xi * normalizedProlateDeriv c Phi xi := by
  have hc : 0 < c := pos_of_window hK hcK
  intro xi hxi
  have hxiK : |xi| ≤ K := by
    rw [abs_of_nonneg hxi.1]
    exact hxi.2
  have hpos : 0 < c - xi ^ (2 : ℕ) := lt_of_lt_of_le (by linarith) (half_le_sub_sq hK hcK hxiK)
  have hbase := deriv2_eq_of_hermiteDefect (c := c) (mu := c * radialSeparationRatio c chi)
    (u := prolateHermiteRescale c Phi) (xi := xi) hc.ne' hpos.ne'
    (prolateHermiteRescale_radial_defect hc heig xi)
  rw [normalizedProlateDeriv2, normalizedProlateProfile, normalizedProlateDeriv, hbase]
  ring

/-- **Window hypotheses discharged.**  The normalized rescaled profile of an even prolate mode is a
solution of the rescaled equation on the window with the Gaussian's initial phase vector. -/
theorem normalizedProlate_window_package {c lam chi K : ℝ} {Phi : ℝ → ℝ}
    (hK : 0 < K) (hcK : 2 * K ^ (2 : ℕ) ≤ c)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Phi)
    (hne : Phi ≠ 0) (heven : Function.Even Phi) (hlam : lam ≠ 0)
    (hband : ∀ x : ℝ, bandTransform c Phi x = lam * Phi x)
    (heig : ∀ x : ℝ, prolateSLAction c Phi x = chi * Phi x) :
    (∀ xi, HasDerivAt (normalizedProlateProfile c Phi) (normalizedProlateDeriv c Phi xi) xi) ∧
      (∀ xi, HasDerivAt (normalizedProlateDeriv c Phi) (normalizedProlateDeriv2 c Phi xi) xi) ∧
      (∀ xi ∈ Icc (0 : ℝ) K,
        normalizedProlateDeriv2 c Phi xi
          = rescaledProlateP c (c * radialSeparationRatio c chi) xi
              * normalizedProlateProfile c Phi xi
            + rescaledProlateQ c xi * normalizedProlateDeriv c Phi xi) ∧
      normalizedProlateProfile c Phi 0 = 1 ∧ normalizedProlateDeriv c Phi 0 = 0 := by
  have h0 : Phi 0 ≠ 0 :=
    value_zero_ne_of_even_joint_prolate_band_eigen hsm hne heven hlam hband heig
  exact ⟨hasDerivAt_normalizedProlateProfile hsm, hasDerivAt_normalizedProlateDeriv hsm,
    normalizedProlate_ode hK hcK heig, normalizedProlateProfile_zero c h0,
    normalizedProlateDeriv_zero c heven⟩

/-- **Orthogonality transfers to the rescaled window.**  If two profiles are orthogonal on the
aperture, their normalized rescalings are orthogonal on the window `[−√c, √c]`. -/
theorem integral_normalizedProlate_mul_eq_zero {c : ℝ} (hc : 0 < c) {Phi Psi : ℝ → ℝ}
    (horth : (∫ x in (-1 : ℝ)..1, Phi x * Psi x) = 0) :
    (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
        normalizedProlateProfile c Phi xi * normalizedProlateProfile c Psi xi) = 0 := by
  have hbase := integral_comp_div_sqrt hc (fun x => Phi x * Psi x)
  have hrw : (∫ xi in (-Real.sqrt c)..(Real.sqrt c),
      normalizedProlateProfile c Phi xi * normalizedProlateProfile c Psi xi)
      = (1 / (Phi 0 * Psi 0))
        * ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            Phi (xi / Real.sqrt c) * Psi (xi / Real.sqrt c) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun xi _ => ?_
    rw [normalizedProlateProfile, normalizedProlateProfile, prolateHermiteRescale,
      prolateHermiteRescale]
    ring
  rw [hrw, hbase, horth]
  ring

end RHTower
