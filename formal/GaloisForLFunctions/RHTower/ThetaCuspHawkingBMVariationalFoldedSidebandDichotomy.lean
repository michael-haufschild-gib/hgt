import Mathlib

/-!
# Inverse-character sidebands and folded cubic variation

Two Fourier characters closed under the inverse-character rule `x - y + z` generate the affine
sideband lattice

`omegaC + n * (omegaR - omegaC)`.

If the frequencies differ, this lattice is infinite. This rule does not model the Birmingham--
Mokhtari reality-partner QNM grade: its physical `++-` frequency is `2 * omegaPlus + omegaMinus`,
so the sideband result supplies no BM instability argument.

For two diagonal scalar Euler fields, changing variables to mean and defect gives the exact folded
linear and cubic equations below. The cubic folded equation contains mean-dependent terms. A pure
defect current occurs on the antisymmetric slice only, with fixed normalization conditions.
-/

open Complex Real

namespace RHTower

noncomputable section

/-- Affine frequency lattice closed under the inverse-character rule `x - y + z`. -/
def d4BMFoldedCubicSidebandFrequency
    (omegaR omegaC : ℂ) (n : ℤ) : ℂ :=
  omegaC + (n : ℂ) * (omegaR - omegaC)

theorem d4BMFoldedCubicSidebandFrequency_zero (omegaR omegaC : ℂ) :
    d4BMFoldedCubicSidebandFrequency omegaR omegaC 0 = omegaC := by
  simp [d4BMFoldedCubicSidebandFrequency]

theorem d4BMFoldedCubicSidebandFrequency_one (omegaR omegaC : ℂ) :
    d4BMFoldedCubicSidebandFrequency omegaR omegaC 1 = omegaR := by
  simp [d4BMFoldedCubicSidebandFrequency]

theorem d4BMFoldedCubicSidebandFrequency_two (omegaR omegaC : ℂ) :
    d4BMFoldedCubicSidebandFrequency omegaR omegaC 2 =
      2 * omegaR - omegaC := by
  simp [d4BMFoldedCubicSidebandFrequency]
  ring

theorem d4BMFoldedCubicSidebandFrequency_neg_one (omegaR omegaC : ℂ) :
    d4BMFoldedCubicSidebandFrequency omegaR omegaC (-1) =
      2 * omegaC - omegaR := by
  simp [d4BMFoldedCubicSidebandFrequency]
  ring

/-- The full integer ladder is closed under every iterated inverse-character interaction. -/
theorem d4BMFoldedCubicSidebandFrequency_closed
    (omegaR omegaC : ℂ) (a b c : ℤ) :
    d4BMFoldedCubicSidebandFrequency omegaR omegaC a -
        d4BMFoldedCubicSidebandFrequency omegaR omegaC b +
          d4BMFoldedCubicSidebandFrequency omegaR omegaC c =
      d4BMFoldedCubicSidebandFrequency omegaR omegaC (a - b + c) := by
  simp [d4BMFoldedCubicSidebandFrequency]
  ring

/-- Nonzero detuning makes all sideband labels distinct. -/
theorem d4BMFoldedCubicSidebandFrequency_injective
    {omegaR omegaC : ℂ} (hfrequency : omegaR ≠ omegaC) :
    Function.Injective
      (d4BMFoldedCubicSidebandFrequency omegaR omegaC) := by
  intro a b hab
  have hmul : (a : ℂ) * (omegaR - omegaC) =
      (b : ℂ) * (omegaR - omegaC) := by
    simpa [d4BMFoldedCubicSidebandFrequency] using
      congrArg (fun z => z - omegaC) hab
  have hcast : (a : ℂ) = (b : ℂ) :=
    mul_right_cancel₀ (sub_ne_zero.mpr hfrequency) hmul
  exact_mod_cast hcast

/-- Nonzero detuning forces infinitely many nonlinear sideband frequencies. -/
theorem d4BMFoldedCubicSidebandFrequency_range_infinite
    {omegaR omegaC : ℂ} (hfrequency : omegaR ≠ omegaC) :
    (Set.range (d4BMFoldedCubicSidebandFrequency omegaR omegaC)).Infinite :=
  Set.infinite_range_of_injective
    (d4BMFoldedCubicSidebandFrequency_injective hfrequency)

/-- A nonzero purely imaginary detuning forces the infinite inverse-character ladder. -/
theorem d4BMFoldedCubicSidebandFrequency_range_infinite_of_tilt
    {omegaR omegaC : ℂ} {tilt : ℝ}
    (hfrequency : omegaR - omegaC =
      2 * Complex.I * (tilt : ℂ)) (htilt : tilt ≠ 0) :
    (Set.range (d4BMFoldedCubicSidebandFrequency omegaR omegaC)).Infinite := by
  apply d4BMFoldedCubicSidebandFrequency_range_infinite
  intro heq
  have hzero : omegaR - omegaC = 0 := sub_eq_zero.mpr heq
  rw [hfrequency] at hzero
  have him := congrArg Complex.im hzero
  simp at him
  exact htilt (by linarith)

/-- The sideband lattice collapses to one frequency exactly at zero detuning. -/
theorem d4BMFoldedCubicSidebandFrequency_collapse_iff
    (omegaR omegaC : ℂ) :
    (∀ n : ℤ,
      d4BMFoldedCubicSidebandFrequency omegaR omegaC n = omegaC) ↔
      omegaR = omegaC := by
  constructor
  · intro h
    simpa [d4BMFoldedCubicSidebandFrequency] using h 1
  · rintro rfl
    simp [d4BMFoldedCubicSidebandFrequency]

/-- Scalar radial cubic Euler coefficient in one separated sector. -/
def d4BMSectorRadialCubicEuler (beta z : ℂ) : ℂ :=
  beta * (Complex.normSq z : ℂ) * z

/-- Defect variation of two diagonal radial cubic sectors under
`zR = mean + defect / 2`, `zC = mean - defect / 2`. -/
def d4BMTwoSectorFoldedCubicEuler
    (betaR betaC mean defect : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (d4BMSectorRadialCubicEuler betaR (mean + defect / 2) -
      d4BMSectorRadialCubicEuler betaC (mean - defect / 2))

/-- Exact mean/defect decomposition of the two-sector cubic variation. -/
theorem d4BMTwoSectorFoldedCubicEuler_eq
    (betaR betaC mean defect : ℂ) :
    d4BMTwoSectorFoldedCubicEuler betaR betaC mean defect =
      (betaR + betaC) / 4 *
        (mean ^ 2 * (starRingEnd ℂ) defect +
          2 * (Complex.normSq mean : ℂ) * defect +
          (1 / 4 : ℂ) * (Complex.normSq defect : ℂ) * defect) +
      (betaR - betaC) / 4 *
        (2 * (Complex.normSq mean : ℂ) * mean +
          (Complex.normSq defect : ℂ) * mean +
          (1 / 2 : ℂ) * defect ^ 2 * (starRingEnd ℂ) mean) := by
  simp only [d4BMTwoSectorFoldedCubicEuler, d4BMSectorRadialCubicEuler]
  repeat rw [Complex.normSq_eq_conj_mul_self]
  simp
  rw [map_ofNat (starRingEnd ℂ) 2]
  ring

/-- On the antisymmetric slice, only the scalar defect cubic remains. -/
theorem d4BMTwoSectorFoldedCubicEuler_mean_zero
    (betaR betaC defect : ℂ) :
    d4BMTwoSectorFoldedCubicEuler betaR betaC 0 defect =
      (betaR + betaC) / 16 *
        (Complex.normSq defect : ℂ) * defect := by
  rw [d4BMTwoSectorFoldedCubicEuler_eq]
  simp
  ring

/-- At zero defect, unequal sector vertices source the folded equation through the mean mode. -/
theorem d4BMTwoSectorFoldedCubicEuler_defect_zero
    (betaR betaC mean : ℂ) :
    d4BMTwoSectorFoldedCubicEuler betaR betaC mean 0 =
      (betaR - betaC) / 2 *
        (Complex.normSq mean : ℂ) * mean := by
  rw [d4BMTwoSectorFoldedCubicEuler_eq]
  simp
  ring

/-- Defect variation of two diagonal linear boundary kernels. -/
def d4BMTwoSectorFoldedLinearEuler
    (kR kC mean defect : ℂ) : ℂ :=
  (1 / 2 : ℂ) *
    (kR * (mean + defect / 2) - kC * (mean - defect / 2))

theorem d4BMTwoSectorFoldedLinearEuler_eq
    (kR kC mean defect : ℂ) :
    d4BMTwoSectorFoldedLinearEuler kR kC mean defect =
      (kR - kC) / 2 * mean + (kR + kC) / 4 * defect := by
  simp [d4BMTwoSectorFoldedLinearEuler]
  ring

/-- Folded Euler polynomial through cubic order in the two separated amplitudes. -/
def d4BMTwoSectorFoldedEuler
    (kR kC betaR betaC mean defect : ℂ) : ℂ :=
  d4BMTwoSectorFoldedLinearEuler kR kC mean defect +
    d4BMTwoSectorFoldedCubicEuler betaR betaC mean defect

/-- Exact antisymmetric-slice Euler equation. -/
theorem d4BMTwoSectorFoldedEuler_mean_zero
    (kR kC betaR betaC defect : ℂ) :
    d4BMTwoSectorFoldedEuler kR kC betaR betaC 0 defect =
      (kR + kC) / 4 * defect +
        (betaR + betaC) / 16 *
          (Complex.normSq defect : ℂ) * defect := by
  rw [d4BMTwoSectorFoldedEuler, d4BMTwoSectorFoldedLinearEuler_eq,
    d4BMTwoSectorFoldedCubicEuler_mean_zero]
  simp

/-- Current proposed by the scalar folded ansatz. -/
def d4BMVariationalScalarFoldedBoundaryCurrent
    (period defect : ℂ) : ℂ :=
  defect - Complex.I * period *
    (Complex.normSq defect : ℂ) * defect

/-- Exact coefficient conditions under which the antisymmetric two-sector action yields the
scalar folded current. -/
theorem d4BMTwoSectorFoldedEuler_mean_zero_eq_scalarCurrent
    (kR kC betaR betaC period defect : ℂ)
    (hk : kR + kC = 4)
    (hbeta : betaR + betaC = -16 * Complex.I * period) :
    d4BMTwoSectorFoldedEuler kR kC betaR betaC 0 defect =
      d4BMVariationalScalarFoldedBoundaryCurrent period defect := by
  rw [d4BMTwoSectorFoldedEuler_mean_zero, hk, hbeta]
  simp [d4BMVariationalScalarFoldedBoundaryCurrent]
  ring

end

end RHTower
