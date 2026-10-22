import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMPhysicalPoincareRadialNoGo
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicCornerRenormalizedSecondDerivative

/-!
# Pulling the physical Poincare radial derivative through the BM chart

The exact Rindler--AdS/Poincare chart is

`T = sigma * sqrt(1-rho²) * sinh(tau)`,
`Y = sigma * sqrt(1-rho²) * cosh(tau)`,
`Z = rho * sigma`.

The inverse-Jacobian vector field at fixed `(T,Y)` is therefore

`partial_Z = rho * partial_sigma + (1-rho²)/sigma * partial_rho`.

This module proves the coordinate-vector identity from actual derivatives: the displayed operator
annihilates `T,Y` and sends `Z` to one. Since `z_BM = 1-rho²`, its action on a BM first radial jet
whose BM derivative is `J` is

`-2*rho*(1-rho²)/sigma * J`.

The corner-renormalized BM `++` second derivative has a nonzero endpoint finite part on every Xi
fibre. Its proved convergence yields an actual interior BM radius where the second derivative is
nonzero. At that radius, the pulled-back `partial_Z` coefficient differs at `sigma=1` and
`sigma=2`. Hence the physical derivative of the actual corner-renormalized first jet cannot
descend to any scalar function of the BM radius.

This closes the scalar-radial differential shortcut. It does not compute the remaining
time/horizon derivatives in the full deformed kinematic bracket, the negative-helicity leg,
Einstein boundary completion, or the conserved left-QNM projection.

`[NEW CONSEQUENCE] [PAPER-PROVED] [LEAN-PROVED] [HC94] [PHYSICAL DERIVATIVE NO-GO]`
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Poincare time coordinate in the Rindler--AdS chart. -/
def d4BMRindlerToPoincareTime (tau rho sigma : ℝ) : ℝ :=
  sigma * Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.sinh tau

/-- Poincare horizon-transverse coordinate in the Rindler--AdS chart. -/
def d4BMRindlerToPoincareHorizonY (tau rho sigma : ℝ) : ℝ :=
  sigma * Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.cosh tau

/-- Pullback of the Poincare coordinate vector `partial_Z` to real Rindler coordinate jets. -/
def d4PoincareRadialPullbackOperator
    (rho sigma partialSigma partialRho : ℝ) : ℝ :=
  rho * partialSigma + (1 - rho ^ (2 : ℕ)) / sigma * partialRho

/-- Complex-field version of the pulled-back Poincare radial coordinate vector. -/
def d4PoincareRadialPullbackOperatorComplex
    (rho sigma : ℝ) (partialSigma partialRho : ℂ) : ℂ :=
  (rho : ℂ) * partialSigma + (((1 - rho ^ (2 : ℕ)) / sigma : ℝ) : ℂ) * partialRho

theorem hasDerivAt_d4BMRindlerToPoincareTime_sigma
    (tau rho sigma : ℝ) :
    HasDerivAt (fun s => d4BMRindlerToPoincareTime tau rho s)
      (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.sinh tau) sigma := by
  simpa [d4BMRindlerToPoincareTime, mul_assoc] using
    (hasDerivAt_id sigma).mul_const
      (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.sinh tau)

theorem hasDerivAt_sqrt_one_sub_sq
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt (fun r : ℝ => Real.sqrt (1 - r ^ (2 : ℕ)))
      (-rho / Real.sqrt (1 - rho ^ (2 : ℕ))) rho := by
  have hpos : 0 < 1 - rho ^ (2 : ℕ) := by nlinarith [sq_nonneg rho]
  have hinner : HasDerivAt (fun r : ℝ => 1 - r ^ (2 : ℕ)) (-2 * rho) rho := by
    simpa using (hasDerivAt_pow 2 rho).const_sub 1
  have hsqrt := hinner.sqrt hpos.ne'
  refine hsqrt.congr_deriv ?_
  have hsqrt0 : Real.sqrt (1 - rho ^ (2 : ℕ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  field_simp [hsqrt0]

theorem hasDerivAt_d4BMRindlerToPoincareTime_rho
    (tau sigma : ℝ) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt (fun r => d4BMRindlerToPoincareTime tau r sigma)
      (sigma * (-rho / Real.sqrt (1 - rho ^ (2 : ℕ))) * Real.sinh tau) rho := by
  simpa [d4BMRindlerToPoincareTime, mul_assoc] using
    ((hasDerivAt_sqrt_one_sub_sq hrho hrho1).const_mul sigma).mul_const
      (Real.sinh tau)

theorem hasDerivAt_d4BMRindlerToPoincareHorizonY_sigma
    (tau rho sigma : ℝ) :
    HasDerivAt (fun s => d4BMRindlerToPoincareHorizonY tau rho s)
      (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.cosh tau) sigma := by
  simpa [d4BMRindlerToPoincareHorizonY, mul_assoc] using
    (hasDerivAt_id sigma).mul_const
      (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.cosh tau)

theorem hasDerivAt_d4BMRindlerToPoincareHorizonY_rho
    (tau sigma : ℝ) {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) :
    HasDerivAt (fun r => d4BMRindlerToPoincareHorizonY tau r sigma)
      (sigma * (-rho / Real.sqrt (1 - rho ^ (2 : ℕ))) * Real.cosh tau) rho := by
  simpa [d4BMRindlerToPoincareHorizonY, mul_assoc] using
    ((hasDerivAt_sqrt_one_sub_sq hrho hrho1).const_mul sigma).mul_const
      (Real.cosh tau)

theorem hasDerivAt_d4PoincareRadialCoordinateFromBMRindler_sigma
    (rho sigma : ℝ) :
    HasDerivAt (fun s => d4PoincareRadialCoordinateFromBMRindler rho s) rho sigma := by
  simpa [d4PoincareRadialCoordinateFromBMRindler, mul_comm] using
    (hasDerivAt_id sigma).mul_const rho

theorem hasDerivAt_d4PoincareRadialCoordinateFromBMRindler_rho
    (rho sigma : ℝ) :
    HasDerivAt (fun r => d4PoincareRadialCoordinateFromBMRindler r sigma) sigma rho := by
  simpa [d4PoincareRadialCoordinateFromBMRindler] using
    (hasDerivAt_id rho).mul_const sigma

/-- The pulled-back operator is exactly `partial_Z`: it fixes `T,Y` and differentiates `Z` to
one. -/
theorem d4PoincareRadialPullbackOperator_is_coordinateVector
    (tau : ℝ) {rho sigma : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1)
    (hsigma : 0 < sigma) :
    d4PoincareRadialPullbackOperator rho sigma
        (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.sinh tau)
        (sigma * (-rho / Real.sqrt (1 - rho ^ (2 : ℕ))) * Real.sinh tau) = 0 ∧
      d4PoincareRadialPullbackOperator rho sigma
        (Real.sqrt (1 - rho ^ (2 : ℕ)) * Real.cosh tau)
        (sigma * (-rho / Real.sqrt (1 - rho ^ (2 : ℕ))) * Real.cosh tau) = 0 ∧
      d4PoincareRadialPullbackOperator rho sigma rho sigma = 1 := by
  have hpos : 0 < 1 - rho ^ (2 : ℕ) := by nlinarith [sq_nonneg rho]
  have hsqrt0 : Real.sqrt (1 - rho ^ (2 : ℕ)) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
  have hsqrt2 : Real.sqrt (1 - rho ^ (2 : ℕ)) ^ (2 : ℕ) = 1 - rho ^ (2 : ℕ) :=
    Real.sq_sqrt hpos.le
  have hsigma0 : sigma ≠ 0 := ne_of_gt hsigma
  constructor
  · unfold d4PoincareRadialPullbackOperator
    field_simp [hsqrt0, hsigma0]
    rw [hsqrt2]
    ring
  constructor
  · unfold d4PoincareRadialPullbackOperator
    field_simp [hsqrt0, hsigma0]
    rw [hsqrt2]
    ring
  · unfold d4PoincareRadialPullbackOperator
    field_simp [hsigma0]
    ring

/-- Pullback of `partial_Z` applied to a BM first-radial jet whose BM derivative is `J`. -/
def d4PoincareRadialDerivativeOnBMFirstRadialJet
    (rho sigma : ℝ) (J : ℂ) : ℂ :=
  (((-2 * rho * (1 - rho ^ (2 : ℕ))) / sigma : ℝ) : ℂ) * J

theorem d4PoincareRadialPullbackOperatorComplex_on_BMFirstRadialJet
    (rho sigma : ℝ) (J : ℂ) :
    d4PoincareRadialPullbackOperatorComplex rho sigma 0 ((-2 * rho : ℝ) * J) =
      d4PoincareRadialDerivativeOnBMFirstRadialJet rho sigma J := by
  simp [d4PoincareRadialPullbackOperatorComplex,
    d4PoincareRadialDerivativeOnBMFirstRadialJet]
  ring

theorem d4PoincareRadialDerivativeOnBMFirstRadialJet_same_BM_radius_ne
    {J : ℂ} (hJ : J ≠ 0) :
    d4PoincareRadialDerivativeOnBMFirstRadialJet (1 / 2) 1 J ≠
      d4PoincareRadialDerivativeOnBMFirstRadialJet (1 / 2) 2 J := by
  intro h
  norm_num [d4PoincareRadialDerivativeOnBMFirstRadialJet] at h
  exact hJ h

theorem d4PoincareRadialDerivativeOnBMFirstRadialJet_same_rho_ne
    {rho : ℝ} (hrho : 0 < rho) (hrho1 : rho < 1) {J : ℂ} (hJ : J ≠ 0) :
    d4PoincareRadialDerivativeOnBMFirstRadialJet rho 1 J ≠
      d4PoincareRadialDerivativeOnBMFirstRadialJet rho 2 J := by
  intro h
  change
    ((((-2 * rho * (1 - rho ^ (2 : ℕ))) / 1 : ℝ) : ℂ) * J) =
      ((((-2 * rho * (1 - rho ^ (2 : ℕ))) / 2 : ℝ) : ℂ) * J) at h
  have hreal :
      ((-2 * rho * (1 - rho ^ (2 : ℕ))) / 1 : ℝ) -
          ((-2 * rho * (1 - rho ^ (2 : ℕ))) / 2 : ℝ) ≠ 0 := by
    have hgap : 0 < 1 - rho ^ (2 : ℕ) := by nlinarith [sq_nonneg rho]
    intro hz
    field_simp at hz
    nlinarith
  have hcoef :
      (((((-2 * rho * (1 - rho ^ (2 : ℕ))) / 1 : ℝ) : ℂ) -
          (((-2 * rho * (1 - rho ^ (2 : ℕ))) / 2 : ℝ) : ℂ))) ≠ 0 := by
    exact_mod_cast hreal
  have hz :
      (((((-2 * rho * (1 - rho ^ (2 : ℕ))) / 1 : ℝ) : ℂ) -
          (((-2 * rho * (1 - rho ^ (2 : ℕ))) / 2 : ℝ) : ℂ))) * J = 0 := by
    rw [sub_mul, h, sub_self]
  exact hJ ((mul_eq_zero.mp hz).resolve_left hcoef)

theorem not_exists_d4BMRadialFactor_poincareRadialDerivativeOnBMFirstRadialJet
    {J : ℂ} (hJ : J ≠ 0) :
    ¬ ∃ F : ℝ → ℂ, ∀ rho sigma : ℝ,
      0 < rho → rho < 1 → 0 < sigma →
        d4PoincareRadialDerivativeOnBMFirstRadialJet rho sigma J =
          F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) := by
  rintro ⟨F, hF⟩
  have h1 := hF (1 / 2) 1 (by norm_num) (by norm_num) (by norm_num)
  have h2 := hF (1 / 2) 2 (by norm_num) (by norm_num) (by norm_num)
  exact d4PoincareRadialDerivativeOnBMFirstRadialJet_same_BM_radius_ne hJ
    (h1.trans h2.symm)

/-- Every Xi corner-renormalized second derivative is nonzero at some actual interior BM radius.
This follows from its nonzero endpoint finite part, without treating the endpoint value as a
constant interior jet. -/
theorem exists_d4BMXiPlusPlusCornerRenormalizedSecondDerivative_ne_zero_interior
    (n : ℕ) (q : XiZeroCopy) :
    ∃ z : ℝ, 0 < z ∧ z < 1 ∧
      d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 := by
  have hlim :=
    tendsto_d4BMXiPlusPlusCornerRenormalizedRegularSecondDerivative_one n q
  rw [nhdsWithin_Ico_eq_nhdsLT (by norm_num : (0 : ℝ) < 1)] at hlim
  have hnonzero :
      ∀ᶠ z : ℝ in 𝓝[<] (1 : ℝ),
        d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n
          (d4BMXiMixedHorizonAngularMomentum q) z ≠ 0 :=
    hlim.eventually (eventually_ne_nhds
      (d4BMXiPlusPlusCornerRenormalizedSecondDerivativeFinitePart_ne_zero n q))
  have hlt : ∀ᶠ z : ℝ in 𝓝[<] (1 : ℝ), z < 1 := self_mem_nhdsWithin
  have hpos : ∀ᶠ z : ℝ in 𝓝[<] (1 : ℝ), 0 < z :=
    Filter.Eventually.filter_mono inf_le_left
      (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))
  rcases (hnonzero.and (hpos.and hlt)).exists with ⟨z, hz, hz0, hz1⟩
  exact ⟨z, hz0, hz1, hz⟩

/-- Actual pullback coefficient on the corner-renormalized BM first radial jet. -/
def d4PoincareRadialDerivativeOnBMXiCornerFirstJet
    (n : ℕ) (q : XiZeroCopy) (rho sigma : ℝ) : ℂ :=
  d4PoincareRadialDerivativeOnBMFirstRadialJet rho sigma
    (d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n
      (d4BMXiMixedHorizonAngularMomentum q)
      (d4BMBlackHoleRadialCoordinateFromRindlerRho rho))

/-- Premise-free: on every Xi fibre, the actual physical Poincare radial derivative of the
corner-renormalized BM first jet cannot descend to a scalar function of BM radius. -/
theorem not_exists_d4BMRadialFactor_poincareRadialDerivativeOnBMXiCornerFirstJet
    (n : ℕ) (q : XiZeroCopy) :
    ¬ ∃ F : ℝ → ℂ, ∀ rho sigma : ℝ,
      0 < rho → rho < 1 → 0 < sigma →
        d4PoincareRadialDerivativeOnBMXiCornerFirstJet n q rho sigma =
          F (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) := by
  rcases exists_d4BMXiPlusPlusCornerRenormalizedSecondDerivative_ne_zero_interior n q with
    ⟨z, hz0, hz1, hz⟩
  let rho := Real.sqrt (1 - z)
  have hgap : 0 < 1 - z := by linarith
  have hrho0 : 0 < rho := Real.sqrt_pos.2 hgap
  have hrho_sq : rho ^ (2 : ℕ) = 1 - z := Real.sq_sqrt hgap.le
  have hrho1 : rho < 1 := by
    have hrho_nonneg : 0 ≤ rho := Real.sqrt_nonneg _
    nlinarith
  have hcoord : d4BMBlackHoleRadialCoordinateFromRindlerRho rho = z := by
    simp [d4BMBlackHoleRadialCoordinateFromRindlerRho, hrho_sq]
  have hJ :
      d4BMPlusPlusCornerRenormalizedRegularSecondDerivative n
        (d4BMXiMixedHorizonAngularMomentum q)
        (d4BMBlackHoleRadialCoordinateFromRindlerRho rho) ≠ 0 := by
    simpa [hcoord] using hz
  rintro ⟨F, hF⟩
  have h1 := hF rho 1 hrho0 hrho1 (by norm_num)
  have h2 := hF rho 2 hrho0 hrho1 (by norm_num)
  apply d4PoincareRadialDerivativeOnBMFirstRadialJet_same_rho_ne hrho0 hrho1 hJ
  simpa [d4PoincareRadialDerivativeOnBMXiCornerFirstJet] using h1.trans h2.symm

end

end RHTower
