import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinActualThirdJet

/-!
# Literal Bochner current for the actual second Stokes defect

Corpus conjecture C-A.9t4b closes the last pointwise analytic premise in the balanced spin-two
coefficient.  For the actual repeated completed Poincare leg `F`, set

`e = y^(2 : ℕ) (F_x^(2 : ℕ) + F_y^(2 : ℕ))`.

The genuine third jets prove the hyperbolic Bochner law

`L e = 2 |Hess F|^(2 : ℕ) + 2 (lambda - 1) e`.

For the actual projecting leg `G`, the current `K = G grad e - e grad G` therefore satisfies

`2 secondDefect = y^(2 : ℕ) div K`.

No premise, proxy moment, symbolic derivative, or boundary assumption occurs.  The RH chain is

`actual second defect = divergence -> second modular Green/Stokes -> actual balanced BM ++-
coefficient -> negative BM leg -> conserved left-QNM projection -> HC94 -> RH`.
-/

open Complex Real Filter Set Topology

namespace RHTower
noncomputable section

/-- Hyperbolic gradient energy of the repeated actual completed Poincare leg. -/
def d4BMActualSecondStokesEnergy
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  (z.y : ℂ) ^ (2 : ℕ) *
    (d4BMCompletedPoincareHorizontalFirstJet z P ^ (2 : ℕ) +
      d4BMCompletedPoincareVerticalFirstJet z P ^ (2 : ℕ))

/-- Genuine horizontal derivative of the hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyHorizontalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * (z.y : ℂ) ^ (2 : ℕ) *
    (d4BMCompletedPoincareHorizontalFirstJet z P *
        d4BMCompletedPoincareHorizontalSecondJet z P +
      d4BMCompletedPoincareVerticalFirstJet z P *
        d4BMCompletedPoincareMixedSecondJet z P)

/-- Genuine vertical derivative of the hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyVerticalFirstJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * (z.y : ℂ) *
      (d4BMCompletedPoincareHorizontalFirstJet z P ^ (2 : ℕ) +
        d4BMCompletedPoincareVerticalFirstJet z P ^ (2 : ℕ)) +
    2 * (z.y : ℂ) ^ (2 : ℕ) *
      (d4BMCompletedPoincareHorizontalFirstJet z P *
          d4BMCompletedPoincareMixedSecondJet z P +
        d4BMCompletedPoincareVerticalFirstJet z P *
          d4BMCompletedPoincareVerticalSecondJet z P)

/-- Genuine horizontal second derivative of the hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyHorizontalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 * (z.y : ℂ) ^ (2 : ℕ) *
    (d4BMCompletedPoincareHorizontalSecondJet z P ^ (2 : ℕ) +
      d4BMCompletedPoincareHorizontalFirstJet z P *
        d4BMCompletedPoincareHorizontalThirdJet z P +
      d4BMCompletedPoincareMixedSecondJet z P ^ (2 : ℕ) +
      d4BMCompletedPoincareVerticalFirstJet z P *
        d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P)

/-- Genuine vertical second derivative of the hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyVerticalSecondJet
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  2 *
      (d4BMCompletedPoincareHorizontalFirstJet z P ^ (2 : ℕ) +
        d4BMCompletedPoincareVerticalFirstJet z P ^ (2 : ℕ)) +
    8 * (z.y : ℂ) *
      (d4BMCompletedPoincareHorizontalFirstJet z P *
          d4BMCompletedPoincareMixedSecondJet z P +
        d4BMCompletedPoincareVerticalFirstJet z P *
          d4BMCompletedPoincareVerticalSecondJet z P) +
    2 * (z.y : ℂ) ^ (2 : ℕ) *
      (d4BMCompletedPoincareMixedSecondJet z P ^ (2 : ℕ) +
        d4BMCompletedPoincareHorizontalFirstJet z P *
          d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P +
        d4BMCompletedPoincareVerticalSecondJet z P ^ (2 : ℕ) +
        d4BMCompletedPoincareVerticalFirstJet z P *
          d4BMCompletedPoincareVerticalThirdJet z P)

theorem hasDerivAt_d4BMActualSecondStokesEnergy_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMActualSecondStokesEnergy (d4BMHorizontalCoordinate z x) P)
      (d4BMActualSecondStokesEnergyHorizontalFirstJet z P) z.x := by
  have hFx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z P
  have hFy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal z P
  have h := ((hFx.pow 2).add (hFy.pow 2)).const_mul ((z.y : ℂ) ^ (2 : ℕ))
  have hz : d4BMHorizontalCoordinate z z.x = z := by cases z; rfl
  rw [hz] at h
  have h' : HasDerivAt
      (fun x : ℝ => (z.y : ℂ) ^ (2 : ℕ) *
        (d4BMCompletedPoincareHorizontalFirstJet (d4BMHorizontalCoordinate z x) P ^ (2 : ℕ) +
          d4BMCompletedPoincareVerticalFirstJet (d4BMHorizontalCoordinate z x) P ^ (2 : ℕ)))
      (d4BMActualSecondStokesEnergyHorizontalFirstJet z P) z.x := by
    apply h.congr_deriv
    unfold d4BMActualSecondStokesEnergyHorizontalFirstJet
    norm_num
    ring
  simpa [d4BMActualSecondStokesEnergy, d4BMHorizontalCoordinate] using h'

theorem hasDerivAt_d4BMActualSecondStokesEnergyHorizontalFirstJet_horizontal
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMActualSecondStokesEnergyHorizontalFirstJet
        (d4BMHorizontalCoordinate z x) P)
      (d4BMActualSecondStokesEnergyHorizontalSecondJet z P) z.x := by
  have hFx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z P
  have hFxx := hasDerivAt_d4BMCompletedPoincareHorizontalSecondJet_horizontal z P
  have hFy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJet_horizontal z P
  have hFxy := hasDerivAt_d4BMCompletedPoincareMixedSecondJet_horizontal z P
  have h := ((hFx.mul hFxx).add (hFy.mul hFxy)).const_mul
    (2 * (z.y : ℂ) ^ (2 : ℕ))
  have hz : d4BMHorizontalCoordinate z z.x = z := by cases z; rfl
  rw [hz] at h
  have h' : HasDerivAt
      (fun x : ℝ => 2 * (z.y : ℂ) ^ (2 : ℕ) *
        (d4BMCompletedPoincareHorizontalFirstJet (d4BMHorizontalCoordinate z x) P *
            d4BMCompletedPoincareHorizontalSecondJet (d4BMHorizontalCoordinate z x) P +
          d4BMCompletedPoincareVerticalFirstJet (d4BMHorizontalCoordinate z x) P *
            d4BMCompletedPoincareMixedSecondJet (d4BMHorizontalCoordinate z x) P))
      (d4BMActualSecondStokesEnergyHorizontalSecondJet z P) z.x := by
    apply h.congr_deriv
    unfold d4BMActualSecondStokesEnergyHorizontalSecondJet
    ring
  simpa [d4BMActualSecondStokesEnergyHorizontalFirstJet,
    d4BMHorizontalCoordinate] using h'

/-- Vertical slice of the actual hyperbolic gradient energy. -/
def d4BMActualSecondStokesEnergyVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  (y : ℂ) ^ (2 : ℕ) *
    (d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P y ^ (2 : ℕ) +
      d4BMCompletedPoincareVerticalFirstJetSlice z P y ^ (2 : ℕ))

/-- Vertical slice of the genuine first vertical energy jet. -/
def d4BMActualSecondStokesEnergyVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  2 * (y : ℂ) *
      (d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P y ^ (2 : ℕ) +
        d4BMCompletedPoincareVerticalFirstJetSlice z P y ^ (2 : ℕ)) +
    2 * (y : ℂ) ^ (2 : ℕ) *
      (d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P y *
          d4BMCompletedPoincareMixedSecondJetVerticalSlice z P y +
        d4BMCompletedPoincareVerticalFirstJetSlice z P y *
          d4BMCompletedPoincareVerticalSecondJetSlice z P y)

@[simp] theorem d4BM_actualSecondStokesEnergyVerticalSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergyVerticalSlice z P z.y =
      d4BMActualSecondStokesEnergy z P := by rfl

@[simp] theorem d4BM_actualSecondStokesEnergyVerticalFirstJetSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesEnergyVerticalFirstJetSlice z P z.y =
      d4BMActualSecondStokesEnergyVerticalFirstJet z P := by rfl

theorem hasDerivAt_d4BMActualSecondStokesEnergyVerticalSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMActualSecondStokesEnergyVerticalSlice z P)
      (d4BMActualSecondStokesEnergyVerticalFirstJet z P) z.y := by
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.y := hidR.ofReal_comp
  have hFx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P
  have hFy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z P
  have h := (hid.pow 2).mul ((hFx.pow 2).add (hFy.pow 2))
  simp only [Pi.pow_apply, Pi.add_apply,
    d4BM_completedPoincareHorizontalFirstJetVerticalSlice_at_height,
    d4BMCompletedPoincareVerticalFirstJetSlice_at_height] at h
  refine h.congr_deriv ?_
  unfold d4BMActualSecondStokesEnergyVerticalFirstJet
  ring

theorem hasDerivAt_d4BMActualSecondStokesEnergyVerticalFirstJetSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMActualSecondStokesEnergyVerticalFirstJetSlice z P)
      (d4BMActualSecondStokesEnergyVerticalSecondJet z P) z.y := by
  have hidR : HasDerivAt (fun y : ℝ => y) 1 z.y := hasDerivAt_id z.y
  have hid : HasDerivAt (fun y : ℝ => (y : ℂ)) 1 z.y := hidR.ofReal_comp
  have hFx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJetVerticalSlice z P
  have hFy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z P
  have hFxy := hasDerivAt_d4BMCompletedPoincareMixedSecondJetVerticalSlice z P
  have hFyy := hasDerivAt_d4BMCompletedPoincareVerticalSecondJetSlice z P
  have hq := (hFx.pow 2).add (hFy.pow 2)
  have hr := (hFx.mul hFxy).add (hFy.mul hFyy)
  have h := ((hid.const_mul (2 : ℂ)).mul hq).add
    (((hid.pow 2).const_mul (2 : ℂ)).mul hr)
  have hz : (⟨z.x, z.y, z.y_pos⟩ : D4BMUpperHalfPlaneCoordinate) = z := by
    cases z
    rfl
  simp only [Pi.pow_apply, Pi.add_apply, Pi.mul_apply,
    d4BM_completedPoincareHorizontalFirstJetVerticalSlice_at_height,
    d4BMCompletedPoincareVerticalFirstJetSlice_at_height,
    d4BM_completedPoincareMixedSecondJetVerticalSlice_at_height,
    d4BMCompletedPoincareVerticalSecondJetSlice_eq_at z P z.y_pos] at h
  rw [hz] at h
  refine h.congr_deriv ?_
  unfold d4BMActualSecondStokesEnergyVerticalSecondJet
  ring

/-- Horizontal component of the literal second Bochner--Stokes current. -/
def d4BMActualSecondStokesHorizontalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMActualSecondStokesEnergyHorizontalFirstJet z P -
    d4BMActualSecondStokesEnergy z P *
      d4BMCompletedPoincareHorizontalFirstJet z Q

/-- Vertical component of the literal second Bochner--Stokes current. -/
def d4BMActualSecondStokesVerticalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMActualSecondStokesEnergyVerticalFirstJet z P -
    d4BMActualSecondStokesEnergy z P *
      d4BMCompletedPoincareVerticalFirstJet z Q

def d4BMActualSecondStokesHorizontalDivergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMActualSecondStokesEnergyHorizontalSecondJet z P -
    d4BMActualSecondStokesEnergy z P *
      d4BMCompletedPoincareHorizontalSecondJet z Q

def d4BMActualSecondStokesVerticalDivergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) : ℂ :=
  d4BMCompletedEisensteinPoincareSeries z Q *
      d4BMActualSecondStokesEnergyVerticalSecondJet z P -
    d4BMActualSecondStokesEnergy z P *
      d4BMCompletedPoincareVerticalSecondJet z Q

theorem hasDerivAt_d4BMActualSecondStokesHorizontalCurrent
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt
      (fun x : ℝ => d4BMActualSecondStokesHorizontalCurrent
        (d4BMHorizontalCoordinate z x) P Q)
      (d4BMActualSecondStokesHorizontalDivergence z P Q) z.x := by
  have hG := hasDerivAt_d4BMCompletedEisensteinPoincareSeries_horizontal z Q
  have hEx := hasDerivAt_d4BMActualSecondStokesEnergyHorizontalFirstJet_horizontal z P
  have hE := hasDerivAt_d4BMActualSecondStokesEnergy_horizontal z P
  have hGx := hasDerivAt_d4BMCompletedPoincareHorizontalFirstJet_horizontal z Q
  have h := (hG.mul hEx).sub (hE.mul hGx)
  have hz : d4BMHorizontalCoordinate z z.x = z := by cases z; rfl
  rw [hz] at h
  refine h.congr_deriv ?_
  unfold d4BMActualSecondStokesHorizontalDivergence
  ring

/-- Vertical slice of the second Bochner--Stokes current. -/
def d4BMActualSecondStokesVerticalCurrentSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) (y : ℝ) : ℂ :=
  d4BMCompletedPoincareVerticalSlice z Q y *
      d4BMActualSecondStokesEnergyVerticalFirstJetSlice z P y -
    d4BMActualSecondStokesEnergyVerticalSlice z P y *
      d4BMCompletedPoincareVerticalFirstJetSlice z Q y

@[simp] theorem d4BM_actualSecondStokesVerticalCurrentSlice_at_height
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    d4BMActualSecondStokesVerticalCurrentSlice z P Q z.y =
      d4BMActualSecondStokesVerticalCurrent z P Q := by rfl

theorem hasDerivAt_d4BMActualSecondStokesVerticalCurrentSlice
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    HasDerivAt (d4BMActualSecondStokesVerticalCurrentSlice z P Q)
      (d4BMActualSecondStokesVerticalDivergence z P Q) z.y := by
  have hG := hasDerivAt_d4BMCompletedPoincareVerticalSlice z Q
  have hEy := hasDerivAt_d4BMActualSecondStokesEnergyVerticalFirstJetSlice z P
  have hE := hasDerivAt_d4BMActualSecondStokesEnergyVerticalSlice z P
  have hGy := hasDerivAt_d4BMCompletedPoincareVerticalFirstJetSlice z Q
  have h := (hG.mul hEy).sub (hE.mul hGy)
  simp only [d4BMCompletedPoincareVerticalSlice_at_height,
    d4BM_actualSecondStokesEnergyVerticalFirstJetSlice_at_height,
    d4BM_actualSecondStokesEnergyVerticalSlice_at_height,
    d4BMCompletedPoincareVerticalFirstJetSlice_at_height] at h
  refine h.congr_deriv ?_
  unfold d4BMActualSecondStokesVerticalDivergence
  ring

/-- Vertically differentiated completed eigen equation in denominator-free form. -/
theorem d4BM_completedPoincare_thirdJet_verticalEigenEquation
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ (3 : ℕ) *
        (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P +
          d4BMCompletedPoincareVerticalThirdJet z P) =
      P.s * (P.s - 1) * (z.y : ℂ) *
          d4BMCompletedPoincareVerticalFirstJet z P -
        2 * P.s * (P.s - 1) *
          d4BMCompletedEisensteinPoincareSeries z P := by
  have hy : (z.y : ℂ) ≠ 0 := by exact_mod_cast z.y_pos.ne'
  unfold d4BMCompletedPoincareVerticalThirdJet
  field_simp [hy]
  ring

private theorem d4BM_secondStokes_bochner_algebra
    (y f fx fy fxx fxy fyy fxxx fxxy fxyy fyyy lambda : ℂ)
    (htrace : y ^ (2 : ℕ) * (fxx + fyy) = lambda * f)
    (hx : y ^ (2 : ℕ) * (fxxx + fxyy) = lambda * fx)
    (hy : y ^ (3 : ℕ) * (fxxy + fyyy) = lambda * y * fy - 2 * lambda * f) :
    y ^ (2 : ℕ) *
        (2 * y ^ (2 : ℕ) * (fxx ^ (2 : ℕ) + fx * fxxx + fxy ^ (2 : ℕ) + fy * fxxy) +
          (2 * (fx ^ (2 : ℕ) + fy ^ (2 : ℕ)) +
            8 * y * (fx * fxy + fy * fyy) +
            2 * y ^ (2 : ℕ) * (fxy ^ (2 : ℕ) + fx * fxyy + fyy ^ (2 : ℕ) + fy * fyyy))) =
      2 * ((y ^ (2 : ℕ) * fxx - y * fy) ^ (2 : ℕ) +
        2 * (y ^ (2 : ℕ) * fxy + y * fx) ^ (2 : ℕ) +
        (y ^ (2 : ℕ) * fyy + y * fy) ^ (2 : ℕ)) +
      2 * (lambda - 1) * (y ^ (2 : ℕ) * (fx ^ (2 : ℕ) + fy ^ (2 : ℕ))) := by
  linear_combination
    2 * y ^ (2 : ℕ) * fx * hx + 2 * y * fy * hy + 4 * y * fy * htrace

/-- **C-A.9t4b actual Bochner identity.**  Genuine third jets give the exact hyperbolic
energy-Hessian law for the actual completed Poincare series. -/
theorem d4BM_actualSecondStokes_bochnerIdentity
    (z : D4BMUpperHalfPlaneCoordinate)
    (P : D4BMEisensteinAbsoluteConvergenceParameter) :
    (z.y : ℂ) ^ (2 : ℕ) *
        (d4BMActualSecondStokesEnergyHorizontalSecondJet z P +
          d4BMActualSecondStokesEnergyVerticalSecondJet z P) =
      2 * (d4BMActualHyperbolicHessianXX z P ^ (2 : ℕ) +
        2 * d4BMActualHyperbolicHessianXY z P ^ (2 : ℕ) +
        d4BMActualHyperbolicHessianYY z P ^ (2 : ℕ)) +
      2 * (P.s * (P.s - 1) - 1) * d4BMActualSecondStokesEnergy z P := by
  have htrace :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z P
  have hx := d4BM_completedPoincare_thirdJet_horizontalEigenEquation z P
  have hy := d4BM_completedPoincare_thirdJet_verticalEigenEquation z P
  have hy' :
      (z.y : ℂ) ^ (3 : ℕ) *
          (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P +
            d4BMCompletedPoincareVerticalThirdJet z P) =
        (P.s * (P.s - 1)) * (z.y : ℂ) *
            d4BMCompletedPoincareVerticalFirstJet z P -
          2 * (P.s * (P.s - 1)) *
            d4BMCompletedEisensteinPoincareSeries z P := by
    simpa only [mul_assoc] using hy
  unfold d4BMActualSecondStokesEnergyHorizontalSecondJet
    d4BMActualSecondStokesEnergyVerticalSecondJet
    d4BMActualHyperbolicHessianXX d4BMActualHyperbolicHessianXY
    d4BMActualHyperbolicHessianYY d4BMActualSecondStokesEnergy
  exact d4BM_secondStokes_bochner_algebra
    (z.y : ℂ)
    (d4BMCompletedEisensteinPoincareSeries z P)
    (d4BMCompletedPoincareHorizontalFirstJet z P)
    (d4BMCompletedPoincareVerticalFirstJet z P)
    (d4BMCompletedPoincareHorizontalSecondJet z P)
    (d4BMCompletedPoincareMixedSecondJet z P)
    (d4BMCompletedPoincareVerticalSecondJet z P)
    (d4BMCompletedPoincareHorizontalThirdJet z P)
    (d4BMCompletedPoincareHorizontalHorizontalVerticalThirdJet z P)
    (d4BMCompletedPoincareHorizontalVerticalVerticalThirdJet z P)
    (d4BMCompletedPoincareVerticalThirdJet z P)
    (P.s * (P.s - 1)) htrace hx hy'

/-- **C-A.9t4b second-defect divergence theorem.**  The sole surviving actual balanced
spin-two defect is exactly one literal Bochner-current divergence.  Thus no interior analytic
premise remains: only the modular-domain boundary theorem can obstruct the coefficient route. -/
theorem d4BM_actualSecondStokesDefectDensity_eq_divergence
    (z : D4BMUpperHalfPlaneCoordinate)
    (P Q : D4BMEisensteinAbsoluteConvergenceParameter) :
    2 * d4BMActualSecondStokesDefectDensity z P Q =
      (z.y : ℂ) ^ (2 : ℕ) *
        (d4BMActualSecondStokesHorizontalDivergence z P Q +
          d4BMActualSecondStokesVerticalDivergence z P Q) := by
  have hbochner := d4BM_actualSecondStokes_bochnerIdentity z P
  have hQ :=
    d4BM_completedEisensteinPoincareSeries_hyperbolicLaplacian_eq_eigenvalue z Q
  unfold d4BMActualSecondStokesDefectDensity d4BMHyperbolicSecondStokesDefect
    d4BMHyperbolicDiagonalGradientShift d4BMActualSecondStokesHessianDensity
    d4BMActualFirstStokesGradientDensity
    d4BMActualSecondStokesHorizontalDivergence
    d4BMActualSecondStokesVerticalDivergence
  unfold d4BMActualSecondStokesEnergy at hbochner ⊢
  linear_combination
    -d4BMCompletedEisensteinPoincareSeries z Q * hbochner +
      ((z.y : ℂ) ^ (2 : ℕ) *
        (d4BMCompletedPoincareHorizontalFirstJet z P ^ (2 : ℕ) +
          d4BMCompletedPoincareVerticalFirstJet z P ^ (2 : ℕ))) * hQ

end
end RHTower
