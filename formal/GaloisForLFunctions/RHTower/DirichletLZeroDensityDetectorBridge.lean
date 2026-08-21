/-
# CGL detector bridge from centered completed-Dirichlet-L zero windows

This module turns an actual completed-Dirichlet-L zero selected from the
literal centered zero-density window at real-part threshold `1 / 2` into the
certified CGL critical-strip L-zero consumed by the Mellin zero detector.  The
conversion internally discharges the gamma-factor exception at zero and the
strict upper strip bound using the window certificate and Dirichlet
nonvanishing on `Re(s) ≥ 1`.

No RH, GRH, zero-detection alternative, large-value estimate, or density
bound is used.
-/

import GaloisForLFunctions.RHTower.DirichletLZeroDensityWindowRows
import GaloisForLFunctions.RHTower.ChenGuptaLiNonprincipalContourBalance

open Complex Filter

noncomputable section

namespace RHTower

/-- A certified completed-L zero in the literal `1 / 2 ≤ Re(s) ≤ 1` window
gives the CGL critical-strip L-zero used by the Mellin detector. -/
def cglCriticalStripLZeroOfWindowPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H) :
    CGLCriticalStripLZero n := by
  have hwindow := cglZeroDensityVerticalWindowZeroSupport_subset_window n χ (1 / 2) τ H z.2
  have hhalf : (1 / 2 : ℝ) ≤ z.1.re := hwindow.1
  have hpoint_ne_zero : z.1 ≠ 0 := by
    intro hzero
    have hreal := congrArg Complex.re hzero
    rw [hreal] at hhalf
    norm_num at hhalf
  have hLzero : DirichletCharacter.LFunction χ.1 z.1 = 0 := by
    rw [DirichletCharacter.LFunction_eq_completed_div_gammaFactor χ.1 z.1 (Or.inl hpoint_ne_zero)]
    rw [cglZeroDensityVerticalWindowZeroSupportPoint_isZero n χ (1 / 2) τ H z]
    exact zero_div _
  have hlt_one : z.1.re < 1 := by
    by_contra hnot
    exact (DirichletCharacter.LFunction_ne_zero_of_one_le_re χ.1 (Or.inl χ.2)
      (le_of_not_gt hnot)) hLzero
  let hbase : CGLDirichletLZero n :=
    { character := χ.1
      point := z.1
      vanishes := hLzero }
  exact CGLCriticalStripLZero.mk hbase hhalf hlt_one

/-- The finite CGL detector remainder is exactly one at every certified
centered-window zero in the critical strip. -/
theorem cglFiniteDetectorRemainder_at_windowPoint
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H) :
    cglFiniteDetectorRemainder X n
      (cglCriticalStripLZeroOfWindowPoint n χ τ H z).toCGLDirichletLZero = 1 :=
  cglFiniteDetectorRemainder_at_zero X n
    (cglCriticalStripLZeroOfWindowPoint n χ τ H z).toCGLDirichletLZero

/-- The finite CGL detector remainder has norm one at every certified
centered-window zero in the critical strip. -/
theorem norm_cglFiniteDetectorRemainder_at_windowPoint
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H) :
    ‖cglFiniteDetectorRemainder X n
      (cglCriticalStripLZeroOfWindowPoint n χ τ H z).toCGLDirichletLZero‖ = 1 :=
  norm_cglFiniteDetectorRemainder_at_zero X n
    (cglCriticalStripLZeroOfWindowPoint n χ τ H z).toCGLDirichletLZero

/-- The apparent Gamma pole of the CGL Mellin detector cancels at every
certified centered-window zero in the critical strip. -/
theorem cglDetectorMellinIntegrand_poleLimit_at_windowPoint
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H) :
    Tendsto (fun w : ℂ => w * cglDetectorMellinIntegrand X n
      (cglCriticalStripLZeroOfWindowPoint n χ τ H z) w)
      (nhdsWithin 0 ({0}ᶜ : Set ℂ)) (nhds 0) :=
  cglDetectorMellinIntegrand_poleLimit_at_criticalZero X n
    (cglCriticalStripLZeroOfWindowPoint n χ τ H z)

/-- The window character's nonprincipality upgrades its critical-strip zero
to the CGL nonprincipal contour branch. -/
def cglNonprincipalCriticalStripLZeroOfWindowPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H) :
    CGLNonprincipalCriticalStripLZero n :=
  CGLNonprincipalCriticalStripLZero.mk
    (cglCriticalStripLZeroOfWindowPoint n χ τ H z) χ.2

/-- On every certified safe rectangle, the CGL detector attached to an actual
centered-window zero has vanishing contour boundary integral. -/
theorem rectIntegral_cglNonprincipalDetectorMellinIntegrand_at_windowPoint
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (z : CGLZeroDensityVerticalWindowZero (n := n) χ (1 / 2) τ H)
    (r : CGLNonprincipalDetectorRectangle) :
    rectIntegral (cglDetectorMellinIntegrand X n
      (cglNonprincipalCriticalStripLZeroOfWindowPoint n χ τ H z).toCGLCriticalStripLZero)
      r.lower r.upper = 0 :=
  rectIntegral_cglNonprincipalDetectorMellinIntegrand_eq_zero X n
    (cglNonprincipalCriticalStripLZeroOfWindowPoint n χ τ H z) r

/-- The nonprincipal critical-strip zero retained by a selected CGL row in
the `1 / 2` window. -/
def cglNonprincipalCriticalStripLZeroOfSelectedRowsPoint
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ (1 / 2) τ H)))
    (r : Fin (Fintype.card (↑S))) : CGLNonprincipalCriticalStripLZero n :=
  cglNonprincipalCriticalStripLZeroOfWindowPoint n χ τ H
    (cglZeroDensityVerticalWindowSelectedRowsPoint n χ (1 / 2) τ H S r)

/-- The certified selected row stores exactly the ordinate of its
nonprincipal critical-strip zero companion. -/
theorem cglNonprincipalCriticalStripLZeroOfSelectedRowsPoint_im_eq_time
    (n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ (1 / 2) τ H)))
    (r : Fin (Fintype.card (↑S))) :
    (cglNonprincipalCriticalStripLZeroOfSelectedRowsPoint n χ τ H S r).point.im =
      (cglZeroDensityVerticalWindowSelectedRows n χ (1 / 2) τ H S r).time := by
  exact cglZeroDensityVerticalWindowSelectedRowsPoint_im_eq_time n χ (1 / 2) τ H S r

/-- Every selected unit-window CGL row has the verified nonprincipal detector
contour cancellation on each certified safe rectangle. -/
theorem rectIntegral_cglNonprincipalDetectorMellinIntegrand_at_selectedRowsPoint
    (X n : ℕ) (χ : NonprincipalDirichletCharacter n) (τ : ℝ) (H : NNReal)
    (S : Finset (Fin (cglZeroDensityVerticalWindowCopyCard n χ (1 / 2) τ H)))
    (r : Fin (Fintype.card (↑S))) (R : CGLNonprincipalDetectorRectangle) :
    rectIntegral (cglDetectorMellinIntegrand X n
      (cglNonprincipalCriticalStripLZeroOfSelectedRowsPoint n χ τ H S r).toCGLCriticalStripLZero)
      R.lower R.upper = 0 :=
  rectIntegral_cglNonprincipalDetectorMellinIntegrand_at_windowPoint X n χ τ H
    (cglZeroDensityVerticalWindowSelectedRowsPoint n χ (1 / 2) τ H S r) R

end RHTower
