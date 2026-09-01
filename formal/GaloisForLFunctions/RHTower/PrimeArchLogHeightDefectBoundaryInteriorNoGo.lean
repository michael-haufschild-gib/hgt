import GaloisForLFunctions.RHTower.PrimeArchLogHeightDefectLocalizedRationalPoleEscape
import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelEnergyPrimeD2GaussianRatWindowCriterion
import GaloisForLFunctions.RHTower.IsolatingAnnulusRung

/-!
# D2 boundary-to-interior no-go

The surviving D2 route asks for a lower bound on the actual prime--archimedean log-height defect.
This module tests a contour shortcut against the corpus's exact pole-escape law. Under false RH,
an off-line Xi zero admits an admissible rational rectangle whose complete frontier is zero-free.
The actual D2 defect is therefore continuous and bounded below on that compact frontier, while its
Gaussian-rational interior values are unbounded below at the enclosed negative-residue pole.

Consequently the proposed principle

`frontier lower bound → Gaussian-rational interior lower bound`

for every admissible D2 window is equivalent to RH itself. Boundary-size control cannot discharge
the D2 burden; a successful contour proof must first supply the RH-bearing zero/residue exclusion.
-/

open Complex Filter Topology Set Metric

namespace RHTower

noncomputable section

/-- Every positive margin admits an isolating rational rectangle around a Xi zero whose
closed envelope stays inside the margin ball. -/
theorem exists_ratRectangle_isolating_xiDivisor_closure_subset_ball
    (rho : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ u v x y : ℚ, rho ∈ ratRectangle u v x y ∧
      closure (ratRectangle u v x y) ⊆ ball rho ε ∧
      {z : ℂ | xi z = 0} ∩ frontier (ratRectangle u v x y) = ∅ ∧
      rho.re - ε / 4 < (u : ℝ) ∧ (v : ℝ) < rho.re + ε / 4 ∧
      rho.im - ε / 4 < (x : ℝ) ∧ (y : ℝ) < rho.im + ε / 4 := by
  obtain ⟨R, hR, hiso⟩ := xi_exists_isolating_radius rho
  let δ : ℝ := min R ε
  have hδ : 0 < δ := lt_min hR hε
  obtain ⟨u, huLower, huRho⟩ :=
    exists_rat_btwn (show rho.re - δ / 4 < rho.re by linarith)
  obtain ⟨v, hvRho, hvUpper⟩ :=
    exists_rat_btwn (show rho.re < rho.re + δ / 4 by linarith)
  obtain ⟨x, hxLower, hxRho⟩ :=
    exists_rat_btwn (show rho.im - δ / 4 < rho.im by linarith)
  obtain ⟨y, hyRho, hyUpper⟩ :=
    exists_rat_btwn (show rho.im < rho.im + δ / 4 by linarith)
  have hrhoRect : rho ∈ ratRectangle u v x y :=
    ⟨huRho, hvRho, hxRho, hyRho⟩
  have hclos : closure (ratRectangle u v x y) ⊆ ball rho δ := by
    have hclosed : IsClosed (closedRatRectangle u v x y) :=
      (isCompact_closedRatRectangle u v x y).isClosed
    have hclosureClosed : closure (ratRectangle u v x y) ⊆
        closedRatRectangle u v x y :=
      closure_minimal (ratRectangle_subset_closedRatRectangle u v x y) hclosed
    intro z hz
    have hzClosed := hclosureClosed hz
    have hre : |z.re - rho.re| < δ / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hzClosed.1.1, hzClosed.1.2]
    have him : |z.im - rho.im| < δ / 2 := by
      rw [abs_lt]
      constructor <;> linarith [hzClosed.2.1, hzClosed.2.2]
    have hdist : dist z rho ≤ |z.re - rho.re| + |z.im - rho.im| := by
      rw [Complex.dist_eq]
      simpa [Complex.sub_re, Complex.sub_im] using
        Complex.norm_le_abs_re_add_abs_im (z - rho)
    rw [mem_ball]
    linarith
  refine ⟨u, v, x, y, hrhoRect, ?_, ?_, ?_⟩
  · intro z hz
    have hzδ := hclos hz
    rw [mem_ball] at hzδ ⊢
    exact hzδ.trans_le (min_le_right R ε)
  · rw [Set.eq_empty_iff_forall_notMem]
    rintro z ⟨hzZero, hzFront⟩
    by_cases hzr : z = rho
    · subst z
      have hrhoInterior : rho ∈ interior (ratRectangle u v x y) := by
        rw [(isOpen_ratRectangle u v x y).interior_eq]
        exact hrhoRect
      exact hzFront.2 hrhoInterior
    · have hzδ := hclos (frontier_subset_closure hzFront)
      have hzR : z ∈ ball rho R := by
        rw [mem_ball] at hzδ ⊢
        exact hzδ.trans_le (min_le_left R ε)
      exact (hiso z hzR hzr) hzZero
  · have hδε : δ ≤ ε := min_le_right R ε
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- A high left-strip Xi zero has an admissible isolating D2 rational rectangle. -/
theorem exists_admissibleD2RatRectangle_isolating_xiDivisor
    {rho : ℂ} (hrhoRe : 0 < rho.re) (hrhoHalf : rho.re < 1 / 2)
    (hrhoHigh : 233 / 20 < rho.im) :
    ∃ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y ∧
      rho ∈ ratRectangle u v x y ∧
      {z : ℂ | xi z = 0} ∩ frontier (ratRectangle u v x y) = ∅ := by
  let ε : ℝ := min rho.re (min (1 / 2 - rho.re) (rho.im - 233 / 20))
  have hε : 0 < ε := by
    dsimp only [ε]
    exact lt_min hrhoRe (lt_min (sub_pos.mpr hrhoHalf) (sub_pos.mpr hrhoHigh))
  obtain ⟨u, v, x, y, hrhoRect, _hclos, hfront,
      huNear, hvNear, hxNear, hyNear⟩ :=
    exists_ratRectangle_isolating_xiDivisor_closure_subset_ball rho hε
  have huPos : 0 < (u : ℝ) := by
    have hεle : ε ≤ rho.re := min_le_left _ _
    linarith
  have hvHalf : (v : ℝ) < 1 / 2 := by
    have hεle : ε ≤ 1 / 2 - rho.re :=
      (min_le_right _ _).trans (min_le_left _ _)
    linarith
  have hxHigh : 233 / 20 < (x : ℝ) := by
    have hεle : ε ≤ rho.im - 233 / 20 :=
      (min_le_right _ _).trans (min_le_right _ _)
    linarith
  exact ⟨u, v, x, y,
    ⟨huPos, hrhoRect.1.trans hrhoRect.2.1, hvHalf,
      hxHigh, hrhoRect.2.2.1.trans hrhoRect.2.2.2⟩,
    hrhoRect, hfront⟩

/-- A rational rectangle frontier is compact. -/
theorem isCompact_frontier_ratRectangle (u v x y : ℚ) :
    IsCompact (frontier (ratRectangle u v x y)) := by
  have hclosed : IsClosed (closedRatRectangle u v x y) :=
    (isCompact_closedRatRectangle u v x y).isClosed
  have hsub : frontier (ratRectangle u v x y) ⊆ closedRatRectangle u v x y :=
    frontier_subset_closure.trans
      (closure_minimal (ratRectangle_subset_closedRatRectangle u v x y) hclosed)
  exact (isCompact_closedRatRectangle u v x y).of_isClosed_subset isClosed_frontier hsub

/-- On a zero-free admissible rectangle frontier, the actual D2 defect has a finite lower bound. -/
theorem exists_primeArchLogHeightDefect_frontier_lower_of_xiZeroFree
    {u v x y : ℚ} (hRect : IsAdmissibleD2RatRectangle u v x y)
    (hzeroFree : {z : ℂ | xi z = 0} ∩ frontier (ratRectangle u v x y) = ∅) :
    ∃ L : ℝ, ∀ z : ℂ, z ∈ frontier (ratRectangle u v x y) →
      L ≤ primeArchLogHeightDefect z := by
  have hclosed : IsClosed (closedRatRectangle u v x y) :=
    (isCompact_closedRatRectangle u v x y).isClosed
  have hfrontClosed : frontier (ratRectangle u v x y) ⊆
      closedRatRectangle u v x y :=
    frontier_subset_closure.trans
      (closure_minimal (ratRectangle_subset_closedRatRectangle u v x y) hclosed)
  have hcont : ContinuousOn primeArchLogHeightDefect
      (frontier (ratRectangle u v x y)) := by
    intro z hz
    have hzClosed := hfrontClosed hz
    have hzRePos : 0 < z.re := hRect.1.trans_le hzClosed.1.1
    have hzReHalf : z.re < 1 / 2 := hzClosed.1.2.trans_lt hRect.2.2.1
    have hzImPos : 0 < z.im := by
      have hxPos : 0 < (x : ℝ) := by linarith [hRect.2.2.2.1]
      exact hxPos.trans_le hzClosed.2.1
    have hxi : xi z ≠ 0 := by
      intro hzXi
      exact (Set.eq_empty_iff_forall_notMem.mp hzeroFree z) ⟨hzXi, hz⟩
    have hzOne : z ≠ 1 := by
      intro hz1
      have hre := congrArg Complex.re hz1
      simp at hre
      linarith
    have hzeta : riemannZeta z ≠ 0 := by
      intro hzetaZero
      exact hxi ((xi_eq_zero_iff hzRePos hzOne).mpr hzetaZero)
    have hc :=
      continuousAt_primeArchLogHeightComplexDefect_of_riemannZeta_ne_zero
        hzImPos hzeta
    have hcRe : ContinuousAt
        (fun w : ℂ ↦ (primeArchLogHeightComplexDefect w).re) z :=
      Complex.continuous_re.continuousAt.comp hc
    simpa only [primeArchLogHeightComplexDefect_re] using hcRe.continuousWithinAt
  have himage : IsCompact
      (primeArchLogHeightDefect '' frontier (ratRectangle u v x y)) :=
    (isCompact_frontier_ratRectangle u v x y).image_of_continuousOn hcont
  obtain ⟨L, hL⟩ := himage.bddBelow
  refine ⟨L, ?_⟩
  intro z hz
  exact hL ⟨z, hz, rfl⟩

/-- A boundary-good but interior-bad window for the actual D2 defect. -/
def PrimeArchLogHeightDefectBoundaryBlindWindow : Prop :=
  ∃ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y ∧
    (∃ L : ℝ, ∀ z : ℂ, z ∈ frontier (ratRectangle u v x y) →
      L ≤ primeArchLogHeightDefect z) ∧
    ∀ B : ℝ, ∃ q : ℚ × ℚ,
      gaussianRatPoint q ∈ ratRectangle u v x y ∧
      primeArchLogHeightDefect (gaussianRatPoint q) < B

/-- False RH produces a window whose actual D2 defect is bounded below on the complete boundary
but unbounded below at Gaussian-rational interior points. -/
theorem primeArchLogHeightDefectBoundaryBlindWindow_of_not_rh
    (hnot : ¬RiemannHypothesis) :
    PrimeArchLogHeightDefectBoundaryBlindWindow := by
  obtain ⟨rho, hrhoRe, hrhoHalf, hrhoHigh, hrhoZero⟩ :=
    exists_leftUpperXiZero_above_twoHundredThirtyThree_twentieths_of_not_rh hnot
  obtain ⟨u, v, x, y, hRect, hrhoRect, hzeroFree⟩ :=
    exists_admissibleD2RatRectangle_isolating_xiDivisor hrhoRe hrhoHalf hrhoHigh
  have hboundary :=
    exists_primeArchLogHeightDefect_frontier_lower_of_xiZeroFree hRect hzeroFree
  refine ⟨u, v, x, y, hRect, hboundary, ?_⟩
  intro B
  exact exists_gaussianRat_primeArchLogHeightDefect_lt_in_ratRectangle_of_xiZero
    hrhoRe hrhoHalf (by linarith) hrhoZero (by linarith [hRect.2.2.2.1]) hrhoRect B

theorem not_rh_of_primeArchLogHeightDefectBoundaryBlindWindow
    (hbad : PrimeArchLogHeightDefectBoundaryBlindWindow) :
    ¬RiemannHypothesis := by
  apply not_rh_of_primeArchLogHeightDefectGaussianRatLocalizedUnboundedBelow
  obtain ⟨u, v, x, y, hRect, _hboundary, hinterior⟩ := hbad
  exact ⟨u, v, x, y, hRect, hinterior⟩

theorem primeArchLogHeightDefectBoundaryBlindWindow_iff_not_rh :
    PrimeArchLogHeightDefectBoundaryBlindWindow ↔ ¬RiemannHypothesis :=
  ⟨not_rh_of_primeArchLogHeightDefectBoundaryBlindWindow,
    primeArchLogHeightDefectBoundaryBlindWindow_of_not_rh⟩

/-- Proposed D2 contour bridge: a finite lower bound on an admissible window boundary forces a
finite lower bound on all Gaussian-rational points in its interior. -/
def PrimeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower : Prop :=
  ∀ u v x y : ℚ, IsAdmissibleD2RatRectangle u v x y →
    (∃ L : ℝ, ∀ z : ℂ, z ∈ frontier (ratRectangle u v x y) →
      L ≤ primeArchLogHeightDefect z) →
    ∃ L : ℝ, ∀ q : ℚ × ℚ, gaussianRatPoint q ∈ ratRectangle u v x y →
      L ≤ primeArchLogHeightDefect (gaussianRatPoint q)

theorem primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower_of_rh
    (hRH : RiemannHypothesis) :
    PrimeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower := by
  have hwindows :=
    primeArchLogHeightDefectGaussianRatAdmissibleWindowsBoundedBelow_of_rh hRH
  intro u v x y hRect _hboundary
  exact hwindows u v x y hRect

theorem riemannHypothesis_of_primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower
    (hbridge : PrimeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower) :
    RiemannHypothesis := by
  by_contra hnot
  obtain ⟨u, v, x, y, hRect, hboundary, hinterior⟩ :=
    primeArchLogHeightDefectBoundaryBlindWindow_of_not_rh hnot
  obtain ⟨L, hL⟩ := hbridge u v x y hRect hboundary
  obtain ⟨q, hqRect, hqBad⟩ := hinterior L
  exact (not_lt_of_ge (hL q hqRect)) hqBad

/-- Exact classification of the boundary-only contour bridge: for the actual D2 defect it is
equivalent to RH, so it cannot be an independent route to the missing interior lower bound. -/
theorem primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower_iff_rh :
    PrimeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower ↔
      RiemannHypothesis :=
  ⟨riemannHypothesis_of_primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower,
    primeArchLogHeightDefectFrontierLowerForcesGaussianRatInteriorLower_of_rh⟩

end

end RHTower
