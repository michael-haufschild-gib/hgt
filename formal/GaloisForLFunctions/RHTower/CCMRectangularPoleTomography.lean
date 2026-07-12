import GaloisForLFunctions.RHTower.CCMRectangularTransverseGrowth

/-!
# Pole tomography from one rectangular Dirichlet carrier

The Xi-cancelled shifted-zeta series divided by its cancelling Xi factor is a
canonical meromorphic continuation of half the rectangular dominant Dirichlet
series.  In the half-plane `Re s > 1`, its poles are simple and occur exactly
at `1 + (rho - 1/2)` for the Xi zeros to the right of the critical line.
-/

open Complex Filter Function Set

namespace RHTower

noncomputable section

/-- The canonical meromorphic continuation of the unscaled right rectangular
Dirichlet carrier. -/
def xiRectangularRightDirichletContinuation (L : ℝ) (s : ℂ) : ℂ :=
  xiRectangularCancelledSeries L s / xi (s - 1 / 2)

/-- A shifted Xi zero in `Re s > 1` is exactly a right-divisor pole
coordinate. -/
theorem exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero
    {s : ℂ} (hs : 1 < s.re) (hzero : xi (s - 1 / 2) = 0) :
    ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  let ρ : XiDivisorSupport :=
    ⟨s - 1 / 2, mem_xi_divisor_support_of_eq_zero hzero⟩
  have hm : 0 < Int.toNat
      ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
    exact Int.toNat_pos.mpr (xi_divisor_pos_on_support ρ)
  let q0 : XiZeroCopy := ⟨ρ, ⟨0, hm⟩⟩
  have hq0 : 0 < (I * xiSpectralPoint q0).re := by
    rw [I_mul_xiSpectralPoint]
    dsimp only [q0, ρ]
    simp only [Complex.sub_re, ofReal_re]
    linarith
  let q : XiRightZeroCopy := ⟨q0, hq0⟩
  refine ⟨q, ?_⟩
  rw [xiRightShiftedPole, xiRightCenteredZero, I_mul_xiSpectralPoint]
  dsimp only [q, q0, ρ]
  ring

/-- Every right-divisor pole coordinate is a zero of the shifted Xi factor. -/
theorem xi_shifted_eq_zero_at_xiRightShiftedPole (q : XiRightZeroCopy) :
    xi (xiRightShiftedPole q - 1 / 2) = 0 := by
  rw [xiRightShiftedPole_sub_half]
  exact xi_eq_zero_of_mem_divisor_support q.1.1

/-- The continuation is meromorphic throughout the connected half-plane
`Re s > 1`. -/
theorem meromorphicOn_xiRectangularRightDirichletContinuation_rightOne
    (L : ℝ) :
    MeromorphicOn (xiRectangularRightDirichletContinuation L)
      {s : ℂ | 1 < s.re} := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hnum : AnalyticOnNhd ℂ (xiRectangularCancelledSeries L) U :=
    (differentiableOn_xiRectangularCancelledSeries_rightOne L).analyticOnNhd hU
  have hden : AnalyticOnNhd ℂ (fun s : ℂ => xi (s - 1 / 2)) U := by
    intro s hs
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  exact hnum.meromorphicOn.div hden.meromorphicOn

/-- The continuation has a simple pole at every right Xi divisor point,
independently of the Xi-zero multiplicity. -/
theorem meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one
    {L : ℝ} (hL : 0 < L) (q : XiRightZeroCopy) :
    meromorphicOrderAt (xiRectangularRightDirichletContinuation L)
        (xiRightShiftedPole q) = ((-1 : ℤ) : WithTop ℤ) := by
  let U : Set ℂ := {s : ℂ | 1 < s.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hpoleU : xiRightShiftedPole q ∈ U := by
    rw [Set.mem_setOf_eq, xiRightShiftedPole, Complex.add_re,
      Complex.one_re]
    exact add_lt_add_left (xiRightCenteredZero_re_pos q) 1
  have hnum : AnalyticAt ℂ (xiRectangularCancelledSeries L)
      (xiRightShiftedPole q) :=
    ((differentiableOn_xiRectangularCancelledSeries_rightOne L).analyticOnNhd hU)
      _ hpoleU
  have hden : AnalyticAt ℂ (fun s : ℂ => xi (s - 1 / 2))
      (xiRightShiftedPole q) := by
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  rw [xiRectangularRightDirichletContinuation,
    meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
    hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
    xiRectangularCancelledSeries_order hL q, xi_shifted_half_order]
  rw [ENat.map_coe, ENat.map_coe]
  have hm : 0 < xiRightMultiplicity q := xiRightMultiplicity_pos q
  exact_mod_cast (show
    ((xiRightMultiplicity q - 1 : ℕ) : ℤ) - xiRightMultiplicity q = -1 by
      omega)

/-- Away from right-divisor pole coordinates, the continuation is analytic
on `Re s > 1`. -/
theorem analyticAt_xiRectangularRightDirichletContinuation_of_ne_poles
    (L : ℝ) {s : ℂ} (hs : 1 < s.re)
    (hne : ∀ q : XiRightZeroCopy, xiRightShiftedPole q ≠ s) :
    AnalyticAt ℂ (xiRectangularRightDirichletContinuation L) s := by
  let U : Set ℂ := {z : ℂ | 1 < z.re}
  have hU : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hsU : s ∈ U := hs
  have hnum : AnalyticAt ℂ (xiRectangularCancelledSeries L) s :=
    ((differentiableOn_xiRectangularCancelledSeries_rightOne L).analyticOnNhd hU)
      s hsU
  have hden : AnalyticAt ℂ (fun z : ℂ => xi (z - 1 / 2)) s := by
    exact (xi_analyticOnNhd_univ _ (Set.mem_univ _)).comp
      (analyticAt_id.sub analyticAt_const)
  have hden0 : xi (s - 1 / 2) ≠ 0 := by
    intro hzero
    obtain ⟨q, hq⟩ :=
      exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero hs hzero
    exact hne q hq
  exact hnum.div hden hden0

/-- Exact pole-support tomography in `Re s > 1`: a point is a simple pole of
the continuation exactly when it is the shifted coordinate of a right Xi
zero. -/
theorem meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one_iff
    {L : ℝ} (hL : 0 < L) {s : ℂ} (hs : 1 < s.re) :
    meromorphicOrderAt (xiRectangularRightDirichletContinuation L) s =
        ((-1 : ℤ) : WithTop ℤ) ↔
      ∃ q : XiRightZeroCopy, xiRightShiftedPole q = s := by
  constructor
  · intro horder
    by_contra hnone
    push Not at hnone
    have han :=
      analyticAt_xiRectangularRightDirichletContinuation_of_ne_poles L hs
        (fun q => Ne.symm (hnone q))
    rw [han.meromorphicOrderAt_eq] at horder
    simp at horder
  · rintro ⟨q, rfl⟩
    exact meromorphicOrderAt_xiRectangularRightDirichletContinuation_eq_neg_one
      hL q

/-- On every initial half-plane lying strictly right of the full transverse
divisor, the ordinary coefficient L-series equals twice the meromorphic
continuation. -/
theorem LSeries_xiRectangularRightDirichletComplex_eq_continuation
    (L : ℝ) {delta : ℝ}
    (hupper : ∀ q : XiRightZeroCopy,
      (xiRightCenteredZero q).re ≤ delta)
    {s : ℂ} (hs : 1 + delta < s.re) :
    LSeries (fun n => xiRectangularRightDirichletComplex L n) s =
      2 * xiRectangularRightDirichletContinuation L s := by
  rw [LSeries_xiRectangularRightDirichletComplex_eq_shiftedZeta L hupper hs]
  have hxi0 : xi (s - 1 / 2) ≠ 0 := by
    intro hzero
    have hs1 : 1 < s.re := by
      have hdelta : 0 ≤ delta := by
        by_contra hneg
        push Not at hneg
        obtain ⟨q⟩ := Classical.choice inferInstance
        have := hupper q
        linarith [xiRightCenteredZero_re_pos q]
      linarith
    obtain ⟨q, hq⟩ :=
      exists_xiRightZeroCopy_shiftedPole_eq_of_xi_shifted_eq_zero hs1 hzero
    have hre := congrArg Complex.re hq
    rw [xiRightShiftedPole, Complex.add_re, Complex.one_re] at hre
    have := hupper q
    linarith
  rw [xiRectangularRightDirichletContinuation,
    xiRectangularCancelledSeries_eq_xi_mul_shiftedZeta L hupper hs]
  field_simp

end

end RHTower
