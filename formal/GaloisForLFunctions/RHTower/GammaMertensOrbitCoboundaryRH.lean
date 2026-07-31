import GaloisForLFunctions.HTGeometry.PrincipalPartDifferentialOperator
import GaloisForLFunctions.RHTower.BornTemperatureFactorType

/-!
# The Gamma-shift orbit residue of the reflected Mertens pole pair

The completed Xi logarithmic derivative has a natural shift by two.  The leading reflected
Mertens principal part at a Xi zero `rho` has opposite simple poles at `-rho` and
`conj rho - 1`.  If that pair is a finite coboundary for translation by two, the two poles must
lie on the same translation orbit.  Their displacement has real part strictly between `-1` and
`1`, whereas a nonzero shift-two orbit displacement has absolute real part at least `2`.
Consequently the supports coincide and `rho.re = 1 / 2`.

This gives an exact RH criterion.  It is a consumer theorem, not the missing source theorem:
constructing the finite coboundary from the completed Euler--Gamma source without using the Xi
divisor remains open.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

open GaloisForLFunctions

noncomputable section

/-- A nonzero differential image of the reflected Mertens pole pair can be a finite
shift-two coboundary only on the critical line. -/
theorem mertensPolePair_re_eq_half_of_finiteShiftTwoCoboundary
    {rho : ℂ} (hstrip : 0 < rho.re ∧ rho.re < 1)
    {L : Polynomial ℂ} (hL : L ≠ 0)
    (E : ℂ →₀ (ℕ →₀ ℂ))
    (hcob :
      simplePolePairDifferentialOperator L 1 (-rho) (starRingEnd ℂ rho - 1) =
        finiteOrbitCoboundary (2 : ℂ) E) :
    rho.re = 1 / 2 := by
  have horbit :
      ((-rho : ℂ) : ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) =
        ((starRingEnd ℂ rho - 1 : ℂ) : ℂ ⧸ AddSubgroup.zmultiples (2 : ℂ)) := by
    by_contra hne
    exact (simplePolePairDifferentialOperator_ne_finiteOrbitCoboundary
      (2 : ℂ) (-rho) (starRingEnd ℂ rho - 1) hL one_ne_zero hne E) hcob
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_zmultiples_iff] at horbit
  rcases horbit with ⟨n, hn⟩
  have hnre : 2 * (n : ℝ) = 1 - 2 * rho.re := by
    have hre := congrArg Complex.re hn
    norm_num at hre
    linarith
  have hnlowR : (-1 : ℝ) < (n : ℝ) := by
    linarith [hstrip.2]
  have hnhighR : (n : ℝ) < 1 := by
    linarith [hstrip.1]
  have hnlow : (-1 : ℤ) < n := by
    exact_mod_cast hnlowR
  have hnhigh : n < (1 : ℤ) := by
    exact_mod_cast hnhighR
  have hn0 : n = 0 := by
    omega
  subst n
  norm_num at hnre
  linarith

/-- Every Xi-zero reflected Mertens pole pair is a finite coboundary for the completed
Gamma/Xi shift by two.  This predicate is deliberately stated as the exact missing producer
surface; the definition does not assert that such a coboundary has been constructed. -/
def GammaMertensShiftTwoCoboundaryCriterion : Prop :=
  ∀ rho : ℂ, xi rho = 0 → ∃ E : ℂ →₀ (ℕ →₀ ℂ),
    simplePolePairDifferentialOperator (1 : Polynomial ℂ) 1
        (-rho) (starRingEnd ℂ rho - 1) =
      finiteOrbitCoboundary (2 : ℂ) E

/-- The finite completed-Gamma-shift coboundary criterion is exactly equivalent to RH. -/
theorem gammaMertensShiftTwoCoboundaryCriterion_iff_riemannHypothesis :
    GammaMertensShiftTwoCoboundaryCriterion ↔ RiemannHypothesis := by
  constructor
  · intro hcrit
    apply rh_iff_xi_ne_zero_right.mpr
    intro rho hrho hzero
    obtain ⟨E, hE⟩ := hcrit rho hzero
    have hhalf := mertensPolePair_re_eq_half_of_finiteShiftTwoCoboundary
      (xi_zero_re_mem_open_unit hzero) (L := (1 : Polynomial ℂ)) one_ne_zero E hE
    have hright := mem_rightHalf.mp hrho
    linarith
  · intro hRH rho hzero
    refine ⟨0, ?_⟩
    have hhalf := xi_zero_re_eq_half_of_RH hRH hzero
    have hsupports : -rho = starRingEnd ℂ rho - 1 := by
      apply Complex.ext
      · simp only [neg_re, Complex.conj_re, sub_re, one_re]
        linarith
      · simp only [neg_im, Complex.conj_im, sub_im, one_im]
        ring
    rw [← hsupports]
    simp [simplePolePairDifferentialOperator, finiteOrbitCoboundary,
      translateFiniteSupport]

end

end RHTower
