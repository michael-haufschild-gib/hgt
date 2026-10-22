import GaloisForLFunctions.RHTower.CCM.CCMFirstClockAsymptoticBohrLaw
import GaloisForLFunctions.RHTower.Suzuki.SuzukiExplicitScrewZeroSeries

/-!
# Suzuki's bounded screw-function criterion

This module formalizes Theorem 1.6 of Suzuki, *Aspects of the screw function
corresponding to the Riemann zeta-function* (arXiv:2206.03682).

The source object is the literal multiplicity-exact zero series

`Psi(t) = sum_gamma (1 - cos (gamma t)) / gamma^(2 : ℕ)`,

implemented by `xiScrewDivisor`.  Boundedness is asserted on the source half-line
`[0, infinity)`.  Both implications are theorem-proved: RH gives the nonnegative
summable real screw series; conversely, a uniform bound gives a uniform lower bound
for every fixed-width logarithmic screw curvature, whose exact completeness theorem
forces RH.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Suzuki's `Psi(t) = O(1)` condition on `[0, infinity)`, for the literal Xi zero series. -/
def SuzukiXiScrewBounded : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → ‖xiScrewDivisor t‖ ≤ C

/-- Suzuki's displayed prime--Lerch function `Psi` is bounded on `[0, infinity)`. -/
def SuzukiExplicitScrewBounded : Prop :=
  ∃ C : ℝ, ∀ t : ℝ, 0 ≤ t → |suzukiPsi t| ≤ C

/-- The explicit prime--Lerch formula and the multiplicity-exact zero series have exactly the
same half-line boundedness condition. -/
theorem suzukiExplicitScrewBounded_iff_xiScrewBounded :
    SuzukiExplicitScrewBounded ↔ SuzukiXiScrewBounded := by
  constructor
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t ht => by
      rw [← abs_suzukiPsi_eq_norm_xiScrewDivisor ht]
      exact hC t ht⟩
  · rintro ⟨C, hC⟩
    exact ⟨C, fun t ht => by
      rw [abs_suzukiPsi_eq_norm_xiScrewDivisor ht]
      exact hC t ht⟩

/-- Under RH the literal Suzuki screw series is uniformly bounded by its relation-hull maximum. -/
theorem suzukiXiScrewBounded_of_riemannHypothesis
    (hRH : RiemannHypothesis) : SuzukiXiScrewBounded := by
  refine ⟨screwHullMax xiCriticalScrewWeight xiRealSpectralPoint, ?_⟩
  intro t _ht
  have hsum := summable_xiCriticalScrewWeight_of_rh hRH
  have hnonneg : 0 ≤ (xiScrewDivisor t).re := by
    rw [xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh hRH]
    exact screwSeries_nonneg xiCriticalScrewWeight_nonneg t
  have hle : (xiScrewDivisor t).re ≤
      screwHullMax xiCriticalScrewWeight xiRealSpectralPoint := by
    rw [xiScrewDivisor_re_eq_xiCriticalScrewSeries_of_rh hRH]
    exact screwSeries_le_screwHullMax xiCriticalScrewWeight_nonneg hsum t
  have hreal : xiScrewDivisor t = ((xiScrewDivisor t).re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa using xiScrewDivisor_im_eq_zero t
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact hle

/-- A half-line bound for the literal Suzuki screw series forces RH. -/
theorem riemannHypothesis_of_suzukiXiScrewBounded
    (hbounded : SuzukiXiScrewBounded) : RiemannHypothesis := by
  rcases hbounded with ⟨C, hC⟩
  apply (riemannHypothesis_iff_xiScrewWindowCurvature_logSample_eventually_bddBelow
    (L := 1) one_pos).mpr
  refine ⟨-12 * C, 0, ?_⟩
  intro n _hn hwidth
  have hx0 : 0 ≤ Real.log n := by linarith
  have hx1 : 0 ≤ Real.log n - 1 := by linarith
  have hx2 : 0 ≤ Real.log n - 2 * 1 := by linarith
  have hbound (x : ℝ) (hx : 0 ≤ x) : |(xiScrewDivisor x).re| ≤ C :=
    (Complex.abs_re_le_norm (xiScrewDivisor x)).trans (hC x hx)
  have hA := (abs_le.mp (hbound (Real.log n) hx0))
  have hB := (abs_le.mp (hbound (Real.log n - 2 * 1) hx2))
  have hD := (abs_le.mp (hbound (Real.log n - 1) hx1))
  have hE := (abs_le.mp (hbound 1 (by norm_num)))
  rcases hA with ⟨hAlo, _hAhi⟩
  rcases hB with ⟨hBlo, _hBhi⟩
  rcases hD with ⟨_hDlo, hDhi⟩
  rcases hE with ⟨hElo, _hEhi⟩
  norm_num at hBlo
  have hinside : -6 * C ≤
      (xiScrewDivisor (Real.log n)).re +
        (xiScrewDivisor (Real.log n - 2)).re -
          2 * (xiScrewDivisor (Real.log n - 1)).re +
            2 * (xiScrewDivisor 1).re := by
    linarith only [hAlo, hBlo, hDhi, hElo]
  rw [xiScrewWindowCurvature]
  norm_num [Complex.mul_re]
  linarith only [hinside]

/-- **Suzuki 2022, Theorem 1.6.**  RH is equivalent to boundedness of the literal
multiplicity-exact screw function on the nonnegative half-line. -/
theorem riemannHypothesis_iff_suzukiXiScrewBounded :
    RiemannHypothesis ↔ SuzukiXiScrewBounded :=
  ⟨suzukiXiScrewBounded_of_riemannHypothesis,
    riemannHypothesis_of_suzukiXiScrewBounded⟩

/-- **Suzuki 2022, Theorem 1.6, displayed-formula version.**  RH is equivalent to boundedness
on `[0, infinity)` of Suzuki's explicit prime--Lerch function `Psi`. -/
theorem riemannHypothesis_iff_suzukiExplicitScrewBounded :
    RiemannHypothesis ↔ SuzukiExplicitScrewBounded := by
  rw [suzukiExplicitScrewBounded_iff_xiScrewBounded]
  exact riemannHypothesis_iff_suzukiXiScrewBounded

end

end RHTower
