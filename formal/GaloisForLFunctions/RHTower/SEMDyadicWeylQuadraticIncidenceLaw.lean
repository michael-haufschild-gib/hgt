import GaloisForLFunctions.RHTower.IntegralJetQuadraticIncidence
import GaloisForLFunctions.RHTower.SEMDyadicWeylDegeneracyLaw

/-!
# Dyadic Weyl symmetry selects quadratic Xi incidence

The boundary Weyl classification detects divisibility of the completed SEM hole count by `2^k`.
The integral-jet quadratic index identifies the square of that same count with the square of the
local Xi order.  Their closure upgrades the linear charge obstruction to a quadratic incidence
selection rule at dyadic level `2k`.
-/

open Complex Matrix Polynomial

noncomputable section

namespace RHTower

/-- Divisibility of the completed SEM hole count by `2^k` forces square-level divisibility of
the integral quadratic incidence at every positive jet depth. -/
theorem dyadicSquare_dvd_integralJetQuadraticIndex_of_holeCount
    {rho : ℂ} {r0 R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hsplit : SEMSplitData rho r0 R N zs u) (hlen : zs.length = n + 1)
    {k : ℕ} (hdvd : 2 ^ k ∣ n + 1) {m : ℕ} (hm : 1 ≤ m) :
    ((2 : ℤ) ^ k) ^ 2 ∣
      integralJetQuadraticIndex m hm (completedSEMContourBoundaryZ rho r0 R N m) := by
  rw [integralJetQuadraticIndex_eq_splitCount_sq hsplit hm, hlen]
  exact pow_dvd_pow_of_dvd (Int.natCast_dvd_natCast.mpr hdvd) 2

/-- **SEM dyadic Weyl quadratic-incidence law.**  Every boundary-completed SEM jet satisfying
the depth-`k` Weyl equation lies on exactly the singular zero-wrap branch or on a quadratic
incidence stratum divisible by `((2^k)^2)`.  On the latter branch the same divisor controls the
square of the local Xi order. -/
theorem boundaryCompletedJetWeyl_implies_zeroWrap_or_quadraticXiIncidence
    {rho : ℂ} {r0 R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hsplit : SEMSplitData rho r0 R N zs u) (hlen : zs.length = n + 1)
    (k : ℕ) (holonomy : ℂ) {m : ℕ} (hm : 1 ≤ m)
    (hweyl :
      truncatedJetClock n (Bottcher.dyadicRoot k) *
            boundaryCompletedJetShift n holonomy =
          Bottcher.dyadicRoot k •
            (boundaryCompletedJetShift n holonomy *
              truncatedJetClock n (Bottcher.dyadicRoot k))) :
    holonomy = 0 ∨
      (((2 : ℤ) ^ k) ^ 2 ∣
          integralJetQuadraticIndex m hm (completedSEMContourBoundaryZ rho r0 R N m)) ∧
        ((2 : ℤ) ^ k) ^ 2 ∣ (((analyticOrderAt xi rho).toNat : ℤ) ^ 2) := by
  rcases (dyadicBoundaryCompletedJetWeyl_iff_zero_or_dvd n k holonomy).mp hweyl with
    hzero | hdvd
  · exact Or.inl hzero
  · right
    have hquad :=
      dyadicSquare_dvd_integralJetQuadraticIndex_of_holeCount hsplit hlen hdvd hm
    refine ⟨hquad, ?_⟩
    rw [← integralJetQuadraticIndex_eq_xiOrder_sq hsplit hm]
    exact hquad

/-- Failure of the quadratic Xi-incidence divisor forbids every nonsingular depth-`k` boundary
Weyl realization. -/
theorem no_nonzeroWrap_boundaryCompletedJetWeyl_of_quadraticXiIncidence_not_dvd
    {rho : ℂ} {r0 R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (hsplit : SEMSplitData rho r0 R N zs u) (hlen : zs.length = n + 1)
    (k : ℕ) (holonomy : ℂ) (hholonomy : holonomy ≠ 0) {m : ℕ} (hm : 1 ≤ m)
    (hnot : ¬ ((2 : ℤ) ^ k) ^ 2 ∣
      integralJetQuadraticIndex m hm (completedSEMContourBoundaryZ rho r0 R N m)) :
    ¬ (truncatedJetClock n (Bottcher.dyadicRoot k) *
          boundaryCompletedJetShift n holonomy =
        Bottcher.dyadicRoot k •
          (boundaryCompletedJetShift n holonomy *
            truncatedJetClock n (Bottcher.dyadicRoot k))) := by
  intro hweyl
  rcases boundaryCompletedJetWeyl_implies_zeroWrap_or_quadraticXiIncidence
      hsplit hlen k holonomy hm hweyl with hzero | hquad
  · exact hholonomy hzero
  · exact hnot hquad.1

end RHTower

end
