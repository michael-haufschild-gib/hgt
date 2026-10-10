import GaloisForLFunctions.HTGeometry.ReciprocalTotalPositivityRealZeros
import GaloisForLFunctions.HTGeometry.EvenEntireSquareLift
import GaloisForLFunctions.RHTower.XiSuperchargeHarnackDefect
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing

/-!
# A single-sequence sufficient condition for RH

`Ξ(σ) = ξ(½ + iσ)` (`XiC`) is even and entire, so `Ξ(σ) = F(−σ²)` for the entire function
`F = xiCentreLift` (`xiCentreLift_neg_sq`), built from the even Taylor coefficients of `Ξ`.  The
reciprocal `1/F(−z) = 1/Ξ(√z)` is analytic near `0`.

**Theorem** (`riemannHypothesis_of_reciprocalTP_xiCentreLift`).  If the Taylor coefficients of
`z ↦ 1/Ξ(√z)` at `0` are nonnegative reals forming a consecutive-row totally positive sequence
(`ReciprocalTP xiCentreLift`), then the Riemann hypothesis holds.

By the deflation theorem (`HTGeometry.ReciprocalTP.eq_neg_of_apply_eq_zero`) every zero of `F` is
a negative real `−D`.  A zero `t` of `Ξ` gives `F(−t²) = 0`, hence `t² = D > 0` and `t` is real.
This is a criterion at a single height, the centre: it concerns one explicit sequence,
with no condition imposed at any other height.
-/

open Complex
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- The centre lift `F(y) = Ξ(√(−y))`, entire, with `F(−σ²) = Ξ(σ)`. -/
def xiCentreLift (y : ℂ) : ℂ := evenSquareLift XiC (-y)

theorem differentiable_xiCentreLift : Differentiable ℂ xiCentreLift :=
  (differentiable_evenSquareLift XiC_differentiable).comp differentiable_neg

theorem xiCentreLift_neg_sq (σ : ℂ) : xiCentreLift (-(σ ^ 2)) = XiC σ := by
  unfold xiCentreLift
  rw [neg_neg]
  exact evenSquareLift_sq XiC_differentiable XiC_even σ

theorem xiCentreLift_zero_ne_zero : xiCentreLift 0 ≠ 0 := by
  have h := xiCentreLift_neg_sq 0
  rw [show -((0 : ℂ) ^ 2) = 0 by ring] at h
  rw [h]
  have : XiC 0 = xi (((1 / 2 : ℝ)) : ℂ) := by
    simp [XiC]
  rw [this]
  exact xi_ne_zero_of_real _

/-- **Reciprocal total positivity of `Ξ` at the centre implies RH.** -/
theorem riemannHypothesis_of_reciprocalTP_xiCentreLift (h : ReciprocalTP xiCentreLift) :
    RiemannHypothesis := by
  rw [riemannHypothesis_iff_XiC_zeros_real]
  intro t ht
  have hz : xiCentreLift (-(t ^ 2)) = 0 := by
    rw [xiCentreLift_neg_sq]
    exact ht
  obtain ⟨D, hD, hDeq⟩ := h.eq_neg_of_apply_eq_zero hz
  have ht2 : t ^ 2 = (D : ℂ) := by linear_combination -hDeq
  have him := congrArg Complex.im ht2
  have hre := congrArg Complex.re ht2
  simp only [sq, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re] at him hre
  by_contra hne
  have hre0 : t.re = 0 := by
    have : 2 * t.re * t.im = 0 := by linarith
    rcases mul_eq_zero.mp this with h1 | h1
    · linarith
    · exact absurd h1 hne
  rw [hre0] at hre
  nlinarith [sq_nonneg t.im]

end

end RHTower
