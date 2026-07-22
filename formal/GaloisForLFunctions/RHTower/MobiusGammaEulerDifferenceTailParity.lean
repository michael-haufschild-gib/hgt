import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Gamma--Euler central-difference tail parity

Multiplication by one normalized Euler factor on a Gamma height line acts on the Gamma
characteristic function by a weighted central difference.  This file isolates its exact action on
exponential tail modes.  The leading Gamma mode is annihilated, while the next mode has a negative
eigenvalue.  One Euler difference therefore makes the next-mode coefficient positive; two make it
negative.

This is the algebraic core of the prime-by-prime Gamma-contraction obstruction.  No zeta zero,
RH assumption, asymptotic computation, or numerical input occurs here.
-/

namespace RHTower

noncomputable section

/-- Central-difference multiplier induced by an Euler factor on a Gamma characteristic. -/
def gammaEulerCentralDifferenceEigenvalue (r h lambda : ℝ) : ℝ :=
  2 * (Real.cosh (r * h / 2) - Real.cosh (lambda * h))

/-- Central-difference operator whose base exponential rate is `r/2`. -/
def gammaEulerCentralDifference (r h : ℝ) (f : ℝ → ℝ) (u : ℝ) : ℝ :=
  2 * Real.cosh (r * h / 2) * f u - f (u + h) - f (u - h)

/-- Every real exponential is an eigenfunction of the Gamma--Euler central difference. -/
theorem gammaEulerCentralDifference_exp (r h lambda u : ℝ) :
    gammaEulerCentralDifference r h (fun v => Real.exp (-lambda * v)) u =
      gammaEulerCentralDifferenceEigenvalue r h lambda * Real.exp (-lambda * u) := by
  rw [gammaEulerCentralDifference, gammaEulerCentralDifferenceEigenvalue]
  simp only [Real.cosh_eq]
  rw [show Real.exp (-lambda * (u + h)) =
      Real.exp (-lambda * u) * Real.exp (-lambda * h) by
        rw [← Real.exp_add]
        congr 1
        ring,
    show Real.exp (-lambda * (u - h)) =
      Real.exp (-lambda * u) * Real.exp (lambda * h) by
        rw [← Real.exp_add]
        congr 1
        ring]
  ring_nf

/-- Leading hyperbolic-secant tail mode is killed exactly. -/
@[simp] theorem gammaEulerCentralDifferenceEigenvalue_base (r h : ℝ) :
    gammaEulerCentralDifferenceEigenvalue r h (r / 2) = 0 := by
  rw [gammaEulerCentralDifferenceEigenvalue]
  have heq : (r / 2) * h = r * h / 2 := by ring
  rw [heq, sub_self, mul_zero]

/-- Next hyperbolic-secant tail mode has strictly negative eigenvalue. -/
theorem gammaEulerCentralDifferenceEigenvalue_next_neg
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) < 0 := by
  rw [gammaEulerCentralDifferenceEigenvalue]
  have hbase : 0 ≤ r * h / 2 := by positivity
  have hlt : r * h / 2 < (r / 2 + 1) * h := by nlinarith
  have hnext : 0 < (r / 2 + 1) * h := by positivity
  have hcosh : Real.cosh (r * h / 2) < Real.cosh ((r / 2 + 1) * h) := by
    rw [Real.cosh_lt_cosh, abs_of_nonneg hbase, abs_of_pos hnext]
    exact hlt
  linarith

/-- Positive scale `2^r` in the hyperbolic-secant tail expansion, written without overloaded
real-power notation. -/
def gammaEulerTailScale (r : ℝ) : ℝ :=
  Real.exp (r * Real.log 2)

theorem gammaEulerTailScale_pos (r : ℝ) : 0 < gammaEulerTailScale r := by
  exact Real.exp_pos _

/-- Coefficient of the next tail mode after one Euler difference. -/
def gammaEulerOneDifferenceNextCoefficient (r h : ℝ) : ℝ :=
  -r * gammaEulerTailScale r * gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1)

/-- One Euler difference flips the negative next Gamma-tail coefficient to positive. -/
theorem gammaEulerOneDifferenceNextCoefficient_pos
    {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    0 < gammaEulerOneDifferenceNextCoefficient r h := by
  rw [gammaEulerOneDifferenceNextCoefficient]
  have heig := gammaEulerCentralDifferenceEigenvalue_next_neg hr hh
  have hscale : 0 < gammaEulerTailScale r := gammaEulerTailScale_pos r
  have hnr : -r < 0 := by linarith
  have hleft : -r * gammaEulerTailScale r < 0 :=
    mul_neg_of_neg_of_pos hnr hscale
  exact mul_pos_of_neg_of_neg hleft heig

/-- Coefficient of the next tail mode after two Euler differences. -/
def gammaEulerTwoDifferenceNextCoefficient (r h k : ℝ) : ℝ :=
  -r * gammaEulerTailScale r *
    gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) *
    gammaEulerCentralDifferenceEigenvalue r k (r / 2 + 1)

/-- **Two-channel sign reversal.** Two positive-scale Euler differences make the next Gamma-tail
coefficient strictly negative. -/
theorem gammaEulerTwoDifferenceNextCoefficient_neg
    {r h k : ℝ} (hr : 0 < r) (hh : 0 < h) (hk : 0 < k) :
    gammaEulerTwoDifferenceNextCoefficient r h k < 0 := by
  rw [gammaEulerTwoDifferenceNextCoefficient]
  have heigH := gammaEulerCentralDifferenceEigenvalue_next_neg hr hh
  have heigK := gammaEulerCentralDifferenceEigenvalue_next_neg hr hk
  have hscale : 0 < gammaEulerTailScale r := gammaEulerTailScale_pos r
  have hprod : 0 <
      gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) *
        gammaEulerCentralDifferenceEigenvalue r k (r / 2 + 1) :=
    mul_pos_of_neg_of_neg heigH heigK
  have htotal : 0 < r * gammaEulerTailScale r *
      (gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) *
        gammaEulerCentralDifferenceEigenvalue r k (r / 2 + 1)) :=
    mul_pos (mul_pos hr hscale) hprod
  calc
    -r * gammaEulerTailScale r *
        gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) *
        gammaEulerCentralDifferenceEigenvalue r k (r / 2 + 1) =
      -(r * gammaEulerTailScale r *
        (gammaEulerCentralDifferenceEigenvalue r h (r / 2 + 1) *
          gammaEulerCentralDifferenceEigenvalue r k (r / 2 + 1))) := by ring
    _ < 0 := by linarith

/-- Coefficient of the first surviving Gamma-tail mode after an arbitrary finite block of Euler
differences. -/
def gammaEulerManyDifferenceNextCoefficient {ι : Type*}
    (r : ℝ) (S : Finset ι) (h : ι → ℝ) : ℝ :=
  -r * gammaEulerTailScale r *
    ∏ i ∈ S, gammaEulerCentralDifferenceEigenvalue r (h i) (r / 2 + 1)

/-- **Finite-block tail parity.** After any finite block of positive-scale Euler differences,
the first surviving Gamma-tail coefficient has sign `(-1)^(card S + 1)`. -/
theorem gammaEulerManyDifferenceNextCoefficient_signed_pos {ι : Type*}
    {r : ℝ} {S : Finset ι} {h : ι → ℝ}
    (hr : 0 < r) (hh : ∀ i ∈ S, 0 < h i) :
    0 < (-1 : ℝ) ^ (S.card + 1) *
      gammaEulerManyDifferenceNextCoefficient r S h := by
  have hscale : 0 < gammaEulerTailScale r := gammaEulerTailScale_pos r
  have hprod : 0 <
      ∏ i ∈ S, -gammaEulerCentralDifferenceEigenvalue r (h i) (r / 2 + 1) := by
    apply Finset.prod_pos
    intro i hi
    exact neg_pos.mpr
      (gammaEulerCentralDifferenceEigenvalue_next_neg hr (hh i hi))
  have hid :
      (-1 : ℝ) ^ (S.card + 1) *
          gammaEulerManyDifferenceNextCoefficient r S h =
        r * gammaEulerTailScale r *
          ∏ i ∈ S, -gammaEulerCentralDifferenceEigenvalue r (h i) (r / 2 + 1) := by
    rw [gammaEulerManyDifferenceNextCoefficient, Finset.prod_neg, pow_succ]
    ring
  rw [hid]
  exact mul_pos (mul_pos hr hscale) hprod

end

end RHTower
