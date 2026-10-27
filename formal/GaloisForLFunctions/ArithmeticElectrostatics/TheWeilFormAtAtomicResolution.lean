import GaloisForLFunctions.ArithmeticElectrostatics.TheStabilityLawAtAtomicResolution
import GaloisForLFunctions.RHTower.EulerMaclaurinCountertermQuadratureAndOneSidedPBAP

/-!
# The Weil form at atomic resolution

Weil's form of `ζ` on the autocorrelation of a real test `f` is the archimedean-minus-prime form plus
the pole term, `Re W(f) = M(f) + Re P(f)` (`RHTower.markovEnergy_eq_W_sub`), and the pole term is a
rank-two form of signature `(1, 1)`, `Re P(f) = 2C(f)² − 2S(f)²` with `C(f) = ∫ f cosh(u/2)`,
`S(f) = ∫ f sinh(u/2)` (`RHTower.re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq`). On atomic
tests of width at most `atomicWidth N` the archimedean place pays the prime form (`M ≥ 0`,
`markovEnergy_atomicTest_nonneg`). This file adds the pole.

* **The coupled form** (`re_W_atomicTest_eq`): `Re W(f) = M(f) + 2C(f)² − 2S(f)²` on atomic tests.
* **A rank-one counterterm couples the two places and the pole** (`re_W_add_sinh_sq_nonneg`):
  `Re W(f) + 2S(f)² ≥ 0` on every atomic test of width at most `atomicWidth N`. The counterterm has
  rank one, below the number `N` of orders.
* **Weil positivity on a cone of atomic tests** (`re_W_atomicTest_nonneg_of_abs_le`,
  `re_W_atomicTest_nonneg_of_nonneg`): `Re W(f) ≥ 0` whenever `|S(f)| ≤ |C(f)|`, in particular for
  nonnegative weights and a nonnegative bump, since the atoms `log n` lie in `u ≥ 0`, where
  `0 ≤ sinh(u/2) ≤ cosh(u/2)`.

This is the coupled renormalization of the two places and the pole at atomic resolution: a family
whose joint counterterm has rank one and whose survival cone contains every nonnegative atomic test.
It does not reach the spacing scale `w ≍ 1/N`, where the Lévy gain no longer pays the prime form.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticElectrostatics

open Zeta23

variable {g : ℝ → ℝ} {w : ℝ}

theorem contDiff_ofReal_atomicTest (hg : ContDiff ℝ 2 g) (N : ℕ) (x : ℕ → ℝ) :
    ContDiff ℝ 2 fun u => (atomicTest N x g u : ℂ) :=
  Complex.ofRealCLM.contDiff.comp (contDiff_atomicTest hg N x)

theorem hasCompactSupport_ofReal_atomicTest (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (N : ℕ)
    (x : ℕ → ℝ) : HasCompactSupport fun u => (atomicTest N x g u : ℂ) :=
  HasCompactSupport.comp_left (g := ((↑) : ℝ → ℂ)) (hasCompactSupport_atomicTest hgsupp N x)
    Complex.ofReal_zero

/-- **The coupled form**: `Re W(f) = M(f) + 2C(f)² − 2S(f)²` on atomic tests. -/
theorem re_W_atomicTest_eq (hg : ContDiff ℝ 2 g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (N : ℕ) (x : ℕ → ℝ) :
    (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ)) fun u => (atomicTest N x g u : ℂ)).re =
      markovEnergy (fun u => (atomicTest N x g u : ℂ)) +
        (2 * coshHalfMoment (atomicTest N x g) ^ 2 - 2 * sinhHalfMoment (atomicTest N x g) ^ 2) := by
  rw [markovEnergy_eq_W_sub (contDiff_ofReal_atomicTest hg N x)
      (hasCompactSupport_ofReal_atomicTest hgsupp N x),
    re_weilPoleTerm_ofReal_eq_two_mul_cosh_sq_sub_sinh_sq (contDiff_atomicTest hg N x).continuous
      (hasCompactSupport_atomicTest hgsupp N x)]
  ring

/-- **A rank-one counterterm**: `Re W(f) + 2S(f)² ≥ 0` on atomic tests of width `≤ atomicWidth N`. -/
theorem re_W_add_sinh_sq_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomicWidth N) (x : ℕ → ℝ) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re + 2 * sinhHalfMoment (atomicTest N x g) ^ 2 := by
  rw [re_W_atomicTest_eq hg hgsupp N x]
  have hM := markovEnergy_atomicTest_nonneg hg hgc hgsupp hN hw0 hw x
  nlinarith [sq_nonneg (coshHalfMoment (atomicTest N x g))]

/-- **Weil positivity on the cone `|S| ≤ |C|`** of atomic tests of width `≤ atomicWidth N`. -/
theorem re_W_atomicTest_nonneg_of_abs_le (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {N : ℕ} (hN : 1 ≤ N) (hw0 : 0 < w)
    (hw : w ≤ atomicWidth N) (x : ℕ → ℝ)
    (hSC : |sinhHalfMoment (atomicTest N x g)| ≤ |coshHalfMoment (atomicTest N x g)|) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re := by
  rw [re_W_atomicTest_eq hg hgsupp N x]
  have hM := markovEnergy_atomicTest_nonneg hg hgc hgsupp hN hw0 hw x
  have hsq : sinhHalfMoment (atomicTest N x g) ^ 2 ≤ coshHalfMoment (atomicTest N x g) ^ 2 := by
    rw [← sq_abs, ← sq_abs (coshHalfMoment _)]
    exact pow_le_pow_left₀ (abs_nonneg _) hSC 2
  linarith

/-- **Weil positivity on nonnegative atomic tests**: nonnegative weights and a nonnegative bump of
width `≤ atomicWidth N` give `Re W(f) ≥ 0`. -/
theorem re_W_atomicTest_nonneg_of_nonneg (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hg0 : ∀ u, 0 ≤ g u) {N : ℕ} (hN : 1 ≤ N)
    (hw0 : 0 < w) (hw : w ≤ atomicWidth N) {x : ℕ → ℝ} (hx : ∀ n, 0 ≤ x n) :
    0 ≤ (zetaZeroConfig.W (fun u => (atomicTest N x g u : ℂ))
        fun u => (atomicTest N x g u : ℂ)).re := by
  set f := atomicTest N x g
  have hf := contDiff_atomicTest hg N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hf0 : ∀ u, 0 ≤ f u := fun u => sum_nonneg fun n _ => mul_nonneg (hx n) (hg0 _)
  -- the atoms sit in `u ≥ 0`
  have hneg : ∀ u, u < 0 → f u = 0 := fun u hu => sum_eq_zero fun n hn => by
    have hlog : 0 ≤ Real.log n := Real.log_natCast_nonneg n
    rw [hgsupp _ fun h => by linarith [h.1], mul_zero]
  have hint : ∀ φ : ℝ → ℝ, Continuous φ → Integrable fun u => f u * φ u := fun φ hφ =>
    (hf.continuous.mul hφ).integrable_of_hasCompactSupport (hfc.mul_right)
  have hS0 : 0 ≤ sinhHalfMoment f := integral_nonneg fun u => by
    show 0 ≤ f u * Real.sinh (u / 2)
    rcases lt_or_ge u 0 with hu | hu
    · rw [hneg u hu, zero_mul]
    · exact mul_nonneg (hf0 u) (Real.sinh_nonneg_iff.mpr (by linarith))
  have hSC : sinhHalfMoment f ≤ coshHalfMoment f :=
    integral_mono (hint _ (Real.continuous_sinh.comp (continuous_id.div_const 2)))
      (hint _ (Real.continuous_cosh.comp (continuous_id.div_const 2))) fun u =>
        mul_le_mul_of_nonneg_left (Real.sinh_lt_cosh _).le (hf0 u)
  refine re_W_atomicTest_nonneg_of_abs_le hg hgc hgsupp hN hw0 hw x ?_
  rw [abs_of_nonneg hS0, abs_of_nonneg (hS0.trans hSC)]
  exact hSC

end GaloisForLFunctions.ArithmeticElectrostatics
