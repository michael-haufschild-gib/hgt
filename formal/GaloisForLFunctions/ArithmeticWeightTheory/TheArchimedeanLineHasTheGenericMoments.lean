import GaloisForLFunctions.ArithmeticWeightTheory.TheGenericFibreHasUniformWeights
import GaloisForLFunctions.ArithmeticKunnethTheory.ProductMomentsAreDiagonalBelowTheThreshold

/-!
# The archimedean line has the generic moments

A specialization map from the generic fibre to `ζ` must at least carry Frobenius statistics. The
vertical shifts of `ζ` are the points `x_t = (p^{it})_p` of the archimedean line, and the window
trace of `x_t` is the spline-smoothed prime sum of `ζ` at height `t`
(`expSum_eq_fibreTrace_archimedean`). This file compares their tensor moments with those of the
generic fibre.

**Specialization below the threshold** (`vertical_moment_eq_generic`). For a `C²` height window
`η` supported in `[−r, r]` and `2r X^k ≤ 1`, `X = ⌊e^{u+R}⌋`,

  `∫ |η̂|² (ξ) |T_{x_{2πξ}}(u)|^{2k} dξ = ‖η‖² · ∫ |T_x(u)|^{2k} dx`:

averaged over heights up to the square-root scale `X^k`, the `2k`-th Frobenius moment of the
special fibre's vertical family is exactly the generic one (the gauge coinvariants, `≤ k!`
pairings). Below this scale nothing distinguishes `ζ` from a Haar-generic fibre, at every tensor
power.

**Coherence above it** (`generic_moment_le_vertical_moment`). For nonnegative windows the vertical
moment is the generic one plus a nonnegative off-diagonal of near-coincident products, at every
length: the non-invariant part of the vertical coinvariant identity only adds. Specialization along
the archimedean line runs in the coherent direction, special `≥` generic.
-/

open MeasureTheory Complex Set
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry ArithmeticKunnethTheory SquareRootThreshold Zeta23
  _root_.RHTower _root_.RHTower.WeilRegular

/-- The vertical window trace at height `2πξ` is the window trace of the archimedean point. -/
theorem expSum_eq_fibreTrace_archimedean (g : ℝ → ℝ) (R u ξ : ℝ) :
    expSum (windowPrimes R u) (windowWeight g u) logFreq ξ =
      fibreTrace g R u (HTGeometry.clockPhasePoint (fun p => Real.log p) (2 * π * ξ)) := by
  unfold expSum fibreTrace twistSum
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [twist_clockPhasePoint, logFreq]
  congr 2
  push_cast
  ring

/-- **The archimedean line has the generic moments below the square-root threshold.** -/
theorem vertical_moment_eq_generic {η : ℝ → ℂ} (hη : ContDiff ℝ 2 η) {r : ℝ}
    (hηs : tsupport η ⊆ Icc (-r) r) (g : ℝ → ℝ) (R u : ℝ) {k : ℕ}
    (hthr : 2 * r * ((⌊Real.exp (u + R)⌋₊ : ℕ) : ℝ) ^ k ≤ 1) :
    ∫ ξ : ℝ, pairTransform η ξ *
        (expSum (windowPrimes R u) (windowWeight g u) logFreq ξ *
          conj (expSum (windowPrimes R u) (windowWeight g u) logFreq ξ)) ^ k =
      ((∫ t, ‖η t‖ ^ 2 : ℝ) : ℂ) * ((∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar : ℝ) : ℂ) := by
  have hs : ∀ n ∈ windowPrimes R u, 1 ≤ n ∧ n ≤ ⌊Real.exp (u + R)⌋₊ := fun n hn =>
    ⟨(Nat.mem_primesLE.mp hn).2.one_lt.le, (Nat.mem_primesLE.mp hn).1⟩
  rw [integral_pairTransform_mul_normSq_pow_eq_diag hη hηs hs _ hthr]
  congr 1
  unfold fibreTrace
  rw [integral_normSq_twistSum_pow (s := windowPrimes R u)
    (fun n hn => (Nat.mem_primesLE.mp hn).2.ne_zero)]
  push_cast
  rfl

/-- The real window weight `e^{−u/2} log n · g(log n − u)`. -/
def windowWeightReal (g : ℝ → ℝ) (u : ℝ) (n : ℕ) : ℝ :=
  Real.exp (-(u / 2)) * Real.log n * g (Real.log n - u)

/-- **Coherence of the vertical family.** For nonnegative windows the vertical `2k`-th moment
dominates the generic one at every length. -/
theorem generic_moment_le_vertical_moment {w : ℝ → ℝ} (hw : ContDiff ℝ 2 (fun t => (w t : ℂ)))
    (hwc : HasCompactSupport (fun t => (w t : ℂ))) (hw0 : ∀ t, 0 ≤ w t) {g : ℝ → ℝ}
    (hg0 : ∀ v, 0 ≤ g v) (R u : ℝ) (k : ℕ) :
    (∫ t, ‖(w t : ℂ)‖ ^ 2) * ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar ≤
      ∫ ξ : ℝ, ‖paperFT (fun t => (w t : ℂ)) (-(2 * π * (ξ : ℂ)))‖ ^ 2 *
        ‖expSum (windowPrimes R u) (windowWeight g u) logFreq ξ‖ ^ (2 * k) := by
  have hs : ∀ n ∈ windowPrimes R u, 1 ≤ n := fun n hn => (Nat.mem_primesLE.mp hn).2.one_lt.le
  have hc : ∀ n, 0 ≤ windowWeightReal g u n := fun n =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n)) (hg0 _)
  obtain ⟨hid, hoff⟩ := integral_normSq_pow_eq_diag_add_offDiag_nonneg hw hwc hw0 hs hc k
  have hww : windowWeight g u = fun n => ((windowWeightReal g u n : ℝ) : ℂ) := rfl
  have hmom : ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar =
      ∑ N ∈ ArithmeticKunnethTheory.powSupport (windowPrimes R u) k,
        powCoeffReal (windowPrimes R u) (windowWeightReal g u) k N ^ 2 := by
    unfold fibreTrace
    rw [hww, integral_normSq_twistSum_pow (s := windowPrimes R u)
      (fun n hn => (Nat.mem_primesLE.mp hn).2.ne_zero)]
    refine Finset.sum_congr rfl fun N _ => ?_
    rw [powCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [hmom]
  calc (∫ t, ‖(w t : ℂ)‖ ^ 2) * ∑ N ∈ ArithmeticKunnethTheory.powSupport (windowPrimes R u) k,
        powCoeffReal (windowPrimes R u) (windowWeightReal g u) k N ^ 2
      ≤ _ + _ := le_add_of_nonneg_right hoff
    _ = _ := by rw [hww]; exact hid

end GaloisForLFunctions.ArithmeticWeightTheory
