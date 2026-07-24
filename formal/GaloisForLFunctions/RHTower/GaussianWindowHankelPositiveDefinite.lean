import GaloisForLFunctions.RHTower.HedenmalmGaussianHankelRH
import GaloisForLFunctions.HTGeometry.MomentInnerProduct

/-!
# Strict positive-definiteness of the Gaussian-windowed Hankel tower

The complete Hankel sign-cone law identifies positive *semi*-definiteness of the whole Gaussian
Hankel tower of a bounded continuous density with almost-everywhere nonnegativity of the density.
Here that is sharpened to strict positive-definiteness: if the density is everywhere nonnegative
and strictly positive at even a single point, then every finite Gaussian-windowed Hankel section is
positive *definite* at every positive temperature.

The mechanism is that the Gaussian window charges every nonempty open set, while a nonnegative
density that is positive at a point is positive on an open interval, and a nonzero real polynomial
vanishes only on a finite set.  Hence the square integral `∫ p² J dμ` is strictly positive for every
nonzero polynomial, which is exactly positive-definiteness of the moment form.  This is the
positive-definite input consumed by the Gaussian moment-defect recession law: the limiting matrix of
strong cooling is a positive multiple of a genuine positive-definite Gaussian Hankel matrix.
-/

noncomputable section

open MeasureTheory Polynomial Set
open scoped BigOperators ENNReal

namespace RHTower

variable {tau : ℝ} {J : ℝ → ℝ}

/-- A nonempty open subset of the real line is infinite. -/
theorem isOpen_nonempty_infinite {U : Set ℝ} (hU : IsOpen U) (hne : U.Nonempty) : U.Infinite := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hU x hx
  refine Set.Infinite.mono hball ?_
  rw [Real.ball_eq_Ioo]
  exact Set.Ioo_infinite (by linarith)

/-- A square of a polynomial times a bounded density is integrable against a positive Gaussian
window. -/
theorem gaussianWindow_integrable_sq_mul (htau : 0 < tau)
    (hJ : MemLp J ∞ (gaussianWindowMeasure tau)) (p : Polynomial ℝ) :
    Integrable (fun x : ℝ => (p.eval x) ^ 2 * J x) (gaussianWindowMeasure tau) := by
  letI := gaussianWindowMeasure_finite htau
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments htau
  have hrw : (fun x : ℝ => (p.eval x) ^ 2 * J x) =
      fun x => ∑ k ∈ (p ^ 2).support, (p ^ 2).coeff k * (x ^ k * J x) := by
    funext x
    rw [← Polynomial.eval_pow, eval_eq_sum, Polynomial.sum_def, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hrw]
  apply integrable_finsetSum
  intro k _
  exact (integrable_monomial_mul_of_entireExponentialMoments hmu J hJ k).const_mul _

/-- **Strict positivity of the Gaussian square integral.**  For a nonnegative continuous density
that is strictly positive at one point, the Gaussian-windowed square integral of every nonzero real
polynomial is strictly positive. -/
theorem gaussianWindow_integral_sq_mul_pos (htau : 0 < tau)
    (hJc : Continuous J) (hJnn : ∀ x, 0 ≤ J x)
    (hJ : MemLp J ∞ (gaussianWindowMeasure tau)) {x₀ : ℝ} (hJpos : 0 < J x₀)
    {p : Polynomial ℝ} (hp : p ≠ 0) :
    0 < ∫ x, (p.eval x) ^ 2 * J x ∂(gaussianWindowMeasure tau) := by
  have hnn : (0 : ℝ → ℝ) ≤ fun x => (p.eval x) ^ 2 * J x :=
    fun x => mul_nonneg (sq_nonneg _) (hJnn x)
  rw [integral_pos_iff_support_of_nonneg hnn (gaussianWindow_integrable_sq_mul htau hJ p)]
  set W : Set ℝ := {x : ℝ | 0 < J x} ∩ {x : ℝ | p.eval x ≠ 0} with hW
  have hWopen : IsOpen W :=
    (isOpen_lt continuous_const hJc).inter (isOpen_ne.preimage p.continuous)
  have hWne : W.Nonempty := by
    by_contra hempty
    rw [Set.not_nonempty_iff_eq_empty] at hempty
    have hsub : {x : ℝ | 0 < J x} ⊆ {x : ℝ | p.IsRoot x} := by
      intro x hx
      by_contra hpx
      have hmem : x ∈ W := ⟨hx, hpx⟩
      rw [hempty] at hmem
      exact hmem
    have hinf : {x : ℝ | 0 < J x}.Infinite :=
      isOpen_nonempty_infinite (isOpen_lt continuous_const hJc) ⟨x₀, hJpos⟩
    exact hp (Polynomial.eq_zero_of_infinite_isRoot p (Set.Infinite.mono hsub hinf))
  have hWsub : W ⊆ Function.support (fun x => (p.eval x) ^ 2 * J x) := by
    intro x hx
    have hpx : (0 : ℝ) < (p.eval x) ^ 2 :=
      lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hx.2))
    exact Function.mem_support.mpr (ne_of_gt (mul_pos hpx hx.1))
  exact lt_of_lt_of_le (IsOpen.measure_pos (gaussianWindowMeasure tau) hWopen hWne)
    (measure_mono hWsub)

/-- **Positive-definiteness of the Gaussian moment form.**  A nonnegative continuous density that is
strictly positive at one point induces a strictly positive-definite moment form on real polynomials
for every positive Gaussian window. -/
theorem gaussianWindow_positiveMomentForm_of_nonneg (htau : 0 < tau)
    (hJc : Continuous J) (hJnn : ∀ x, 0 ≤ J x)
    (hJ : MemLp J ∞ (gaussianWindowMeasure tau)) {x₀ : ℝ} (hJpos : 0 < J x₀) :
    HTGeometry.PositiveMomentForm (weightedMoment (gaussianWindowMeasure tau) J) := by
  letI := gaussianWindowMeasure_finite htau
  have hmu := gaussianWindowMeasure_hasEntireExponentialMoments htau
  refine ⟨fun p hp => ?_⟩
  rw [HTGeometry.momentInner_self,
    momentFunctional_weightedMoment_sq_eq_integral hmu J hJ]
  exact gaussianWindow_integral_sq_mul_pos htau hJc hJnn hJ hJpos hp

/-- **Strict positive-definiteness of the complete Gaussian Hankel tower.**  Every finite Hankel
section of the Gaussian-windowed moments of a nonnegative continuous density that is positive at one
point is positive definite, at every positive temperature. -/
theorem gaussianWindow_momentHankelMatrix_posDef_of_nonneg (htau : 0 < tau)
    (hJc : Continuous J) (hJnn : ∀ x, 0 ≤ J x)
    (hJ : MemLp J ∞ (gaussianWindowMeasure tau)) {x₀ : ℝ} (hJpos : 0 < J x₀) (n : ℕ) :
    (HTGeometry.momentHankelMatrix (weightedMoment (gaussianWindowMeasure tau) J) n).PosDef :=
  HTGeometry.positiveMomentForm_iff_momentHankelMatrix_posDef.mp
    (gaussianWindow_positiveMomentForm_of_nonneg htau hJc hJnn hJ hJpos) n

end RHTower
