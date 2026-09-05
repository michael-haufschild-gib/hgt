import Mathlib
import GaloisForLFunctions.HTGeometry.BlockProductMetric

/-!
# Lipschitz scaling and uniform convergence for rough metrics

This file formalizes the metric algebra in arXiv:2603.05669,
*Lipschitz Bounds and Uniform Convergence for Sequences of Bounded Rough Riemannian Metrics*.

A quadratic-form comparison by `c` scales speed, length, and distance by `sqrt c`, not by `c`.
Theorems below make that square-root law explicit and characterize exactly when the paper's printed
linear coefficient is nevertheless a valid weaker estimate.  Taking `min c 1` for lower bounds and
`max c 1` for upper bounds repairs the coefficient without extra geometric assumptions.

The file also formalizes the paper's two-sided-envelope uniform-convergence theorem and applies it to
the bounded-distance transform already used by `BlockProductMetric` throughout this corpus.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

section SquareRootScaling

/-- For nonnegative `c`, the printed lower coefficient `c` is below the correct `sqrt c` exactly
when `c ≤ 1`. -/
theorem self_le_sqrt_iff {c : ℝ} (hc : 0 ≤ c) :
    c ≤ Real.sqrt c ↔ c ≤ 1 := by
  constructor
  · intro h
    have hs := Real.sq_sqrt hc
    have hsq : c ^ 2 ≤ c := by nlinarith [Real.sqrt_nonneg c]
    nlinarith
  · intro h
    have hs := Real.sq_sqrt hc
    nlinarith [Real.sqrt_nonneg c]

/-- For nonnegative `c`, the printed upper coefficient dominates `sqrt c` exactly when `c ≥ 1`,
apart from the degenerate value `c = 0`. -/
theorem sqrt_le_self_iff {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt c ≤ c ↔ 1 ≤ c ∨ c = 0 := by
  constructor
  · intro h
    have hs := Real.sq_sqrt hc
    by_cases hz : c = 0
    · exact Or.inr hz
    · left
      have hp : 0 < c := lt_of_le_of_ne hc (Ne.symm hz)
      nlinarith [Real.sqrt_nonneg c]
  · rintro (h | rfl)
    · have hs := Real.sq_sqrt hc
      nlinarith [Real.sqrt_nonneg c]
    · simp

/-- Normalizing a lower quadratic-form coefficient by `min c 1` always gives a valid linear
distance coefficient. -/
theorem normalizedLowerCoefficient_le_sqrt {c : ℝ} (hc : 0 ≤ c) :
    min c 1 ≤ Real.sqrt c := by
  rcases le_total c 1 with h | h
  · rw [min_eq_left h]
    exact (self_le_sqrt_iff hc).mpr h
  · rw [min_eq_right h]
    nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]

/-- Normalizing an upper quadratic-form coefficient by `max c 1` always dominates the correct
square-root coefficient. -/
theorem sqrt_le_normalizedUpperCoefficient {c : ℝ} (hc : 0 ≤ c) :
    Real.sqrt c ≤ max c 1 := by
  rcases le_total c 1 with h | h
  · rw [max_eq_right h]
    nlinarith [Real.sq_sqrt hc, Real.sqrt_nonneg c]
  · rw [max_eq_left h]
    exact (sqrt_le_self_iff hc).mpr (Or.inl h)

/-- Distance produced by scaling a quadratic metric tensor by `c`. -/
def quadraticScaleDistance (c : ℝ) {X : Type*} [PseudoMetricSpace X] (x y : X) : ℝ :=
  Real.sqrt c * dist x y

/-- Quadratically scaled distance has the expected squared value. -/
theorem quadraticScaleDistance_sq {c : ℝ} (hc : 0 ≤ c)
    {X : Type*} [PseudoMetricSpace X] (x y : X) :
    quadraticScaleDistance c x y ^ 2 = c * dist x y ^ 2 := by
  rw [quadraticScaleDistance, mul_pow, Real.sq_sqrt hc]

/-- Quadratically scaled distance is nonnegative. -/
theorem quadraticScaleDistance_nonneg {c : ℝ} (X : Type*) [PseudoMetricSpace X]
    (x y : X) : 0 ≤ quadraticScaleDistance c x y := by
  exact mul_nonneg (Real.sqrt_nonneg _) dist_nonneg

/-- Quadratically scaled distance vanishes on the diagonal. -/
@[simp] theorem quadraticScaleDistance_self {c : ℝ}
    {X : Type*} [PseudoMetricSpace X] (x : X) : quadraticScaleDistance c x x = 0 := by
  simp [quadraticScaleDistance]

/-- Quadratically scaled distance is symmetric. -/
theorem quadraticScaleDistance_comm {c : ℝ}
    {X : Type*} [PseudoMetricSpace X] (x y : X) :
    quadraticScaleDistance c x y = quadraticScaleDistance c y x := by
  simp [quadraticScaleDistance, dist_comm]

/-- Quadratically scaled distance satisfies the triangle inequality. -/
theorem quadraticScaleDistance_triangle {c : ℝ} (X : Type*) [PseudoMetricSpace X]
    (x y z : X) :
    quadraticScaleDistance c x z ≤
      quadraticScaleDistance c x y + quadraticScaleDistance c y z := by
  unfold quadraticScaleDistance
  rw [← mul_add]
  exact mul_le_mul_of_nonneg_left (dist_triangle _ _ _) (Real.sqrt_nonneg _)

/-- Positive quadratic scaling preserves separation. -/
theorem quadraticScaleDistance_eq_zero_iff {c : ℝ} (hc : 0 < c)
    {X : Type*} [MetricSpace X] (x y : X) :
    quadraticScaleDistance c x y = 0 ↔ x = y := by
  constructor
  · intro h
    rcases mul_eq_zero.mp h with hsqrt | hdist
    · exact False.elim ((Real.sqrt_pos.mpr hc).ne' hsqrt)
    · exact dist_eq_zero.mp hdist
  · rintro rfl
    simp

/-- At distinct points, the printed upper coefficient `c` bounds the true scaled distance exactly
in the range characterized by `sqrt_le_self_iff`. -/
theorem quadraticScaleDistance_le_printed_iff {c : ℝ} (hc : 0 ≤ c)
    {X : Type*} [MetricSpace X] {x y : X} (hxy : x ≠ y) :
    quadraticScaleDistance c x y ≤ c * dist x y ↔ 1 ≤ c ∨ c = 0 := by
  rw [quadraticScaleDistance, mul_le_mul_iff_left₀ (dist_pos.mpr hxy)]
  exact sqrt_le_self_iff hc

/-- At distinct points, the printed lower coefficient `c` is bounded by the true scaled distance
exactly when `c ≤ 1`. -/
theorem printed_lower_le_quadraticScaleDistance_iff {c : ℝ} (hc : 0 ≤ c)
    {X : Type*} [MetricSpace X] {x y : X} (hxy : x ≠ y) :
    c * dist x y ≤ quadraticScaleDistance c x y ↔ c ≤ 1 := by
  rw [quadraticScaleDistance, mul_le_mul_iff_left₀ (dist_pos.mpr hxy)]
  exact self_le_sqrt_iff hc

end SquareRootScaling

section UniformEnvelope

/-- A two-sided additive distance envelope gives an absolute-error envelope. -/
theorem twoSidedDistanceEnvelope_abs
    {d₀ dₙ lowerError upperError : ℝ}
    (hlower : d₀ - lowerError ≤ dₙ) (hupper : dₙ ≤ d₀ + upperError) :
    |dₙ - d₀| ≤ max lowerError upperError := by
  rw [abs_le]
  constructor
  · have := le_max_left lowerError upperError
    linarith
  · have := le_max_right lowerError upperError
    linarith

/-- The paper's uniform squeeze theorem, generalized to asymmetric lower and upper errors. -/
theorem tendstoUniformlyOn_of_twoSidedEnvelope
    {X N : Type*} {l : Filter N}
    {F : N → X → ℝ} {f : X → ℝ}
    {lowerError upperError : N → ℝ}
    (hlower : Tendsto lowerError l (𝓝 0))
    (hupper : Tendsto upperError l (𝓝 0))
    (henvelope : ∀ n x,
      f x - lowerError n ≤ F n x ∧ F n x ≤ f x + upperError n) :
    TendstoUniformlyOn F f l Set.univ := by
  have hmax : Tendsto (fun n => max (lowerError n) (upperError n)) l (𝓝 0) := by
    simpa using hlower.max hupper
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [hmax.eventually_lt_const hε] with n hn x hx
  rw [Real.dist_eq, abs_sub_comm]
  exact lt_of_le_of_lt
    (twoSidedDistanceEnvelope_abs (henvelope n x).1 (henvelope n x).2) hn

end UniformEnvelope

section CorpusBoundedDistance

/-- Canonical harmonic contraction of the corpus's bounded-distance transform. -/
def harmonicContractedBoundedDistance (n : ℕ)
    {X : Type*} [PseudoMetricSpace X] (x y : X) : ℝ :=
  (1 - 1 / ((n : ℝ) + 1)) * HTGeometry.boundedDist (dist x y)

/-- Harmonic contraction lies in the additive envelope of radius `1 / (n + 1)`. -/
theorem harmonicContractedBoundedDistance_envelope (n : ℕ)
    {X : Type*} [PseudoMetricSpace X] (x y : X) :
    HTGeometry.boundedDist (dist x y) - 1 / ((n : ℝ) + 1) ≤
        harmonicContractedBoundedDistance n x y ∧
      harmonicContractedBoundedDistance n x y ≤
        HTGeometry.boundedDist (dist x y) + 1 / ((n : ℝ) + 1) := by
  have hδ : 0 ≤ 1 / ((n : ℝ) + 1) := by positivity
  have hb0 : 0 ≤ HTGeometry.boundedDist (dist x y) :=
    HTGeometry.boundedDist_nonneg dist_nonneg
  have hb1 : HTGeometry.boundedDist (dist x y) ≤ 1 :=
    HTGeometry.boundedDist_le_one dist_nonneg
  unfold harmonicContractedBoundedDistance
  constructor <;> nlinarith

/-- The harmonic contractions converge uniformly on all pairs in every pseudo-metric space.  The
global estimate is available because the corpus transform `boundedDist` is at most one. -/
theorem harmonicContractedBoundedDistance_tendstoUniformly
    (X : Type*) [PseudoMetricSpace X] :
    TendstoUniformlyOn
      (fun n (p : X × X) => harmonicContractedBoundedDistance n p.1 p.2)
      (fun p : X × X => HTGeometry.boundedDist (dist p.1 p.2))
      atTop Set.univ := by
  apply tendstoUniformlyOn_of_twoSidedEnvelope
    (lowerError := fun n : ℕ => 1 / ((n : ℝ) + 1))
    (upperError := fun n : ℕ => 1 / ((n : ℝ) + 1))
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
  · intro n p
    exact harmonicContractedBoundedDistance_envelope n p.1 p.2

end CorpusBoundedDistance

end GaloisForLFunctions.HTGeometry
