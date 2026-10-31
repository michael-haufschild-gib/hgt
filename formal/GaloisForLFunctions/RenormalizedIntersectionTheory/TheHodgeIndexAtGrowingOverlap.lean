import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds

/-!
# The Hodge index at growing overlap

At finite resolution the scaling correspondences are the atoms of the tilted unit spline at overlap
`c` on the horizon `{1, …, N}`, their intersection matrix is the complete Weil matrix, and the pole
class is the normalized Ramanujan vector `v_1`. At fixed `c` the Hodge index holds with a gap
(`TheHodgeIndexHoldsAtEveryFixedOverlap`). Along growing overlap schedules `c = c_N`:

* **Iterated-logarithmic overlap: the Hodge index holds** (`eventually_completeWeil_hodgeIndex_iteratedLog`):
  for `1 ≤ c ≤ (log log N)^α`, `α < 1/16`, the complete Weil energy is nonnegative on the pole
  hyperplane `v_1^⊥` (indeed everywhere), unconditionally.
* **Logarithmic overlap: RH gives the Hodge index** (`eventually_completeWeil_hodgeIndex_log_of_RH`):
  at `c = 2(log N)^α`, `α > 1/4`, nonnegativity on the whole space is RH
  (`RenormalizedArithmeticPotentialTheory.riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log`),
  so RH gives the Hodge index there.
* **The Hodge index leaves at most one square** (`eigenvalues_nonneg_or_of_nonneg_on_orthogonal`,
  `eventually_completeWeil_eigenvalues_nonneg_or_log_of_RH`): positivity on one hyperplane allows at
  most one negative eigenvalue, since two negative eigenvectors span a plane that meets every
  hyperplane.

So at logarithmic overlap the renormalized Hodge index lies between "at most one negative eigenvalue"
and RH. It is RH exactly when the off-line negative direction can be placed on the pole hyperplane
at finite resolution, which is what the glued (infinite-resolution) form does
(`riemannHypothesis_iff_hyperplane_nonneg`).
-/

noncomputable section
open Filter Finset
open scoped RealInnerProductSpace
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.CriticalArithmeticCorrelationTheory

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The tilted unit spline, the profile of the atoms. -/
local notation "φ₀" => SpacingScaleHarmonicAnalysis.tiltedUnitSpline

section Codimension

variable {I : Type*} [Fintype I] [DecidableEq I] {A : Matrix I I ℝ}

/-- A positive-definite symmetric matrix has nonnegative energy. -/
theorem energy_nonneg_of_posDef (hA : A.IsHermitian) (hpd : A.PosDef) (x : EuclideanSpace ℝ I) :
    0 ≤ ⟪Matrix.toEuclideanLin A x, x⟫ := by
  have h := shiftedHermitianEnergy_eq_sum hA 0 x
  have hev := hA.posDef_iff_eigenvalues_pos.mp hpd
  have hs : 0 ≤ ∑ i, hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 :=
    sum_nonneg fun i _ => mul_nonneg (hev i).le (sq_nonneg _)
  have e : ∑ i, (0 - hA.eigenvalues i) * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 =
      -∑ i, hA.eigenvalues i * ⟪x, hA.eigenvectorBasis i⟫ ^ 2 := by
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun i _ => by ring
  rw [e, zero_mul, zero_sub] at h
  linarith

/-- **One hyperplane leaves at most one negative eigenvalue.** If the energy is nonnegative on
`v^⊥`, then of any two eigenvalues at least one is nonnegative. -/
theorem eigenvalues_nonneg_or_of_nonneg_on_orthogonal (hA : A.IsHermitian)
    (v : EuclideanSpace ℝ I) (h : ∀ x, ⟪x, v⟫ = 0 → 0 ≤ ⟪Matrix.toEuclideanLin A x, x⟫)
    {i j : I} (hij : i ≠ j) : 0 ≤ hA.eigenvalues i ∨ 0 ≤ hA.eigenvalues j := by
  by_contra hneg
  rw [not_or, not_le, not_le] at hneg
  obtain ⟨hi, hj⟩ := hneg
  set e := hA.eigenvectorBasis
  have hon := e.orthonormal
  have happ : ∀ k, Matrix.toEuclideanLin A (e k) = hA.eigenvalues k • e k := fun k => by
    ext l
    exact congrFun (hA.mulVec_eigenvectorBasis k) l
  have hn : ∀ k, ⟪e k, e k⟫ = 1 := fun k => by
    rw [real_inner_self_eq_norm_sq, hon.1 k, one_pow]
  have h0 : ⟪e i, e j⟫ = 0 := hon.2 hij
  have h0' : ⟪e j, e i⟫ = 0 := hon.2 hij.symm
  -- energy and pole moment of a combination of the two eigenvectors
  have henergy : ∀ a b : ℝ, ⟪Matrix.toEuclideanLin A (a • e i + b • e j), a • e i + b • e j⟫ =
      a ^ 2 * hA.eigenvalues i + b ^ 2 * hA.eigenvalues j := fun a b => by
    rw [map_add, map_smul, map_smul, happ, happ]
    simp only [inner_add_left, inner_add_right, real_inner_smul_left, real_inner_smul_right, hn,
      h0, h0']
    ring
  have hmom : ∀ a b : ℝ, ⟪a • e i + b • e j, v⟫ = a * ⟪e i, v⟫ + b * ⟪e j, v⟫ := fun a b => by
    rw [inner_add_left, real_inner_smul_left, real_inner_smul_left]
  by_cases hp : ⟪e i, v⟫ = 0
  · have h1 := h ((1 : ℝ) • e i + (0 : ℝ) • e j) (by rw [hmom, hp]; ring)
    rw [henergy] at h1
    linarith
  · have h1 := h (⟪e j, v⟫ • e i + (-⟪e i, v⟫) • e j) (by rw [hmom]; ring)
    rw [henergy] at h1
    have hp2 : 0 < (-⟪e i, v⟫) ^ 2 := by
      rw [neg_sq]; exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hp))
    nlinarith [sq_nonneg ⟪e j, v⟫, mul_pos hp2 (neg_pos.mpr hj)]

end Codimension

/-- **The Hodge index holds at iterated-logarithmic overlap.** -/
theorem eventually_completeWeil_hodgeIndex_iteratedLog {α : ℝ} (hα : 0 < α) (hα16 : α < 1 / 16) :
    ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c → c ≤ Real.log (Real.log (N : ℝ)) ^ α →
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
          0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix φ₀ c N) x, x⟫ := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef_iteratedLog hα hα16]
    with N hN c hc hcup x _
  exact energy_nonneg_of_posDef (completeWeilMatrix_isHermitian φ₀ c N)
    (hN c hc hcup) x

/-- **RH gives the Hodge index at logarithmic overlap.** -/
theorem eventually_completeWeil_hodgeIndex_log_of_RH {α : ℝ} (hα : 1 / 4 < α)
    (hRH : RiemannHypothesis) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy φ₀ (2 * Real.log N ^ α) N x := by
  filter_upwards [(riemannHypothesis_iff_tiltedUnitSpline_completeWeil_nonneg_log hα).mp hRH]
    with N hN x _
  exact hN x

/-- **The Hodge index at an overlap leaves at most one negative eigenvalue there.** -/
theorem completeWeil_eigenvalues_nonneg_or_of_hodgeIndex {c : ℝ} {N : ℕ}
    (h : ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 → 0 ≤ completeWeilEnergy φ₀ c N x)
    {i j : PrimeHorizonIndex N} (hij : i ≠ j) :
    0 ≤ (completeWeilMatrix_isHermitian φ₀ c N).eigenvalues i ∨
      0 ≤ (completeWeilMatrix_isHermitian φ₀ c N).eigenvalues j :=
  eigenvalues_nonneg_or_of_nonneg_on_orthogonal _ _ h hij

end GaloisForLFunctions.RenormalizedIntersectionTheory
