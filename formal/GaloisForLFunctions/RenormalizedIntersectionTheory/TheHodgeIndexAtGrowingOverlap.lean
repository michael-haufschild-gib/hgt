import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold
import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheWeilEnergiesOfTheArithmeticModes

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
* **Logarithmic overlap: the Hodge index is RH** (`riemannHypothesis_iff_completeWeil_hodgeIndex_log`):
  at `c = 2(log N)^α`, `α > 1/2`, RH holds iff eventually the complete Weil energy is nonnegative on
  `v_1^⊥`. The pole class carries no information: positivity on its orthogonal complement already
  forces RH.
* **The Hodge index leaves at most one square** (`eigenvalues_nonneg_or_of_nonneg_on_orthogonal`,
  `completeWeil_eigenvalues_nonneg_or_of_hodgeIndex`): positivity on one hyperplane allows at most
  one negative eigenvalue, since two negative eigenvectors span a plane that meets every hyperplane.

The mechanism of the equivalence: on the atomic tests `f_x = Σ x_n g(· − log n)` the continuous pole
moment is `∫ f_x e^{−u/2} = (∫ g e^{−u/2}) Σ x_n/√n` (SelectiveMultiscaleArithmeticPositivity), so the
pole hyperplane of Weil's form is `v_1^⊥`; there Weil's form is the Markov form, and RH is the
positivity of the Markov form on the pole hyperplane under overlap growth (SpacingScaleHarmonicAnalysis,
where a pole-free negative test of an off-line zero is synthesized and corrected into the
hyperplane). The complete Weil energy is Weil's form on the recentred atoms
(RenormalizedArithmeticPotentialTheory).
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

/-! ### The Hodge index at logarithmic overlap is RH -/

section Logarithmic

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

theorem tiltedUnitSpline_nonneg (u : ℝ) : 0 ≤ φ₀ u := by
  unfold tiltedUnitSpline atomDilate
  exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _

theorem integral_tiltedUnitSpline_pos : 0 < ∫ u, φ₀ u :=
  lt_of_le_of_ne (MeasureTheory.integral_nonneg tiltedUnitSpline_nonneg)
    (Ne.symm integral_tiltedUnitSpline_ne_zero)

/-- The lower pole moment of a dilated atom is positive. -/
theorem poleMoment_atomDilate_pos {w : ℝ} (hw : 0 < w) :
    0 < ∫ u, atomDilate φ₀ w u * Real.exp (-(u / 2)) := by
  obtain ⟨hg2, hgs, hgc⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  have hi1 : MeasureTheory.Integrable (fun u => Real.exp (-(w / 2)) * atomDilate φ₀ w u) :=
    (hg2.continuous.integrable_of_hasCompactSupport hgc).const_mul _
  have hi2 : MeasureTheory.Integrable (fun u => atomDilate φ₀ w u * Real.exp (-(u / 2))) :=
    (hg2.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hle : ∫ u, Real.exp (-(w / 2)) * atomDilate φ₀ w u ≤
      ∫ u, atomDilate φ₀ w u * Real.exp (-(u / 2)) := by
    refine MeasureTheory.integral_mono hi1 hi2 fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · have h0 : 0 ≤ atomDilate φ₀ w u := tiltedUnitSpline_nonneg _
      have he : Real.exp (-(w / 2)) ≤ Real.exp (-(u / 2)) :=
        Real.exp_le_exp.mpr (by linarith [hu.2])
      nlinarith
    · simp only [hgs u hu, mul_zero, zero_mul, le_refl]
  rw [MeasureTheory.integral_const_mul, integral_atomDilate hw] at hle
  exact lt_of_lt_of_le (by have := integral_tiltedUnitSpline_pos; positivity) hle

/-- **The continuous pole hyperplane is the harmonic hyperplane** for the recentred atoms: if the
lower pole moment of the atomic test vanishes, so does `Σ_{n ≤ N} y_n/√n`. -/
theorem harmonic_eq_zero_of_poleMomentNeg_eq_zero {w : ℝ} (hw : 0 < w) (N : ℕ) (y : ℕ → ℝ)
    (h0 : poleMomentNeg (atomicTest N y (dilate (2 / w) (recentredProfile φ₀))) = 0) :
    ∑ n ∈ Icc 1 N, y n / Real.sqrt n = 0 := by
  set k := w * ∫ u, φ₀ u
  have hk : 0 < k := mul_pos hw integral_tiltedUnitSpline_pos
  obtain ⟨hg2, hgs, -⟩ := atomDilate_facts contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero hw
  set A := atomicTest N (fun n => y n / k) (atomDilate φ₀ w)
  have hT : atomicTest N y (dilate (2 / w) (recentredProfile φ₀)) =
      fun u => A (u - -(w / 2)) := by
    funext u
    unfold A atomicTest
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [dilate_profile_eq_atomDilate hw, show u - -(w / 2) - Real.log n =
      u - Real.log n + w / 2 by ring]
    ring
  have hmA := SelectiveMultiscaleArithmeticPositivity.integral_atomicTest_mul_exp_neg_half
    hg2.continuous hgs N (fun n => y n / k)
  have hshift := SelectiveMultiscaleArithmeticPositivity.integral_shift_mul_exp A (-(w / 2))
    (-(1 / 2))
  simp only [show ∀ u : ℝ, -(1 / 2) * u = -(u / 2) from fun u => by ring] at hshift
  rw [poleMomentNeg, hT, hshift, hmA] at h0
  have hsum : ∑ n ∈ Icc 1 N, y n / k / Real.sqrt n = (∑ n ∈ Icc 1 N, y n / Real.sqrt n) / k := by
    rw [sum_div]
    exact sum_congr rfl fun n _ => by ring
  rw [hsum] at h0
  have hm := poleMoment_atomDilate_pos hw
  have hS : (∑ n ∈ Icc 1 N, y n / Real.sqrt n) / k = 0 := by
    rcases mul_eq_zero.mp h0 with h | h
    · exact absurd h (Real.exp_pos _).ne'
    · exact (mul_eq_zero.mp h).resolve_left hm.ne'
  exact (div_eq_zero_iff.mp hS).resolve_right hk.ne'

/-- **The renormalized Hodge index at logarithmic overlap is RH.** For `α > 1/2`, RH holds iff,
eventually in `N`, the complete Weil energy of the tilted unit spline at overlap `2(log N)^α` is
nonnegative on the orthogonal complement of the pole conductor `v_1`. -/
theorem riemannHypothesis_iff_completeWeil_hodgeIndex_log {α : ℝ} (hα : 1 / 2 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy φ₀ (2 * Real.log N ^ α) N x := by
  refine ⟨eventually_completeWeil_hodgeIndex_log_of_RH (by linarith), fun H => ?_⟩
  have hκeq : (fun N : ℕ => 2 / (2 * Real.log N ^ α / N)) =
      fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
    funext N
    rw [div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]
  have hκ : OverlapGrowth fun N : ℕ => 2 / (2 * Real.log N ^ α / N) := by
    rw [hκeq]; exact overlapGrowth_log hα
  have hφ2 := contDiff_recentredProfile contDiff_tiltedUnitSpline
  have hφ1 := vanishesOff_recentredProfile tiltedUnitSpline_eq_zero
  refine (riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg hκ hφ2 hφ1
    (integral_recentredProfile integral_tiltedUnitSpline_ne_zero)).mpr ?_
  filter_upwards [H, eventually_ge_atTop 2] with N hN hN2 y hy
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  set c := 2 * Real.log N ^ α
  have hc : 0 < c := by positivity
  have hN1 : 1 ≤ N := by omega
  have hw : 0 < c / N := div_pos hc (by positivity)
  obtain ⟨hT2, hTc⟩ := atomicTest_dilate_mem hφ2 hφ1 (show 0 < 2 / (c / N) by positivity) N y
  rw [markovQuad_eq hT2 hTc, hy, zero_mul, mul_zero, sub_zero]
  have hsum := harmonic_eq_zero_of_poleMomentNeg_eq_zero hw N y hy
  set k := c / N * ∫ u, φ₀ u
  have hk : 0 < k := mul_pos hw integral_tiltedUnitSpline_pos
  rw [weilQuad_atomicTest_dilate_recentred hw, atomicTest_restrict]
  set x : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
    WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n / k)
  have hx : ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 := by
    rw [normalizedRamanujanHorizonVector, real_inner_smul_right,
      EuclideanSpace.inner_eq_star_dotProduct]
    change (Real.sqrt (Real.log N))⁻¹ *
      ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n * (y n / k) = 0
    have e : ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n * (y n / k) =
        (∑ n ∈ Icc 1 N, y n / Real.sqrt n) / k := by
      rw [sum_div, ← Finset.sum_coe_sort (Icc 1 N)]
      refine sum_congr rfl fun n _ => ?_
      simp only [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one,
        Nat.cast_one, Real.sqrt_one, div_one]
      ring
    rw [e, hsum, zero_div, mul_zero]
  have h := hN x hx
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN1] at h
  have hG : 0 < ∫ u, atomDilate φ₀ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  exact (div_nonneg_iff.mp h).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.mpr hG)

end Logarithmic

end GaloisForLFunctions.RenormalizedIntersectionTheory
