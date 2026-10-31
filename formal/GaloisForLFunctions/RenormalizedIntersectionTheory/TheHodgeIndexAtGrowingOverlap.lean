import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.LogarithmicOverlapOfTheCompleteWeilMatrixIsTheRiemannHypothesis
import GaloisForLFunctions.HTGeometry.HermitianSpectralWindowBounds
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleIsTheOnlyNegativeSquareBeyondTheThreshold
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.ThePoleAtEveryRoot
import GaloisForLFunctions.SuccessorShellArithmetic.FixedConductorPacketsArePositiveBelowTheNineteenthRoot
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
* **Every power of the logarithm** (`riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log`,
  `riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log`): for a smooth nonnegative profile on
  `[0, 1]` the same holds at `c = 2(log N)^α` for every `α > 0`.
* **Packets below the nineteenth root** (`eventually_completeWeil_hodgeIndex_packet_root`,
  `exists_growing_packet_hodgeIndex_root`): at overlap `(log N)^α`, `α < 1/19`, the Hodge index holds
  on every fixed conductor packet and on slowly growing initial packets
  (SuccessorShellArithmetic). What is RH at a power of the logarithm is its uniformity over all of
  `v_1^⊥`.
* **One hyperplane, two readings** (`poleHyperplane_markov_nonneg_iff_hodgeIndex`): at each horizon,
  Markov positivity on the recentred atomic tests with `m₋ = 0` is Hodge positivity on `v_1^⊥`.
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

section Profiles

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

variable {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)

include hφ hsupp in
/-- The lower pole moment of a dilated nonnegative atom is positive. -/
theorem poleMoment_atomDilate_pos_of (hnn : ∀ u, 0 ≤ φ u) (hint : 0 < ∫ u, φ u) {w : ℝ}
    (hw : 0 < w) : 0 < ∫ u, atomDilate φ w u * Real.exp (-(u / 2)) := by
  obtain ⟨hg2, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  have hi1 : MeasureTheory.Integrable (fun u => Real.exp (-(w / 2)) * atomDilate φ w u) :=
    (hg2.continuous.integrable_of_hasCompactSupport hgc).const_mul _
  have hi2 : MeasureTheory.Integrable (fun u => atomDilate φ w u * Real.exp (-(u / 2))) :=
    (hg2.continuous.mul (by fun_prop)).integrable_of_hasCompactSupport hgc.mul_right
  have hle : ∫ u, Real.exp (-(w / 2)) * atomDilate φ w u ≤
      ∫ u, atomDilate φ w u * Real.exp (-(u / 2)) := by
    refine MeasureTheory.integral_mono hi1 hi2 fun u => ?_
    by_cases hu : u ∈ Set.Icc 0 w
    · have h0 : 0 ≤ atomDilate φ w u := hnn _
      have he : Real.exp (-(w / 2)) ≤ Real.exp (-(u / 2)) :=
        Real.exp_le_exp.mpr (by linarith [hu.2])
      nlinarith
    · simp only [hgs u hu, mul_zero, zero_mul, le_refl]
  rw [MeasureTheory.integral_const_mul, integral_atomDilate hw] at hle
  exact lt_of_lt_of_le (by positivity) hle

include hφ hsupp in
/-- **The pole moment of a recentred atomic test** is a fixed multiple of the harmonic sum
`Σ_{n ≤ N} y_n/√n`. -/
theorem poleMomentNeg_recentred {w : ℝ} (hw : 0 < w) (N : ℕ) (y : ℕ → ℝ) :
    poleMomentNeg (atomicTest N y (dilate (2 / w) (recentredProfile φ))) =
      Real.exp (w / 4) * ((∫ u, atomDilate φ w u * Real.exp (-(u / 2))) *
        ((∑ n ∈ Icc 1 N, y n / Real.sqrt n) / (w * ∫ u, φ u))) := by
  set k := w * ∫ u, φ u
  obtain ⟨hg2, hgs, -⟩ := atomDilate_facts hφ hsupp hw
  set A := atomicTest N (fun n => y n / k) (atomDilate φ w)
  have hT : atomicTest N y (dilate (2 / w) (recentredProfile φ)) =
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
  rw [poleMomentNeg, hT, hshift, hmA, sum_div, show -(-(w / 2) / 2) = w / 4 by ring]
  congr 2
  exact sum_congr rfl fun n _ => by ring

/-- The pairing with the pole conductor is the harmonic sum of the extended coefficients. -/
theorem inner_normalizedRamanujanHorizonVector_one {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = (Real.sqrt (Real.log N))⁻¹ *
      ∑ n ∈ Icc 1 N, primeHorizonExtension x n / Real.sqrt n := by
  rw [normalizedRamanujanHorizonVector, real_inner_smul_right,
    EuclideanSpace.inner_eq_star_dotProduct]
  change (Real.sqrt (Real.log N))⁻¹ * ∑ n : PrimeHorizonIndex N, ramanujanPoleProfile 1 n * x n = _
  congr 1
  rw [← Finset.sum_coe_sort (Icc 1 N)]
  refine sum_congr rfl fun n _ => ?_
  simp only [ramanujanPoleProfile, normalizedRamanujanMode, ramanujanMode_one, Nat.totient_one,
    Nat.cast_one, Real.sqrt_one, div_one, primeHorizonExtension_coe]
  ring

include hφ hsupp in
/-- **One hyperplane, two readings.** At a horizon `N ≥ 2` and overlap `c > 0`, the Markov form is
nonnegative on the recentred atomic tests in the pole hyperplane `m₋ = 0` iff the complete Weil
energy is nonnegative on `v_1^⊥`. -/
theorem poleHyperplane_markov_nonneg_iff_hodgeIndex (hnn : ∀ u, 0 ≤ φ u)
    (hint : 0 < ∫ u, φ u) (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 2 ≤ N) :
    (∀ y : ℕ → ℝ, poleMomentNeg (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) = 0 →
        0 ≤ markovQuad (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ)))) ↔
      ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy φ c N x := by
  have hN1 : 1 ≤ N := by omega
  have hw : 0 < c / N := div_pos hc (by positivity)
  have hlog : 0 < Real.sqrt (Real.log N) := Real.sqrt_pos.mpr (Real.log_pos (by exact_mod_cast hN))
  set k := c / N * ∫ u, φ u
  have hk : 0 < k := mul_pos hw hint
  have hm := poleMoment_atomDilate_pos_of hφ hsupp hnn hint hw
  have hG : 0 < ∫ u, atomDilate φ (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]; exact mul_pos hw hM
  have hφS := contDiff_recentredProfile hφ
  have hφ1 := vanishesOff_recentredProfile hsupp
  -- the Markov form is Weil's form on the pole hyperplane
  have hmarkov : ∀ y : ℕ → ℝ,
      poleMomentNeg (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) = 0 →
      markovQuad (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) =
        weilQuad (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) := fun y hy => by
    obtain ⟨hT2, hTc⟩ := atomicTest_dilate_mem hφS hφ1 (show 0 < 2 / (c / N) by positivity) N y
    rw [markovQuad_eq hT2 hTc, hy, zero_mul, mul_zero, sub_zero]
  -- the pole moment vanishes exactly on the harmonic hyperplane
  have hpole : ∀ y : ℕ → ℝ,
      poleMomentNeg (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) = 0 ↔
        ∑ n ∈ Icc 1 N, y n / Real.sqrt n = 0 := fun y => by
    rw [poleMomentNeg_recentred hφ hsupp hw]
    constructor
    · intro h
      rcases mul_eq_zero.mp h with h | h
      · exact absurd h (Real.exp_pos _).ne'
      · exact (div_eq_zero_iff.mp ((mul_eq_zero.mp h).resolve_left hm.ne')).resolve_right hk.ne'
    · intro h; rw [h, zero_div, mul_zero, mul_zero]
  constructor
  · intro H x hx
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN1]
    refine div_nonneg ?_ hG.le
    set y : ℕ → ℝ := fun n => primeHorizonExtension x n * k
    have hy : poleMomentNeg (atomicTest N y (dilate (2 / (c / N)) (recentredProfile φ))) = 0 := by
      rw [hpole]
      rw [inner_normalizedRamanujanHorizonVector_one] at hx
      have hs := (mul_eq_zero.mp hx).resolve_left (inv_ne_zero hlog.ne')
      have e : ∑ n ∈ Icc 1 N, y n / Real.sqrt n =
          k * ∑ n ∈ Icc 1 N, primeHorizonExtension x n / Real.sqrt n := by
        rw [mul_sum]; exact sum_congr rfl fun n _ => by simp only [y]; ring
      rw [e, hs, mul_zero]
    have h := H y hy
    rw [hmarkov y hy, weilQuad_atomicTest_dilate_recentred hw] at h
    have e : (fun n => primeHorizonExtension x n * k / (c / N * ∫ u, φ u)) =
        primeHorizonExtension x := funext fun n => mul_div_cancel_right₀ _ hk.ne'
    rwa [e] at h
  · intro H y hy
    rw [hmarkov y hy, weilQuad_atomicTest_dilate_recentred hw, atomicTest_restrict]
    set x : EuclideanSpace ℝ (PrimeHorizonIndex N) :=
      WithLp.toLp 2 (fun n : PrimeHorizonIndex N => y n / k)
    have hx : ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 := by
      rw [inner_normalizedRamanujanHorizonVector_one]
      have e : ∑ n ∈ Icc 1 N, primeHorizonExtension x n / Real.sqrt n =
          (∑ n ∈ Icc 1 N, y n / Real.sqrt n) / k := by
        rw [sum_div]
        refine sum_congr rfl fun n hn => ?_
        simp only [x, primeHorizonExtension, dif_pos hn]
        ring
      rw [e, (hpole y).mp hy, zero_div, mul_zero]
    have h := H x hx
    rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad hφ hsupp hc hN1] at h
    exact (div_nonneg_iff.mp h).elim (fun h' => h'.1) fun h' => absurd h'.2 (not_le.mpr hG)

end Profiles

section Logarithmic

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics

theorem tiltedUnitSpline_nonneg (u : ℝ) : 0 ≤ φ₀ u := by
  unfold tiltedUnitSpline atomDilate
  exact BiScaleUncertainty.ChebyshevGauge.splineProbe_nonneg _

theorem integral_tiltedUnitSpline_pos : 0 < ∫ u, φ₀ u :=
  lt_of_le_of_ne (MeasureTheory.integral_nonneg tiltedUnitSpline_nonneg)
    (Ne.symm integral_tiltedUnitSpline_ne_zero)

theorem kappa_log_eq (α : ℝ) : (fun N : ℕ => 2 / (2 * Real.log N ^ α / N)) =
    fun N : ℕ => (N : ℝ) / Real.log N ^ α := by
  funext N
  rw [div_div_eq_mul_div, mul_div_mul_left _ _ two_ne_zero]

/-- **The renormalized Hodge index at logarithmic overlap is RH.** For `α > 1/2`, RH holds iff,
eventually in `N`, the complete Weil energy of the tilted unit spline at overlap `2(log N)^α` is
nonnegative on the orthogonal complement of the pole conductor `v_1`. -/
theorem riemannHypothesis_iff_completeWeil_hodgeIndex_log {α : ℝ} (hα : 1 / 2 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy φ₀ (2 * Real.log N ^ α) N x := by
  have hκ : OverlapGrowth fun N : ℕ => 2 / (2 * Real.log N ^ α / N) := by
    rw [kappa_log_eq]; exact overlapGrowth_log hα
  rw [riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg hκ
    (contDiff_recentredProfile contDiff_tiltedUnitSpline)
    (vanishesOff_recentredProfile tiltedUnitSpline_eq_zero)
    (integral_recentredProfile integral_tiltedUnitSpline_ne_zero)]
  refine eventually_congr ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  exact poleHyperplane_markov_nonneg_iff_hodgeIndex contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero tiltedUnitSpline_nonneg integral_tiltedUnitSpline_pos
    integral_tiltedUnitSpline_sq_pos (by positivity) hN2

end Logarithmic

/-! ### Packets below the nineteenth root -/

section Packets

open CompletedArithmeticForms SuccessorShellArithmetic

/-- **The Hodge index on fixed conductor packets below the nineteenth root.** -/
theorem eventually_completeWeil_hodgeIndex_packet_root {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 19)
    {d : ℕ} (m : Fin d → ℕ+) (hm : Function.Injective m) :
    ∀ᶠ N : ℕ in atTop, ∀ b : Fin d → ℝ,
      ⟪∑ i, b i • normalizedRamanujanHorizonVector (m i) N, normalizedRamanujanHorizonVector 1 N⟫ =
          0 →
        0 ≤ completeWeilEnergy φ₀ (logarithmicPacketOverlap α N) N
          (∑ i, b i • normalizedRamanujanHorizonVector (m i) N) := by
  filter_upwards [eventually_tiltedWeil_packet_pos_of_lt_one_nineteenth hα0 hα m hm] with N hN b _
  by_cases hb : b = 0
  · subst hb
    simp [completeWeilEnergy]
  · exact (hN b hb).le

/-- **The Hodge index on slowly growing initial packets below the nineteenth root.** -/
theorem exists_growing_packet_hodgeIndex_root {α : ℝ} (hα0 : 0 < α) (hα : α < 1 / 19) :
    ∃ Q : ℕ → ℕ, Filter.Tendsto Q atTop atTop ∧ ∀ N : ℕ, ∀ b : Fin (Q N) → ℝ,
      0 ≤ completeWeilEnergy φ₀ (logarithmicPacketOverlap α N) N
        (∑ i, b i • normalizedRamanujanHorizonVector (firstConductors (Q N) i) N) := by
  obtain ⟨Q, hQ, h⟩ := exists_growing_packet_pos_of_lt_one_nineteenth hα0 hα
  refine ⟨Q, hQ, fun N b => ?_⟩
  by_cases hb : b = 0
  · subst hb
    simp [completeWeilEnergy]
  · exact (h N b hb).le

end Packets

/-! ### Every power of the logarithm -/

section EveryRoot

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
open scoped ContDiff

/-- **For a smooth profile the Hodge index at every power of the logarithm is RH.** For every
`C^∞` nonnegative profile on `[0, 1]` with positive mass and every `α > 0`, RH holds iff eventually
the complete Weil energy at overlap `2(log N)^α` is nonnegative on `v_1^⊥`. -/
theorem riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ)
    (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hnn : ∀ u, 0 ≤ φ u) (hint : 0 < ∫ u, φ u)
    (hM : 0 < ∫ u, φ u ^ 2) {α : ℝ} (hα : 0 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy φ (2 * Real.log N ^ α) N x := by
  have hφ2 : ContDiff ℝ 2 φ := hφ.of_le (natCast_le_infty 2)
  set q : ℕ := ⌈1 / α⌉₊ + 1
  have hq : 1 < (q : ℝ) * α := by
    have h1 : 1 / α ≤ ⌈1 / α⌉₊ := Nat.le_ceil _
    have h2 : (1 : ℝ) = 1 / α * α := by field_simp
    have : (q : ℝ) = ⌈1 / α⌉₊ + 1 := by simp [q]
    rw [this]; nlinarith
  have hκ : OverlapGrowthPow q fun N : ℕ => 2 / (2 * Real.log N ^ α / N) := by
    rw [kappa_log_eq]; exact overlapGrowthPow_log hα hq
  have hφS : ContDiff ℝ ∞ (recentredProfile φ) := by
    unfold recentredProfile
    exact (hφ.comp ((contDiff_id.add contDiff_const).div_const _)).div_const _
  rw [riemannHypothesis_iff_poleHyperplane_atomicFamilies_nonneg_of_growthPow hκ hφS
    (vanishesOff_recentredProfile hsupp) (integral_recentredProfile hint.ne')]
  refine eventually_congr ?_
  filter_upwards [eventually_ge_atTop 2] with N hN2
  have hlog : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  exact poleHyperplane_markov_nonneg_iff_hodgeIndex hφ2 hsupp hnn hint hM (by positivity) hN2

/-- A smooth bump on `[0, 1]`, equal to one on `[1/4, 3/4]`. -/
def unitBump : ContDiffBump (1 / 2 : ℝ) := ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

theorem unitBump_eq_zero (u : ℝ) (hu : u ∉ Set.Icc 0 1) : unitBump u = 0 := by
  rw [← Function.notMem_support, unitBump.support_eq]
  intro h
  have hr : unitBump.rOut = 1 / 2 := rfl
  rw [Metric.mem_ball, Real.dist_eq, abs_lt, hr] at h
  exact hu ⟨by linarith [h.1], by linarith [h.2]⟩

theorem integral_unitBump_sq_pos : 0 < ∫ u, unitBump u ^ 2 := by
  have hc : Continuous fun u => unitBump u ^ 2 := unitBump.continuous.pow 2
  have hcs : HasCompactSupport fun u => unitBump u ^ 2 :=
    unitBump.hasCompactSupport.comp_left (g := fun t : ℝ => t ^ 2) (by norm_num)
  rw [MeasureTheory.integral_pos_iff_support_of_nonneg (fun u => sq_nonneg _)
    (hc.integrable_of_hasCompactSupport hcs)]
  have hs : Function.support (fun u => unitBump u ^ 2) = Metric.ball (1 / 2 : ℝ) (1 / 2) := by
    have hb : Function.support (unitBump : ℝ → ℝ) = Metric.ball (1 / 2 : ℝ) (1 / 2) :=
      unitBump.support_eq
    rw [← hb]
    ext u
    simp [Function.mem_support]
  rw [hs]
  exact Metric.measure_ball_pos _ _ (by norm_num)

/-- **The Hodge index at every power of the logarithm is RH**, for the smooth unit bump. -/
theorem riemannHypothesis_iff_unitBump_hodgeIndex_rpow_log {α : ℝ} (hα : 0 < α) :
    RiemannHypothesis ↔ ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      ⟪x, normalizedRamanujanHorizonVector 1 N⟫ = 0 →
        0 ≤ completeWeilEnergy unitBump (2 * Real.log N ^ α) N x :=
  riemannHypothesis_iff_completeWeil_hodgeIndex_rpow_log unitBump.contDiff unitBump_eq_zero
    (fun _ => unitBump.nonneg) unitBump.integral_pos integral_unitBump_sq_pos hα

end EveryRoot

end GaloisForLFunctions.RenormalizedIntersectionTheory
