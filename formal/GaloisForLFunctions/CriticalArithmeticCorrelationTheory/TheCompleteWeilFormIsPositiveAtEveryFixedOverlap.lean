import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheUpwardPrimeRowsRealizeTheCompletedShellCorrection
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilResidualIsTheUpwardDefect
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapTiltedSplineReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap

/-!
# Complete Weil positivity at every fixed overlap

The literal upward prime-power residual vanishes in normalized Euclidean norm. Subtracting it
from the complete residual identity gives the completed conductor energies as actual norm
quasimode energies. For the tilted unit spline, the prime-defect reserve and common positive
conductor floor then put the entire complete Weil spectrum above a positive constant.

The overlap is any fixed positive real number. The horizon and spectral floor may depend on it.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics BezoutValuationIncidence

/-- The literal upward row reads only horizon coordinates and preserves scalar multiplication. -/
theorem upwardPrimeRow_congr_smul {g : ℝ → ℝ} {N n : ℕ} {x y : ℕ → ℝ} {r : ℝ}
    (h : ∀ j ∈ Icc 1 N, x j = r * y j) :
    upwardPrimeRow g N x n = r * upwardPrimeRow g N y n := by
  unfold upwardPrimeRow
  have hk : ∀ k : ℕ, _root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N, x j *
      (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n))) =
      r * (_root_.RHTower.vonMangoldtAtom k * ∑ j ∈ Icc 1 N, y j *
        (if j = k * n then 0 else bumpCorr g (Real.log k - (Real.log j - Real.log n)))) := by
    intro k
    rw [mul_left_comm r]
    congr 1
    rw [mul_sum]
    exact sum_congr rfl fun j hj => by rw [h j hj]; ring
  simp_rw [hk]
  exact tsum_mul_left

/-- The operator's normalized upward defect is the literal source residual, scaled by conductor mass. -/
theorem upwardPrimeVector_ramanujan_residual_eq (φ : ℝ → ℝ) (c : ℝ) (N : ℕ)
    {m : ℕ} (hm : 0 < m) :
    upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N =
      (Real.sqrt (m.totient : ℝ))⁻¹ • normalizedUpwardPrimeResidual φ c N m := by
  let s := (Real.sqrt (Real.log N))⁻¹
  let r := (Real.sqrt (m.totient : ℝ))⁻¹
  have hext : ∀ j ∈ Icc 1 N, primeHorizonExtension (normalizedRamanujanHorizonVector m N) j =
      (s * r) * (ramanujanLagCoefficient m j / Real.sqrt j) := by
    intro j hj
    rw [primeHorizonExtension, dif_pos hj]
    change s * ramanujanPoleProfile m j = _
    rw [ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm]
    dsimp only [r]
    ring
  ext n
  have hup := upwardPrimeRow_congr_smul (g := atomDilate φ (c / N)) (n := (n : ℕ)) hext
  change upwardPrimeRow (atomDilate φ (c / N)) N
      (primeHorizonExtension (normalizedRamanujanHorizonVector m N)) n /
      (∫ u, atomDilate φ (c / N) u ^ 2) -
      shellCorrection φ c m * (s * ramanujanPoleProfile m n) =
    r * (actualUpwardRowError φ c N m n / Real.sqrt (Real.log N))
  rw [hup, ramanujanPoleProfile, normalizedRamanujanMode_eq_coefficient hm]
  dsimp only [s, r, actualUpwardRowError]
  ring

/-- Every normalized conductor vector has vanishing literal upward defect. -/
theorem tendsto_upwardPrimeVector_ramanujan_residual_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have h := (tendsto_normalizedUpwardPrimeResidual_norm hφ hsupp hM hc hm).const_mul
    |(Real.sqrt (m.totient : ℝ))⁻¹|
  simpa only [upwardPrimeVector_ramanujan_residual_eq φ c _ hm, norm_smul, Real.norm_eq_abs,
    mul_zero] using h

/-- At every fixed overlap, the actual complete Weil matrix has the completed conductor norm quasimodes. -/
theorem tendsto_completeWeilMatrix_completedConductor_residual_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hA := tendsto_completeWeilMatrix_ramanujan_residual_add_upward_norm hφ hsupp hM hc hm
  have hU := tendsto_upwardPrimeVector_ramanujan_residual_norm hφ hsupp hM hc hm
  have hlim := hA.add hU
  simp only [zero_add] at hlim
  apply squeeze_zero (fun N => norm_nonneg _) _ hlim
  intro N
  have h := norm_sub_le
    (Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N +
      (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
        shellCorrection φ c m • normalizedRamanujanHorizonVector m N))
    (upwardPrimeVector φ c N (normalizedRamanujanHorizonVector m N) -
      shellCorrection φ c m • normalizedRamanujanHorizonVector m N)
  simpa only [add_sub_cancel_right] using h

/-- The complete spectrum has a strictly positive horizon-independent floor at each fixed overlap. -/
theorem exists_tiltedUnitSpline_completeWeil_eigenvalue_floor {c : ℝ} (hc : 0 < c) :
    ∃ e : ℝ, 0 < e ∧ ∀ᶠ N : ℕ in atTop, ∀ i : PrimeHorizonIndex N,
      e ≤ completeWeilEigenvalue tiltedUnitSpline c N i := by
  obtain ⟨a, β, hβ, hres⟩ := exists_tiltedUnitSpline_completeWeilEnergy_reserve hc
  obtain ⟨e, he, hfloor⟩ := exists_tiltedUnitSpline_conductor_floor hc
  refine ⟨e / 2, half_pos he, ?_⟩
  exact eventually_completeWeil_eigenvalues_ge_of_reserve_quasimodes hβ hres
    (fun m hm => tendsto_completeWeilMatrix_completedConductor_residual_norm
      contDiff_tiltedUnitSpline tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm)
    hfloor (half_lt_self he)

/-- The literal complete Weil form is eventually nonnegative on every atomic test
at each fixed positive overlap, for the explicit tilted unit spline. -/
theorem eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg {c : ℝ} (hc : 0 < c) :
    ∀ᶠ N : ℕ in atTop, ∀ y : ℕ → ℝ,
      0 ≤ weilQuad (atomicTest N y (atomDilate tiltedUnitSpline (c / N))) := by
  filter_upwards [eventually_tiltedUnitSpline_completeWeilMatrix_posDef hc,
    eventually_ge_atTop 1] with N hpos hN y
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw : 0 < c / N := div_pos hc hN0
  have hM : 0 < ∫ u, atomDilate tiltedUnitSpline (c / N) u ^ 2 := by
    rw [integral_atomDilate_sq hw]
    exact mul_pos hw integral_tiltedUnitSpline_sq_pos
  have hA := completeWeilMatrix_isHermitian tiltedUnitSpline c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp hpos
  have hquad : 0 ≤ ⟪Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (horizonProfileVector y N), horizonProfileVector y N⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN] at hquad
  have htest : atomicTest N (primeHorizonExtension (horizonProfileVector y N))
      (atomDilate tiltedUnitSpline (c / N)) =
      atomicTest N y (atomDilate tiltedUnitSpline (c / N)) := by
    funext u
    unfold atomicTest
    apply sum_congr rfl
    intro n hn
    have hcoe : primeHorizonExtension (horizonProfileVector y N) n = y n :=
      primeHorizonExtension_coe (horizonProfileVector y N) ⟨n, hn⟩
    rw [hcoe]
  rw [htest, div_nonneg_iff] at hquad
  rcases hquad with ⟨hq, -⟩ | ⟨-, hneg⟩
  · exact hq
  · linarith only [hM, hneg]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.tendsto_completeWeilMatrix_completedConductor_residual_norm
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_tiltedUnitSpline_completeWeil_eigenvalue_floor

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.eventually_tiltedUnitSpline_weilQuad_atomicTest_nonneg
