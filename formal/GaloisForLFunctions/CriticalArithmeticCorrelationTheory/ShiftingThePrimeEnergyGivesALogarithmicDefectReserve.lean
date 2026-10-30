import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.FiniteRamanujanCoordinatesTransferSpectralFloors
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.MacroscopicOverlapPositivityAtEveryOverlap
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilReserveHasPolynomialOverlapCost
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PrimeDefectConfinementMustRetainLowEnergyConductors
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheConductorEnergyKeepsALogarithmicReserve

/-!
# A logarithmic mass loss in the complete Weil defect reserve

Subtracting half the available prime-energy reserve preserves finite conductor confinement.
The shifted matrix has the same norm quasimodes, with the adjunction energy subtracted from
each completed conductor energy. Their logarithmic lower bound therefore transfers to every
coefficient vector. The horizon is allowed to depend on the fixed overlap.
-/

noncomputable section
open MeasureTheory Filter Topology Finset
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticEffectivityTheory

/-- The complete Weil operator minus a fixed fraction of renormalized prime energy. -/
def shiftedCompleteWeilMatrix (φ : ℝ → ℝ) (c δ : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  completeWeilMatrix φ c N - δ • (Real.log N • 1 - fullPrimeMatrix N)

theorem shiftedCompleteWeilMatrix_isHermitian (φ : ℝ → ℝ) (c δ : ℝ) (N : ℕ) :
    (shiftedCompleteWeilMatrix φ c δ N).IsHermitian := by
  exact (completeWeilMatrix_isHermitian φ c N).sub
    (((Matrix.isHermitian_one.smul (by rfl : IsSelfAdjoint (Real.log N))).sub
      (fullPrimeMatrix_isHermitian N)).smul (by rfl : IsSelfAdjoint δ))

private theorem identity_action {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

private theorem shiftedCompleteWeilMatrix_action (φ : ℝ → ℝ) (c δ : ℝ) {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (shiftedCompleteWeilMatrix φ c δ N) x =
      Matrix.toEuclideanLin (completeWeilMatrix φ c N) x -
        δ • (Real.log N • x - Matrix.toEuclideanLin (fullPrimeMatrix N) x) := by
  simp only [shiftedCompleteWeilMatrix, map_sub, map_smul, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_action]

theorem shiftedCompleteWeilMatrix_inner (φ : ℝ → ℝ) (c δ : ℝ) {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (shiftedCompleteWeilMatrix φ c δ N) x, x⟫ =
      completeWeilEnergy φ c N x - δ * renormalizedPrimeEnergy N x := by
  rw [shiftedCompleteWeilMatrix_action]
  simp only [inner_sub_left, real_inner_smul_left, real_inner_self_eq_norm_sq,
    completeWeilEnergy, renormalizedPrimeEnergy]

/-- The lower row bound is the reverse comparison between defect and prime energy. -/
theorem primeEnergy_le_poleDefect_add_row_cost {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    renormalizedPrimeEnergy N x ≤
      poleDefect N (primeHorizonExtension x) + (Real.log 8 + 4) * ‖x‖ ^ 2 := by
  have hrow : (Real.log N - (Real.log 8 + 4)) *
        (∑ n ∈ Icc 1 N, primeHorizonExtension x n ^ 2) ≤
      atomicWeilForm N (primeHorizonExtension x) + poleDefect N (primeHorizonExtension x) := by
    rw [atomicWeilForm_add_poleDefect, mul_sum]
    apply sum_le_sum
    intro n hn
    have h := row_ge (mem_Icc.mp hn).1 (mem_Icc.mp hn).2
    exact mul_le_mul_of_nonneg_right (by linarith only [h]) (sq_nonneg _)
  rw [sum_primeHorizonExtension_sq, atomicWeilForm_primeHorizonExtension] at hrow
  unfold renormalizedPrimeEnergy
  linarith only [hrow]

/-- The two actual operators have common conductor norm quasimodes; no commutation is needed. -/
theorem tendsto_shiftedCompleteWeilMatrix_quasimode_norm {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) (δ : ℝ) {m : ℕ} (hm : 0 < m) :
    Tendsto (fun N : ℕ =>
      ‖Matrix.toEuclideanLin (shiftedCompleteWeilMatrix φ c δ N)
          (normalizedRamanujanHorizonVector m N) -
        (completedConductorEnergy φ c m - δ * ramanujanAdjunctionEnergy m) •
          normalizedRamanujanHorizonVector m N‖) atTop (𝓝 0) := by
  have hw := tendsto_completeWeilMatrix_ramanujan_quasimode_norm hφ hsupp hM hc hm
  have hp := tendsto_normalizedRamanujanHorizonVector_residual_norm hm
  have heq (N : ℕ) :
      Matrix.toEuclideanLin (shiftedCompleteWeilMatrix φ c δ N)
          (normalizedRamanujanHorizonVector m N) -
        (completedConductorEnergy φ c m - δ * ramanujanAdjunctionEnergy m) •
          normalizedRamanujanHorizonVector m N =
      (Matrix.toEuclideanLin (completeWeilMatrix φ c N) (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy φ c m • normalizedRamanujanHorizonVector m N) +
      δ • (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) := by
    rw [shiftedCompleteWeilMatrix_action]
    module
  refine squeeze_zero (fun N => norm_nonneg _) (fun N => ?_)
    (by simpa only [mul_zero, add_zero] using hw.add (hp.const_mul |δ|))
  rw [heq]
  exact (norm_add_le _ _).trans_eq (by rw [norm_smul, Real.norm_eq_abs])

/-- Shifting half a defect reserve transfers the conductor energy comparison to all vectors. -/
theorem eventually_completeWeilEnergy_ge_half_reserve_primeEnergy {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc : 0 < c) {a β L : ℝ} (hβ : 0 < β)
    (hres : ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      a * ‖x‖ ^ 2 + β * poleDefect N (primeHorizonExtension x) ≤ completeWeilEnergy φ c N x)
    (hscalar : ∀ m : ℕ, 0 < m → β / 2 * (ramanujanAdjunctionEnergy m - L) ≤
      completedConductorEnergy φ c m) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      β / 2 * (renormalizedPrimeEnergy N x - (L + 1) * ‖x‖ ^ 2) ≤
        completeWeilEnergy φ c N x := by
  let b := -(β / 2) * (L + 1)
  have hfloor : ∀ m : ℕ, 0 < m → -(β / 2) * L ≤
      completedConductorEnergy φ c m - β / 2 * ramanujanAdjunctionEnergy m := by
    intro m hm
    linarith only [hscalar m hm]
  have hb : b < -(β / 2) * L := by dsimp only [b]; linarith only [hβ]
  obtain ⟨S, hS, hcert⟩ := exists_finite_ramanujan_coordinate_certificate_of_reserve hβ hres
    (2 * b - a + β * (Real.log 8 + 4))
  have hcapture : ∃ S : Finset ℕ, (∀ m ∈ S, 0 < m) ∧
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        ‖x‖ = 1 → ⟪Matrix.toEuclideanLin (shiftedCompleteWeilMatrix φ c (β / 2) N) x, x⟫ ≤ b →
          1 / 18 ≤ ∑ m ∈ S, ⟪x, normalizedRamanujanHorizonVector m N⟫ ^ 2 := by
    refine ⟨S, hS, ?_⟩
    filter_upwards [hcert, hres] with N hcN hrN
    intro x hx hAx
    apply hcN x hx
    rw [shiftedCompleteWeilMatrix_inner] at hAx
    have hr := hrN x
    have hp := mul_le_mul_of_nonneg_left (primeEnergy_le_poleDefect_add_row_cost x) hβ.le
    rw [hx, one_pow, mul_one] at hr hp
    nlinarith only [hr, hp, hAx]
  have h := eventually_matrix_energy_ge_of_ramanujan_certificates
    (shiftedCompleteWeilMatrix_isHermitian φ c (β / 2))
    (fun _ hm => tendsto_shiftedCompleteWeilMatrix_quasimode_norm hφ hsupp hM hc (β / 2) hm)
    hfloor hb hcapture
  filter_upwards [h] with N hN
  intro x
  have hx := hN x
  rw [shiftedCompleteWeilMatrix_inner] at hx
  dsimp only [b] at hx
  linarith only [hx]

private theorem tiltedSpline_matrix_polynomial_reserve {c : ℝ} (hc1 : 1 ≤ c) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      -growingCompleteReserveCost c * ‖x‖ ^ 2 +
        (growingDefectFraction c / 4) * poleDefect N (primeHorizonExtension x) ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  filter_upwards [eventually_ge_atTop (growingDefectCutoff c), eventually_ge_atTop 1]
    with N hcut hN
  intro x
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have h := tiltedUnitSpline_complete_defect_reserve_explicit hc1 hcut (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at h
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc hN, integral_atomDilate_sq (div_pos hc hNR)]
  linarith only [h]

/-- The complete form retains an explicit fraction of the defect with logarithmic mass loss.
All vectors share one horizon at each fixed overlap. -/
theorem eventually_tiltedSpline_completeWeilEnergy_ge_logarithmic_defect {c : ℝ} (hc1 : 1 ≤ c) :
    ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
      growingDefectFraction c / 8 * (poleDefect N (primeHorizonExtension x) -
        (conductorLogarithmicLoss tiltedUnitSpline c + Real.log 4 + 5) * ‖x‖ ^ 2) ≤
          completeWeilEnergy tiltedUnitSpline c N x := by
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hβ := div_pos (growingDefectFraction_pos hc) (show (0 : ℝ) < 4 by norm_num)
  have hδ : 0 < growingDefectFraction c / 8 :=
    div_pos (growingDefectFraction_pos hc) (by norm_num)
  have hδ1 : growingDefectFraction c / 8 ≤ 1 := by
    have hpow : 1 ≤ c ^ 7 := one_le_pow₀ hc1
    have hm : 0 ≤ min growingMassConstant (1 / 2) :=
      le_min growingMassConstant_pos.le (by norm_num)
    have hg := (div_le_self hm hpow).trans (min_le_right growingMassConstant (1 / 2))
    change growingDefectFraction c ≤ 1 / 2 at hg
    linarith only [hg]
  have hscalar : ∀ m : ℕ, 0 < m → (growingDefectFraction c / 4) / 2 *
      (ramanujanAdjunctionEnergy m - conductorLogarithmicLoss tiltedUnitSpline c) ≤
        completedConductorEnergy tiltedUnitSpline c m := by
    intro m hm
    have h := completedConductorEnergy_ge_logarithmic_reserve contDiff_tiltedUnitSpline
      tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc1 hm hδ.le hδ1
    convert h using 1 <;> ring
  have h := eventually_completeWeilEnergy_ge_half_reserve_primeEnergy contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hβ
    (tiltedSpline_matrix_polynomial_reserve hc1) hscalar
  filter_upwards [h] with N hN
  intro x
  have hx := hN x
  have hd := mul_le_mul_of_nonneg_left (poleDefect_le_primeEnergy_add_row_cost x) hδ.le
  nlinarith only [hx, hd]

/-- Absolute constants give the complete all-vector reserve with `c⁻⁷` defect coefficient
and `log(2c)` mass loss. The eventual horizon may depend on `c`. -/
theorem exists_completeWeil_logarithmic_defect_reserve :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 < C ∧ ∀ c : ℝ, 1 ≤ c →
      ∀ᶠ N : ℕ in atTop, ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
        a / c ^ 7 * (poleDefect N (primeHorizonExtension x) -
          C * Real.log (2 * c) * ‖x‖ ^ 2) ≤ completeWeilEnergy tiltedUnitSpline c N x := by
  let a := min growingMassConstant (1 / 2) / 8
  let K := |Real.eulerMascheroniConstant| +
    |completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant| +
      2 * Real.log 8 + Real.log 4 + 6
  let C := 16 + K / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have ha : 0 < a := div_pos (lt_min growingMassConstant_pos (by norm_num)) (by norm_num)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨a, ha, C, hC, fun c hc1 => ?_⟩
  have hc : 0 < c := zero_lt_one.trans_le hc1
  have hlog : Real.log 2 ≤ Real.log (2 * c) :=
    Real.log_le_log (by norm_num) (by linarith only [hc1])
  have hcost : conductorLogarithmicLoss tiltedUnitSpline c + Real.log 4 + 5 ≤
      C * Real.log (2 * c) := by
    have h := mul_le_mul_of_nonneg_left hlog (div_nonneg hK hlog2.le)
    rw [div_mul_cancel₀ K hlog2.ne'] at h
    dsimp only [C]
    unfold conductorLogarithmicLoss
    dsimp only [K] at h
    linarith only [h]
  have heq : a / c ^ 7 = growingDefectFraction c / 8 := by
    dsimp only [a, growingDefectFraction]
    ring
  filter_upwards [eventually_tiltedSpline_completeWeilEnergy_ge_logarithmic_defect hc1]
    with N hN
  intro x
  rw [heq]
  apply le_trans ?_ (hN x)
  apply mul_le_mul_of_nonneg_left ?_ (div_nonneg (growingDefectFraction_pos hc).le (by norm_num))
  have h := mul_le_mul_of_nonneg_right hcost (sq_nonneg ‖x‖)
  linarith only [h]

#print axioms eventually_tiltedSpline_completeWeilEnergy_ge_logarithmic_defect
#print axioms exists_completeWeil_logarithmic_defect_reserve

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory
