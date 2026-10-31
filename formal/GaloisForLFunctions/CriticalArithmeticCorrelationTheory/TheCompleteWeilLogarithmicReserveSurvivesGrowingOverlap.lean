import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.ShiftingThePrimeEnergyGivesALogarithmicDefectReserve
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.CompleteConductorResidualsAreUniformOnLogarithmicFamilies
import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixIsPositiveAtIteratedLogarithmicOverlap
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.BoundedPrimeDefectHasAnExponentialConductorCutoff

/-!
# The logarithmic complete Weil reserve at growing overlap

Subtracting a fixed fraction of renormalized prime energy preserves
exponential conductor confinement. A scalar logarithmic correction leaves
a positive conductor floor, and the common residual rate transfers this
floor to the full shifted matrix. The reverse prime-row comparison gives
an all-vector defect reserve throughout subcritical iterated-logarithmic
overlap, with absolute constants.
-/

noncomputable section
open MeasureTheory Finset Filter Topology
open scoped RealInnerProductSpace Matrix
namespace GaloisForLFunctions.CriticalArithmeticCorrelationTheory
open RenormalizedArithmeticPotentialTheory SpacingScaleHarmonicAnalysis
  RenormalizedArithmeticPotentialTheory.CompletedShell ArithmeticElectrostatics

private theorem uniform_identity_action {N : ℕ} (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

/-- Shifting the prime energy and its scalar conductor loss leaves a positive conductor floor. -/
def logarithmicReserveMatrix (a c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  shiftedCompleteWeilMatrix tiltedUnitSpline c (a / c ^ 7) N +
    ((a / c ^ 7) * (conductorLogarithmicLoss tiltedUnitSpline c + 1)) • 1

theorem logarithmicReserveMatrix_isHermitian (a c : ℝ) (N : ℕ) :
    (logarithmicReserveMatrix a c N).IsHermitian :=
  (shiftedCompleteWeilMatrix_isHermitian tiltedUnitSpline c (a / c ^ 7) N).add
    (Matrix.isHermitian_one.smul (by rfl))

theorem logarithmicReserveMatrix_inner (a c : ℝ) {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (logarithmicReserveMatrix a c N) x, x⟫ =
      completeWeilEnergy tiltedUnitSpline c N x - (a / c ^ 7) * renormalizedPrimeEnergy N x +
        (a / c ^ 7) * (conductorLogarithmicLoss tiltedUnitSpline c + 1) * ‖x‖ ^ 2 := by
  simp only [logarithmicReserveMatrix, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, uniform_identity_action, inner_add_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, shiftedCompleteWeilMatrix_inner]

private theorem conductorLogarithmicLoss_nonneg_at_overlap {c : ℝ} (hc : 1 ≤ c) :
    0 ≤ conductorLogarithmicLoss tiltedUnitSpline c := by
  have h8 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
  have h2c := Real.log_nonneg (show 1 ≤ 2 * c by linarith only [hc])
  unfold conductorLogarithmicLoss
  positivity

/-- The scalar shift leaves every conductor energy at least `a/c⁷`. -/
theorem logarithmicReserve_conductor_floor {a c : ℝ} (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (hc : 1 ≤ c) {m : ℕ} (hm : 0 < m) :
    a / c ^ 7 ≤ completedConductorEnergy tiltedUnitSpline c m -
      (a / c ^ 7) * ramanujanAdjunctionEnergy m +
      (a / c ^ 7) * (conductorLogarithmicLoss tiltedUnitSpline c + 1) := by
  have hc0 := zero_lt_one.trans_le hc
  have hδ0 : 0 ≤ a / c ^ 7 := div_nonneg ha (pow_nonneg hc0.le 7)
  have hδ1 : a / c ^ 7 ≤ 1 :=
    (div_le_one (pow_pos hc0 7)).mpr (ha1.trans (one_le_pow₀ hc))
  have hfloor := completedConductorEnergy_ge_logarithmic_reserve contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero integral_tiltedUnitSpline_sq_pos hc hm hδ0 hδ1
  nlinarith only [hfloor]

private theorem exists_completeWeil_matrix_polynomial_reserve :
    ∃ b B H : ℝ, 0 < b ∧ 0 < B ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          b / c ^ 7 * poleDefect N (primeHorizonExtension x) - B * c ^ 9 * ‖x‖ ^ 2 ≤
            completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨b, B, H, hb, hB, hH, hr⟩ := exists_tiltedUnitSpline_complete_defect_reserve_polynomial
  refine ⟨b, B, H, hb, hB, hH, ?_⟩
  intro c hc N hN x
  have hc0 := zero_lt_one.trans_le hc
  have hN0 : (0 : ℝ) < N := (mul_pos hH (pow_pos hc0 8)).trans_le hN
  have hN1 : 1 ≤ N := by exact_mod_cast (show 0 < N by exact_mod_cast hN0)
  have hh := hr c hc N hN (primeHorizonExtension x)
  rw [sum_primeHorizonExtension_sq] at hh
  rw [completeWeilEnergy, completeWeilMatrix_inner_eq_weilQuad contDiff_tiltedUnitSpline
    tiltedUnitSpline_eq_zero hc0 hN1, integral_atomDilate_sq (div_pos hc0 hN0)]
  exact hh

/-- The half-reserve shift keeps exponential confinement with constants independent of overlap. -/
theorem exists_logarithmicReserve_negative_conductor_cutoff :
    ∃ a C D H : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ 0 < C ∧ 0 < D ∧ 0 < H ∧
      ∀ c : ℝ, 1 ≤ c → ∃ R : ℕ,
        (R : ℝ) ≤ Real.exp (D * (C * c ^ 16 + 1)) ∧
        ∀ N : ℕ, H * c ^ 8 ≤ (N : ℝ) →
          ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N), ‖x‖ = 1 →
            ⟪Matrix.toEuclideanLin (logarithmicReserveMatrix a c N) x, x⟫ ≤ 0 →
            ∃ b : ℕ → ℝ, (∑ n ∈ Icc 1 N,
              (primeHorizonExtension x n -
                ∑ m ∈ Icc 1 R, b m * ramanujanPoleProfile m n) ^ 2) ≤ 1 / 4 := by
  obtain ⟨b, B, H, hb, hB, hH, hreserve⟩ := exists_completeWeil_matrix_polynomial_reserve
  obtain ⟨D, hD, happrox⟩ := exists_exponential_conductor_cutoff_of_poleDefect_le
    (by norm_num : (0 : ℝ) < 1 / 4)
  let a := min (b / 2) (1 / 2)
  let J := Real.log 8 + 4
  let C := B / a + J
  have ha : 0 < a := lt_min (half_pos hb) (by norm_num)
  have haHalf : a ≤ 1 / 2 := min_le_right _ _
  have hab : 2 * a ≤ b := by
    have hh : a ≤ b / 2 := min_le_left _ _
    linarith only [hh]
  have hJ : 0 ≤ J := by
    have hh := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)
    dsimp only [J]
    positivity
  have hC : 0 < C := add_pos_of_pos_of_nonneg (div_pos hB ha) hJ
  refine ⟨a, C, D, H, ha, haHalf, hC, hD, hH, ?_⟩
  intro c hc
  have hc0 := zero_lt_one.trans_le hc
  obtain ⟨R, hR, happ⟩ := happrox (C * c ^ 16) (by positivity)
  refine ⟨R, hR, ?_⟩
  intro N hN x hx hneg
  have hr := hreserve c hc N hN x
  have hp := primeEnergy_le_poleDefect_add_row_cost x
  rw [logarithmicReserveMatrix_inner, hx, one_pow, mul_one] at hneg
  rw [hx, one_pow, mul_one] at hr hp
  have hL := conductorLogarithmicLoss_nonneg_at_overlap hc
  have hd : 0 ≤ poleDefect N (primeHorizonExtension x) := poleDefect_nonneg _ _
  have hδ : 0 < a / c ^ 7 := div_pos ha (pow_pos hc0 _)
  have hβ : 2 * (a / c ^ 7) ≤ b / c ^ 7 := by
    have hh := div_le_div_of_nonneg_right hab (pow_nonneg hc0.le 7)
    exact (by simpa only [mul_div_assoc] using hh)
  have hrow := mul_le_mul_of_nonneg_left hp hδ.le
  have hshift := mul_nonneg hδ.le (show 0 ≤ conductorLogarithmicLoss tiltedUnitSpline c + 1 by positivity)
  have hretain := mul_le_mul_of_nonneg_right hβ hd
  have hdef : (a / c ^ 7) * poleDefect N (primeHorizonExtension x) ≤
      B * c ^ 9 + (a / c ^ 7) * J := by
    dsimp only [J]
    nlinarith only [hr, hneg, hrow, hshift, hretain]
  have hscaled := mul_le_mul_of_nonneg_right hdef (pow_nonneg hc0.le 7)
  have heLeft : ((a / c ^ 7) * poleDefect N (primeHorizonExtension x)) * c ^ 7 =
      a * poleDefect N (primeHorizonExtension x) := by field_simp [hc0.ne']
  have heRight : (B * c ^ 9 + (a / c ^ 7) * J) * c ^ 7 = B * c ^ 16 + a * J := by
    field_simp [hc0.ne']
  rw [heLeft, heRight] at hscaled
  have hJpow := mul_le_mul_of_nonneg_left (one_le_pow₀ hc : 1 ≤ c ^ 16)
    (mul_nonneg ha.le hJ)
  have hfinal : poleDefect N (primeHorizonExtension x) ≤ C * c ^ 16 := by
    calc
      _ ≤ (B * c ^ 16 + a * J * c ^ 16) / a := by
        apply (le_div_iff₀ ha).mpr
        nlinarith only [hscaled, hJpow]
      _ = C * c ^ 16 := by
        dsimp only [C]
        field_simp [ha.ne']
  apply happ N (primeHorizonExtension x) _ hfinal
  rw [sum_primeHorizonExtension_sq, hx, one_pow]

/-- A bounded half-reserve shift retains the complete common-horizon residual rate. -/
theorem exists_logarithmicReserve_uniform_conductor_residual_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ A : ℝ, 0 ≤ A → ∀ᶠ N : ℕ in atTop,
      ∀ a : ℝ, 0 ≤ a → a ≤ 1 → ∀ m : ℕ, 0 < m →
      (m : ℝ) ≤ Real.log (N : ℝ) ^ A → ∀ c : ℝ, 1 ≤ c →
      4 * (Real.exp 1 + 3) ^ 2 * c ^ 2 ≤ (N : ℝ) →
        ‖Matrix.toEuclideanLin (logarithmicReserveMatrix a c N)
          (normalizedRamanujanHorizonVector m N) -
          (completedConductorEnergy tiltedUnitSpline c m - (a / c ^ 7) * ramanujanAdjunctionEnergy m +
            (a / c ^ 7) * (conductorLogarithmicLoss tiltedUnitSpline c + 1)) •
              normalizedRamanujanHorizonVector m N‖ ^ 2 ≤ K * (m : ℝ) ^ 4 *
          (c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
            c ^ 3 / Real.sqrt (Real.log N)) := by
  obtain ⟨Cw, hCw, hw⟩ := exists_tiltedUnitSpline_uniform_conductor_residual_bound
  obtain ⟨Cp, hCp, hp⟩ := exists_primeResidual_uniform_conductor_bound
  refine ⟨2 * (Cw + Cp), by positivity, ?_⟩
  intro A hA
  have hLlim : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hw A hA, hLlim.eventually_ge_atTop 1] with N hwN hL
  intro a ha ha1 m hm hmN c hc hlarge
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hc0 := zero_lt_one.trans_le hc
  have hL0 := zero_lt_one.trans_le hL
  let δ := a / c ^ 7
  let rate := c ^ 5 / Real.log N + c ^ 10 * (Real.log (N : ℝ) / N) ^ 2 +
    c ^ 3 / Real.sqrt (Real.log N)
  have hrate : 0 ≤ rate := by dsimp only [rate]; positivity
  have hδ0 : 0 ≤ δ := div_nonneg ha (pow_nonneg hc0.le 7)
  have hδ1 : δ ≤ 1 := by
    apply (div_le_one (pow_pos hc0 7)).mpr
    exact ha1.trans (one_le_pow₀ hc)
  have hδ2 : δ ^ 2 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hδ0 hδ1 2
  have hprime : ‖Matrix.toEuclideanLin (fullPrimeMatrix N)
      (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N‖ ^ 2 ≤
      Cp * (m : ℝ) ^ 4 * rate := by
    have hm34 := pow_le_pow_right₀ hm1 (by norm_num : 3 ≤ 4)
    have hc5 : 1 ≤ c ^ 5 := one_le_pow₀ hc
    have hnum : Cp * (m : ℝ) ^ 3 ≤ Cp * (m : ℝ) ^ 4 * c ^ 5 := by
      exact (mul_le_mul_of_nonneg_left hm34 hCp.le).trans
        (by simpa only [mul_one] using
          (mul_le_mul_of_nonneg_left hc5 (show 0 ≤ Cp * (m : ℝ) ^ 4 by positivity)))
    calc
      _ ≤ Cp * (m : ℝ) ^ 3 / Real.log N := hp m hm N
      _ ≤ (Cp * (m : ℝ) ^ 4 * c ^ 5) / Real.log N :=
        div_le_div_of_nonneg_right hnum hL0.le
      _ = Cp * (m : ℝ) ^ 4 * (c ^ 5 / Real.log N) := by ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        dsimp only [rate]
        exact (le_add_of_nonneg_right (by positivity : 0 ≤ c ^ 10 * (Real.log (N : ℝ) / N) ^ 2)).trans
          (le_add_of_nonneg_right (by positivity))
  have hscaled : ‖δ • (Matrix.toEuclideanLin (fullPrimeMatrix N)
      (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)‖ ^ 2 ≤
      Cp * (m : ℝ) ^ 4 * rate := by
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    simpa only [one_mul] using mul_le_mul hδ2 hprime (sq_nonneg _) zero_le_one
  have heq : Matrix.toEuclideanLin (logarithmicReserveMatrix a c N)
      (normalizedRamanujanHorizonVector m N) -
      (completedConductorEnergy tiltedUnitSpline c m - δ * ramanujanAdjunctionEnergy m +
        δ * (conductorLogarithmicLoss tiltedUnitSpline c + 1)) •
          normalizedRamanujanHorizonVector m N =
      (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
        (normalizedRamanujanHorizonVector m N) -
        completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N) +
      δ • (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
        (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N) := by
    simp only [logarithmicReserveMatrix, shiftedCompleteWeilMatrix, map_add, map_sub,
      map_smul, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      uniform_identity_action]
    dsimp only [δ]
    module
  rw [heq]
  have htriangle := norm_add_le
    (Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N)
    (δ • (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N))
  have hsq := pow_le_pow_left₀ (norm_nonneg _) htriangle 2
  have hdiff := sq_nonneg
    (‖Matrix.toEuclideanLin (completeWeilMatrix tiltedUnitSpline c N)
      (normalizedRamanujanHorizonVector m N) -
      completedConductorEnergy tiltedUnitSpline c m • normalizedRamanujanHorizonVector m N‖ -
    ‖δ • (Matrix.toEuclideanLin (fullPrimeMatrix N) (normalizedRamanujanHorizonVector m N) -
      (Real.log N - ramanujanAdjunctionEnergy m) • normalizedRamanujanHorizonVector m N)‖)
  have hfull := hwN m hm hmN c hc hlarge
  change _ ≤ Cw * (m : ℝ) ^ 4 * rate at hfull
  change _ ≤ (2 * (Cw + Cp)) * (m : ℝ) ^ 4 * rate
  nlinarith only [hsq, hdiff, hfull, hscaled]

/-- One absolute half-reserve coefficient gives positive shifted matrices on every
subcritical iterated-logarithmic overlap range. -/
theorem exists_logarithmicReserveMatrix_posDef_iteratedLog :
    ∃ a : ℝ, 0 < a ∧ a ≤ 1 / 2 ∧ ∀ α : ℝ, 0 < α → α < 1 / 16 →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
        c ≤ Real.log (Real.log (N : ℝ)) ^ α → (logarithmicReserveMatrix a c N).PosDef := by
  obtain ⟨a, C, D, H, ha, haHalf, hC, hD, hH, hcut⟩ :=
    exists_logarithmicReserve_negative_conductor_cutoff
  obtain ⟨K, hK, hres⟩ := exists_logarithmicReserve_uniform_conductor_residual_bound
  have ha1 : a ≤ 1 := haHalf.trans (by norm_num)
  refine ⟨a, ha, haHalf, fun α hα hα16 => ?_⟩
  exact eventually_matrix_posDef_iteratedLog_of_conductor_bounds
    (logarithmicReserveMatrix a)
    (fun c m => completedConductorEnergy tiltedUnitSpline c m - (a / c ^ 7) * ramanujanAdjunctionEnergy m +
      (a / c ^ 7) * (conductorLogarithmicLoss tiltedUnitSpline c + 1))
    (logarithmicReserveMatrix_isHermitian a) ha
    (fun c hc m hm => logarithmicReserve_conductor_floor ha.le ha1 hc hm)
    ⟨C, D, H, hC, hD, hH, hcut⟩
    ⟨K, hK, fun A hA => (hres A hA).mono fun N hN m hm hmN c hc hlarge =>
      hN a ha.le ha1 m hm hmN c hc hlarge⟩ hα hα16

/-- The actual complete Weil form retains `a/c⁷` of prime defect with only
logarithmic mass loss, uniformly at prescribed growing overlap. -/
theorem exists_completeWeil_logarithmic_defect_reserve_iteratedLog :
    ∃ a C : ℝ, 0 < a ∧ 0 < C ∧ ∀ α : ℝ, 0 < α → α < 1 / 16 →
      ∀ᶠ N : ℕ in atTop, ∀ c : ℝ, 1 ≤ c →
        c ≤ Real.log (Real.log (N : ℝ)) ^ α →
        ∀ x : EuclideanSpace ℝ (PrimeHorizonIndex N),
          a / c ^ 7 * (poleDefect N (primeHorizonExtension x) -
            C * Real.log (2 * c) * ‖x‖ ^ 2) ≤ completeWeilEnergy tiltedUnitSpline c N x := by
  obtain ⟨a, ha, _, hpos⟩ := exists_logarithmicReserveMatrix_posDef_iteratedLog
  let B := |Real.eulerMascheroniConstant| +
    |completeWeilSelfFinitePart tiltedUnitSpline 1 - Real.eulerMascheroniConstant| +
      2 * Real.log 8 + Real.log 4 + 6
  let C := 16 + B / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlog8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨a, C, ha, hC, ?_⟩
  intro α hα hα16
  filter_upwards [hpos α hα hα16] with N hposN
  intro c hc hcup x
  have hc0 := zero_lt_one.trans_le hc
  have hδ : 0 < a / c ^ 7 := div_pos ha (pow_pos hc0 7)
  have hlog : Real.log 2 ≤ Real.log (2 * c) :=
    Real.log_le_log (by norm_num) (by linarith only [hc])
  have hcost : conductorLogarithmicLoss tiltedUnitSpline c + Real.log 4 + 5 ≤
      C * Real.log (2 * c) := by
    have hh := mul_le_mul_of_nonneg_left hlog (div_nonneg hB hlog2.le)
    rw [div_mul_cancel₀ B hlog2.ne'] at hh
    dsimp only [C]
    unfold conductorLogarithmicLoss
    dsimp only [B] at hh
    linarith only [hh]
  have hA := logarithmicReserveMatrix_isHermitian a c N
  have heig := hA.posDef_iff_eigenvalues_pos.mp (hposN c hc hcup)
  have henergy : 0 ≤ ⟪Matrix.toEuclideanLin (logarithmicReserveMatrix a c N) x, x⟫ := by
    rw [HTGeometry.hermitianEnergy_eq_sum hA]
    exact sum_nonneg fun i _ => mul_nonneg (heig i).le (sq_nonneg _)
  rw [logarithmicReserveMatrix_inner] at henergy
  have hdef := mul_le_mul_of_nonneg_left (poleDefect_le_primeEnergy_add_row_cost x) hδ.le
  have hpay := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_right hcost (sq_nonneg ‖x‖)) hδ.le
  nlinarith only [henergy, hdef, hpay]

end GaloisForLFunctions.CriticalArithmeticCorrelationTheory

#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicReserve_negative_conductor_cutoff
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicReserve_uniform_conductor_residual_bound
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.logarithmicReserve_conductor_floor
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_logarithmicReserveMatrix_posDef_iteratedLog
#print axioms GaloisForLFunctions.CriticalArithmeticCorrelationTheory.exists_completeWeil_logarithmic_defect_reserve_iteratedLog
