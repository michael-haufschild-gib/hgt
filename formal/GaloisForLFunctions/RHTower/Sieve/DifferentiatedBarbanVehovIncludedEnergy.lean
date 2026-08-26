import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedError
import GaloisForLFunctions.RHTower.Sieve.DifferentiatedBarbanVehovIncludedOriginalForms

/-!
# Included detector-head energy

Packages the three cancellation-preserving included moments into one normalized detector energy.
The existing pointwise-to-moment estimates then give a single quantitative approximation by the
included polynomial main term.
-/

namespace RHTower.Sieve

noncomputable section

/-- Exact lcm-side quadratic energy of the included long detector head. -/
def barbanVehovIncludedLongEnergyLcm (lam : ℝ) (L M : ℕ) : ℝ :=
  (barbanVehovIncludedLongBaseLcm L M +
      2 * lam * barbanVehovIncludedLongCrossLcm L M +
      lam ^ 2 * barbanVehovIncludedLongDerivativeLcm L M) /
    Real.log M ^ 2

/-- Continuous quadratic energy of the included long detector head. -/
def barbanVehovIncludedLongEnergyContinuous (lam : ℝ) (L M : ℕ) : ℝ :=
  (barbanVehovIncludedLongBaseContinuous L M +
      2 * lam * barbanVehovIncludedLongCrossContinuous L M +
      lam ^ 2 * barbanVehovIncludedLongDerivativeContinuous L M) /
    Real.log M ^ 2

/-- Polynomial quadratic energy at logarithmic detector scale `ell`. -/
def barbanVehovIncludedLongEnergyPolynomialMain
    (lam ell : ℝ) (M : ℕ) : ℝ :=
  (barbanVehovIncludedLongBasePolynomialMain M +
      2 * lam * barbanVehovIncludedLongCrossPolynomialMain ell M +
      lam ^ 2 * barbanVehovIncludedLongDerivativePolynomialMain ell M) /
    Real.log M ^ 2

private theorem abs_quadraticCombination_sub_le
    (lam A B C a b c : ℝ) :
    |(A + 2 * lam * B + lam ^ 2 * C) -
        (a + 2 * lam * b + lam ^ 2 * c)| ≤
      |A - a| + 2 * |lam| * |B - b| + lam ^ 2 * |C - c| := by
  rw [show
    (A + 2 * lam * B + lam ^ 2 * C) -
        (a + 2 * lam * b + lam ^ 2 * c) =
      (A - a) + 2 * lam * (B - b) + lam ^ 2 * (C - c) by ring]
  calc
    |(A - a) + 2 * lam * (B - b) + lam ^ 2 * (C - c)| ≤
        |A - a| + |2 * lam * (B - b)| + |lam ^ 2 * (C - c)| := by
      exact (abs_add_le ((A - a) + 2 * lam * (B - b))
        (lam ^ 2 * (C - c))).trans
          (add_le_add (abs_add_le (A - a) (2 * lam * (B - b))) le_rfl)
    _ = _ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_pow, sq_abs]

/-- The exact long detector energy is its included lcm quadratic form. -/
theorem levinsonCriticalDetectorLongEnergy_eq_includedLcm
    (lam : ℝ) (L : ℕ) {M : ℕ} (hM : 1 < M) (hML : M ≤ L) :
    levinsonCriticalDetectorLongEnergy lam L M =
      barbanVehovIncludedLongEnergyLcm lam L M := by
  rw [RHTower.levinsonCriticalDetectorLongEnergy_eq_includedMomentQuadratic
    lam L hM]
  rw [barbanVehovIncludedLongEnergyLcm,
    levinsonCriticalDetectorIncludedLongBaseMoment_eq_lcm hM hML,
    levinsonCriticalDetectorIncludedLongCrossMoment_eq_lcm hM hML,
    levinsonCriticalDetectorIncludedLongDerivativeMoment_eq_lcm hM hML]

/-- Continuous included energy is exactly its polynomial main term. -/
theorem barbanVehovIncludedLongEnergyContinuous_eq_polynomialMain
    (lam : ℝ) {L M : ℕ} (hL : 0 < L) :
    barbanVehovIncludedLongEnergyContinuous lam L M =
      barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M := by
  rw [barbanVehovIncludedLongEnergyContinuous,
    barbanVehovIncludedLongEnergyPolynomialMain,
    barbanVehovIncludedLongBaseContinuous_eq_polynomialMain hL,
    barbanVehovIncludedLongCrossContinuous_eq_polynomialMain hL,
    barbanVehovIncludedLongDerivativeContinuous_eq_polynomialMain hL]

/-- Quantitative included lcm-energy approximation by its polynomial main term. -/
theorem abs_barbanVehovIncludedLongEnergyLcm_sub_polynomialMain_le
    (lam : ℝ) {L M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ 2 ≤ L) :
    |barbanVehovIncludedLongEnergyLcm lam L M -
        barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M| ≤
      (((M : ℝ) * Real.log M) ^ 2 * (3 / (L : ℝ)) +
          2 * |lam| * (((M : ℝ) * Real.log M) ^ 2 *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ))) +
          lam ^ 2 * (((M : ℝ) * Real.log M) ^ 2 *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)))) /
        Real.log M ^ 2 := by
  have hM1 : 1 ≤ M := by omega
  have hMpos : 0 < M := by omega
  have hleftpos : 0 < 8 * M ^ 2 := Nat.mul_pos (by norm_num) (pow_pos hMpos 2)
  have hL : 0 < L := hleftpos.trans_le hscale
  have hlog : 0 < Real.log M := Real.log_pos (by exact_mod_cast hM)
  have hquad := abs_quadraticCombination_sub_le lam
    (barbanVehovIncludedLongBaseLcm L M)
    (barbanVehovIncludedLongCrossLcm L M)
    (barbanVehovIncludedLongDerivativeLcm L M)
    (barbanVehovIncludedLongBaseContinuous L M)
    (barbanVehovIncludedLongCrossContinuous L M)
    (barbanVehovIncludedLongDerivativeContinuous L M)
  have hbase := abs_barbanVehovIncludedLongBaseLcm_sub_continuous_le hM1 hscale
  have hcross := abs_barbanVehovIncludedLongCrossLcm_sub_continuous_le hM1 hscale
  have hderiv := abs_barbanVehovIncludedLongDerivativeLcm_sub_continuous_le hM1 hscale
  rw [barbanVehovIncludedLongEnergyLcm,
    ← barbanVehovIncludedLongEnergyContinuous_eq_polynomialMain lam hL,
    barbanVehovIncludedLongEnergyContinuous]
  rw [← sub_div, abs_div, abs_of_pos (pow_pos hlog 2)]
  apply div_le_div_of_nonneg_right _ (pow_pos hlog 2).le
  exact hquad.trans (add_le_add (add_le_add hbase
    (mul_le_mul_of_nonneg_left hcross (by positivity)))
      (mul_le_mul_of_nonneg_left hderiv (sq_nonneg lam)))

/-- Quantitative approximation of the actual finite detector's long energy. -/
theorem abs_levinsonCriticalDetectorLongEnergy_sub_includedPolynomialMain_le
    (lam : ℝ) {L M : ℕ} (hM : 1 < M) (hscale : 8 * M ^ 2 ≤ L) :
    |levinsonCriticalDetectorLongEnergy lam L M -
        barbanVehovIncludedLongEnergyPolynomialMain lam (Real.log L) M| ≤
      (((M : ℝ) * Real.log M) ^ 2 * (3 / (L : ℝ)) +
          2 * |lam| * (((M : ℝ) * Real.log M) ^ 2 *
            (6 * Real.log (L * M + 1 : ℕ) / (L : ℝ))) +
          lam ^ 2 * (((M : ℝ) * Real.log M) ^ 2 *
            (12 * Real.log (L * M + 1 : ℕ) ^ 2 / (L : ℝ)))) /
        Real.log M ^ 2 := by
  have hMpos : 0 < M := by omega
  have hML : M ≤ L := by
    calc
      M ≤ M * M := Nat.le_mul_of_pos_right M hMpos
      _ ≤ 8 * (M * M) := Nat.le_mul_of_pos_left (M * M) (by norm_num)
      _ = 8 * M ^ 2 := by rw [pow_two]
      _ ≤ L := hscale
  rw [levinsonCriticalDetectorLongEnergy_eq_includedLcm lam L hM hML]
  exact abs_barbanVehovIncludedLongEnergyLcm_sub_polynomialMain_le
    lam hM hscale

end

end RHTower.Sieve
