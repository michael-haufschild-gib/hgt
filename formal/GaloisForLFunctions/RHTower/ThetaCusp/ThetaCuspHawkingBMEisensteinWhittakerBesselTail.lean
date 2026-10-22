import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMEisensteinWhittakerArithmeticEnvelope
import GaloisForLFunctions.HTGeometry.PolyExpDecayLimit

/-!
# Actual Bessel-valued completed Eisenstein cusp tails

The arithmetic admission alone does not control the actual nonconstant Eisenstein expansion: its
radial kernel is the corpus modified Bessel function at argument `2*pi*n*Y`, not a bare
exponential.  The arbitrary-complex-order exterior envelope now removes this source-specific gap.

At every positive Fourier index and cusp height `Y >= 1`, the new envelope simplifies to

`||K_nu(2*pi*n*Y)|| <= exp(||nu||^(2 : ℕ)/2) * exp(-n*Y)`.

Combining it with the actual divisor coefficient packet, polynomial absorption, and corpus Tannery
proves that the full infinite Bessel-valued jet tail tends to zero for every complex arithmetic
parameter, every complex Bessel order, and every fixed jet degree.  Arbitrary order is essential:
the two balanced Maass steps produce a finite family of shifted orders, all covered by the same
theorem.

This closes the nonconstant analytic tail, rather than a finite-mode or abstract-kernel surrogate,
needed for the completed weights `0,±4` Eisenstein Stokes calculation.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [ACTUAL BESSEL WHITTAKER TAIL]`
-/

open Complex Real Finset Filter Topology
open scoped BigOperators NNReal

namespace RHTower

noncomputable section

/-- Actual positive Bessel argument at Fourier index `n` and cusp height at least one. -/
def d4BMCuspBesselArgument
    (n : D4BMPositiveIndex) (Y : {y : ℝ // 1 ≤ y}) : {s : ℝ // 0 < s} :=
  ⟨2 * Real.pi * (n.1 : ℝ) * (Y : ℝ), by
    have hYpos : (0 : ℝ) < Y := zero_lt_one.trans_le Y.2
    exact mul_pos (mul_pos (mul_pos (by norm_num) Real.pi_pos)
      (by exact_mod_cast n.2)) hYpos⟩

/-- The arbitrary-order Bessel envelope simplifies to a uniform cusp exponential at actual
Whittaker arguments. -/
theorem d4BM_norm_modifiedBesselKOrder_cusp_le
    (n : D4BMPositiveIndex) (Y : {y : ℝ // 1 ≤ y}) (nu : ℂ) :
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (d4BMCuspBesselArgument n Y : ℝ) nu‖ ≤
      Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-((n.1 : ℝ) * (Y : ℝ))) := by
  let s := d4BMCuspBesselArgument n Y
  have hnOne : (1 : ℝ) ≤ n.1 := by exact_mod_cast n.2
  have htwoPi : (1 : ℝ) ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  have hn_le_ny : (n.1 : ℝ) ≤ (n.1 : ℝ) * (Y : ℝ) := by
    have h := mul_le_mul_of_nonneg_left Y.2 (by positivity : (0 : ℝ) ≤ n.1)
    simpa using h
  have hnyOne : (1 : ℝ) ≤ (n.1 : ℝ) * (Y : ℝ) := hnOne.trans hn_le_ny
  have hnyNonneg : (0 : ℝ) ≤ (n.1 : ℝ) * (Y : ℝ) := zero_le_one.trans hnyOne
  have hny_le_s : (n.1 : ℝ) * (Y : ℝ) ≤ (s : ℝ) := by
    dsimp [s, d4BMCuspBesselArgument]
    nlinarith [mul_le_mul_of_nonneg_right htwoPi hnyNonneg]
  have hsOne : (1 : ℝ) ≤ (s : ℝ) := hnyOne.trans hny_le_s
  have hExpArg : ‖nu‖ ^ 2 / (2 * (s : ℝ)) ≤ ‖nu‖ ^ 2 / 2 := by
    apply div_le_div_of_nonneg_left (sq_nonneg ‖nu‖) (by norm_num)
    nlinarith
  have hSqrt : Real.sqrt (2 * Real.pi / (s : ℝ)) ≤ 1 := by
    rw [Real.sqrt_le_one, div_le_one s.property]
    dsimp [s, d4BMCuspBesselArgument]
    have htwoPiPos : (0 : ℝ) < 2 * Real.pi := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hnyOne htwoPiPos.le]
  have hEnvelope := d4BM_norm_modifiedBesselKOrder_le s nu
  calc
    ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder (s : ℝ) nu‖
        ≤ Real.exp (-(s : ℝ)) * Real.exp (‖nu‖ ^ 2 / (2 * (s : ℝ))) *
            Real.sqrt (2 * Real.pi / (s : ℝ)) := hEnvelope
    _ ≤ Real.exp (-((n.1 : ℝ) * (Y : ℝ))) * Real.exp (‖nu‖ ^ 2 / 2) * 1 := by
      gcongr
    _ = Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-((n.1 : ℝ) * (Y : ℝ))) := by ring

/-- Bessel-valued nonconstant completed Eisenstein jet tail, with arbitrary fixed order. -/
def d4BMCompletedEisensteinBesselJetTail
    (u nu : ℂ) (degree : ℕ) (Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      (Y : ℂ) ^ degree *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

/-- Every actual completed Eisenstein Bessel jet tail tends to zero at the cusp. -/
theorem tendsto_d4BMCompletedEisensteinBesselJetTail_atTop_zero
    (u nu : ℂ) (degree : ℕ) :
    Tendsto (d4BMCompletedEisensteinBesselJetTail u nu degree) atTop (𝓝 0) := by
  let packet := d4BMCompletedEisensteinArithmeticJetPacket u degree
  let C : ℝ := Real.exp (‖nu‖ ^ 2 / 2)
  apply GaloisForLFunctions.HTGeometry.tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant
    (packet.weightedNormSummable.mul_left C)
  · intro N
    apply GaloisForLFunctions.HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
      (C := C * ‖packet.coefficient N‖) (δ := (N : ℝ) + 1)
      (N := degree) (by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            C * Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, C, Nat.cast_add, Nat.cast_one] using hK
    dsimp [d4BMCompletedEisensteinBesselJetTail, packet,
      d4BMCompletedEisensteinArithmeticJetPacket, n, Yp] at hK ⊢
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hY)]
    calc
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          Y ^ degree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          Y ^ degree * (C * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = C * ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          Y ^ degree * Real.exp (-((↑N + 1) * Y)) := by ring
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    intro N
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            Real.exp (‖nu‖ ^ 2 / 2) *
              Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, Nat.cast_add, Nat.cast_one] using hK
    have hY0 : 0 ≤ Y := zero_le_one.trans hY
    have ha : 0 < (N : ℝ) + 1 := by positivity
    have habsorb := pow_mul_exp_neg_le_absorb_half ha hY0 degree
    dsimp [d4BMCompletedEisensteinBesselJetTail, packet,
      d4BMCompletedEisensteinArithmeticJetPacket, C, n, Yp] at hK ⊢
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hY0]
    calc
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          Y ^ degree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
          Y ^ degree *
          (Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
            (Y ^ degree * Real.exp (-((↑N + 1) * Y)))) := by ring
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
            ((degree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ degree *
              Real.exp (-(((N : ℝ) + 1) * Y / 2)))) := by gcongr
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
            ((degree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ degree *
              Real.exp (-(((N : ℝ) + 1) / 2)))) := by
            gcongr
            nlinarith
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩‖ *
            (degree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ degree *
            Real.exp (-(((N : ℝ) + 1) / 2))) := by ring

end

end RHTower
