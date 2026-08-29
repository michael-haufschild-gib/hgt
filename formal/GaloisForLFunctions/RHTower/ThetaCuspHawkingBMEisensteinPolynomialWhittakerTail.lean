import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMBesselArgumentDerivative

/-!
# Polynomial-index completed Eisenstein Whittaker tails

Two literal Maass steps introduce powers of both cusp height and Fourier index.  The preceding
actual Bessel-tail theorem covered arbitrary height jets but no index powers.  This module proves
the source-stable extension for all fixed degrees:

`sum_n a_u(n) n^j Y^m K_nu(2*pi*n*Y) -> 0` as `Y -> infinity`.

The actual divisor coefficient has polynomial growth, so multiplying by `n^j` merely increases
its real-power exponent.  Corpus polynomial--exponential summability and the arbitrary-order
Bessel cusp envelope supply one parameter-independent Tannery majorant.  The result is stronger
than the two-step Maass need `j <= 2`: every fixed index and height jet vanishes.

`[NEW] [PAPER-PROVED] [LEAN-PROVED] [HC94] [POLYNOMIAL WHITTAKER TAIL]`
-/

open Complex Real Finset Filter Topology
open scoped BigOperators NNReal

namespace RHTower

noncomputable section

/-- Actual Eisenstein arithmetic coefficients remain summably admitted after arbitrary fixed
powers of the Fourier index and cusp-jet weighting. -/
theorem d4BM_completedEisensteinPolynomialWhittakerCoefficient_weightedSummable
    (u : ℂ) (indexDegree heightDegree : ℕ) :
    Summable (fun N : ℕ =>
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ *
        (heightDegree.factorial : ℝ) * (2 / ((N : ℝ) + 1)) ^ heightDegree *
        Real.exp (-(((N : ℝ) + 1) / 2))) := by
  let baseExponent : ℝ := 3 * |u.re| + 1
  let r : ℝ := baseExponent + indexDegree
  have hr : 0 ≤ r := by dsimp [r, baseExponent]; positivity
  have hbase : Summable (fun N : ℕ =>
      ((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ)))) :=
    (summable_natSucc_rpow_exp_neg_and_tsum_le hr (by norm_num : (0 : ℝ) < 1 / 2)).1
  have hmajor : Summable (fun N : ℕ =>
      ((heightDegree.factorial : ℝ) * (2 : ℝ) ^ heightDegree) *
        (((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ))))) :=
    hbase.mul_left ((heightDegree.factorial : ℝ) * (2 : ℝ) ^ heightDegree)
  refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hmajor
  let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
  have hcoeff := d4BM_norm_completedEisensteinWhittakerCoefficient_le u n
  have hnPos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hCoeffPow :
      ‖d4BMCompletedEisensteinWhittakerCoefficient u n *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ ≤
        ((N : ℝ) + 1) ^ r := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      ‖d4BMCompletedEisensteinWhittakerCoefficient u n‖ *
          (N + 1 : ℝ) ^ indexDegree
        ≤ (N + 1 : ℝ) ^ baseExponent * (N + 1 : ℝ) ^ indexDegree := by
          gcongr
          simpa [n, baseExponent, Nat.cast_add, Nat.cast_one] using hcoeff
      _ = ((N : ℝ) + 1) ^ r := by
          rw [← Real.rpow_natCast, ← Real.rpow_add hnPos]
  have hdenom : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hratio : 2 / ((N : ℝ) + 1) ≤ (2 : ℝ) := by
    rw [div_le_iff₀ hdenom]
    nlinarith
  have hpow : (2 / ((N : ℝ) + 1)) ^ heightDegree ≤ (2 : ℝ) ^ heightDegree := by
    gcongr
  have hexp : Real.exp (-(((N : ℝ) + 1) / 2)) ≤
      Real.exp (-((N : ℝ) * (1 / 2 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    ring_nf
    norm_num
  calc
    ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          ((N + 1 : ℕ) : ℂ) ^ indexDegree‖ *
          (heightDegree.factorial : ℝ) *
          (2 / ((N : ℝ) + 1)) ^ heightDegree *
          Real.exp (-(((N : ℝ) + 1) / 2))
        ≤ ((N : ℝ) + 1) ^ r * (heightDegree.factorial : ℝ) *
          (2 : ℝ) ^ heightDegree * Real.exp (-((N : ℝ) * (1 / 2 : ℝ))) := by
            gcongr
    _ = ((heightDegree.factorial : ℝ) * (2 : ℝ) ^ heightDegree) *
          (((N : ℝ) + 1) ^ r * Real.exp (-((N : ℝ) * (1 / 2 : ℝ)))) := by ring

/-- Literal Bessel-valued Eisenstein tail with arbitrary fixed Fourier-index and cusp-height
degrees. -/
def d4BMCompletedEisensteinPolynomialBesselJetTail
    (u nu : ℂ) (indexDegree heightDegree : ℕ) (Y : ℝ) : ℂ :=
  ∑' N : ℕ,
    (d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree) *
      (Y : ℂ) ^ heightDegree *
      GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
        (2 * Real.pi * ((N : ℝ) + 1) * Y) nu

/-- Every fixed polynomial-index actual completed Eisenstein Bessel jet tail vanishes at the
cusp. -/
theorem tendsto_d4BMCompletedEisensteinPolynomialBesselJetTail_atTop_zero
    (u nu : ℂ) (indexDegree heightDegree : ℕ) :
    Tendsto
      (d4BMCompletedEisensteinPolynomialBesselJetTail
        u nu indexDegree heightDegree) atTop (𝓝 0) := by
  let coefficient : ℕ → ℂ := fun N =>
    d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
      ((N + 1 : ℕ) : ℂ) ^ indexDegree
  let C : ℝ := Real.exp (‖nu‖ ^ 2 / 2)
  have hsum :=
    d4BM_completedEisensteinPolynomialWhittakerCoefficient_weightedSummable
      u indexDegree heightDegree
  apply GaloisForLFunctions.HTGeometry.tendsto_tsum_zero_of_pointwise_damping_of_summable_majorant
    (hsum.mul_left C)
  · intro N
    apply GaloisForLFunctions.HTGeometry.tendsto_zero_of_eventually_norm_le_polyExp
      (C := C * ‖coefficient N‖) (δ := (N : ℝ) + 1)
      (N := heightDegree) (by positivity)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            C * Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, C, Nat.cast_add, Nat.cast_one] using hK
    dsimp [d4BMCompletedEisensteinPolynomialBesselJetTail, coefficient, n, Yp]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (zero_le_one.trans hY)]
    calc
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ * Y ^ heightDegree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ * Y ^ heightDegree *
          (C * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = C * ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ * Y ^ heightDegree *
          Real.exp (-((↑N + 1) * Y)) := by ring
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    intro N
    let n : D4BMPositiveIndex := ⟨N + 1, by omega⟩
    let Yp : {y : ℝ // 1 ≤ y} := ⟨Y, hY⟩
    have hK := d4BM_norm_modifiedBesselKOrder_cusp_le n Yp nu
    have hK' :
        ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
          (2 * Real.pi * ((N : ℝ) + 1) * Y) nu‖ ≤
            Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-(((N : ℝ) + 1) * Y)) := by
      simpa [n, Yp, d4BMCuspBesselArgument, Nat.cast_add, Nat.cast_one] using hK
    have hY0 : 0 ≤ Y := zero_le_one.trans hY
    have ha : 0 < (N : ℝ) + 1 := by positivity
    have habsorb := pow_mul_exp_neg_le_absorb_half ha hY0 heightDegree
    dsimp [d4BMCompletedEisensteinPolynomialBesselJetTail, coefficient, C, n, Yp]
    rw [norm_mul, norm_mul, norm_pow, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hY0]
    calc
      ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ * Y ^ heightDegree *
          ‖GaloisForLFunctions.HTGeometry.modifiedBesselKOrder
            (2 * Real.pi * (↑N + 1) * Y) nu‖
        ≤ ‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
          (↑(N + 1) : ℂ) ^ indexDegree‖ * Y ^ heightDegree *
          (Real.exp (‖nu‖ ^ 2 / 2) * Real.exp (-((↑N + 1) * Y))) := by gcongr
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree‖ *
            (Y ^ heightDegree * Real.exp (-((↑N + 1) * Y)))) := by ring
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree‖ *
            ((heightDegree.factorial : ℝ) *
              (2 / ((N : ℝ) + 1)) ^ heightDegree *
              Real.exp (-(((N : ℝ) + 1) * Y / 2)))) := by gcongr
      _ ≤ Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree‖ *
            ((heightDegree.factorial : ℝ) *
              (2 / ((N : ℝ) + 1)) ^ heightDegree *
              Real.exp (-(((N : ℝ) + 1) / 2)))) := by
            gcongr
            nlinarith
      _ = Real.exp (‖nu‖ ^ 2 / 2) *
          (‖d4BMCompletedEisensteinWhittakerCoefficient u ⟨N + 1, by omega⟩ *
            (↑(N + 1) : ℂ) ^ indexDegree‖ *
            (heightDegree.factorial : ℝ) *
            (2 / ((N : ℝ) + 1)) ^ heightDegree *
            Real.exp (-(((N : ℝ) + 1) / 2))) := by ring

end

end RHTower
