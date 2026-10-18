import GaloisForLFunctions.BezoutValuationIncidence.FermiCellJumpReciprocityAndPronicTailBridge
import GaloisForLFunctions.RHTower.MobiusMertensLittlewood

/-!
# First-octave Möbius power saving and RH

The literal first-octave Fermi response minus one is `M(n) - M(N)`. Uniform bounds at
every strict half-power exponent on `N < n ≤ 2N` are equivalent to the corresponding
Mertens bounds: strong induction on the upper endpoint sums the geometric scale loss.
The proved Littlewood equivalence then gives RH without an extra classical-converse
parameter. This criterion concerns increments, not the raw prime-tail defect whose
sublinear bounds are ruled out in `PrimeTailCalibrationAndMobiusDefect`.
-/

open Finset RHTower

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section

private theorem norm_le_rpow_of_octave_increments (A : ℕ → ℂ) {a C : ℝ}
    (ha : 0 < a) (hC : 0 ≤ C)
    (hinc : ∀ N n : ℕ, 1 ≤ N → N + 1 ≤ n → n ≤ 2 * N →
      ‖A n - A N‖ ≤ C * ((n : ℝ) + 1) ^ a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖A n‖ ≤ K * ((n : ℝ) + 1) ^ a := by
  let q : ℝ := (3 / 4 : ℝ) ^ a
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) ha
  let B := ‖A 0‖ + ‖A 1‖ + ‖A 2‖ + C + 1
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have hCB : C ≤ B := by
    dsimp [B]
    nlinarith [norm_nonneg (A 0), norm_nonneg (A 1), norm_nonneg (A 2)]
  let K := B / (1 - q)
  have hK0 : 0 ≤ K := div_nonneg hB0 (sub_pos.mpr hq1).le
  have hKB : K * (1 - q) = B := div_mul_cancel₀ B (sub_pos.mpr hq1).ne'
  have hBK : B ≤ K := by nlinarith [mul_nonneg hK0 hq0]
  have hstep : K * q + C ≤ K := by nlinarith
  refine ⟨K,hK0,fun n => ?_⟩
  induction n using Nat.strong_induction_on with
  | h n ih =>
    by_cases hn : n ≤ 2
    · have hnB : ‖A n‖ ≤ B := by
        interval_cases n <;> dsimp [B] <;> nlinarith [norm_nonneg (A 0),
          norm_nonneg (A 1),norm_nonneg (A 2)]
      exact hnB.trans (hBK.trans (le_mul_of_one_le_right hK0
        (Real.one_le_rpow (by have := Nat.cast_nonneg (α := ℝ) n; linarith) ha.le)))
    · let N := (n + 1) / 2
      have hN1 : 1 ≤ N := by dsimp [N]; omega
      have hNn : N + 1 ≤ n := by dsimp [N]; omega
      have hnN : n ≤ 2 * N := by dsimp [N]; omega
      have hscale : (N : ℝ) + 1 ≤ (3 / 4 : ℝ) * ((n : ℝ) + 1) := by
        have hi : 4 * (N + 1) ≤ 3 * (n + 1) := by dsimp [N]; omega
        have hr : (4 : ℝ) * ((N : ℝ) + 1) ≤ 3 * ((n : ℝ) + 1) := by exact_mod_cast hi
        linarith
      have hpow : ((N : ℝ) + 1) ^ a ≤ q * ((n : ℝ) + 1) ^ a := by
        calc
          _ ≤ ((3 / 4 : ℝ) * ((n : ℝ) + 1)) ^ a :=
            Real.rpow_le_rpow (by positivity) hscale ha.le
          _ = _ := Real.mul_rpow (by norm_num) (by positivity)
      calc
        ‖A n‖ = ‖A N + (A n - A N)‖ := by congr 1; ring
        _ ≤ ‖A N‖ + ‖A n - A N‖ := norm_add_le _ _
        _ ≤ K * ((N : ℝ) + 1) ^ a + C * ((n : ℝ) + 1) ^ a :=
          add_le_add (ih N (by omega)) (hinc N n hN1 hNn hnN)
        _ ≤ K * (q * ((n : ℝ) + 1) ^ a) + C * ((n : ℝ) + 1) ^ a := by gcongr
        _ = (K * q + C) * ((n : ℝ) + 1) ^ a := by ring
        _ ≤ K * ((n : ℝ) + 1) ^ a :=
          mul_le_mul_of_nonneg_right hstep (Real.rpow_nonneg (by positivity) _)

private theorem mertens_sub_eq_moebius_sum {N n : ℕ} (h : N ≤ n) :
    mobiusMertensPartialSum n - mobiusMertensPartialSum N =
      ((∑ k ∈ Finset.Icc (N + 1) n, moebiusReal k : ℝ) : ℂ) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Complex.ofReal_sum,
    Finset.sum_Ico_eq_sub _ (by omega : N + 1 ≤ n + 1)]
  simp only [mobiusMertensPartialSum, mobiusComplexCoefficient, moebiusReal,
    Complex.ofReal_intCast]

private theorem norm_mertens_sub_eq_fermiCell {N n : ℕ}
    (hN : 1 ≤ N) (hn : N + 1 ≤ n) (hn2 : n ≤ 2 * N) :
    ‖mobiusMertensPartialSum n - mobiusMertensPartialSum N‖ =
      |fermiCellResponse N moebiusReal n - 1| := by
  rw [mertens_sub_eq_moebius_sum (by omega),
    fermiCellResponse_moebiusReal_first_octave hN hn hn2]
  rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]

/-- Every strict half-power bound for actual first-octave Möbius increments. -/
def MobiusFirstOctavePowerSaving : Prop :=
  ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧ ∀ N n : ℕ,
    1 ≤ N → N + 1 ≤ n → n ≤ 2 * N →
      |fermiCellResponse N moebiusReal n - 1| ≤
        C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ)

/-- First-octave increment control is exactly the classical Mertens scale. -/
theorem mobiusFirstOctavePowerSaving_iff_mertens :
    MobiusFirstOctavePowerSaving ↔ MobiusMertensAllStrictHalfPowerBound := by
  constructor
  · intro h δ hδ
    obtain ⟨C,hC,hbound⟩ := h δ hδ
    exact norm_le_rpow_of_octave_increments mobiusMertensPartialSum
      (by linarith) hC (fun N n hN hn hn2 => by
        rw [norm_mertens_sub_eq_fermiCell hN hn hn2]
        exact hbound N n hN hn hn2)
  · intro h δ hδ
    obtain ⟨C,hC,hbound⟩ := h δ hδ
    refine ⟨2*C,by positivity,fun N n hN hn hn2 => ?_⟩
    rw [← norm_mertens_sub_eq_fermiCell hN hn hn2]
    calc
      _ ≤ ‖mobiusMertensPartialSum n‖ + ‖mobiusMertensPartialSum N‖ := norm_sub_le _ _
      _ ≤ C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) +
          C * ((N : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := add_le_add (hbound n) (hbound N)
      _ ≤ C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) +
          C * ((n : ℝ) + 1) ^ ((1 / 2 : ℝ) + δ) := by
        gcongr
        exact_mod_cast (show N ≤ n by omega)
      _ = _ := by ring

/-- The first-octave power-saving criterion has no classical-converse premise. -/
theorem mobiusFirstOctavePowerSaving_iff_riemannHypothesis :
    MobiusFirstOctavePowerSaving ↔ RiemannHypothesis :=
  mobiusFirstOctavePowerSaving_iff_mertens.trans
    mobiusMertensAllStrictHalfPowerBound_iff_riemannHypothesis

end
end GaloisForLFunctions.BezoutValuationIncidence
