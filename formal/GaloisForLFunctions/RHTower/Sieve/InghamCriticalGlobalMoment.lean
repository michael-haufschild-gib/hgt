import GaloisForLFunctions.RHTower.SmoothAFEZetaSquareInghamCriticalMoment
import Mathlib.Data.Nat.Log

/-!
# Global critical-line fourth moment of the Riemann zeta function

This module upgrades the dyadic critical-line fourth-moment bound
`∫_N^{2N} |ζ(1/2+it)|^4 dt ≤ C N^{101/100}` to initial segments `[0, N]` and to symmetric
windows `[-N, N]`. The initial-segment bound follows by summing dyadic shells up to the next power
of two above `N`; the symmetric bound uses the reflection `ζ(conj s) = conj ζ(s)`, which makes the
fourth-moment density even in `t`.

## Main results

- `exists_inghamCriticalZetaFourthMoment_initial_nat_le_routeTBudget`: there is `D ≥ 0` with
  `∫_0^N |ζ(1/2+it)|^4 dt ≤ D N^{101/100}` for every natural `N ≥ 4`.
- `exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_routeTBudget`: there is `D ≥ 0` with
  `∫_{-N}^{N} |ζ(1/2+it)|^4 dt ≤ D N^{101/100}` for every natural `N ≥ 4`.

## Hypotheses

The main results are unconditional. They rest on the imported unconditional dyadic bound
`exists_inghamCriticalZetaFourthMoment_dyadic_le_routeTBudget`; the only range condition is
`4 ≤ N`.
-/

open Complex Set MeasureTheory intervalIntegral

namespace RHTower.Sieve

noncomputable section

/-- The fourth-moment density `t ↦ |ζ(1/2+it)|^4` on the critical line. -/
private def criticalZetaFourthDensity (t : ℝ) : ℝ :=
  ‖riemannZeta (inghamCriticalPoint t)‖ ^ (4 : ℝ)

private theorem continuous_criticalZetaFourthDensity :
    Continuous criticalZetaFourthDensity := by
  exact continuous_riemannZeta_inghamCriticalPoint.norm.rpow_const
    (fun _ => Or.inr (by norm_num))

private theorem inghamCriticalZetaFourthMoment_eq_intervalIntegral
    {a b : ℝ} (hab : a ≤ b) :
    inghamCriticalZetaFourthMoment a b =
      ∫ t in a..b, criticalZetaFourthDensity t := by
  rw [inghamCriticalZetaFourthMoment,
    intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_Icc_eq_integral_Ioc]
  rfl

/-- Additivity of the critical fourth moment over adjacent intervals `[a,b] ∪ [b,c]`. -/
private theorem inghamCriticalZetaFourthMoment_add_adjacent
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    inghamCriticalZetaFourthMoment a c =
      inghamCriticalZetaFourthMoment a b +
        inghamCriticalZetaFourthMoment b c := by
  rw [inghamCriticalZetaFourthMoment_eq_intervalIntegral (hab.trans hbc),
    inghamCriticalZetaFourthMoment_eq_intervalIntegral hab,
    inghamCriticalZetaFourthMoment_eq_intervalIntegral hbc]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (continuous_criticalZetaFourthDensity.intervalIntegrable a b)
    (continuous_criticalZetaFourthDensity.intervalIntegrable b c)).symm

private theorem inghamCriticalZetaFourthMoment_nonneg {a b : ℝ} :
    0 ≤ inghamCriticalZetaFourthMoment a b := by
  unfold inghamCriticalZetaFourthMoment
  exact setIntegral_nonneg measurableSet_Icc fun _ _ =>
    Real.rpow_nonneg (norm_nonneg _) _

private theorem inghamCriticalZetaFourthMoment_mono_right
    {a b c : ℝ} (hab : a ≤ b) (hbc : b ≤ c) :
    inghamCriticalZetaFourthMoment a b ≤
      inghamCriticalZetaFourthMoment a c := by
  rw [inghamCriticalZetaFourthMoment_add_adjacent hab hbc]
  exact le_add_of_nonneg_right inghamCriticalZetaFourthMoment_nonneg

/-- Dyadic summation: assuming the shell bound `∫_N^{2N} |ζ(1/2+it)|^4 ≤ C N^{101/100}` for all
`N ≥ 4`, the segment `[4, 4·2^k]` satisfies `∫ |ζ(1/2+it)|^4 ≤ C (4·2^k)^{101/100}`. -/
private theorem dyadic_initial_inghamCriticalZetaFourthMoment_le
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
        C * (N : ℝ) ^ (101 / 100 : ℝ)) :
    ∀ k : ℕ,
      inghamCriticalZetaFourthMoment 4 (4 * 2 ^ k : ℕ) ≤
        C * ((4 * 2 ^ k : ℕ) : ℝ) ^ (101 / 100 : ℝ) := by
  intro k
  induction k with
  | zero =>
      norm_num only [pow_zero, mul_one, Nat.cast_ofNat]
      rw [show inghamCriticalZetaFourthMoment 4 4 = 0 by
        norm_num [inghamCriticalZetaFourthMoment]]
      exact mul_nonneg hC (Real.rpow_nonneg (by norm_num) _)
  | succ k ih =>
      let N : ℕ := 4 * 2 ^ k
      have hN4 : 4 ≤ N := by
        dsimp only [N]
        have hp : 0 < 2 ^ k := pow_pos (by omega : 0 < (2 : ℕ)) k
        omega
      have hnext : 4 * 2 ^ (k + 1) = 2 * N := by
        dsimp only [N]
        rw [pow_succ]
        ring
      have hsplit := inghamCriticalZetaFourthMoment_add_adjacent
        (a := (4 : ℝ)) (b := (N : ℝ)) (c := 2 * (N : ℝ))
        (by exact_mod_cast hN4) (by
          have hN0 : (0 : ℝ) ≤ N := by positivity
          linarith)
      have hshell := hbound hN4
      have htwo : (2 : ℝ) ≤ (2 : ℝ) ^ (101 / 100 : ℝ) := by
        calc
          (2 : ℝ) = (2 : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (2 : ℝ) ^ (101 / 100 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have hN0 : (0 : ℝ) ≤ N := by positivity
      rw [hnext]
      norm_num only [Nat.cast_mul, Nat.cast_ofNat]
      rw [hsplit]
      calc
        inghamCriticalZetaFourthMoment 4 (N : ℝ) +
              inghamCriticalZetaFourthMoment (N : ℝ) (2 * N : ℝ) ≤
            C * (N : ℝ) ^ (101 / 100 : ℝ) +
              C * (N : ℝ) ^ (101 / 100 : ℝ) := add_le_add ih hshell
        _ = C * 2 * (N : ℝ) ^ (101 / 100 : ℝ) := by ring
        _ ≤ C * (2 : ℝ) ^ (101 / 100 : ℝ) *
              (N : ℝ) ^ (101 / 100 : ℝ) := by
            gcongr
        _ = C * (2 * (N : ℝ)) ^ (101 / 100 : ℝ) := by
            rw [Real.mul_rpow (by norm_num) hN0]
            ring

/-- For `N > 1`, the least power of two that is at least `N` is less than `2N`. -/
private theorem pow_clog_two_lt_two_mul {N : ℕ} (hN : 1 < N) :
    2 ^ Nat.clog 2 N < 2 * N := by
  have hkpos : 0 < Nat.clog 2 N := Nat.clog_pos (by norm_num) hN
  have hpred := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hN
  rw [← Nat.succ_pred_eq_of_pos hkpos, pow_succ]
  omega

/-- Unconditional initial-segment fourth moment: some `D ≥ 0` gives
`∫_0^N |ζ(1/2+it)|^4 dt ≤ D N^{101/100}` for all natural `N ≥ 4`. -/
theorem exists_inghamCriticalZetaFourthMoment_initial_nat_le_routeTBudget :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment 0 (N : ℝ) ≤
        D * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_dyadic_le_routeTBudget
  let B : ℝ := inghamCriticalZetaFourthMoment 0 4
  let D : ℝ := B + C * (8 : ℝ) ^ (101 / 100 : ℝ)
  have hB : 0 ≤ B := inghamCriticalZetaFourthMoment_nonneg
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro N hN
  let k : ℕ := Nat.clog 2 N
  have hN1 : 1 < N := by omega
  have hNpow : N ≤ 2 ^ k := by
    dsimp only [k]
    exact Nat.le_pow_clog (by norm_num) N
  have hpowUpper : 4 * 2 ^ k ≤ 8 * N := by
    have hlt := pow_clog_two_lt_two_mul hN1
    dsimp only [k]
    omega
  have hNendpoint : N ≤ 4 * 2 ^ k :=
    hNpow.trans (Nat.le_mul_of_pos_left (2 ^ k) (by omega))
  have hmono : inghamCriticalZetaFourthMoment 4 (N : ℝ) ≤
      inghamCriticalZetaFourthMoment 4 (4 * 2 ^ k : ℕ) :=
    inghamCriticalZetaFourthMoment_mono_right
      (by exact_mod_cast hN) (by exact_mod_cast hNendpoint)
  have hdyadic := dyadic_initial_inghamCriticalZetaFourthMoment_le C hC hbound k
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hpow1 : 1 ≤ (N : ℝ) ^ (101 / 100 : ℝ) :=
    Real.one_le_rpow hNreal (by norm_num)
  have hscale : ((4 * 2 ^ k : ℕ) : ℝ) ^ (101 / 100 : ℝ) ≤
      (8 : ℝ) ^ (101 / 100 : ℝ) * (N : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      ((4 * 2 ^ k : ℕ) : ℝ) ^ (101 / 100 : ℝ) ≤
          ((8 * N : ℕ) : ℝ) ^ (101 / 100 : ℝ) := by
        apply Real.rpow_le_rpow (by positivity)
        · exact_mod_cast hpowUpper
        · norm_num
      _ = (8 : ℝ) ^ (101 / 100 : ℝ) *
          (N : ℝ) ^ (101 / 100 : ℝ) := by
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        exact Real.mul_rpow (by norm_num) (by positivity)
  have hBscale : B ≤ B * (N : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      B = B * 1 := by ring
      _ ≤ B * (N : ℝ) ^ (101 / 100 : ℝ) :=
        mul_le_mul_of_nonneg_left hpow1 hB
  have hCscale :
      C * ((4 * 2 ^ k : ℕ) : ℝ) ^ (101 / 100 : ℝ) ≤
        C * ((8 : ℝ) ^ (101 / 100 : ℝ) *
          (N : ℝ) ^ (101 / 100 : ℝ)) :=
    mul_le_mul_of_nonneg_left hscale hC
  rw [inghamCriticalZetaFourthMoment_add_adjacent (a := 0) (b := 4)
    (c := (N : ℝ)) (by norm_num) (by exact_mod_cast hN)]
  calc
    B + inghamCriticalZetaFourthMoment 4 (N : ℝ) ≤
        B + inghamCriticalZetaFourthMoment 4 (4 * 2 ^ k : ℕ) := by gcongr
    _ ≤ B + C * ((4 * 2 ^ k : ℕ) : ℝ) ^ (101 / 100 : ℝ) := by gcongr
    _ ≤ B * (N : ℝ) ^ (101 / 100 : ℝ) +
        C * ((8 : ℝ) ^ (101 / 100 : ℝ) *
          (N : ℝ) ^ (101 / 100 : ℝ)) := add_le_add hBscale hCscale
    _ = D * (N : ℝ) ^ (101 / 100 : ℝ) := by
      dsimp only [D]
      ring

/-- The density `|ζ(1/2+it)|^4` is even in `t`, by `ζ(conj s) = conj ζ(s)`. -/
private theorem criticalZetaFourthDensity_neg (t : ℝ) :
    criticalZetaFourthDensity (-t) = criticalZetaFourthDensity t := by
  have hpoint : inghamCriticalPoint (-t) = starRingEnd ℂ (inghamCriticalPoint t) := by
    apply Complex.ext <;> simp [inghamCriticalPoint]
  rw [criticalZetaFourthDensity, criticalZetaFourthDensity, hpoint,
    riemannZeta_conj, Complex.norm_conj]

private theorem inghamCriticalZetaFourthMoment_neg_eq
    {H : ℝ} (hH : 0 ≤ H) :
    inghamCriticalZetaFourthMoment (-H) 0 =
      inghamCriticalZetaFourthMoment 0 H := by
  rw [inghamCriticalZetaFourthMoment_eq_intervalIntegral (by linarith),
    inghamCriticalZetaFourthMoment_eq_intervalIntegral hH]
  calc
    (∫ t in -H..0, criticalZetaFourthDensity t) =
        ∫ t in 0..H, criticalZetaFourthDensity (-t) := by
      simpa using (intervalIntegral.integral_comp_neg criticalZetaFourthDensity
        (a := 0) (b := H)).symm
    _ = ∫ t in 0..H, criticalZetaFourthDensity t := by
      apply intervalIntegral.integral_congr
      intro t _
      exact criticalZetaFourthDensity_neg t

/-- Unconditional symmetric fourth moment: some `D ≥ 0` gives
`∫_{-N}^{N} |ζ(1/2+it)|^4 dt ≤ D N^{101/100}` for all natural `N ≥ 4`. -/
theorem exists_inghamCriticalZetaFourthMoment_symmetric_nat_le_routeTBudget :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 4 ≤ N →
      inghamCriticalZetaFourthMoment (-(N : ℝ)) (N : ℝ) ≤
        D * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_inghamCriticalZetaFourthMoment_initial_nat_le_routeTBudget
  refine ⟨2 * C, by positivity, ?_⟩
  intro N hN
  have hpos : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hneg : -(N : ℝ) ≤ 0 := neg_nonpos.mpr hpos
  rw [inghamCriticalZetaFourthMoment_add_adjacent (a := -(N : ℝ))
    (b := 0) (c := (N : ℝ)) hneg hpos,
    inghamCriticalZetaFourthMoment_neg_eq hpos]
  nlinarith [hbound hN]

end

end RHTower.Sieve
