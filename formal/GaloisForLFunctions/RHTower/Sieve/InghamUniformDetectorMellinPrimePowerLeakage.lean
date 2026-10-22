import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinFullTwoTail
import GaloisForLFunctions.RHTower.Sieve.MaynardLocalPrimePowerLeakage

/-!
# Prime-power leakage in Route T's short window is negligible

With `N_X = X^{1000/299}` and `H_X = N_X / X^{999/1000}`, this module defines the normalized
prime-power leakage `L_X = (log(N_X + 2H_X)/log 2) (√(2H_X) + 1) log(N_X + 2H_X) / H_X`, which
bounds the contribution of proper prime powers to a smoothed von Mangoldt sum over
`[N_X, N_X + 2H_X]`, and proves `L_X → 0`. The proof uses `√H_X = X^{701299/598000}` and
`log(N_X + 2H_X) ≤ log 3 + (1000/299) log X`, so `L_X` is dominated by `(log X)^2 / X^{701299/598000}`.

## Main results

- `inghamRouteTBufferedPrimePowerLeakage`: the leakage `L_X`.
- `tendsto_inghamRouteTBufferedPrimePowerLeakage_zero`: `L_X → 0` as `X → ∞`.

## Hypotheses

The result is unconditional.
-/

open Complex Filter Topology Set Finset
open MeasureTheory ArithmeticFunction
open GaloisForLFunctions.HTGeometry

namespace RHTower.Sieve

noncomputable section

/-- Normalized prime-power leakage
`(log(N_X + 2H_X)/log 2) (√(2H_X) + 1) log(N_X + 2H_X) / H_X` of Route T's window. -/
def inghamRouteTBufferedPrimePowerLeakage (X : ℕ) : ℝ :=
  (Real.log (inghamRouteTMellinPhysicalCenter X +
      2 * inghamRouteTMellinBufferedPhysicalWidth X) / Real.log 2) *
    (Real.sqrt (2 * inghamRouteTMellinBufferedPhysicalWidth X) + 1) *
    Real.log (inghamRouteTMellinPhysicalCenter X +
      2 * inghamRouteTMellinBufferedPhysicalWidth X) /
    inghamRouteTMellinBufferedPhysicalWidth X

/-- The envelope `((√2 + 1)/log 2) (log 3 + (1000/299) log x)^2 / x^{701299/598000}` tends to `0`. -/
private theorem tendsto_routeT_leakage_envelope_zero :
    Tendsto (fun x : ℝ =>
      ((Real.sqrt 2 + 1) / Real.log 2) *
        (Real.log 3 + (1000 / 299 : ℝ) * Real.log x) ^ 2 /
        x ^ (701299 / 598000 : ℝ)) atTop (nhds 0) := by
  have ha : (0 : ℝ) < 701299 / 598000 := by norm_num
  have h0 := HTGeometry.tendsto_logPow_div_rpow ha 0
  have h1 := HTGeometry.tendsto_logPow_div_rpow ha 1
  have h2 := HTGeometry.tendsto_logPow_div_rpow ha 2
  have hsum :=
    ((h0.const_mul (Real.log 3 ^ 2)).add
      (h1.const_mul (2 * Real.log 3 * (1000 / 299 : ℝ)))).add
      (h2.const_mul ((1000 / 299 : ℝ) ^ 2))
  have hscaled := hsum.const_mul ((Real.sqrt 2 + 1) / Real.log 2)
  simpa only [pow_zero, pow_one, mul_one, mul_zero, add_zero] using
    hscaled.congr' (Filter.Eventually.of_forall fun x => by ring)

/-- The normalized prime-power leakage of Route T's short window tends to `0` as `X → ∞`. -/
theorem tendsto_inghamRouteTBufferedPrimePowerLeakage_zero :
    Tendsto inghamRouteTBufferedPrimePowerLeakage atTop (nhds 0) := by
  have henv := tendsto_routeT_leakage_envelope_zero.comp
    tendsto_natCast_atTop_atTop
  refine squeeze_zero' ?_ ?_ henv
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    unfold inghamRouteTBufferedPrimePowerLeakage
    have hN := inghamRouteTMellinPhysicalCenter_pos hX
    have hH := inghamRouteTMellinBufferedPhysicalWidth_pos hX
    have hlog2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
    have hsum1 : 1 ≤ inghamRouteTMellinPhysicalCenter X +
        2 * inghamRouteTMellinBufferedPhysicalWidth X := by
      linarith [inghamRouteTMellinPhysicalCenter_one_le hX]
    have hlog := Real.log_nonneg hsum1
    positivity
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with X hX
    let N := inghamRouteTMellinPhysicalCenter X
    let H := inghamRouteTMellinBufferedPhysicalWidth X
    have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX
    have hX0 : (0 : ℝ) < X := by linarith
    have hN : 0 < N := inghamRouteTMellinPhysicalCenter_pos hX
    have hN1 : 1 ≤ N := inghamRouteTMellinPhysicalCenter_one_le hX
    have hH : 0 < H := inghamRouteTMellinBufferedPhysicalWidth_pos hX
    have hH1 : 1 ≤ H := by
      dsimp only [H]
      rw [inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow hX]
      exact Real.one_le_rpow hN1 (by norm_num)
    have hHN : H ≤ N := inghamRouteTMellinBufferedPhysicalWidth_le_center hX
    have hsum1 : 1 ≤ N + 2 * H := by linarith
    have hsumle : N + 2 * H ≤ 3 * N := by linarith
    have hlogle : Real.log (N + 2 * H) ≤ Real.log (3 * N) :=
      Real.log_le_log (by linarith) hsumle
    have hlogN : Real.log N = (1000 / 299 : ℝ) * Real.log X := by
      dsimp only [N, inghamRouteTMellinPhysicalCenter,
        inghamRouteTPhysicalScaleExponent]
      exact Real.log_rpow hX0 (1000 / 299 : ℝ)
    have hlog3N : Real.log (3 * N) =
        Real.log 3 + (1000 / 299 : ℝ) * Real.log X := by
      rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hN.ne', hlogN]
    have hlog0 : 0 ≤ Real.log (N + 2 * H) := Real.log_nonneg hsum1
    have hlog3N0 : 0 ≤ Real.log 3 + (1000 / 299 : ℝ) * Real.log X := by
      rw [← hlog3N]
      exact Real.log_nonneg (by nlinarith)
    have hsqrtH : Real.sqrt H =
        (X : ℝ) ^ (701299 / 598000 : ℝ) := by
      rw [Real.sqrt_eq_rpow]
      dsimp only [H]
      rw [inghamRouteTMellinBufferedPhysicalWidth_eq_center_rpow hX]
      rw [← Real.rpow_mul hN.le]
      dsimp only [N, inghamRouteTMellinPhysicalCenter,
        inghamRouteTPhysicalScaleExponent]
      rw [← Real.rpow_mul hX0.le]
      congr 1
      norm_num
    have hsqrtTwoH : Real.sqrt (2 * H) = Real.sqrt 2 * Real.sqrt H := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    have hsqrtH1 : 1 ≤ Real.sqrt H := by
      exact (Real.one_le_sqrt).2 hH1
    have hratio : (Real.sqrt (2 * H) + 1) / H ≤
        (Real.sqrt 2 + 1) / Real.sqrt H := by
      rw [hsqrtTwoH]
      have hsqrtH0 : 0 < Real.sqrt H := Real.sqrt_pos.2 hH
      rw [div_le_div_iff₀ hH hsqrtH0]
      nlinarith [Real.sq_sqrt hH.le, Real.sqrt_nonneg 2]
    have hlogSq : Real.log (N + 2 * H) ^ 2 ≤
        (Real.log 3 + (1000 / 299 : ℝ) * Real.log X) ^ 2 := by
      rw [← hlog3N]
      nlinarith
    have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    unfold inghamRouteTBufferedPrimePowerLeakage
    dsimp only [N, H] at *
    calc
      Real.log (inghamRouteTMellinPhysicalCenter X +
            2 * inghamRouteTMellinBufferedPhysicalWidth X) /
          Real.log 2 *
          (Real.sqrt (2 * inghamRouteTMellinBufferedPhysicalWidth X) + 1) *
          Real.log (inghamRouteTMellinPhysicalCenter X +
            2 * inghamRouteTMellinBufferedPhysicalWidth X) /
          inghamRouteTMellinBufferedPhysicalWidth X =
        (Real.log (inghamRouteTMellinPhysicalCenter X +
            2 * inghamRouteTMellinBufferedPhysicalWidth X) ^ 2 /
            Real.log 2) *
          ((Real.sqrt (2 * inghamRouteTMellinBufferedPhysicalWidth X) + 1) /
            inghamRouteTMellinBufferedPhysicalWidth X) := by ring
      _ ≤ ((Real.log 3 + (1000 / 299 : ℝ) * Real.log X) ^ 2 /
            Real.log 2) *
          ((Real.sqrt 2 + 1) /
            Real.sqrt (inghamRouteTMellinBufferedPhysicalWidth X)) := by
        gcongr
      _ = ((Real.sqrt 2 + 1) / Real.log 2) *
          (Real.log 3 + (1000 / 299 : ℝ) * Real.log X) ^ 2 /
          (X : ℝ) ^ (701299 / 598000 : ℝ) := by
        rw [hsqrtH]
        ring

end

end RHTower.Sieve
