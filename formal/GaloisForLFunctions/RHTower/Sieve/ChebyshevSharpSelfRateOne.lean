import GaloisForLFunctions.RHTower.Sieve.ChebyshevSharpMassRateOne
import GaloisForLFunctions.RHTower.Sieve.ChebyshevMainTermLimit

/-!
# The sharp Chebyshev sum against the cutoff itself

The cutoff's mass lies between `N` and `N + H`, so replacing it by `N` costs `H`, and at the
balanced width `H` is itself below the contour's shape.  What is left is the Chebyshev estimate in
its usual form,

```text
‖ ψ(⌊N⌋) - N ‖ ≤ B · Z · exp( -√(log Z) / 960000 ),      Z = N + chebWidthOne N + 1.
```
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology ArithmeticFunction GaloisForLFunctions.HTGeometry

/-- The smoothing width is itself below the contour's shape. -/
theorem chebWidthOne_le_shape {N : ℝ} (hN3 : 3 ≤ N) (hlogN : 16 ≤ Real.log N) :
    chebWidthOne N ≤ (N + chebWidthOne N + 1)
      * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hHN := chebWidthOne_le hN0.le
  have hH0 := chebWidthOne_nonneg hN0.le
  have hhalf := sqrt_log_shift_le hN3 (by linarith) hHN
  have hexpcmp : Real.exp (-(Real.sqrt (Real.log N) / 240000))
      ≤ Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hHeq : chebWidthOne N = N * Real.exp (-(Real.sqrt (Real.log N) / 240000)) :=
    chebWidthOne_eq N
  have h1 : N * Real.exp (-(Real.sqrt (Real.log N) / 240000))
      ≤ N * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
    mul_le_mul_of_nonneg_left hexpcmp hN0.le
  have h2 : N * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))
      ≤ (N + chebWidthOne N + 1)
          * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000)) :=
    mul_le_mul_of_nonneg_right (by linarith) (Real.exp_pos _).le
  linarith [hHeq, h1, h2]

/-- **The mass differs from the cutoff by at most the window.** -/
theorem norm_mellin_one_sub_ofReal_le {N H : ℝ} (hN0 : 0 ≤ N) (hH0 : 0 < H) :
    ‖mellin (fun x : ℝ =>
        ((GaloisForLFunctions.HTGeometry.smoothWeight N H x : ℝ) : ℂ)) 1 - ((N : ℝ) : ℂ)‖
      ≤ H := by
  rw [mellin_smoothWeight_one_eq_ofReal, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs, abs_le]
  have hlo := le_integral_smoothWeight hN0 hH0
  have hhi := integral_smoothWeight_le hN0 hH0
  constructor <;> linarith

/-- **The sharp Chebyshev sum against the cutoff, with an explicit saving of exponent `1/2`.** -/
theorem exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
        ≤ B * (N + chebWidthOne N + 1)
            * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) := by
  obtain ⟨B₂, hB₂, hmass⟩ := exists_norm_sum_vonMangoldt_sub_mass_kappa_one_rate
  refine ⟨B₂ + 1, by linarith, ?_⟩
  filter_upwards [hmass, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (16 : ℝ)] with N hM hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have hH1 : (1 : ℝ) ≤ chebWidthOne N := one_le_chebWidthOne hN0 (by linarith)
  have hZ0 : (0 : ℝ) < N + chebWidthOne N + 1 := by linarith
  have hEF : Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 480000))
      ≤ Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) :=
    Real.exp_le_exp.mpr (by linarith [Real.sqrt_nonneg (Real.log (N + chebWidthOne N + 1))])
  -- the mass is within the window of the cutoff
  have hmw := norm_mellin_one_sub_ofReal_le (N := N) (H := chebWidthOne N) hN0.le (by linarith)
  have hws := chebWidthOne_le_shape hN3 hlogN
  have hshape : chebWidthOne N
      ≤ (N + chebWidthOne N + 1)
        * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) := by
    refine le_trans hws ?_
    exact mul_le_mul_of_nonneg_left hEF hZ0.le
  -- the triangle inequality
  have htri : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1‖
        + ‖mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
            - ((N : ℝ) : ℂ)‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
        - mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1)
      (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthOne N) x : ℝ) : ℂ)) 1
        - ((N : ℝ) : ℂ))
    rwa [sub_add_sub_cancel] at h
  linarith [htri, hM, hmw, hshape]

/-- **The Chebyshev estimate in its usual form.**  Since the shifted cutoff `Z = N + H + 1` is at
most `3N` and its logarithm is the larger one, the rate may be stated against `N` itself:

```text
‖ ψ(⌊N⌋) - N ‖ ≤ B · N · exp( -√(log N) / 960000 ).
``` -/
theorem exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate_self :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
        ≤ B * N * Real.exp (-(Real.sqrt (Real.log N) / 960000)) := by
  obtain ⟨B₃, hB₃, hZrate⟩ := exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate
  refine ⟨3 * B₃, by linarith, ?_⟩
  filter_upwards [hZrate, eventually_ge_atTop (3 : ℝ)] with N hb hN3
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 := chebWidthOne_nonneg hN0.le
  have hHN := chebWidthOne_le hN0.le
  have hZ3 : N + chebWidthOne N + 1 ≤ 3 * N := by linarith
  have hexp : Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000))
      ≤ Real.exp (-(Real.sqrt (Real.log N) / 960000)) :=
    Real.exp_le_exp.mpr
      (by linarith [Real.sqrt_le_sqrt (Real.log_le_log hN0 (by linarith :
        N ≤ N + chebWidthOne N + 1))])
  have hE0 : (0 : ℝ) < Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000)) :=
    Real.exp_pos _
  have h1 : B₃ * (N + chebWidthOne N + 1)
        * Real.exp (-(Real.sqrt (Real.log (N + chebWidthOne N + 1)) / 960000))
      ≤ B₃ * (3 * N) * Real.exp (-(Real.sqrt (Real.log N) / 960000)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hZ3 hB₃) hexp hE0.le ?_
    exact mul_nonneg hB₃ (by linarith)
  linarith [hb, h1]

/-- **The prime number theorem with error term, in Chebyshev form.**  The real-valued statement,
which is what `tendsto_sum_vonMangoldt_div` refines:

```text
|ψ(⌊N⌋) - N| ≤ B · N · exp( -√(log N) / 960000 ).
``` -/
theorem exists_abs_sum_vonMangoldt_sub_self_kappa_one_rate :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      |(∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N|
        ≤ B * N * Real.exp (-(Real.sqrt (Real.log N) / 960000)) := by
  obtain ⟨B, hB, hrate⟩ := exists_norm_sum_vonMangoldt_sub_self_kappa_one_rate_self
  refine ⟨B, hB, ?_⟩
  filter_upwards [hrate] with N hN
  have hcast : ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
      - ((N : ℝ) : ℂ))
      = (((∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [hcast, Complex.norm_real, Real.norm_eq_abs] at hN

end RHTower.Sieve
