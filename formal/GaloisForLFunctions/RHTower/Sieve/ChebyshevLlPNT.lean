import GaloisForLFunctions.RHTower.Sieve.ChebyshevLlSharpRate
import GaloisForLFunctions.PNTPlus.MediumPNT

/-!
# Littlewood's prime number theorem

The cutoff's mass lies between `N` and `N + H`, so replacing it by `N` costs `H`, and at the
balanced width `H` is itself below the contour's shape.  What is left is

```text
| ψ(⌊N⌋) - N |  ≤  B · N · exp( -√(c·log N·log log N) / 48 ) ,
```

Littlewood's 1922 error term, unconditional and with every constant explicit up to the two
existentials the zero-free region carries.  Against the exponent-one chain's
`exp(-√(log N)/960000)` the gain is the factor `√(log log N)` in the exponent, and against the
vendored `MediumPNT`'s `exp(-c(log N)^{1/10})` it is the whole difference between a fractional
power and the square root.
-/

namespace RHTower.Sieve

open Complex MeasureTheory Filter Topology Asymptotics ArithmeticFunction
open GaloisForLFunctions.HTGeometry

/-- **The sharp Chebyshev sum against the cutoff, at Littlewood strength.** -/
theorem exists_norm_sum_vonMangoldt_sub_self_ll_rate :
    ∃ c B : ℝ, 0 < c ∧ c ≤ 1 / 2 ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
        ≤ B * (N + chebWidthLl c N + 1)
            * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 48)) := by
  obtain ⟨c, B₂, hc0, hchalf, hB₂, hmass⟩ := exists_norm_sum_vonMangoldt_sub_mass_ll_rate
  refine ⟨c, B₂ + 1, hc0, hchalf, by linarith, ?_⟩
  filter_upwards [hmass, eventually_cheb_ll_conditions c 0 hc0 (by linarith),
    eventually_ge_atTop (3 : ℝ), Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)]
    with N hM hcond hN3 hlogN
  obtain ⟨hN0, hN1, hH1, hHN, hlogZ0, hQ256, hQ2, hdepth, -⟩ := hcond
  have hZ0 : (0 : ℝ) < N + chebWidthLl c N + 1 := by linarith
  set s : ℝ := Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) with hsdef
  have hs0 : (0 : ℝ) ≤ s := Real.sqrt_nonneg _
  have hE2448 : Real.exp (-(s / 24)) ≤ Real.exp (-(s / 48)) :=
    Real.exp_le_exp.mpr (by linarith)
  -- the mass is within the window of the cutoff
  have hmw := norm_mellin_one_sub_ofReal_le (N := N) (H := chebWidthLl c N) hN0.le (by linarith)
  have hws := chebWidthLl_le_shape (c := c) hc0.le hN3 hlogN
  have hshape : chebWidthLl c N
      ≤ (N + chebWidthLl c N + 1) * Real.exp (-(s / 48)) := by
    refine le_trans hws ?_
    exact mul_le_mul_of_nonneg_left hE2448 hZ0.le
  -- the triangle inequality
  have htri : ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
      ≤ ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
          - mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1‖
        + ‖mellin (fun x : ℝ =>
              ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1
            - ((N : ℝ) : ℂ)‖ := by
    have h := norm_add_le
      ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ))
        - mellin (fun x : ℝ =>
            ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1)
      (mellin (fun x : ℝ =>
          ((GaloisForLFunctions.HTGeometry.smoothWeight N (chebWidthLl c N) x : ℝ) : ℂ)) 1
        - ((N : ℝ) : ℂ))
    rwa [sub_add_sub_cancel] at h
  linarith [htri, hM, hmw, hshape]

/-- **Littlewood's prime number theorem, in Chebyshev form.**  The shifted cutoff is at most `3N`
and its balanced quantity is the larger one, so the rate may be stated against `N`:

```text
‖ ψ(⌊N⌋) - N ‖ ≤ B · N · exp( -√(c·log N·log log N)/48 ).
``` -/
theorem exists_norm_sum_vonMangoldt_sub_self_ll_rate_self :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      ‖(∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ)‖
        ≤ B * N * Real.exp (-(Real.sqrt (chebQuadLl c N) / 48)) := by
  obtain ⟨c, B₃, hc0, hchalf, hB₃, hZrate⟩ := exists_norm_sum_vonMangoldt_sub_self_ll_rate
  refine ⟨c, 3 * B₃, hc0, by linarith, ?_⟩
  filter_upwards [hZrate, eventually_ge_atTop (3 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 : ℝ)] with N hb hN3 hlogN
  have hN0 : (0 : ℝ) < N := by linarith
  have hH0 := chebWidthLl_nonneg (c := c) hN0.le
  have hHN := chebWidthLl_le (c := c) hN0.le
  have hZ3 : N + chebWidthLl c N + 1 ≤ 3 * N := by linarith
  have hmono : Real.sqrt (chebQuadLl c N)
      ≤ Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) := by
    have h := chebSavingLl_mono (c := c) (N := N) (Z := N + chebWidthLl c N + 1)
      hc0.le hN0 (by linarith) (by linarith)
    rw [chebSavingLl, chebSavingLl] at h
    linarith
  have hexp : Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 48))
      ≤ Real.exp (-(Real.sqrt (chebQuadLl c N) / 48)) :=
    Real.exp_le_exp.mpr (by linarith)
  have hE0 : (0 : ℝ) < Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 48)) :=
    Real.exp_pos _
  have h1 : B₃ * (N + chebWidthLl c N + 1)
        * Real.exp (-(Real.sqrt (chebQuadLl c (N + chebWidthLl c N + 1)) / 48))
      ≤ B₃ * (3 * N) * Real.exp (-(Real.sqrt (chebQuadLl c N) / 48)) := by
    refine mul_le_mul (mul_le_mul_of_nonneg_left hZ3 hB₃) hexp hE0.le ?_
    exact mul_nonneg hB₃ (by linarith)
  linarith [hb, h1]

/-- **Littlewood's prime number theorem**, in real form:

```text
|ψ(⌊N⌋) - N| ≤ B · N · exp( -√(c·log N·log log N)/48 ).
``` -/
theorem exists_abs_sum_vonMangoldt_sub_self_ll_rate :
    ∃ c B : ℝ, 0 < c ∧ 0 ≤ B ∧ ∀ᶠ N : ℝ in atTop,
      |(∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N|
        ≤ B * N * Real.exp (-(Real.sqrt (chebQuadLl c N) / 48)) := by
  obtain ⟨c, B, hc0, hB, hrate⟩ := exists_norm_sum_vonMangoldt_sub_self_ll_rate_self
  refine ⟨c, B, hc0, hB, ?_⟩
  filter_upwards [hrate] with N hN
  have hcast : ((∑ n ∈ Finset.range (⌊N⌋₊ + 1), ((vonMangoldt n : ℝ) : ℂ)) - ((N : ℝ) : ℂ))
      = (((∑ n ∈ Finset.range (⌊N⌋₊ + 1), (vonMangoldt n : ℝ)) - N : ℝ) : ℂ) := by
    push_cast
    ring
  rwa [hcast, Complex.norm_real, Real.norm_eq_abs] at hN

/-- **Littlewood's prime number theorem**, in the `IsBigO` shape the vendored `MediumPNT` uses:

```text
ψ - id  =O[atTop]  x · exp( -c·√(log x · log log x) ) ,
```

against `MediumPNT`'s `x · exp(-c(log x)^{1/10})` and the exponent-one chain's
`x · exp(-c√(log x))`. -/
theorem chebyshevPsi_sub_id_isBigO_littlewood :
    ∃ c > 0, (Chebyshev.psi - id) =O[atTop]
      fun x : ℝ => x * Real.exp (-c * Real.sqrt (Real.log x * Real.log (Real.log x))) := by
  obtain ⟨c, B, hc0, hB, hrate⟩ := exists_abs_sum_vonMangoldt_sub_self_ll_rate
  refine ⟨Real.sqrt c / 48, by positivity, Asymptotics.IsBigO.of_bound B ?_⟩
  filter_upwards [hrate, eventually_gt_atTop (0 : ℝ)] with N hN hN0
  have hsplit : Real.sqrt (chebQuadLl c N)
      = Real.sqrt c * Real.sqrt (Real.log N * Real.log (Real.log N)) := by
    rw [chebQuadLl, Real.sqrt_mul hc0.le]
  have hcongr : Real.exp (-(Real.sqrt (chebQuadLl c N) / 48))
      = Real.exp (-(Real.sqrt c / 48) * Real.sqrt (Real.log N * Real.log (Real.log N))) := by
    rw [hsplit]
    congr 1
    ring
  have hgnorm : ‖N * Real.exp (-(Real.sqrt c / 48)
        * Real.sqrt (Real.log N * Real.log (Real.log N)))‖
      = N * Real.exp (-(Real.sqrt c / 48)
        * Real.sqrt (Real.log N * Real.log (Real.log N))) := by
    rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [Pi.sub_apply, id_eq, Chebyshev.psi_eq_sum_range, Real.norm_eq_abs, hgnorm]
  rw [hcongr] at hN
  linarith [hN]

end RHTower.Sieve
