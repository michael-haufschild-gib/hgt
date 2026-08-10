import GaloisForLFunctions.RHTower.PrimeRpowAbelSummation

/-!
# The asymptotic of the prime power sum

For `0 < a < 1` the prime number theorem in Chebyshev form gives

```text
∑_{p ≤ x} p^(a-1) ~ x^a/(a log x).
```

The Abel identity converts the sum into `f(x)θ(x)` minus the integral of `f'θ`; writing
`θ(t) = t(1 + g(t))` with `g → 0`, the main term is `(a-1)` times the logarithmic power integral
minus its doubly logarithmic companion, and the `g`-weighted remainder is of smaller order because
the Abel kernel is dominated by `t^(a-1)/log t`.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-- The `g`-weighted Abel remainder. -/
private theorem tendsto_abelRemainder {a : ℝ} (ha0 : 0 < a) {g : ℝ → ℝ}
    (hgt : Tendsto g atTop (nhds 0))
    (g_int : ∀ x : ℝ, 2 ≤ x → IntegrableOn g (Icc 2 x)) :
    Tendsto (fun x : ℝ =>
        (∫ t in (2 : ℝ)..x, g t * abelKernel a t) * (a * Real.log x) / x ^ a) atTop (nhds 0) := by
  have hgint : ∀ x : ℝ, 2 ≤ x →
      IntervalIntegrable (fun t : ℝ => g t * abelKernel a t) volume 2 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact ((g_int x hx).mul_continuousOn
      (fun t ht => (continuousAt_abelKernel (a := a) ht.1).continuousWithinAt)
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  exact HTGeometry.tendsto_logKernelRemainder ha0 (abelKernelConst_nonneg a) hgt
    (fun t ht => abs_abelKernel_le ht) hgint

/-- **The prime power sum is asymptotic to `x^a/(a log x)`.** -/
theorem tendsto_primeRpowSumIoc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Tendsto (fun x : ℝ => primeRpowSumIoc a x * (a * Real.log x) / x ^ a) atTop (nhds 1) := by
  obtain ⟨g, hg, g_int, hθ⟩ := chebyshev_asymptotic''
  have hgt : Tendsto g atTop (nhds 0) :=
    (Asymptotics.isLittleO_one_iff ℝ).mp (hg 1 one_pos)
  have hJ := HTGeometry.tendsto_logRpowIntegral ha0
  have hK := HTGeometry.tendsto_logSqRpowIntegral ha0
  have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (nhds 0) :=
    (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
  have hgint : ∀ x : ℝ, 2 ≤ x →
      IntervalIntegrable (fun t : ℝ => g t * abelKernel a t) volume 2 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact ((g_int x hx).mul_continuousOn
      (fun t ht => (continuousAt_abelKernel (a := a) ht.1).continuousWithinAt)
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  -- the boundary term
  have hT1 : Tendsto
      (fun x : ℝ => rpowDivLog a x * Chebyshev.theta x * (a * Real.log x) / x ^ a) atTop
      (nhds a) := by
    have hlim : Tendsto (fun x : ℝ => a * (1 + g x)) atTop (nhds a) := by
      have h := (tendsto_const_nhds (x := a)).mul
        ((tendsto_const_nhds (x := (1 : ℝ))).add hgt)
      rw [add_zero, mul_one] at h
      exact h
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
    have hsub : x ^ (a - 1) = x ^ a / x := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [rpowDivLog, hθ x hx0, hsub]
    field_simp
  -- the fixed endpoint term
  have hT2 : Tendsto
      (fun x : ℝ => rpowDivLog a 2 * Chebyshev.theta 2 * (a * Real.log x) / x ^ a) atTop
      (nhds 0) := by
    have h := hlogdiv.const_mul (rpowDivLog a 2 * Chebyshev.theta 2 * a)
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    ring
  -- the main integral
  have hmain : Tendsto
      (fun x : ℝ => (∫ t in (2 : ℝ)..x, abelKernel a t) * (a * Real.log x) / x ^ a) atTop
      (nhds (a - 1)) := by
    have hlim : Tendsto (fun x : ℝ =>
        (a - 1) * (HTGeometry.logRpowIntegral a x * (a * Real.log x) / x ^ a)
          - a * (HTGeometry.logSqRpowIntegral a x * Real.log x / x ^ a)) atTop
        (nhds (a - 1)) := by
      have h := (hJ.const_mul (a - 1)).sub (hK.const_mul a)
      rw [mul_one, mul_zero, sub_zero] at h
      exact h
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
    rw [integral_abelKernel hx]
    ring
  -- the remainder
  have hrem := tendsto_abelRemainder ha0 hgt g_int
  -- assemble
  have hsum : Tendsto (fun x : ℝ =>
      rpowDivLog a x * Chebyshev.theta x * (a * Real.log x) / x ^ a
        - rpowDivLog a 2 * Chebyshev.theta 2 * (a * Real.log x) / x ^ a
        - ((∫ t in (2 : ℝ)..x, abelKernel a t) * (a * Real.log x) / x ^ a
          + (∫ t in (2 : ℝ)..x, g t * abelKernel a t) * (a * Real.log x) / x ^ a)) atTop
      (nhds (a - 0 - ((a - 1) + 0))) := (hT1.sub hT2).sub (hmain.add hrem)
  rw [show a - 0 - ((a - 1) + 0) = 1 by ring] at hsum
  refine hsum.congr' ?_
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hker : IntervalIntegrable (abelKernel a) volume 2 x :=
    intervalIntegrable_abelKernel a (le_refl (2 : ℝ)) hx
  have hdecomp : (∫ t in Ioc (2 : ℝ) x, deriv (rpowDivLog a) t * Chebyshev.theta t)
      = (∫ t in (2 : ℝ)..x, abelKernel a t) + ∫ t in (2 : ℝ)..x, g t * abelKernel a t := by
    rw [← intervalIntegral.integral_of_le hx, ← intervalIntegral.integral_add hker (hgint x hx)]
    refine intervalIntegral.integral_congr fun t ht => ?_
    have ht2 : (2 : ℝ) ≤ t := HTGeometry.two_le_of_mem_uIcc (le_refl (2 : ℝ)) hx ht
    have ht0 : (0 : ℝ) < t := by linarith
    rw [deriv_rpowDivLog ht2, hθ t ht0, abelKernel]
    ring
  rw [primeRpowSumIoc_eq hx, hdecomp]
  ring

end

end RHTower
