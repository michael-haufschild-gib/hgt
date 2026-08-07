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
  have hC0 : 0 ≤ abelKernelConst a := abelKernelConst_nonneg a
  have hJ := HTGeometry.tendsto_logRpowIntegral ha0
  have hgint : ∀ x : ℝ, 2 ≤ x →
      IntervalIntegrable (fun t : ℝ => g t * abelKernel a t) volume 2 x := by
    intro x hx
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hx]
    exact ((g_int x hx).mul_continuousOn
      (fun t ht => (continuousAt_abelKernel (a := a) ht.1).continuousWithinAt)
      isCompact_Icc).mono_set Ioc_subset_Icc_self
  rw [NormedAddGroup.tendsto_nhds_zero]
  intro ε hε
  set C : ℝ := abelKernelConst a with hC
  set δ : ℝ := ε / (4 * (C + 1)) with hδ
  have hδ0 : 0 < δ := by
    rw [hδ]
    positivity
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp (NormedAddGroup.tendsto_nhds_zero.mp hgt δ hδ0)
  set T : ℝ := max T₀ 2 with hT
  have hT2 : (2 : ℝ) ≤ T := le_max_right _ _
  have hTg : ∀ t : ℝ, T ≤ t → |g t| ≤ δ := by
    intro t ht
    have := hT₀ t (le_trans (le_max_left _ _) ht)
    rw [Real.norm_eq_abs] at this
    exact this.le
  set A : ℝ := ∫ t in (2 : ℝ)..T, g t * abelKernel a t with hA
  -- the head is a constant, the tail is `C δ` times the logarithmic power integral
  have hhead : Tendsto (fun x : ℝ => |A| * (a * Real.log x) / x ^ a) atTop (nhds 0) := by
    have hlogdiv : Tendsto (fun x : ℝ => Real.log x / x ^ a) atTop (nhds 0) :=
      (isLittleO_log_rpow_atTop ha0).tendsto_div_nhds_zero
    have h := (hlogdiv.const_mul (|A| * a))
    rw [mul_zero] at h
    refine h.congr fun x => ?_
    ring
  have hsmallhead : ∀ᶠ x : ℝ in atTop, |A| * (a * Real.log x) / x ^ a < ε / 2 :=
    (NormedAddGroup.tendsto_nhds_zero.mp hhead (ε / 2) (by linarith)).mono fun x hx => by
      rw [Real.norm_eq_abs] at hx
      exact lt_of_le_of_lt (le_abs_self _) hx
  have hJbound : ∀ᶠ x : ℝ in atTop,
      HTGeometry.logRpowIntegral a x * (a * Real.log x) / x ^ a < 2 :=
    hJ.eventually (eventually_lt_nhds (by norm_num))
  filter_upwards [eventually_ge_atTop T, hsmallhead, hJbound] with x hx hxhead hxJ
  have hx2 : (2 : ℝ) ≤ x := le_trans hT2 hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
  have hXpos : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx0 a
  -- split the remainder
  have hsplit : (∫ t in (2 : ℝ)..x, g t * abelKernel a t)
      = A + ∫ t in T..x, g t * abelKernel a t := by
    rw [hA]
    exact (intervalIntegral.integral_add_adjacent_intervals (hgint T hT2)
      ((hgint x hx2).mono_set (by
        rw [uIcc_of_le hx, uIcc_of_le hx2]
        exact Icc_subset_Icc hT2 le_rfl))).symm
  -- the tail bound
  have hmajor : IntervalIntegrable
      (fun t : ℝ => C * δ * (t ^ (a - 1) / Real.log t)) volume T x :=
    ((HTGeometry.intervalIntegrable_rpowDivLog a hT2 hx2).const_mul _)
  have htailint : IntervalIntegrable (fun t : ℝ => g t * abelKernel a t) volume T x :=
    (hgint x hx2).mono_set (by
      rw [uIcc_of_le hx, uIcc_of_le hx2]
      exact Icc_subset_Icc hT2 le_rfl)
  have hpt : ∀ t ∈ Icc T x, |g t * abelKernel a t| ≤ C * δ * (t ^ (a - 1) / Real.log t) := by
    intro t ht
    have ht2 : (2 : ℝ) ≤ t := le_trans hT2 ht.1
    have hP : (0 : ℝ) ≤ t ^ (a - 1) / Real.log t := by
      have h1 : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg (by linarith) _
      have h2 : 0 < Real.log t := Real.log_pos (by linarith)
      positivity
    rw [abs_mul]
    calc |g t| * |abelKernel a t|
        ≤ δ * (C * (t ^ (a - 1) / Real.log t)) := by
          refine mul_le_mul (hTg t ht.1) (abs_abelKernel_le ht2) (abs_nonneg _) hδ0.le
      _ = C * δ * (t ^ (a - 1) / Real.log t) := by ring
  have hupper : (∫ t in T..x, g t * abelKernel a t) ≤
      ∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t) :=
    intervalIntegral.integral_mono_on hx htailint hmajor fun t ht =>
      le_trans (le_abs_self _) (hpt t ht)
  have hlower : (∫ t in T..x, -(C * δ * (t ^ (a - 1) / Real.log t))) ≤
      ∫ t in T..x, g t * abelKernel a t :=
    intervalIntegral.integral_mono_on hx hmajor.neg htailint fun t ht =>
      neg_le_of_abs_le (hpt t ht)
  rw [intervalIntegral.integral_neg] at hlower
  have habs : |∫ t in T..x, g t * abelKernel a t| ≤
      ∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t) := abs_le.mpr ⟨hlower, hupper⟩
  have hval : (∫ t in T..x, C * δ * (t ^ (a - 1) / Real.log t)) ≤
      C * δ * HTGeometry.logRpowIntegral a x := by
    rw [intervalIntegral.integral_const_mul]
    have hhd : 0 ≤ ∫ t in (2 : ℝ)..T, t ^ (a - 1) / Real.log t :=
      HTGeometry.logRpowIntegral_nonneg (le_refl (2 : ℝ)) hT2
    have hsp : HTGeometry.logRpowIntegral a x =
        (∫ t in (2 : ℝ)..T, t ^ (a - 1) / Real.log t) + ∫ t in T..x, t ^ (a - 1) / Real.log t :=
      HTGeometry.logRpowIntegral_split hT2 hx
    have hnn : (0 : ℝ) ≤ C * δ := by positivity
    nlinarith [hhd, hsp]
  -- assemble
  have hweight : (0 : ℝ) < a * Real.log x / x ^ a := by positivity
  have hEbound : |∫ t in (2 : ℝ)..x, g t * abelKernel a t| ≤
      |A| + C * δ * HTGeometry.logRpowIntegral a x := by
    rw [hsplit]
    have habsadd : |A + ∫ t in T..x, g t * abelKernel a t| ≤
        |A| + |∫ t in T..x, g t * abelKernel a t| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · linarith [neg_abs_le A, neg_abs_le (∫ t in T..x, g t * abelKernel a t)]
      · linarith [le_abs_self A, le_abs_self (∫ t in T..x, g t * abelKernel a t)]
    linarith [habs, hval, habsadd]
  rw [Real.norm_eq_abs, abs_div, abs_mul, abs_of_pos hXpos,
    abs_of_pos (show (0:ℝ) < a * Real.log x by positivity)]
  have hstep : |∫ t in (2 : ℝ)..x, g t * abelKernel a t| * (a * Real.log x) / x ^ a ≤
      (|A| + C * δ * HTGeometry.logRpowIntegral a x) * (a * Real.log x) / x ^ a := by
    have := mul_le_mul_of_nonneg_right hEbound (show (0:ℝ) ≤ a * Real.log x by positivity)
    exact div_le_div_of_nonneg_right this hXpos.le
  have hexpand : (|A| + C * δ * HTGeometry.logRpowIntegral a x) * (a * Real.log x) / x ^ a
      = |A| * (a * Real.log x) / x ^ a
        + C * δ * (HTGeometry.logRpowIntegral a x * (a * Real.log x) / x ^ a) := by
    ring
  rw [hexpand] at hstep
  have hCδ : C * δ * (HTGeometry.logRpowIntegral a x * (a * Real.log x) / x ^ a) ≤ ε / 2 := by
    have hnn : (0 : ℝ) ≤ C * δ := by positivity
    have h1 : C * δ * (HTGeometry.logRpowIntegral a x * (a * Real.log x) / x ^ a) ≤
        C * δ * 2 := by
      exact mul_le_mul_of_nonneg_left hxJ.le hnn
    have hCC : (0 : ℝ) < 4 * (C + 1) := by linarith
    have hδmul : δ * (4 * (C + 1)) = ε := by
      rw [hδ, div_mul_cancel₀ _ (ne_of_gt hCC)]
    have h2 : C * δ * 2 ≤ ε / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      nlinarith [hδ0, hC0, hδmul]
    linarith
  linarith

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
