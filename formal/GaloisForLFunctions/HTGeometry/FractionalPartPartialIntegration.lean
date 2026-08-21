import GaloisForLFunctions.HTGeometry.LogTrigPowerPrimitives
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.MeasureTheory.Function.Floor

/-!
# Partial integration against the fractional part

The fractional part `{x} = x - ⌊x⌋` is not differentiable: it jumps down by `1` at every integer.
Partial integration of `∫ {x} f(x) dx` is therefore only legitimate on an interval free of jumps.
Carrying it out unit interval by unit interval and adding up produces, for a kernel `f` with first
primitive `P` and second primitive `W` on the positive ray,

`∫_1^{m+1} {x} f(x) dx = ∑_{k<m} P(k+2) - (W(m+1) - W(1))`.

The sum `∑ P(k+2)` is exactly the accumulated boundary contribution of the jumps.  Dropping it —
which is what treating `{x}` as an everywhere-differentiable function with derivative `1` amounts
to — leaves `-(W(m+1) - W(1))`, an expression with an entirely different asymptotic behaviour.
-/

open Real MeasureTheory Set intervalIntegral

namespace GaloisForLFunctions.HTGeometry

/-- **Partial integration on one unit interval.**  On `[n, n+1]` the fractional part agrees almost
everywhere with the smooth function `x - n`, so the classical formula applies and produces one
boundary term `P (n+1)`. -/
theorem integral_unit_fract_mul {f P W : ℝ → ℝ}
    (hP : ∀ x : ℝ, 0 < x → HasDerivAt P (f x) x)
    (hW : ∀ x : ℝ, 0 < x → HasDerivAt W (P x) x)
    (hf : ∀ u v : ℝ, 0 < u → 0 < v → IntervalIntegrable f volume u v)
    (hPi : ∀ u v : ℝ, 0 < u → 0 < v → IntervalIntegrable P volume u v)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ x in (n : ℝ)..((n : ℝ) + 1), Int.fract x * f x)
      = P ((n : ℝ) + 1) - (W ((n : ℝ) + 1) - W (n : ℝ)) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  have huIcc : Set.uIcc (n : ℝ) ((n : ℝ) + 1) = Set.Icc (n : ℝ) ((n : ℝ) + 1) :=
    Set.uIcc_of_le (by linarith)
  have hpos : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), 0 < x := by
    intro x hx
    rw [huIcc] at hx
    exact lt_of_lt_of_le hn0 hx.1
  -- replace the fractional part by the affine function on the interval
  have hae : (∫ x in (n : ℝ)..((n : ℝ) + 1), Int.fract x * f x)
      = ∫ x in (n : ℝ)..((n : ℝ) + 1), (x - (n : ℝ)) * f x := by
    refine intervalIntegral.integral_congr_ae ?_
    have hne : ∀ᵐ x : ℝ, x ≠ (n : ℝ) + 1 := by
      rw [Filter.eventually_iff, MeasureTheory.mem_ae_iff,
        show {x : ℝ | x ≠ (n : ℝ) + 1}ᶜ = {((n : ℝ) + 1)} by ext x; simp]
      exact MeasureTheory.measure_singleton _
    filter_upwards [hne] with x hx hmem
    rw [Set.uIoc_of_le (by linarith : (n : ℝ) ≤ (n : ℝ) + 1)] at hmem
    have hfl : ⌊x⌋ = (n : ℤ) := by
      refine Int.floor_eq_iff.mpr ⟨?_, ?_⟩
      · push_cast
        exact le_of_lt hmem.1
      · push_cast
        exact lt_of_le_of_ne hmem.2 hx
    have hfr : Int.fract x = x - (n : ℝ) := by
      have h : Int.fract x = x - (⌊x⌋ : ℝ) := rfl
      rw [h, hfl]
      push_cast
      ring_nf
    rw [hfr]
  rw [hae]
  -- classical partial integration on a jump-free interval
  have hu : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1),
      HasDerivAt (fun t : ℝ => t - (n : ℝ)) (1 : ℝ) x := by
    intro x _
    simpa using (hasDerivAt_id x).sub_const (n : ℝ)
  have hv : ∀ x ∈ Set.uIcc (n : ℝ) ((n : ℝ) + 1), HasDerivAt P (f x) x :=
    fun x hx => hP x (hpos x hx)
  have hibp := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivWithinAt
    (u := fun t : ℝ => t - (n : ℝ)) (u' := fun _ : ℝ => (1 : ℝ)) (v := P) (v' := f)
    (fun x hx => (hu x hx).hasDerivWithinAt) (fun x hx => (hv x hx).hasDerivWithinAt)
    (intervalIntegrable_const) (hf _ _ hn0 hn1)
  have hPint : (∫ x in (n : ℝ)..((n : ℝ) + 1), P x) = W ((n : ℝ) + 1) - W (n : ℝ) :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hW x (hpos x hx))
      (hPi _ _ hn0 hn1)
  rw [hibp]
  simp only [sub_self, zero_mul, sub_zero, one_mul]
  rw [hPint]
  ring_nf

/-- **The accumulated identity on `[1, m+1]`.**  Every unit interval contributes one boundary term;
the second primitive telescopes. -/
theorem integral_one_to_succ_fract_mul {f P W : ℝ → ℝ}
    (hP : ∀ x : ℝ, 0 < x → HasDerivAt P (f x) x)
    (hW : ∀ x : ℝ, 0 < x → HasDerivAt W (P x) x)
    (hf : ∀ u v : ℝ, 0 < u → 0 < v → IntervalIntegrable f volume u v)
    (hPi : ∀ u v : ℝ, 0 < u → 0 < v → IntervalIntegrable P volume u v)
    (hfract : ∀ u v : ℝ, 0 < u → 0 < v →
      IntervalIntegrable (fun x : ℝ => Int.fract x * f x) volume u v)
    (m : ℕ) :
    (∫ x in (1 : ℝ)..((m : ℝ) + 1), Int.fract x * f x)
      = (∑ k ∈ Finset.range m, P ((k : ℝ) + 2)) - (W ((m : ℝ) + 1) - W 1) := by
  have hpts : ∀ k : ℕ, (0 : ℝ) < (k : ℝ) + 1 := by
    intro k
    positivity
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun x : ℝ => Int.fract x * f x) (μ := volume) (a := fun k : ℕ => (k : ℝ) + 1) (n := m)
    (fun k _ => by
      have := hfract ((k : ℝ) + 1) (((k : ℕ) + 1 : ℕ) + 1 : ℝ) (hpts k) (by positivity)
      simpa using this)
  have hterm : ∀ k ∈ Finset.range m,
      (∫ x in ((k : ℝ) + 1)..(((k + 1 : ℕ) : ℝ) + 1), Int.fract x * f x)
        = P ((k : ℝ) + 2) + (W ((k : ℝ) + 1) - W ((k : ℝ) + 2)) := by
    intro k _
    have h := integral_unit_fract_mul hP hW hf hPi (n := k + 1) (Nat.le_add_left 1 k)
    have hcast : ((k + 1 : ℕ) : ℝ) = (k : ℝ) + 1 := by push_cast; ring
    rw [hcast] at h
    have hcast2 : ((k : ℝ) + 1) + 1 = (k : ℝ) + 2 := by ring
    rw [hcast2] at h
    rw [show (((k + 1 : ℕ) : ℝ) + 1) = (k : ℝ) + 2 by push_cast; ring]
    rw [h]
    ring_nf
  rw [Finset.sum_congr rfl hterm] at hsum
  rw [Finset.sum_add_distrib] at hsum
  have htel : ∀ M : ℕ, (∑ k ∈ Finset.range M, (W ((k : ℝ) + 1) - W ((k : ℝ) + 2)))
      = W 1 - W ((M : ℝ) + 1) := by
    intro M
    induction M with
    | zero => simp
    | succ p ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring_nf
  rw [htel m] at hsum
  simp only [Nat.cast_zero, zero_add] at hsum
  rw [← hsum]
  ring_nf

/-! ## The oscillatory power kernels -/

theorem norm_fract_le (x : ℝ) : ‖Int.fract x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg x)]
  exact (Int.fract_lt_one x).le

theorem intervalIntegrable_fract_mul {f : ℝ → ℝ} {u v : ℝ}
    (hf : IntervalIntegrable f volume u v) :
    IntervalIntegrable (fun x : ℝ => Int.fract x * f x) volume u v :=
  ⟨hf.1.bdd_mul (measurable_fract.aestronglyMeasurable)
      (Filter.Eventually.of_forall norm_fract_le),
   hf.2.bdd_mul (measurable_fract.aestronglyMeasurable)
      (Filter.Eventually.of_forall norm_fract_le)⟩

/-- **Corrected partial integration for the cosine kernel.** -/
theorem integral_one_to_succ_fract_mul_cos_log {c b : ℝ} (h : c ^ 2 + b ^ 2 ≠ 0)
    (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) (m : ℕ) :
    (∫ x in (1 : ℝ)..((m : ℝ) + 1), Int.fract x * (x ^ (c - 1) * Real.cos (b * Real.log x)))
      = (∑ k ∈ Finset.range m, cosLogPrimitive c b ((k : ℝ) + 2))
        - (cosLogSecondPrimitive c b ((m : ℝ) + 1) - cosLogSecondPrimitive c b 1) :=
  integral_one_to_succ_fract_mul
    (fun _ hx => hasDerivAt_cosLogPrimitive hx h)
    (fun _ hx => hasDerivAt_cosLogSecondPrimitive hx h h')
    (fun _ _ hu hv => intervalIntegrable_rpow_mul_cos_log hu hv)
    (fun _ _ hu hv => ((continuousOn_cosLogPrimitive c b).mono
      (uIcc_subset_Ioi hu hv)).intervalIntegrable)
    (fun _ _ hu hv => intervalIntegrable_fract_mul (intervalIntegrable_rpow_mul_cos_log hu hv))
    m

/-- **Corrected partial integration for the sine kernel.** -/
theorem integral_one_to_succ_fract_mul_sin_log {c b : ℝ} (h : c ^ 2 + b ^ 2 ≠ 0)
    (h' : (c + 1) ^ 2 + b ^ 2 ≠ 0) (m : ℕ) :
    (∫ x in (1 : ℝ)..((m : ℝ) + 1), Int.fract x * (x ^ (c - 1) * Real.sin (b * Real.log x)))
      = (∑ k ∈ Finset.range m, sinLogPrimitive c b ((k : ℝ) + 2))
        - (sinLogSecondPrimitive c b ((m : ℝ) + 1) - sinLogSecondPrimitive c b 1) :=
  integral_one_to_succ_fract_mul
    (fun _ hx => hasDerivAt_sinLogPrimitive hx h)
    (fun _ hx => hasDerivAt_sinLogSecondPrimitive hx h h')
    (fun _ _ hu hv => intervalIntegrable_rpow_mul_sin_log hu hv)
    (fun _ _ hu hv => ((continuousOn_sinLogPrimitive c b).mono
      (uIcc_subset_Ioi hu hv)).intervalIntegrable)
    (fun _ _ hu hv => intervalIntegrable_fract_mul (intervalIntegrable_rpow_mul_sin_log hu hv))
    m

end GaloisForLFunctions.HTGeometry
