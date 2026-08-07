import GaloisForLFunctions.HTGeometry.LogWeightedRpowIntegral
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Abel summation of a prime power against the Chebyshev function

For `0 < a < 1` the weight `f(t) = t^(a-1)/log t` turns the prime log mass into the prime power:
`f(p) log p = p^(a-1)`.  Abel summation against `θ` gives

```text
∑_{2 < p ≤ x} p^(a-1) = f(x) θ(x) - f(2) θ(2) - ∫_2^x f'(t) θ(t) dt,
```

and `t f'(t) = (a-1) t^(a-1)/log t - t^(a-1)/log²t` is exactly the pair of logarithmic power
integrals.
-/

open Filter Topology Set MeasureTheory intervalIntegral

namespace RHTower

noncomputable section

/-! ## The two summands -/

/-- The prime logarithm mass. -/
def primeLogWeight (n : ℕ) : ℝ := if n.Prime then Real.log n else 0

theorem sum_primeLogWeight_eq_theta (t : ℝ) :
    ∑ k ∈ Finset.Icc 0 ⌊t⌋₊, primeLogWeight k = Chebyshev.theta t := by
  rw [Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  exact Finset.sum_congr rfl fun n _ => by rw [primeLogWeight]

/-- The Abel weight `t^(a-1)/log t`. -/
def rpowDivLog (a t : ℝ) : ℝ := t ^ (a - 1) / Real.log t

/-- The derivative of the Abel weight. -/
def derivRpowDivLog (a t : ℝ) : ℝ :=
  ((a - 1) * t ^ (a - 2) * Real.log t - t ^ (a - 1) * t⁻¹) / Real.log t ^ 2

theorem hasDerivAt_rpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    HasDerivAt (rpowDivLog a) (derivRpowDivLog a t) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hnum : HasDerivAt (fun s : ℝ => s ^ (a - 1)) ((a - 1) * t ^ (a - 2)) t := by
    have h := Real.hasDerivAt_rpow_const (x := t) (p := a - 1) (Or.inl (ne_of_gt ht0))
    rw [show a - 1 - 1 = a - 2 by ring] at h
    exact h
  have hden : HasDerivAt Real.log t⁻¹ t := Real.hasDerivAt_log (ne_of_gt ht0)
  have h := hnum.div hden (ne_of_gt hlogpos)
  exact h

theorem deriv_rpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    deriv (rpowDivLog a) t = derivRpowDivLog a t :=
  (hasDerivAt_rpowDivLog ht).deriv

theorem differentiableAt_rpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    DifferentiableAt ℝ (rpowDivLog a) t :=
  (hasDerivAt_rpowDivLog ht).differentiableAt

/-- The scaled derivative is the difference of the two logarithmic power weights. -/
theorem mul_derivRpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    t * derivRpowDivLog a t =
      (a - 1) * (t ^ (a - 1) / Real.log t) - t ^ (a - 1) / Real.log t ^ 2 := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hpow : t * t ^ (a - 2) = t ^ (a - 1) := by
    have h := Real.rpow_add ht0 1 (a - 2)
    rw [Real.rpow_one] at h
    rw [show a - 1 = 1 + (a - 2) by ring, h]
  rw [derivRpowDivLog]
  field_simp
  linear_combination ((a - 1) * Real.log t) * hpow

/-! ## Continuity and integrability of the derivative -/

theorem continuousAt_derivRpowDivLog {a t : ℝ} (ht : 2 ≤ t) :
    ContinuousAt (derivRpowDivLog a) t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlogpos : 0 < Real.log t := Real.log_pos (by linarith)
  have hne : Real.log t ^ 2 ≠ 0 := by positivity
  refine ContinuousAt.div ?_ ((Real.continuousAt_log (ne_of_gt ht0)).pow 2) hne
  refine ContinuousAt.sub ?_ ?_
  · exact ((continuousAt_const).mul
      (Real.continuousAt_rpow_const t (a - 2) (Or.inl (ne_of_gt ht0)))).mul
      (Real.continuousAt_log (ne_of_gt ht0))
  · exact (Real.continuousAt_rpow_const t (a - 1) (Or.inl (ne_of_gt ht0))).mul
      (continuousAt_inv₀ (ne_of_gt ht0))

theorem integrableOn_derivRpowDivLog {a x : ℝ} (_hx : 2 ≤ x) :
    IntegrableOn (deriv (rpowDivLog a)) (Icc 2 x) := by
  have hcont : ContinuousOn (derivRpowDivLog a) (Icc 2 x) := fun t ht =>
    (continuousAt_derivRpowDivLog (a := a) ht.1).continuousWithinAt
  have hint : IntegrableOn (derivRpowDivLog a) (Icc 2 x) := hcont.integrableOn_Icc
  refine hint.congr_fun (fun t ht => ?_) measurableSet_Icc
  exact (deriv_rpowDivLog (a := a) ht.1).symm

/-! ## The Abel identity -/

/-- The prime power sum up to `x`, omitting the prime `2`. -/
def primeRpowSumIoc (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.Ioc 2 ⌊x⌋₊, (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) else 0)

theorem rpowDivLog_mul_primeLogWeight {a : ℝ} {k : ℕ} (hk : 2 < k) :
    rpowDivLog a (k : ℝ) * primeLogWeight k =
      (if k.Prime then ((k : ℕ) : ℝ) ^ (a - 1) else 0) := by
  rw [rpowDivLog, primeLogWeight]
  by_cases hp : k.Prime
  · have hk2 : (1 : ℝ) < (k : ℝ) := by exact_mod_cast hk.trans_le' (by norm_num)
    have hlog : Real.log (k : ℝ) ≠ 0 := ne_of_gt (Real.log_pos hk2)
    rw [if_pos hp, if_pos hp, div_mul_cancel₀ _ hlog]
  · rw [if_neg hp, if_neg hp, mul_zero]

/-- **Abel summation of the prime power against the Chebyshev theta function.** -/
theorem primeRpowSumIoc_eq {a x : ℝ} (hx : 2 ≤ x) :
    primeRpowSumIoc a x =
      rpowDivLog a x * Chebyshev.theta x - rpowDivLog a 2 * Chebyshev.theta 2 -
        ∫ t in Ioc (2 : ℝ) x, deriv (rpowDivLog a) t * Chebyshev.theta t := by
  have habel := sum_mul_eq_sub_sub_integral_mul (𝕜 := ℝ) primeLogWeight (f := rpowDivLog a)
    (a := (2 : ℝ)) (b := x) (by norm_num) hx
    (fun t ht => differentiableAt_rpowDivLog ht.1) (integrableOn_derivRpowDivLog hx)
  simp only [sum_primeLogWeight_eq_theta] at habel
  rw [show (⌊(2 : ℝ)⌋₊) = 2 from by norm_num] at habel
  rw [primeRpowSumIoc, ← habel]
  exact Finset.sum_congr rfl fun k hk =>
    (rpowDivLog_mul_primeLogWeight (Finset.mem_Ioc.mp hk).1).symm

/-! ## The Abel kernel -/

/-- The scaled derivative appearing in the Abel integral. -/
def abelKernel (a t : ℝ) : ℝ := t * derivRpowDivLog a t

theorem abelKernel_eq {a t : ℝ} (ht : 2 ≤ t) :
    abelKernel a t =
      (a - 1) * (t ^ (a - 1) / Real.log t) - t ^ (a - 1) / Real.log t ^ 2 :=
  mul_derivRpowDivLog ht

/-- The comparison constant of the Abel kernel. -/
def abelKernelConst (a : ℝ) : ℝ := |a - 1| + 1 / Real.log 2

theorem abelKernelConst_nonneg (a : ℝ) : 0 ≤ abelKernelConst a := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  rw [abelKernelConst]
  positivity

theorem abs_abelKernel_le {a t : ℝ} (ht : 2 ≤ t) :
    |abelKernel a t| ≤ abelKernelConst a * (t ^ (a - 1) / Real.log t) := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlogt : Real.log 2 ≤ Real.log t := Real.log_le_log (by norm_num) ht
  have hlogpos : 0 < Real.log t := lt_of_lt_of_le hlog2 hlogt
  have hP : (0 : ℝ) ≤ t ^ (a - 1) / Real.log t := by
    have : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
    positivity
  have hQ : t ^ (a - 1) / Real.log t ^ 2 ≤ 1 / Real.log 2 * (t ^ (a - 1) / Real.log t) := by
    rw [pow_two, ← div_div, one_div, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left hP hlog2 hlogt
  have hQ0 : (0 : ℝ) ≤ t ^ (a - 1) / Real.log t ^ 2 := by
    have : (0 : ℝ) ≤ t ^ (a - 1) := Real.rpow_nonneg ht0.le _
    positivity
  rw [abelKernel_eq ht, abelKernelConst, add_mul]
  have hlead : |(a - 1) * (t ^ (a - 1) / Real.log t)| = |a - 1| * (t ^ (a - 1) / Real.log t) := by
    rw [abs_mul, abs_of_nonneg hP]
  have habs := abs_sub (((a - 1) * (t ^ (a - 1) / Real.log t)))
    (t ^ (a - 1) / Real.log t ^ 2)
  rw [abs_of_nonneg hQ0] at habs
  rw [hlead] at habs
  linarith

theorem continuousAt_abelKernel {a t : ℝ} (ht : 2 ≤ t) :
    ContinuousAt (abelKernel a) t :=
  continuousAt_id.mul (continuousAt_derivRpowDivLog ht)

theorem continuousOn_abelKernel (a : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    ContinuousOn (abelKernel a) (uIcc u v) := fun _ ht =>
  (continuousAt_abelKernel (a := a) (HTGeometry.two_le_of_mem_uIcc hu hv ht)).continuousWithinAt

theorem intervalIntegrable_abelKernel (a : ℝ) {u v : ℝ} (hu : 2 ≤ u) (hv : 2 ≤ v) :
    IntervalIntegrable (abelKernel a) volume u v :=
  (continuousOn_abelKernel a hu hv).intervalIntegrable

/-- The Abel kernel integrates to the two logarithmic power integrals. -/
theorem integral_abelKernel {a x : ℝ} (hx : 2 ≤ x) :
    (∫ t in (2 : ℝ)..x, abelKernel a t)
      = (a - 1) * HTGeometry.logRpowIntegral a x - HTGeometry.logSqRpowIntegral a x := by
  have hcongr : (∫ t in (2 : ℝ)..x, abelKernel a t) =
      ∫ t in (2 : ℝ)..x, ((a - 1) * (t ^ (a - 1) / Real.log t) - t ^ (a - 1) / Real.log t ^ 2) := by
    refine intervalIntegral.integral_congr fun t ht => ?_
    exact abelKernel_eq (HTGeometry.two_le_of_mem_uIcc (le_refl (2 : ℝ)) hx ht)
  rw [hcongr, intervalIntegral.integral_sub
    ((HTGeometry.intervalIntegrable_rpowDivLog a (le_refl (2 : ℝ)) hx).const_mul _)
    (HTGeometry.intervalIntegrable_rpowDivLogSq a (le_refl (2 : ℝ)) hx),
    intervalIntegral.integral_const_mul]
  rfl

end

end RHTower
