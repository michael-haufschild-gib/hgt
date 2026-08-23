import GaloisForLFunctions.RHTower.PrimeVacuumCurrent
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# Transferring the Chebyshev error to the log-divided counting function

Dividing by the logarithm is an integration against the kernel `1/(t log^2 t)`:
`1/log n = 1/log X + ∫_n^X dt/(t log^2 t)` for `n ≤ X`.  Summing this identity against the von
Mangoldt weights, and integrating it against Lebesgue measure, expresses both the arithmetic and
the continuous counting function through the same kernel, with `psi` respectively the identity in
the integrand.  Their difference is therefore controlled by the Chebyshev error alone, and the
quantitative prime number theorem transfers verbatim to the log-divided counting function.
-/

namespace RHTower

open MeasureTheory Set Filter Topology

noncomputable section

/-- The kernel that undoes division by a logarithm. -/
def logSqKernel (t : ℝ) : ℝ := (t * (Real.log t) ^ 2)⁻¹

theorem hasDerivAt_neg_inv_log' {x : ℝ} (hx : 0 < x) (hne : Real.log x ≠ 0) :
    HasDerivAt (fun t : ℝ => -(Real.log t)⁻¹) (logSqKernel x) x := by
  have h := ((Real.hasDerivAt_log (ne_of_gt hx)).inv hne).neg
  refine h.congr_deriv ?_
  rw [logSqKernel]
  field_simp

theorem logSqKernel_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ logSqKernel t := by
  rw [logSqKernel]
  exact inv_nonneg.mpr (mul_nonneg ht.le (sq_nonneg _))

theorem continuousAt_logSqKernel {t : ℝ} (ht : 1 < t) : ContinuousAt logSqKernel t := by
  have ht0 : (0 : ℝ) < t := by linarith
  have hlog : Real.log t ≠ 0 := ne_of_gt (Real.log_pos ht)
  refine ContinuousAt.inv₀ ?_ (by positivity)
  exact continuousAt_id.mul (((Real.continuousAt_log (ne_of_gt ht0))).pow 2)

theorem intervalIntegrable_logSqKernel {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable logSqKernel volume a b := by
  refine ContinuousOn.intervalIntegrable (fun t ht => ?_)
  rw [Set.uIcc_eq_union] at ht
  have ht1 : 1 < t := by
    rcases ht with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  exact (continuousAt_logSqKernel ht1).continuousWithinAt

/-- **The division-by-logarithm identity.**  `1/log y = 1/log X + ∫_y^X dt/(t log^2 t)`. -/
theorem inv_log_eq_add_integral {y X : ℝ} (hy : 1 < y) (hyX : y ≤ X) :
    (Real.log y)⁻¹ = (Real.log X)⁻¹ + ∫ t in y..X, logSqKernel t := by
  have hX : 1 < X := lt_of_lt_of_le hy hyX
  have hderiv : ∀ t ∈ uIcc y X, HasDerivAt (fun s : ℝ => -(Real.log s)⁻¹) (logSqKernel t) t := by
    intro t ht
    rw [Set.uIcc_of_le hyX] at ht
    have ht1 : 1 < t := lt_of_lt_of_le hy ht.1
    exact hasDerivAt_neg_inv_log' (by linarith) (ne_of_gt (Real.log_pos ht1))
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_logSqKernel hy hX)
  linarith [h]

/-! ## The arithmetic summatory identity -/

theorem sum_Ioc_one_eq {N : ℕ} (f : ℕ → ℝ) (h1 : f 1 = 0) (hN : 1 ≤ N) :
    ∑ n ∈ Finset.Ioc 0 N, f n = ∑ n ∈ Finset.Ioc 1 N, f n := by
  rw [← Finset.sum_Ioc_consecutive f (by norm_num : (0:ℕ) ≤ 1) hN]
  simp [h1]

theorem primeTailCount_eq_sum_Ioc_one {X : ℝ} (hX : 2 ≤ X) :
    primeTailCount X
      = ∑ n ∈ Finset.Ioc 1 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n)⁻¹ := by
  have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast le_trans (by norm_num) hX)
  rw [primeTailCount]
  have hdiv : ∀ n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n
      = (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n)⁻¹ := fun n => div_eq_mul_inv _ _
  simp only [hdiv]
  exact sum_Ioc_one_eq _ (by simp [ArithmeticFunction.vonMangoldt_apply_one]) hN

theorem chebyshevPsi_eq_sum_Ioc_one {N : ℕ} (hN : 1 ≤ N) :
    chebyshevPsi N = ∑ n ∈ Finset.Ioc 1 N, (ArithmeticFunction.vonMangoldt n : ℝ) := by
  rw [chebyshevPsi_eq_sum_Ioc]
  exact sum_Ioc_one_eq _ (by simp [ArithmeticFunction.vonMangoldt_apply_one]) hN

theorem integral_indicator_Ici_logSqKernel {n : ℕ} {X : ℝ} (hn : 2 ≤ n) (_hnX : (n : ℝ) ≤ X) :
    (∫ t in Ioc (1 : ℝ) X, Set.indicator (Ici (n : ℝ)) logSqKernel t)
      = ∫ t in Ioc (n : ℝ) X, logSqKernel t := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [MeasureTheory.setIntegral_indicator measurableSet_Ici]
  have hset : Ioc (1 : ℝ) X ∩ Ici (n : ℝ) = Icc (n : ℝ) X := by
    ext t
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩
      exact ⟨h3, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨⟨lt_of_lt_of_le hn1 h1, h2⟩, h1⟩
  rw [hset, MeasureTheory.integral_Icc_eq_integral_Ioc]

/-- **The summatory identity.**  Dividing by the logarithm is integration of `psi` against the
kernel `1/(t log^2 t)`. -/
theorem primeTailCount_eq_psi_integral {X : ℝ} (hX : 2 ≤ X) :
    primeTailCount X
      = chebyshevPsiReal X * (Real.log X)⁻¹
        + ∫ t in Ioc (1 : ℝ) X, logSqKernel t * chebyshevPsiReal t := by
  have hX1 : (1 : ℝ) < X := by linarith
  have hN : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast le_trans (by norm_num) hX)
  have hfloorX : ((⌊X⌋₊ : ℕ) : ℝ) ≤ X := Nat.floor_le (by linarith)
  have hterm : ∀ n ∈ Finset.Ioc 1 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log n)⁻¹
        = (ArithmeticFunction.vonMangoldt n : ℝ) * (Real.log X)⁻¹
          + (ArithmeticFunction.vonMangoldt n : ℝ)
            * ∫ t in Ioc (1 : ℝ) X, Set.indicator (Ici (n : ℝ)) logSqKernel t := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn2 : 2 ≤ n := hn.1
    have hnX : (n : ℝ) ≤ X := le_trans (by exact_mod_cast hn.2) hfloorX
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn2
    rw [integral_indicator_Ici_logSqKernel hn2 hnX,
      ← intervalIntegral.integral_of_le hnX,
      inv_log_eq_add_integral hn1 hnX]
    ring
  rw [primeTailCount_eq_sum_Ioc_one hX, Finset.sum_congr rfl hterm, Finset.sum_add_distrib,
    ← Finset.sum_mul, ← chebyshevPsi_eq_sum_Ioc_one hN]
  congr 1
  have hmove : ∀ n ∈ Finset.Ioc 1 ⌊X⌋₊,
      (ArithmeticFunction.vonMangoldt n : ℝ)
          * ∫ t in Ioc (1 : ℝ) X, Set.indicator (Ici (n : ℝ)) logSqKernel t
        = ∫ t in Ioc (1 : ℝ) X,
            (ArithmeticFunction.vonMangoldt n : ℝ) * Set.indicator (Ici (n : ℝ)) logSqKernel t :=
    fun n _ => (MeasureTheory.integral_const_mul _ _).symm
  rw [Finset.sum_congr rfl hmove, ← MeasureTheory.integral_finsetSum]
  · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
    have hsplit : ∀ n ∈ Finset.Ioc 1 ⌊X⌋₊,
        (ArithmeticFunction.vonMangoldt n : ℝ) * Set.indicator (Ici (n : ℝ)) logSqKernel t
          = if n ≤ ⌊t⌋₊ then logSqKernel t * (ArithmeticFunction.vonMangoldt n : ℝ) else 0 := by
      intro n _
      by_cases hmem : (n : ℝ) ≤ t
      · rw [Set.indicator_of_mem (by simpa using hmem), if_pos (Nat.le_floor hmem)]
        ring
      · rw [Set.indicator_of_notMem (by simpa using hmem), if_neg ?_]
        · ring
        · intro hcon
          exact hmem (le_trans (by exact_mod_cast hcon) (Nat.floor_le (by linarith [ht.1])))
    rw [Finset.sum_congr rfl hsplit, Finset.sum_ite_eq_sum_filter]
    have hfilter : (Finset.Ioc 1 ⌊X⌋₊).filter (fun n => n ≤ ⌊t⌋₊) = Finset.Ioc 1 ⌊t⌋₊ := by
      ext n
      simp only [Finset.mem_filter, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨h1, _⟩, h3⟩
        exact ⟨h1, h3⟩
      · rintro ⟨h1, h2⟩
        exact ⟨⟨h1, le_trans h2 (Nat.floor_mono ht.2)⟩, h2⟩
    rw [hfilter, ← Finset.mul_sum,
      ← chebyshevPsi_eq_sum_Ioc_one (Nat.le_floor (by exact_mod_cast le_of_lt ht.1))]
    rfl
  · intro n hn
    rw [Finset.mem_Ioc] at hn
    have hn2 : 2 ≤ n := hn.1
    have hn1 : (1 : ℝ) < (n : ℝ) := by exact_mod_cast hn2
    refine MeasureTheory.Integrable.const_mul ?_ _
    refine Integrable.mono' (g := fun _ : ℝ => logSqKernel (n : ℝ)) ?_ ?_ ?_
    · refine integrableOn_const ?_ ?_
      · exact ne_of_lt (lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self)
          (by simp [Real.volume_Icc]))
      · simp [enorm_eq_nnnorm]
    · exact (((measurable_id.mul ((Real.measurable_log).pow_const 2)).inv).indicator
        measurableSet_Ici).aestronglyMeasurable.restrict
    · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
      by_cases hmem : (n : ℝ) ≤ t
      · rw [Set.indicator_of_mem (by simpa using hmem),
          Real.norm_of_nonneg (logSqKernel_nonneg (by linarith))]
        have hlog : Real.log (n : ℝ) ≤ Real.log t := Real.log_le_log (by linarith) hmem
        have hlogn : (0 : ℝ) < Real.log (n : ℝ) := Real.log_pos hn1
        rw [logSqKernel, logSqKernel]
        refine inv_le_inv_of_le (by positivity) ?_
        exact mul_le_mul hmem (by nlinarith) (by positivity) (by linarith)
      · rw [Set.indicator_of_notMem (by simpa using hmem), norm_zero]
        exact logSqKernel_nonneg (by linarith)

end

end RHTower
