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
    rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
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
        refine inv_anti₀ (by positivity) ?_
        exact mul_le_mul hmem (by nlinarith) (by positivity) (by linarith)
      · rw [Set.indicator_of_notMem (by simpa using hmem), norm_zero]
        exact logSqKernel_nonneg (by linarith)

/-! ## The continuous summatory identity -/

/-- The same kernel representation for the continuous logarithmic integral. -/
def logIntegralAux (X : ℝ) : ℝ :=
  (X - Real.exp 1) * (Real.log X)⁻¹
    + ∫ u in (Real.exp 1)..X, logSqKernel u * (u - Real.exp 1)

theorem continuousAt_logSqKernel_mul {t : ℝ} (ht : 1 < t) :
    ContinuousAt (fun u : ℝ => logSqKernel u * (u - Real.exp 1)) t :=
  (continuousAt_logSqKernel ht).mul (continuousAt_id.sub continuousAt_const)

theorem intervalIntegrable_logSqKernel_mul {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable (fun u : ℝ => logSqKernel u * (u - Real.exp 1)) volume a b := by
  refine ContinuousOn.intervalIntegrable (fun t ht => ?_)
  rw [Set.uIcc_eq_union] at ht
  have ht1 : 1 < t := by
    rcases ht with h | h
    · exact lt_of_lt_of_le ha h.1
    · exact lt_of_lt_of_le hb h.1
  exact (continuousAt_logSqKernel_mul ht1).continuousWithinAt

theorem hasDerivAt_logIntegralAux {X : ℝ} (hX : 1 < X) :
    HasDerivAt logIntegralAux (Real.log X)⁻¹ X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog : Real.log X ≠ 0 := ne_of_gt (Real.log_pos hX)
  have hd1 : HasDerivAt (fun u : ℝ => (u - Real.exp 1) * (Real.log u)⁻¹)
      ((Real.log X)⁻¹ + (X - Real.exp 1) * (-logSqKernel X)) X := by
    have ha : HasDerivAt (fun u : ℝ => u - Real.exp 1) 1 X :=
      (hasDerivAt_id X).sub_const _
    have hb : HasDerivAt (fun u : ℝ => (Real.log u)⁻¹) (-logSqKernel X) X := by
      have h := (Real.hasDerivAt_log (ne_of_gt hX0)).inv hlog
      refine h.congr_deriv ?_
      rw [logSqKernel]
      field_simp
    have h := ha.mul hb
    refine h.congr_deriv ?_
    ring
  have hd2 : HasDerivAt (fun Y : ℝ => ∫ u in (Real.exp 1)..Y,
      logSqKernel u * (u - Real.exp 1)) (logSqKernel X * (X - Real.exp 1)) X := by
    refine intervalIntegral.integral_hasDerivAt_right
      (intervalIntegrable_logSqKernel_mul one_lt_exp_one hX) ?_
      (continuousAt_logSqKernel_mul hX)
    refine ContinuousOn.stronglyMeasurableAtFilter isOpen_Ioi ?_ X hX
    intro t ht
    exact (continuousAt_logSqKernel_mul ht).continuousWithinAt
  have hsum := hd1.add hd2
  refine hsum.congr_deriv ?_
  ring

theorem logIntegralCount_eq_aux {X : ℝ} (hX : Real.exp 1 ≤ X) :
    logIntegralCount X = logIntegralAux X := by
  have hbase : logIntegralCount (Real.exp 1) = logIntegralAux (Real.exp 1) := by
    rw [logIntegralCount, logIntegralAux]
    simp
  rcases eq_or_lt_of_le hX with h | h
  · rw [← h, hbase]
  · have hderiv : ∀ t ∈ uIcc (Real.exp 1) X,
        HasDerivAt (fun u : ℝ => logIntegralCount u - logIntegralAux u) 0 t := by
      intro t ht
      rw [Set.uIcc_of_le hX] at ht
      have ht1 : 1 < t := lt_of_lt_of_le one_lt_exp_one ht.1
      have h := (hasDerivAt_logIntegralCount ht1).sub (hasDerivAt_logIntegralAux ht1)
      exact h.congr_deriv (by ring)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      (intervalIntegrable_const (c := (0 : ℝ)))
    simp only [intervalIntegral.integral_zero] at hFTC
    linarith [hFTC, hbase]

/-! ## Integrability of the kernel against the counting functions -/

theorem measurable_logSqKernel : Measurable logSqKernel :=
  ((measurable_id.mul ((Real.measurable_log).pow_const 2)).inv)

theorem chebyshevPsiReal_eq_zero_of_lt_two {t : ℝ} (ht : 1 ≤ t) (ht2 : t < 2) :
    chebyshevPsiReal t = 0 := by
  have hfloor : ⌊t⌋₊ = 1 := by
    refine Nat.floor_eq_iff (by linarith) |>.mpr ⟨by exact_mod_cast ht, ?_⟩
    push_cast
    linarith
  rw [chebyshevPsiReal, hfloor, chebyshevPsi_eq_sum_Ioc]
  simp [ArithmeticFunction.vonMangoldt_apply_one]

theorem logSqKernel_antitone {a b : ℝ} (ha : 1 < a) (hab : a ≤ b) :
    logSqKernel b ≤ logSqKernel a := by
  have ha0 : (0 : ℝ) < a := by linarith
  have hloga : (0 : ℝ) < Real.log a := Real.log_pos ha
  have hlogb : Real.log a ≤ Real.log b := Real.log_le_log ha0 hab
  rw [logSqKernel, logSqKernel]
  refine inv_anti₀ (by positivity) ?_
  exact mul_le_mul hab (by nlinarith) (by positivity) (by linarith)

theorem integrableOn_logSqKernel_mul_psi {X : ℝ} (_hX : 2 ≤ X) :
    IntegrableOn (fun t : ℝ => logSqKernel t * chebyshevPsiReal t) (Ioc 1 X) volume := by
  refine Integrable.mono' (g := fun _ : ℝ => logSqKernel 2 * chebyshevPsiReal X) ?_ ?_ ?_
  · refine integrableOn_const ?_ ?_
    · exact ne_of_lt (lt_of_le_of_lt (measure_mono Ioc_subset_Icc_self)
        (by simp [Real.volume_Icc]))
    · simp only [enorm_eq_nnnorm]
      exact ENNReal.coe_ne_top
  · exact (measurable_logSqKernel.mul
      (chebyshevPsiReal_mono.measurable)).aestronglyMeasurable.restrict
  · filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with t ht
    have ht1 : (1 : ℝ) < t := ht.1
    by_cases ht2 : t < 2
    · rw [chebyshevPsiReal_eq_zero_of_lt_two ht1.le ht2, mul_zero, norm_zero]
      have : (0 : ℝ) ≤ chebyshevPsiReal X := chebyshevPsiReal_nonneg X
      have hk : (0 : ℝ) ≤ logSqKernel 2 := logSqKernel_nonneg (by norm_num)
      positivity
    · rw [not_lt] at ht2
      have hknn : (0 : ℝ) ≤ logSqKernel t := logSqKernel_nonneg (by linarith)
      rw [Real.norm_of_nonneg (mul_nonneg hknn (chebyshevPsiReal_nonneg t))]
      refine mul_le_mul (logSqKernel_antitone (by norm_num) ht2)
        (chebyshevPsiReal_mono ht.2) (chebyshevPsiReal_nonneg t)
        (logSqKernel_nonneg (by norm_num))

/-! ## The exact difference identity -/

theorem two_le_exp_one : (2 : ℝ) ≤ Real.exp 1 := by
  have := Real.exp_one_gt_d9
  linarith

theorem integrableOn_logSqKernel_mul_sub {X : ℝ} (hX : Real.exp 1 ≤ X) :
    IntegrableOn (fun u : ℝ => logSqKernel u * (u - Real.exp 1)) (Ioc (Real.exp 1) X) volume := by
  rw [← intervalIntegrable_iff_integrableOn_Ioc_of_le hX]
  exact intervalIntegrable_logSqKernel_mul one_lt_exp_one (lt_of_lt_of_le one_lt_exp_one hX)

theorem primeTailCount_sub_logIntegralCount {X : ℝ} (hX : Real.exp 1 ≤ X) :
    primeTailCount X - logIntegralCount X
      = (chebyshevPsiReal X - X + Real.exp 1) * (Real.log X)⁻¹
        + (∫ t in Ioc (1 : ℝ) (Real.exp 1), logSqKernel t * chebyshevPsiReal t)
        + ∫ u in Ioc (Real.exp 1) X,
            logSqKernel u * (chebyshevPsiReal u - u + Real.exp 1) := by
  have hX2 : (2 : ℝ) ≤ X := le_trans two_le_exp_one hX
  have hXe : (1 : ℝ) < Real.exp 1 := one_lt_exp_one
  have hpsi := primeTailCount_eq_psi_integral hX2
  have hJ0 := logIntegralCount_eq_aux hX
  have hsplit : (∫ t in Ioc (1 : ℝ) X, logSqKernel t * chebyshevPsiReal t)
      = (∫ t in Ioc (1 : ℝ) (Real.exp 1), logSqKernel t * chebyshevPsiReal t)
        + ∫ t in Ioc (Real.exp 1) X, logSqKernel t * chebyshevPsiReal t := by
    have hunion : Ioc (1 : ℝ) X = Ioc 1 (Real.exp 1) ∪ Ioc (Real.exp 1) X := by
      rw [Set.Ioc_union_Ioc_eq_Ioc hXe.le hX]
    have hdisj : Disjoint (Ioc (1 : ℝ) (Real.exp 1)) (Ioc (Real.exp 1) X) := by
      rw [Set.disjoint_left]
      rintro t ⟨_, h2⟩ ⟨h3, _⟩
      exact absurd h3 (not_lt.mpr h2)
    have hint := integrableOn_logSqKernel_mul_psi hX2
    rw [hunion] at hint ⊢
    exact MeasureTheory.setIntegral_union hdisj measurableSet_Ioc
      (hint.mono_set Set.subset_union_left) (hint.mono_set Set.subset_union_right)
  have hIoc : (∫ u in (Real.exp 1)..X, logSqKernel u * (u - Real.exp 1))
      = ∫ u in Ioc (Real.exp 1) X, logSqKernel u * (u - Real.exp 1) :=
    intervalIntegral.integral_of_le hX
  have hcomb : (∫ t in Ioc (Real.exp 1) X, logSqKernel t * chebyshevPsiReal t)
      - (∫ u in Ioc (Real.exp 1) X, logSqKernel u * (u - Real.exp 1))
      = ∫ u in Ioc (Real.exp 1) X, logSqKernel u * (chebyshevPsiReal u - u + Real.exp 1) := by
    rw [← MeasureTheory.integral_sub
      ((integrableOn_logSqKernel_mul_psi hX2).mono_set (Ioc_subset_Ioc_left hXe.le))
      (integrableOn_logSqKernel_mul_sub hX)]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u _ => ?_)
    ring
  rw [hpsi, hJ0, logIntegralAux, hsplit, hIoc]
  linarith [hcomb]

/-! ## Elementary envelope facts -/

theorem mul_exp_neg_sqrt_log_eq {c X : ℝ} (hX : 0 < X) :
    X * Real.exp (-c * Real.sqrt (Real.log X))
      = Real.exp (Real.log X - c * Real.sqrt (Real.log X)) := by
  rw [Real.exp_sub, Real.exp_log hX, Real.exp_neg]
  field_simp
  rw [Real.exp_neg]
  ring

theorem tendsto_mul_exp_neg_sqrt_log {c : ℝ} :
    Tendsto (fun X : ℝ => X * Real.exp (-c * Real.sqrt (Real.log X))) atTop atTop := by
  have hpoly : Tendsto (fun u : ℝ => u ^ 2 - c * u) atTop atTop := by
    have : ∀ᶠ u : ℝ in atTop, u ^ 2 - c * u = u * (u - c) := by
      filter_upwards with u; ring
    refine Tendsto.congr' this.symm ?_
    exact tendsto_atTop_mul_atTop₀ tendsto_id (tendsto_atTop_add_const_right _ (-c) tendsto_id)
  have hsqrt : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  have hcomp : Tendsto (fun X : ℝ => Real.log X - c * Real.sqrt (Real.log X)) atTop atTop := by
    refine Tendsto.congr' ?_ (hpoly.comp hsqrt)
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with X hX
    have hlog : 0 ≤ Real.log X := Real.log_nonneg hX
    simp only [Function.comp_apply]
    rw [Real.sq_sqrt hlog]
  refine Tendsto.congr' ?_ (Real.tendsto_exp_atTop.comp hcomp)
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
  exact (mul_exp_neg_sqrt_log_eq hX).symm

theorem eventually_const_le_envelope {c K : ℝ} :
    ∀ᶠ X : ℝ in atTop, K ≤ X * Real.exp (-c * Real.sqrt (Real.log X)) :=
  tendsto_mul_exp_neg_sqrt_log.eventually_ge_atTop K

theorem eventually_sqrt_le_envelope {c : ℝ} (hc : 0 < c) :
    ∀ᶠ X : ℝ in atTop, Real.sqrt X ≤ X * Real.exp (-c * Real.sqrt (Real.log X)) := by
  have hsq : Tendsto (fun X : ℝ => Real.sqrt (Real.log X)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_gt_atTop (1 : ℝ), hsq.eventually_ge_atTop (2 * c)] with X hX hbig
  have hX0 : (0 : ℝ) < X := by linarith
  have hlog : 0 ≤ Real.log X := Real.log_nonneg hX.le
  have hsqrtX : Real.sqrt X = Real.exp (Real.log X / 2) := by
    rw [← Real.exp_log hX0, ← Real.exp_mul_self_sqrt] <;> try positivity
    rw [Real.exp_log hX0, ← Real.sqrt_mul_self (le_of_lt (Real.sqrt_pos.mpr hX0))]
    sorry
  sorry

end

end RHTower
