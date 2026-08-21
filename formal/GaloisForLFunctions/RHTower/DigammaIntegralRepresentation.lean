import GaloisForLFunctions.RHTower.EulerMascheroniGaussKernel
import GaloisForLFunctions.HTGeometry.DigammaGaussSeries

/-!
# Gauss's integral representation of the digamma function

For `Re s > 0`,

`ψ(s) = ∫_0^∞ ( e^{-u}/u - e^{-su}/(1 - e^{-u}) ) du`.

The corpus already proves the Gauss *series* `ψ(s) = -γ + ∑_n (1/(n+1) - 1/(s+n))` and the
elementary Laplace realization of each summand.  Summing the Laplace realizations geometrically,

`∑_{n<N} ( e^{-(n+1)u} - e^{-(s+n)u} ) = (1 - e^{-Nu}) · (e^{-u} - e^{-su})/(1 - e^{-u})`,

so dominated convergence — the factor `1 - e^{-Nu}` lies in `(0,1]` — turns the series into

`∑_n (1/(n+1) - 1/(s+n)) = ∫_0^∞ (e^{-u} - e^{-su})/(1 - e^{-u}) du`.

Adding the `s = 1` representation `-γ = ∫_0^∞ (e^{-u}/u - e^{-u}/(1-e^{-u})) du` gives the formula.

The dominating profile is `‖e^{-u} - e^{-su}‖/(1 - e^{-u})`: near the origin the numerator is
`O(u)` by the fundamental theorem of calculus while `1 - e^{-u} ≥ u e^{-u}`, and at infinity both
exponentials decay.
-/

open MeasureTheory Set Filter Real Complex

noncomputable section

namespace RHTower

/-! ## The geometric summation of the Laplace realizations -/

/-- The kernel `(e^{-u} - e^{-su})/(1 - e^{-u})` summing the Laplace realizations. -/
def gaussLaplaceKernel (s : ℂ) (t : ℝ) : ℂ :=
  (Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))) / (1 - Complex.exp (-(t : ℂ)))

theorem norm_exp_neg_ofReal (t : ℝ) : ‖Complex.exp (-(t : ℂ))‖ = Real.exp (-t) := by
  rw [Complex.norm_exp]
  simp

theorem exp_neg_ofReal_ne_one {t : ℝ} (ht : 0 < t) : Complex.exp (-(t : ℂ)) ≠ 1 := by
  intro h
  have hnorm : ‖Complex.exp (-(t : ℂ))‖ = 1 := by rw [h, norm_one]
  rw [norm_exp_neg_ofReal] at hnorm
  have : Real.exp (-t) < 1 := by
    rw [Real.exp_lt_one_iff]; linarith
  linarith

theorem one_sub_exp_neg_ofReal_ne_zero {t : ℝ} (ht : 0 < t) :
    (1 : ℂ) - Complex.exp (-(t : ℂ)) ≠ 0 := by
  intro h
  exact exp_neg_ofReal_ne_one ht (by linear_combination -h)

theorem gaussDigammaLaplaceTerm_eq_geom (s : ℂ) (n : ℕ) (t : ℝ) :
    gaussDigammaLaplaceTerm s n t
      = (Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ)))
          * Complex.exp (-(t : ℂ)) ^ n := by
  rw [gaussDigammaLaplaceTerm]
  have h1 : Complex.exp (-((n : ℂ) + 1) * (t : ℂ))
      = Complex.exp (-(t : ℂ)) * Complex.exp (-(t : ℂ)) ^ n := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  have h2 : Complex.exp (-(s + (n : ℂ)) * (t : ℂ))
      = Complex.exp (-s * (t : ℂ)) * Complex.exp (-(t : ℂ)) ^ n := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    ring
  rw [h1, h2]
  ring

/-- The geometric partial sum of the Laplace realizations. -/
theorem sum_gaussDigammaLaplaceTerm (s : ℂ) {t : ℝ} (ht : 0 < t) (N : ℕ) :
    (∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t)
      = (1 - Complex.exp (-(t : ℂ)) ^ N) * gaussLaplaceKernel s t := by
  have hne : Complex.exp (-(t : ℂ)) ≠ 1 := exp_neg_ofReal_ne_one ht
  have hden : (1 : ℂ) - Complex.exp (-(t : ℂ)) ≠ 0 := one_sub_exp_neg_ofReal_ne_zero ht
  simp_rw [gaussDigammaLaplaceTerm_eq_geom]
  rw [← Finset.mul_sum, geom_sum_eq hne, gaussLaplaceKernel]
  field_simp
  ring

/-! ## The dominating profile -/

theorem norm_exp_neg_sub_exp_neg_mul_le {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 ≤ t) :
    ‖Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))‖ ≤ (1 + ‖s‖) * t := by
  have hderiv : ∀ u ∈ Set.uIcc (0 : ℝ) t,
      HasDerivAt (fun v : ℝ => Complex.exp (-(v : ℂ)) - Complex.exp (-s * (v : ℂ)))
        (-Complex.exp (-(u : ℂ)) + s * Complex.exp (-s * (u : ℂ))) u := by
    intro u _
    have hbase : HasDerivAt (fun v : ℝ => (v : ℂ)) 1 u :=
      Complex.ofRealCLM.hasDerivAt.congr_deriv (by simp)
    have h1 : HasDerivAt (fun v : ℝ => Complex.exp (-(v : ℂ)))
        (-Complex.exp (-(u : ℂ))) u := by
      have := ((hbase.neg).cexp)
      simpa using this
    have h2 : HasDerivAt (fun v : ℝ => Complex.exp (-s * (v : ℂ)))
        (-(s * Complex.exp (-s * (u : ℂ)))) u := by
      have hlin : HasDerivAt (fun v : ℝ => -s * (v : ℂ)) (-s) u := by
        simpa using hbase.const_mul (-s)
      have h := hlin.cexp
      exact h.congr_deriv (by ring)
    exact (h1.sub h2).congr_deriv (by ring)
  have hcont : IntervalIntegrable
      (fun u : ℝ => -Complex.exp (-(u : ℂ)) + s * Complex.exp (-s * (u : ℂ)))
      volume 0 t := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont
  have hval : (Complex.exp (-((0 : ℝ) : ℂ)) - Complex.exp (-s * ((0 : ℝ) : ℂ))) = 0 := by
    simp
  have hbound : ∀ u ∈ Set.uIoc (0 : ℝ) t,
      ‖-Complex.exp (-(u : ℂ)) + s * Complex.exp (-s * (u : ℂ))‖ ≤ 1 + ‖s‖ := by
    intro u hu
    rw [Set.uIoc_of_le ht] at hu
    have hu0 : 0 ≤ u := le_of_lt hu.1
    have h1 : ‖Complex.exp (-(u : ℂ))‖ ≤ 1 := by
      rw [norm_exp_neg_ofReal, Real.exp_le_one_iff]
      linarith
    have h2 : ‖Complex.exp (-s * (u : ℂ))‖ ≤ 1 := by
      rw [Complex.norm_exp]
      rw [Real.exp_le_one_iff]
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      nlinarith [hs, hu0]
    calc ‖-Complex.exp (-(u : ℂ)) + s * Complex.exp (-s * (u : ℂ))‖
        ≤ ‖-Complex.exp (-(u : ℂ))‖ + ‖s * Complex.exp (-s * (u : ℂ))‖ := norm_add_le _ _
      _ = ‖Complex.exp (-(u : ℂ))‖ + ‖s‖ * ‖Complex.exp (-s * (u : ℂ))‖ := by
          rw [norm_neg, norm_mul]
      _ ≤ 1 + ‖s‖ * 1 := by
          gcongr
      _ = 1 + ‖s‖ := by ring
  have hle := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [hFTC, hval, sub_zero, sub_zero, abs_of_nonneg ht] at hle
  exact hle


theorem exp_neg_ofReal_eq (t : ℝ) :
    Complex.exp (-(t : ℂ)) = ((Real.exp (-t) : ℝ) : ℂ) := by
  rw [show (-(t : ℂ)) = ((-t : ℝ) : ℂ) from by push_cast; ring, ← Complex.ofReal_exp]

theorem one_sub_exp_neg_ofReal_eq (t : ℝ) :
    (1 : ℂ) - Complex.exp (-(t : ℂ)) = ((1 - Real.exp (-t) : ℝ) : ℂ) := by
  rw [exp_neg_ofReal_eq]
  push_cast
  ring

/-- The dominating profile of the Laplace kernel. -/
def gaussLaplaceBound (s : ℂ) (t : ℝ) : ℝ :=
  ‖Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))‖ / (1 - Real.exp (-t))

theorem norm_gaussLaplaceKernel (s : ℂ) {t : ℝ} (ht : 0 < t) :
    ‖gaussLaplaceKernel s t‖ = gaussLaplaceBound s t := by
  rw [gaussLaplaceKernel, norm_div, one_sub_exp_neg_ofReal_eq, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg (le_of_lt (one_sub_exp_neg_pos ht)), gaussLaplaceBound]

theorem gaussLaplaceBound_nonneg (s : ℂ) {t : ℝ} (ht : 0 < t) :
    0 ≤ gaussLaplaceBound s t := by
  rw [gaussLaplaceBound]
  have := one_sub_exp_neg_pos ht
  positivity

theorem gaussLaplaceBound_le_small {s : ℂ} (hs : 0 < s.re) {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) :
    gaussLaplaceBound s t ≤ Real.exp 1 * (1 + ‖s‖) := by
  have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))‖ ≤ (1 + ‖s‖) * t :=
    norm_exp_neg_sub_exp_neg_mul_le hs (le_of_lt ht)
  have hden : t * Real.exp (-1 : ℝ) ≤ 1 - Real.exp (-t) := by
    have h1 : t * Real.exp (-t) ≤ 1 - Real.exp (-t) := exp_neg_le_one_sub_exp_neg_div t
    have h2 : Real.exp (-1 : ℝ) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    nlinarith [le_of_lt ht]
  have hdenpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht
  have hexppos : (0 : ℝ) < Real.exp (-1 : ℝ) := Real.exp_pos _
  have hinv : Real.exp 1 * Real.exp (-1 : ℝ) = 1 := by
    rw [← Real.exp_add]; norm_num
  rw [gaussLaplaceBound, div_le_iff₀ hdenpos]
  have hc : (0 : ℝ) ≤ Real.exp 1 * (1 + ‖s‖) := by positivity
  have hstep : Real.exp 1 * (1 + ‖s‖) * (t * Real.exp (-1 : ℝ))
      ≤ Real.exp 1 * (1 + ‖s‖) * (1 - Real.exp (-t)) :=
    mul_le_mul_of_nonneg_left hden hc
  have heq : Real.exp 1 * (1 + ‖s‖) * (t * Real.exp (-1 : ℝ)) = (1 + ‖s‖) * t := by
    linear_combination ((1 + ‖s‖) * t) * hinv
  linarith

theorem gaussLaplaceBound_le_large {s : ℂ} {t : ℝ} (ht1 : 1 ≤ t) :
    gaussLaplaceBound s t
      ≤ (1 - Real.exp (-1 : ℝ))⁻¹ * (Real.exp (-t) + Real.exp (-s.re * t)) := by
  have ht : 0 < t := lt_of_lt_of_le zero_lt_one ht1
  have hdenpos : 0 < 1 - Real.exp (-t) := one_sub_exp_neg_pos ht
  have hpos1 : 0 < 1 - Real.exp (-1 : ℝ) := one_sub_exp_neg_pos zero_lt_one
  have hge : 1 - Real.exp (-1 : ℝ) ≤ 1 - Real.exp (-t) := by
    have := Real.exp_le_exp.mpr (show -t ≤ (-1 : ℝ) by linarith)
    linarith
  have hnum : ‖Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))‖
      ≤ Real.exp (-t) + Real.exp (-s.re * t) := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_exp_neg_ofReal, Complex.norm_exp]
    have : (-s * (t : ℂ)).re = -s.re * t := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im]
      ring
    rw [this]
  have hnumnn : (0 : ℝ) ≤ Real.exp (-t) + Real.exp (-s.re * t) := by positivity
  rw [gaussLaplaceBound, div_le_iff₀ hdenpos]
  have hstep : (1 - Real.exp (-1 : ℝ))⁻¹ * (Real.exp (-t) + Real.exp (-s.re * t))
      * (1 - Real.exp (-1 : ℝ))
      ≤ (1 - Real.exp (-1 : ℝ))⁻¹ * (Real.exp (-t) + Real.exp (-s.re * t))
        * (1 - Real.exp (-t)) := by
    apply mul_le_mul_of_nonneg_left hge
    positivity
  calc ‖Complex.exp (-(t : ℂ)) - Complex.exp (-s * (t : ℂ))‖
      ≤ Real.exp (-t) + Real.exp (-s.re * t) := hnum
    _ = (1 - Real.exp (-1 : ℝ))⁻¹ * (Real.exp (-t) + Real.exp (-s.re * t))
        * (1 - Real.exp (-1 : ℝ)) := by field_simp
    _ ≤ _ := hstep

theorem continuousOn_gaussLaplaceKernel (s : ℂ) :
    ContinuousOn (gaussLaplaceKernel s) (Ioi (0 : ℝ)) := by
  intro t ht
  have ht0 : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · exact one_sub_exp_neg_ofReal_ne_zero ht0

theorem measurable_gaussLaplaceBound (s : ℂ) :
    AEStronglyMeasurable (gaussLaplaceBound s) (volume.restrict (Ioi (0 : ℝ))) := by
  refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
  intro t ht
  have ht0 : 0 < t := ht
  refine ContinuousAt.continuousWithinAt ?_
  apply ContinuousAt.div
  · exact (Continuous.continuousAt (by fun_prop))
  · fun_prop
  · exact ne_of_gt (one_sub_exp_neg_pos ht0)

theorem integrableOn_gaussLaplaceBound {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (gaussLaplaceBound s) (Ioi (0 : ℝ)) volume := by
  have hsplit : Ioc (0 : ℝ) 1 ∪ Ioi (1 : ℝ) = Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi zero_le_one
  have hsmall : IntegrableOn (gaussLaplaceBound s) (Ioc (0 : ℝ) 1) volume := by
    have hconst : IntegrableOn (fun _ : ℝ => Real.exp 1 * (1 + ‖s‖)) (Ioc (0 : ℝ) 1) volume :=
      continuous_const.integrableOn_Ioc
    refine hconst.mono' ((measurable_gaussLaplaceBound s).mono_measure
      (Measure.restrict_mono (fun t ht => ht.1) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    rw [Real.norm_eq_abs, abs_of_nonneg (gaussLaplaceBound_nonneg s ht.1)]
    exact gaussLaplaceBound_le_small hs ht.1 ht.2
  have hlarge : IntegrableOn (gaussLaplaceBound s) (Ioi (1 : ℝ)) volume := by
    have h1 : IntegrableOn (fun t : ℝ => Real.exp (-t)) (Ioi (1 : ℝ)) volume :=
      integrableOn_exp_neg_Ioi_one
    have h2 : IntegrableOn (fun t : ℝ => Real.exp (-s.re * t)) (Ioi (1 : ℝ)) volume :=
      exp_neg_integrableOn_Ioi 1 hs
    have hbound : IntegrableOn
        (fun t : ℝ => (1 - Real.exp (-1 : ℝ))⁻¹ * (Real.exp (-t) + Real.exp (-s.re * t)))
        (Ioi (1 : ℝ)) volume := (h1.add h2).const_mul _
    refine hbound.mono' ((measurable_gaussLaplaceBound s).mono_measure
      (Measure.restrict_mono (Set.Ioi_subset_Ioi zero_le_one) le_rfl)) ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : (1 : ℝ) ≤ t := le_of_lt ht
    rw [Real.norm_eq_abs,
      abs_of_nonneg (gaussLaplaceBound_nonneg s (lt_of_lt_of_le zero_lt_one ht1))]
    exact gaussLaplaceBound_le_large ht1
  rw [← hsplit]
  exact hsmall.union hlarge

theorem integrableOn_gaussLaplaceKernel {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (gaussLaplaceKernel s) (Ioi (0 : ℝ)) volume := by
  refine (integrableOn_gaussLaplaceBound hs).mono'
    ((continuousOn_gaussLaplaceKernel s).aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [norm_gaussLaplaceKernel s ht]


/-! ## Dominated convergence -/

theorem continuous_gaussDigammaLaplaceTerm (s : ℂ) (n : ℕ) :
    Continuous (gaussDigammaLaplaceTerm s n) := by
  unfold gaussDigammaLaplaceTerm
  fun_prop

theorem norm_one_sub_exp_neg_pow_le {t : ℝ} (ht : 0 < t) (N : ℕ) :
    ‖(1 : ℂ) - Complex.exp (-(t : ℂ)) ^ N‖ ≤ 1 := by
  have hrN : Complex.exp (-(t : ℂ)) ^ N = ((Real.exp (-t) ^ N : ℝ) : ℂ) := by
    rw [exp_neg_ofReal_eq]
    push_cast
    ring
  have hx0 : 0 < Real.exp (-t) ^ N := by positivity
  have hx1 : Real.exp (-t) ^ N ≤ 1 := by
    apply pow_le_one₀ (le_of_lt (Real.exp_pos _))
    rw [Real.exp_le_one_iff]
    linarith
  rw [hrN, show (1 : ℂ) - ((Real.exp (-t) ^ N : ℝ) : ℂ) = ((1 - Real.exp (-t) ^ N : ℝ) : ℂ) from by
    push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
  linarith

theorem tendsto_partialSum_gaussDigammaLaplaceTerm (s : ℂ) {t : ℝ} (ht : 0 < t) :
    Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t)
      Filter.atTop (nhds (gaussLaplaceKernel s t)) := by
  have hnorm : ‖Complex.exp (-(t : ℂ))‖ < 1 := by
    rw [norm_exp_neg_ofReal, Real.exp_lt_one_iff]
    linarith
  have hpow : Filter.Tendsto (fun N : ℕ => Complex.exp (-(t : ℂ)) ^ N) Filter.atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hnorm
  have hfac : Filter.Tendsto (fun N : ℕ => (1 - Complex.exp (-(t : ℂ)) ^ N) *
      gaussLaplaceKernel s t) Filter.atTop (nhds (gaussLaplaceKernel s t)) := by
    have h1 : Filter.Tendsto (fun N : ℕ => (1 : ℂ) - Complex.exp (-(t : ℂ)) ^ N)
        Filter.atTop (nhds 1) := by
      simpa using (tendsto_const_nhds (x := (1 : ℂ)) (f := Filter.atTop (α := ℕ))).sub hpow
    simpa using h1.mul (tendsto_const_nhds (x := gaussLaplaceKernel s t))
  refine hfac.congr ?_
  intro N
  exact (sum_gaussDigammaLaplaceTerm s ht N).symm

theorem integral_gaussLaplaceKernel_eq_tsum {s : ℂ} (hs : 0 < s.re) :
    (∫ t in Ioi (0 : ℝ), gaussLaplaceKernel s t)
      = ∑' n : ℕ, gaussDigammaSeriesTerm s n := by
  have hFint : ∀ N : ℕ,
      (∫ t in Ioi (0 : ℝ), ∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t)
        = ∑ n ∈ Finset.range N, gaussDigammaSeriesTerm s n := by
    intro N
    rw [MeasureTheory.integral_finsetSum _
      (fun n _ => integrableOn_gaussDigammaLaplaceTerm hs n)]
    exact Finset.sum_congr rfl (fun n _ => integral_gaussDigammaLaplaceTerm hs n)
  have hmeas : ∀ N : ℕ, AEStronglyMeasurable
      (fun t : ℝ => ∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t)
      (volume.restrict (Ioi (0 : ℝ))) := by
    intro N
    refine Continuous.aestronglyMeasurable ?_
    exact continuous_finsetSum _ (fun n _ => continuous_gaussDigammaLaplaceTerm s n)
  have hbound : ∀ N : ℕ, ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t‖ ≤ gaussLaplaceBound s t := by
    intro N
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    rw [sum_gaussDigammaLaplaceTerm s ht0 N, norm_mul, norm_gaussLaplaceKernel s ht0]
    have h1 := norm_one_sub_exp_neg_pow_le ht0 N
    have h2 := gaussLaplaceBound_nonneg s ht0
    nlinarith
  have hlim : ∀ᵐ t ∂(volume.restrict (Ioi (0 : ℝ))),
      Filter.Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, gaussDigammaLaplaceTerm s n t)
        Filter.atTop (nhds (gaussLaplaceKernel s t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact tendsto_partialSum_gaussDigammaLaplaceTerm s ht
  have hDCT := MeasureTheory.tendsto_integral_of_dominated_convergence
    (gaussLaplaceBound s) hmeas (integrableOn_gaussLaplaceBound hs) hbound hlim
  simp only [hFint] at hDCT
  have hsum : Filter.Tendsto
      (fun N : ℕ => ∑ n ∈ Finset.range N, gaussDigammaSeriesTerm s n) Filter.atTop
      (nhds (∑' n : ℕ, gaussDigammaSeriesTerm s n)) :=
    (summable_gaussDigammaSeriesTerm hs).hasSum.tendsto_sum_nat
  exact tendsto_nhds_unique hDCT hsum

/-! ## The integral representation -/

/-- The Gauss integrand `e^{-t}/t - e^{-st}/(1 - e^{-t})`. -/
def digammaGaussIntegrand (s : ℂ) (t : ℝ) : ℂ :=
  ((Real.exp (-t) / t : ℝ) : ℂ)
    - Complex.exp (-s * (t : ℂ)) / (1 - Complex.exp (-(t : ℂ)))

theorem digammaGaussIntegrand_eq (s : ℂ) {t : ℝ} (ht : 0 < t) :
    digammaGaussIntegrand s t = ((gaussKernel t : ℝ) : ℂ) + gaussLaplaceKernel s t := by
  have hden : (1 : ℂ) - Complex.exp (-(t : ℂ)) ≠ 0 := one_sub_exp_neg_ofReal_ne_zero ht
  have hdenR : (1 : ℝ) - Real.exp (-t) ≠ 0 := ne_of_gt (one_sub_exp_neg_pos ht)
  rw [digammaGaussIntegrand, gaussKernel, gaussLaplaceKernel, one_sub_exp_neg_ofReal_eq,
    exp_neg_ofReal_eq]
  push_cast
  field_simp
  ring

/-- **Gauss's integral representation of the digamma function.**  For `Re s > 0`,
`ψ(s) = ∫_0^∞ ( e^{-u}/u - e^{-su}/(1 - e^{-u}) ) du`. -/
theorem digamma_eq_integral_gauss {s : ℂ} (hs : 0 < s.re) :
    Complex.digamma s = ∫ t in Ioi (0 : ℝ), digammaGaussIntegrand s t := by
  have hgauss : IntegrableOn (fun t : ℝ => ((gaussKernel t : ℝ) : ℂ)) (Ioi (0 : ℝ)) volume := by
    have := integrableOn_gaussKernel
    exact (Complex.ofRealCLM.integrable_comp this)
  have hlap := integrableOn_gaussLaplaceKernel hs
  have hcongr : (∫ t in Ioi (0 : ℝ), digammaGaussIntegrand s t)
      = ∫ t in Ioi (0 : ℝ),
          (((gaussKernel t : ℝ) : ℂ) + gaussLaplaceKernel s t) := by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t ht
    exact digammaGaussIntegrand_eq s ht
  rw [hcongr, MeasureTheory.integral_add hgauss hlap,
    integral_gaussLaplaceKernel_eq_tsum hs]
  have hreal : (∫ t in Ioi (0 : ℝ), ((gaussKernel t : ℝ) : ℂ))
      = ((-Real.eulerMascheroniConstant : ℝ) : ℂ) := by
    rw [_root_.integral_complex_ofReal, integral_gaussKernel]
  rw [hreal, digamma_eq_neg_euler_add_tsum_gauss hs]
  push_cast
  ring


theorem integrableOn_digammaGaussIntegrand {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (digammaGaussIntegrand s) (Ioi (0 : ℝ)) volume := by
  have hgauss : IntegrableOn (fun t : ℝ => ((gaussKernel t : ℝ) : ℂ)) (Ioi (0 : ℝ)) volume :=
    Complex.ofRealCLM.integrable_comp integrableOn_gaussKernel
  have hlap := integrableOn_gaussLaplaceKernel hs
  refine (hgauss.add hlap).congr_fun ?_ measurableSet_Ioi
  intro t ht
  exact (digammaGaussIntegrand_eq s ht).symm

theorem div_ofReal_re (w : ℂ) (r : ℝ) : (w / ((r : ℝ) : ℂ)).re = w.re / r := by
  rcases eq_or_ne r 0 with rfl | hr
  · simp
  · simp only [Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re, Complex.ofReal_im]
    field_simp
    ring

/-- **The archimedean real-part form.**  For real `z`,
`∫_0^∞ ( e^{-u/4} cos(zu/2)/(1 - e^{-u}) - e^{-u}/u ) du = - Re ψ(1/4 + iz/2)`.
This is the identity Suzuki uses to evaluate the Fourier transform of the smooth remainder in the
origin expansion of the screw function. -/
theorem integral_archimedean_gaussKernel (z : ℝ) :
    (∫ u in Ioi (0 : ℝ),
        (Real.exp (-u / 4) * Real.cos (z * u / 2) / (1 - Real.exp (-u))
          - Real.exp (-u) / u))
      = -(Complex.digamma (1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I)).re := by
  set s : ℂ := 1 / 4 + ((z / 2 : ℝ) : ℂ) * Complex.I with hs_def
  have hsre : s.re = 1 / 4 := by
    rw [hs_def]
    simp
  have hs : 0 < s.re := by rw [hsre]; norm_num
  have hsim : s.im = z / 2 := by
    rw [hs_def]
    simp
  have hre : ∀ t : ℝ, t ∈ Ioi (0 : ℝ) → (digammaGaussIntegrand s t).re
      = Real.exp (-t) / t - Real.exp (-t / 4) * Real.cos (z * t / 2) / (1 - Real.exp (-t)) := by
    intro t ht
    have ht0 : 0 < t := ht
    rw [digammaGaussIntegrand, Complex.sub_re, Complex.ofReal_re,
      one_sub_exp_neg_ofReal_eq, div_ofReal_re, Complex.exp_re]
    have hmulre : (-s * (t : ℂ)).re = -t / 4 := by
      simp only [Complex.mul_re, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hsre, hsim]
      ring
    have hmulim : (-s * (t : ℂ)).im = -(z * t / 2) := by
      simp only [Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
        Complex.ofReal_im, hsre, hsim]
      ring
    rw [hmulre, hmulim, Real.cos_neg]
  have hint := integrableOn_digammaGaussIntegrand hs
  have hkey : (Complex.digamma s).re
      = ∫ t in Ioi (0 : ℝ),
          (Real.exp (-t) / t
            - Real.exp (-t / 4) * Real.cos (z * t / 2) / (1 - Real.exp (-t))) := by
    have hcomm := Complex.reCLM.integral_comp_comm hint
    simp only [Complex.reCLM_apply] at hcomm
    rw [digamma_eq_integral_gauss hs, ← hcomm]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hre
  have hneg : (∫ u in Ioi (0 : ℝ),
      (Real.exp (-u / 4) * Real.cos (z * u / 2) / (1 - Real.exp (-u)) - Real.exp (-u) / u))
      = -∫ t in Ioi (0 : ℝ),
          (Real.exp (-t) / t
            - Real.exp (-t / 4) * Real.cos (z * t / 2) / (1 - Real.exp (-t))) := by
    rw [← MeasureTheory.integral_neg]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
    intro t _
    ring
  rw [hneg, hkey]

end RHTower
