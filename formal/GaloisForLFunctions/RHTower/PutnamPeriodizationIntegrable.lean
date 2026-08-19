import GaloisForLFunctions.RHTower.PutnamFourierCoefficients
import GaloisForLFunctions.HTGeometry.FejerKernel

/-!
# Integrability of the periodisation, and its Fejér pairing

The periodisation is measurable and bounded on a period, hence integrable there.  Pairing it
against a Fejér kernel produces a finite combination of its Fourier coefficients, so the pairing
vanishes as soon as those do.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

theorem measurable_putnamPeriodization (a d : ℝ) : Measurable (putnamPeriodization a d) := by
  refine Measurable.tsum (fun k => ?_)
  exact (measurable_putnamKernel a).comp (by fun_prop)

theorem norm_putnamPeriodization_le {a d : ℝ} (hd : 0 < d) (x : ℝ) :
    ‖putnamPeriodization a d x‖
      ≤ Real.exp (|x| / 2) * ∑' k : ℤ, Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hsum : Summable (fun k : ℤ => Real.exp (|x| / 2) *
      Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|))) :=
    (summable_exp_neg_abs_int (r := putnamPeriod d / 2) (by positivity)).mul_left _
  have hbound : ∀ k : ℤ, ‖putnamKernel a (x + (k : ℝ) * putnamPeriod d)‖
      ≤ Real.exp (|x| / 2) * Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)) := by
    intro k
    refine le_trans (norm_putnamKernel_le a _) ?_
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    have habs : |(k : ℝ)| * putnamPeriod d - |x| ≤ |x + (k : ℝ) * putnamPeriod d| := by
      have h := abs_sub_abs_le_abs_sub ((k : ℝ) * putnamPeriod d) (-x)
      rw [abs_neg, sub_neg_eq_add] at h
      have h2 : |(k : ℝ) * putnamPeriod d| = |(k : ℝ)| * putnamPeriod d := by
        rw [abs_mul, abs_of_pos hP]
      rw [h2] at h
      have h3 : |(k : ℝ) * putnamPeriod d + x| = |x + (k : ℝ) * putnamPeriod d| := by rw [add_comm]
      rw [h3] at h
      linarith
    linarith
  rw [putnamPeriodization]
  refine le_trans (norm_tsum_le_tsum_norm ?_) ?_
  · exact hsum.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hbound k)
  · rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum hbound (hsum.of_norm_bounded (fun k => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact hbound k)) ?_
    exact hsum

theorem integrableOn_putnamPeriodization {a d : ℝ} (hd : 0 < d) :
    IntegrableOn (putnamPeriodization a d) (Ioc (0 : ℝ) (putnamPeriod d)) := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  set S : ℝ := ∑' k : ℤ, Real.exp (-(putnamPeriod d / 2 * |(k : ℝ)|)) with hS
  have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d))) ≠ ⊤ := by
    rw [Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  refine Integrable.mono' (g := fun _ : ℝ => Real.exp (putnamPeriod d / 2) * S)
    (integrableOn_const hfin)
    ((measurable_putnamPeriodization a d).aestronglyMeasurable.restrict) ?_
  refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall fun x hx => ?_)
  refine le_trans (norm_putnamPeriodization_le hd x) ?_
  have hxb : |x| ≤ putnamPeriod d := by
    rw [abs_of_pos hx.1]
    exact hx.2
  have hSnn : (0 : ℝ) ≤ S := by
    rw [hS]
    exact tsum_nonneg fun k => (Real.exp_pos _).le
  have : Real.exp (|x| / 2) ≤ Real.exp (putnamPeriod d / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  nlinarith [this, hSnn]

/-- The periodisation twisted by a lattice character. -/
def putnamPeriodTwist (a d : ℝ) (k : ℤ) (x : ℝ) : ℂ :=
  putnamPeriodization a d x * Complex.exp (-((d * k : ℝ) : ℂ) * I * (x : ℂ))

theorem integrableOn_putnamPeriodTwist {a d : ℝ} (hd : 0 < d) (k : ℤ) :
    IntegrableOn (putnamPeriodTwist a d k) (Ioc (0 : ℝ) (putnamPeriod d)) := by
  refine Integrable.mono' (integrableOn_putnamPeriodization (a := a) hd).norm
    (((measurable_putnamPeriodization a d).mul
      (Complex.measurable_exp.comp (by fun_prop))).aestronglyMeasurable.restrict) ?_
  refine Filter.Eventually.of_forall fun x => ?_
  rw [putnamPeriodTwist, norm_mul, Complex.norm_exp]
  have hre : (-((d * k : ℝ) : ℂ) * I * (x : ℂ)).re = 0 := by
    simp [Complex.mul_re]
  rw [hre, Real.exp_zero, mul_one]

/-- **The Fejér pairing vanishes.**  The Fejér kernel is a finite combination of characters with
frequencies in `dℤ`, so pairing it against the periodisation gives a finite combination of the
periodisation's Fourier coefficients. -/
theorem integral_putnamPeriodization_fejer {a d : ℝ} (hd : 0 < d)
    (hzero : ∀ k : ℤ, (∫ x in Ioc (0 : ℝ) (putnamPeriod d), putnamPeriodTwist a d k x) = 0)
    (x₀ : ℝ) (N : ℕ) :
    (∫ x in Ioc (0 : ℝ) (putnamPeriod d),
        putnamPeriodization a d x *
          ((HTGeometry.fejerKernel N (d * (x - x₀)) : ℝ) : ℂ)) = 0 := by
  classical
  set coef : ℕ → ℕ → ℂ := fun n m =>
    ((((N : ℝ) + 1)⁻¹ : ℝ) : ℂ) *
      Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * -x₀ : ℝ) : ℂ) * I) with hcoef
  have hpoint : ∀ x : ℝ, putnamPeriodization a d x *
      ((HTGeometry.fejerKernel N (d * (x - x₀)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          coef n m * putnamPeriodTwist a d ((m : ℤ) - (n : ℤ)) x := by
    intro x
    rw [HTGeometry.fejerKernel_eq_double_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    have hexp : Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * (x - x₀) : ℝ) : ℂ) * I)
        = Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * -x₀ : ℝ) : ℂ) * I) *
          Complex.exp (-((d * (((m : ℤ) - (n : ℤ) : ℤ) : ℝ) : ℝ) : ℂ) * I * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hcoef, putnamPeriodTwist]
    simp only
    rw [hexp]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => hpoint x)]
  rw [MeasureTheory.integral_finsetSum (s := Finset.range (N + 1))
    (f := fun n x => ∑ m ∈ Finset.range (N + 1),
      coef n m * putnamPeriodTwist a d ((m : ℤ) - (n : ℤ)) x)
    (fun n _ => MeasureTheory.integrable_finsetSum (s := Finset.range (N + 1))
      (f := fun m x => coef n m * putnamPeriodTwist a d ((m : ℤ) - (n : ℤ)) x)
      (fun m _ => (integrableOn_putnamPeriodTwist hd ((m : ℤ) - (n : ℤ))).const_mul _))]
  refine Finset.sum_eq_zero fun n _ => ?_
  rw [MeasureTheory.integral_finsetSum (s := Finset.range (N + 1))
    (f := fun m x => coef n m * putnamPeriodTwist a d ((m : ℤ) - (n : ℤ)) x)
    (fun m _ => (integrableOn_putnamPeriodTwist hd ((m : ℤ) - (n : ℤ))).const_mul _)]
  refine Finset.sum_eq_zero fun m _ => ?_
  rw [MeasureTheory.integral_const_mul, hzero ((m : ℤ) - (n : ℤ)), mul_zero]

end RHTower

end
