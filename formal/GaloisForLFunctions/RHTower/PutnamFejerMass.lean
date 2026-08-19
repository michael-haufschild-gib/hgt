import GaloisForLFunctions.RHTower.PutnamPeriodizationIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Fejér mass over a period

The lattice characters integrate to zero over a period except for the trivial one, so the Fejér
kernel — being the normalised diagonal-heavy double sum of characters — has mass exactly one period.
-/

open Complex MeasureTheory Set

noncomputable section

namespace RHTower

theorem integral_lattice_character {d : ℝ} (hd : 0 < d) (k : ℤ) :
    (∫ x in Ioc (0 : ℝ) (putnamPeriod d), Complex.exp (((d * k : ℝ) : ℂ) * I * (x : ℂ)))
      = if k = 0 then ((putnamPeriod d : ℝ) : ℂ) else 0 := by
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  have hIoc : (∫ x in Ioc (0 : ℝ) (putnamPeriod d),
      Complex.exp (((d * k : ℝ) : ℂ) * I * (x : ℂ)))
      = ∫ x in (0 : ℝ)..(putnamPeriod d), Complex.exp (((d * k : ℝ) : ℂ) * I * (x : ℂ)) := by
    rw [intervalIntegral.integral_of_le hP.le]
  rw [hIoc]
  by_cases hk : k = 0
  · subst hk
    simp
  · rw [if_neg hk]
    have hc : ((d * (k : ℝ) : ℝ) : ℂ) * I ≠ 0 := by
      refine mul_ne_zero ?_ Complex.I_ne_zero
      have hdk : (d * (k : ℝ)) ≠ 0 := by
        have : (k : ℝ) ≠ 0 := by exact_mod_cast hk
        exact mul_ne_zero (ne_of_gt hd) this
      exact_mod_cast hdk
    have hrw : ∀ x : ℝ, Complex.exp (((d * k : ℝ) : ℂ) * I * (x : ℂ))
        = Complex.exp ((((d * (k : ℝ) : ℝ) : ℂ) * I) * (x : ℂ)) := by
      intro x
      congr 2
    rw [intervalIntegral.integral_congr (fun x _ => hrw x)]
    rw [integral_exp_mul_complex hc]
    have hval : Complex.exp ((((d * (k : ℝ) : ℝ) : ℂ) * I) * ((putnamPeriod d : ℝ) : ℂ)) = 1 := by
      have hexp : (((d * (k : ℝ) : ℝ) : ℂ) * I) * ((putnamPeriod d : ℝ) : ℂ)
          = ((k : ℂ)) * (2 * (Real.pi : ℂ) * I) := by
        have hPc : ((putnamPeriod d : ℝ) : ℂ) = 2 * (Real.pi : ℂ) / (d : ℂ) := by
          rw [putnamPeriod]
          push_cast
          ring
        have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hd
        rw [hPc]
        push_cast
        field_simp
      rw [hexp]
      exact_mod_cast Complex.exp_int_mul_two_pi_mul_I k
    rw [hval]
    simp

/-- **The Fejér mass over a period.** -/
theorem integral_fejer_mass {d : ℝ} (hd : 0 < d) (x₀ : ℝ) (N : ℕ) :
    (∫ x in Ioc (0 : ℝ) (putnamPeriod d),
        ((HTGeometry.fejerKernel N (d * (x - x₀)) : ℝ) : ℂ))
      = ((putnamPeriod d : ℝ) : ℂ) := by
  classical
  have hP : 0 < putnamPeriod d := putnamPeriod_pos hd
  set coef : ℕ → ℕ → ℂ := fun n m =>
    ((((N : ℝ) + 1)⁻¹ : ℝ) : ℂ) *
      Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * -x₀ : ℝ) : ℂ) * I) with hcoef
  have hpoint : ∀ x : ℝ, ((HTGeometry.fejerKernel N (d * (x - x₀)) : ℝ) : ℂ)
      = ∑ n ∈ Finset.range (N + 1), ∑ m ∈ Finset.range (N + 1),
          coef n m * Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)) := by
    intro x
    rw [HTGeometry.fejerKernel_eq_double_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    refine Finset.sum_congr rfl fun m _ => ?_
    have hexp : Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * (x - x₀) : ℝ) : ℂ) * I)
        = Complex.exp (((n : ℂ) - (m : ℂ)) * ((d * -x₀ : ℝ) : ℂ) * I) *
          Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hcoef]
    simp only
    rw [hexp]
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioc (fun x _ => hpoint x)]
  have hintg : ∀ n m : ℕ, IntegrableOn
      (fun x : ℝ => coef n m *
        Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)))
      (Ioc (0 : ℝ) (putnamPeriod d)) := by
    intro n m
    have hfin : (volume (Ioc (0 : ℝ) (putnamPeriod d))) ≠ ⊤ := by
      rw [Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    refine Integrable.mono' (g := fun _ : ℝ => ‖coef n m‖) (integrableOn_const hfin)
      ((Complex.measurable_exp.comp (by fun_prop)).const_mul _ |>.aestronglyMeasurable.restrict) ?_
    refine Filter.Eventually.of_forall fun x => ?_
    rw [norm_mul, Complex.norm_exp]
    have hre : ((((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ)) * I * (x : ℂ)).re = 0 := by
      simp [Complex.mul_re]
    rw [hre, Real.exp_zero, mul_one]
  rw [MeasureTheory.integral_finsetSum (s := Finset.range (N + 1))
    (f := fun (n : ℕ) (x : ℝ) => ∑ m ∈ Finset.range (N + 1),
      coef n m * Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)))
    (fun n _ => MeasureTheory.integrable_finsetSum
      (μ := volume.restrict (Ioc (0 : ℝ) (putnamPeriod d))) _ (fun m _ => hintg n m))]
  have hinner : ∀ n ∈ Finset.range (N + 1),
      (∫ x in Ioc (0 : ℝ) (putnamPeriod d), ∑ m ∈ Finset.range (N + 1),
        coef n m * Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)))
      = ((((N : ℝ) + 1)⁻¹ : ℝ) : ℂ) * ((putnamPeriod d : ℝ) : ℂ) := by
    intro n hn
    rw [MeasureTheory.integral_finsetSum (s := Finset.range (N + 1))
      (f := fun (m : ℕ) (x : ℝ) => coef n m *
        Complex.exp (((d * (((n : ℤ) - (m : ℤ)) : ℤ) : ℝ) : ℂ) * I * (x : ℂ)))
      (fun m _ => hintg n m)]
    rw [Finset.sum_eq_single n]
    · rw [MeasureTheory.integral_const_mul, integral_lattice_character hd ((n : ℤ) - (n : ℤ))]
      simp only [sub_self]
      rw [hcoef]
      simp
    · intro m _ hmn
      rw [MeasureTheory.integral_const_mul,
        integral_lattice_character hd ((n : ℤ) - (m : ℤ))]
      rw [if_neg (by
        intro hcon
        exact hmn (by omega))]
      ring
    · intro hn'
      exact absurd hn hn'
  rw [Finset.sum_congr rfl hinner, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hne : ((N : ℂ) + 1) ≠ 0 := by
    have : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    exact_mod_cast ne_of_gt this
  push_cast
  field_simp

end RHTower

end
