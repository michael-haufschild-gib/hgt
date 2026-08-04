import GaloisForLFunctions.RHTower.Sieve.LinearWindowMeasurable
import Mathlib.MeasureTheory.Function.JacobianOneDim
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# From the logarithmic variable back to the linear one

The substitution `x = e^u` carries `du` to `dx/x`, so for a nonnegative integrand

    ∫_Y^Z F(x) dx = ∫_{log Y}^{log Z} e^u F(e^u) du ≤ Z · ∫_{log Y}^{log Z} F(e^u) du .

The change of variables is the measure-theoretic one, which needs no continuity of `F` — essential
here, since the window sum jumps at every integer.
-/

namespace RHTower.Sieve

open MeasureTheory

/-- The linear window sum as a function of the starting point. -/
noncomputable def linSum (a : ℕ → ℂ) (s : Finset ℕ) (L x : ℝ) : ℂ :=
  ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + L), a n

theorem linWindowSum_eq_linSum (a : ℕ → ℂ) (s : Finset ℕ) (L u : ℝ) :
    linWindowSum a s L u = linSum a s L (Real.exp u) := by
  rw [linWindowSum_eq, linSum]

/-- The exponential image of an interval. -/
theorem exp_image_Ioc (A B : ℝ) :
    (fun u : ℝ => Real.exp u) '' Set.Ioc A B = Set.Ioc (Real.exp A) (Real.exp B) := by
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    exact ⟨Real.exp_lt_exp.2 hu.1, Real.exp_le_exp.2 hu.2⟩
  · rintro ⟨h1, h2⟩
    have hx0 : (0 : ℝ) < x := lt_trans (Real.exp_pos A) h1
    refine ⟨Real.log x, ⟨?_, ?_⟩, Real.exp_log hx0⟩
    · have := Real.exp_lt_exp.1 (by rwa [Real.exp_log hx0] : Real.exp A < Real.exp (Real.log x))
      exact this
    · have := Real.exp_le_exp.1 (by rwa [Real.exp_log hx0] : Real.exp (Real.log x) ≤ Real.exp B)
      exact this

/-- **The change of variables.** -/
theorem integral_Ioc_eq_integral_log (F : ℝ → ℝ) (A B : ℝ) :
    (∫ x in Set.Ioc (Real.exp A) (Real.exp B), F x)
      = ∫ u in Set.Ioc A B, Real.exp u * F (Real.exp u) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
    (s := Set.Ioc A B) (f := Real.exp) (f' := Real.exp) measurableSet_Ioc
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (Real.exp_injective.injOn) F
  rw [exp_image_Ioc] at h
  rw [h]
  refine setIntegral_congr_fun measurableSet_Ioc fun u _ => ?_
  rw [abs_of_pos (Real.exp_pos u), smul_eq_mul]

/-- The mean square of the linear window sum is integrable on bounded sets, in the linear
variable. -/
theorem integrableOn_normSq_expMul (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) {A B : ℝ} :
    IntegrableOn (fun u : ℝ => Real.exp u * ‖linWindowSum a s L u‖ ^ 2) (Set.Ioc A B) := by
  classical
  have hfin : volume (Set.Ioc A B) ≠ ⊤ := by simp
  have hmeas : AEStronglyMeasurable
      (fun u : ℝ => Real.exp u * ‖linWindowSum a s L u‖ ^ 2)
      (volume.restrict (Set.Ioc A B)) :=
    (Real.continuous_exp.measurable.mul
      ((measurable_linWindowSum a s L).norm.pow_const 2)).aestronglyMeasurable
  set C : ℝ := Real.exp B * (∑ n ∈ s, ‖a n‖) ^ 2 with hC
  refine Integrable.mono' (g := fun _ : ℝ => C) (integrableOn_const hfin (by finiteness))
    hmeas ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Filter.Eventually.of_forall fun u hu => ?_)
  have hexp : Real.exp u ≤ Real.exp B := Real.exp_le_exp.2 hu.2
  have hbd := norm_linWindowSum_le a s L u
  have h0 : (0 : ℝ) ≤ ‖linWindowSum a s L u‖ := norm_nonneg _
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), hC]
  have hsq : ‖linWindowSum a s L u‖ ^ 2 ≤ (∑ n ∈ s, ‖a n‖) ^ 2 := by nlinarith [hbd, h0]
  have hexp0 : (0 : ℝ) < Real.exp u := Real.exp_pos u
  nlinarith [hsq, hexp, hexp0.le, sq_nonneg (∑ n ∈ s, ‖a n‖)]

/-- **The linear mean square is at most the endpoint times the logarithmic one.** -/
theorem integral_Ioc_normSq_linSum_le (a : ℕ → ℂ) (s : Finset ℕ) (L : ℝ) (A B : ℝ) :
    (∫ x in Set.Ioc (Real.exp A) (Real.exp B), ‖linSum a s L x‖ ^ 2)
      ≤ Real.exp B * ∫ u in Set.Ioc A B, ‖linWindowSum a s L u‖ ^ 2 := by
  classical
  have hfin : volume (Set.Ioc A B) ≠ ⊤ := by simp
  rw [integral_Ioc_eq_integral_log (fun x => ‖linSum a s L x‖ ^ 2) A B]
  have hcongr : ∀ u : ℝ, Real.exp u * ‖linSum a s L (Real.exp u)‖ ^ 2
      = Real.exp u * ‖linWindowSum a s L u‖ ^ 2 := by
    intro u
    rw [linWindowSum_eq_linSum]
  rw [setIntegral_congr_fun measurableSet_Ioc (fun u _ => hcongr u)]
  have hle : ∀ u ∈ Set.Ioc A B,
      Real.exp u * ‖linWindowSum a s L u‖ ^ 2
        ≤ Real.exp B * ‖linWindowSum a s L u‖ ^ 2 := by
    intro u hu
    exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 hu.2) (by positivity)
  refine le_trans (setIntegral_mono_on (integrableOn_normSq_expMul a s L)
    (((integrableOn_normSq_linWindowSum a s L hfin)).const_mul _) measurableSet_Ioc hle) ?_
  rw [integral_const_mul]

end RHTower.Sieve
