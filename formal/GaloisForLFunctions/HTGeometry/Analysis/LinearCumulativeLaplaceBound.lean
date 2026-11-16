import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import GaloisForLFunctions.HTGeometry.TwoModeSquareCombination

/-!
# Laplace bounds from linear cumulative mass

Fubini expresses an exponential moment through the terminal cumulative
mass. A linear bound for that mass gives a reciprocal exponential bound.
Applied to the square density, weighted Cauchy–Schwarz gives inverse-linear
Laplace decay without requiring a pointwise boundary value.
-/

noncomputable section
open MeasureTheory Set Filter
namespace GaloisForLFunctions.HTGeometry

/-- A linear terminal mass bound controls every positive exponential moment. -/
theorem integral_exp_mul_Iio_le_of_terminal_mass {g : ℝ → ℝ} {C t : ℝ}
    (hg : IntegrableOn g (Iio 0)) (hg0 : ∀ u < 0, 0 ≤ g u)
    (hbound : ∀ h : ℝ, 0 < h → (∫ u in Ioo (-h) 0, g u) ≤ C*h)
    (ht : 0 < t) :
    (∫ u in Iio 0, g u * Real.exp (t*u)) ≤ C/t := by
  let Φ : ℝ → ℝ → ℝ := fun u h => if -h < u then g u * Real.exp (-t*h) else 0
  have he := exp_neg_integrableOn_Ioi 0 ht
  have hm : MeasurableSet {p : ℝ × ℝ | -p.2 < p.1} :=
    measurableSet_lt measurable_snd.neg measurable_fst
  have hprod : Integrable (Function.uncurry Φ)
      ((volume.restrict (Iio 0)).prod (volume.restrict (Ioi 0))) :=
    (hg.mul_prod he).indicator hm
  have hleft (u : ℝ) (hu : u < 0) :
      (∫ h in Ioi 0, Φ u h) = g u * Real.exp (t*u) / t := by
    have hfun : Φ u = (Ioi (-u)).indicator (fun h => g u * Real.exp (-t*h)) := by
      funext h
      simp only [Φ, indicator_apply, mem_Ioi]
      simp only [show (-h < u) ↔ -u < h by constructor <;> intro hh <;> linarith only [hh]]
    rw [hfun, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi]
    have hi : Ioi (-u) ∩ Ioi (0 : ℝ) = Ioi (-u) := by
      apply inter_eq_left.mpr
      intro h hh
      exact lt_trans (neg_pos.mpr hu) hh
    rw [hi, integral_const_mul, integral_exp_mul_Ioi (neg_neg_of_pos ht)]
    simp only [neg_mul_neg, neg_div_neg_eq]
    ring
  have hright (h : ℝ) :
      (∫ u in Iio 0, Φ u h) = (∫ u in Ioo (-h) 0, g u) * Real.exp (-t*h) := by
    have hfun : (fun u => Φ u h) =
        (Ioi (-h)).indicator (fun u => g u * Real.exp (-t*h)) := by
      funext u
      simp only [Φ, indicator_apply, mem_Ioi]
    rw [hfun, integral_indicator measurableSet_Ioi,
      Measure.restrict_restrict measurableSet_Ioi]
    have hi : Ioi (-h) ∩ Iio (0 : ℝ) = Ioo (-h) 0 := by ext u; rfl
    rw [hi, integral_mul_const]
  have hid : (∫ u in Iio 0, g u * Real.exp (t*u)) / t =
      ∫ h in Ioi 0, (∫ u in Ioo (-h) 0, g u) * Real.exp (-t*h) := by
    rw [← integral_div]
    calc
      _ = ∫ u in Iio 0, ∫ h in Ioi 0, Φ u h :=
        setIntegral_congr_fun measurableSet_Iio fun u hu => (hleft u hu).symm
      _ = ∫ h in Ioi 0, ∫ u in Iio 0, Φ u h := integral_integral_swap hprod
      _ = _ := by simp_rw [hright]
  have hmoment : (∫ h in Ioi (0 : ℝ), h * Real.exp (-t*h)) = 1/t^2 := by
    have h := Real.integral_rpow_mul_exp_neg_mul_Ioi (a := 2) (by norm_num) ht
    norm_num [Real.rpow_two] at h
    simpa only [one_div, neg_mul] using h
  have himoment : IntegrableOn (fun h : ℝ => h * Real.exp (-t*h)) (Ioi 0) :=
    Integrable.of_integral_ne_zero (by rw [hmoment]; positivity)
  have hle : (∫ h in Ioi 0, (∫ u in Ioo (-h) 0, g u) * Real.exp (-t*h)) ≤
      C/t^2 := by
    calc
      _ ≤ ∫ h in Ioi 0, C * (h * Real.exp (-t*h)) := by
        apply integral_mono_of_nonneg
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
          exact mul_nonneg (setIntegral_nonneg measurableSet_Ioo fun u hu => hg0 u hu.2)
            (Real.exp_pos _).le
        · exact himoment.const_mul C
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
          simpa only [mul_assoc] using
            mul_le_mul_of_nonneg_right (hbound h hh) (Real.exp_pos (-t*h)).le
      _ = _ := by rw [integral_const_mul, hmoment]; ring
  rw [← hid] at hle
  have h := (div_le_iff₀ ht).mp hle
  calc
    _ ≤ C/t^2*t := h
    _ = C/t := by field_simp

/-- Linear cumulative square mass gives inverse-linear Laplace decay. -/
theorem abs_integral_exp_mul_Iio_le_of_terminal_square_mass
    {f : ℝ → ℝ} {C t : ℝ} (hm : Measurable f)
    (hf : IntegrableOn (fun u => f u ^ 2) (Iio 0)) (hC : 0 ≤ C)
    (hbound : ∀ h : ℝ, 0 < h → (∫ u in Ioo (-h) 0, f u ^ 2) ≤ C*h)
    (ht : 0 < t) :
    |∫ u in Iio 0, f u * Real.exp (t*u)| ≤ Real.sqrt C / t := by
  have hexp (u : ℝ) : Real.exp (t*u/2)^2 = Real.exp (t*u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hsquare : (fun u => (f u * Real.exp (t*u/2))^2) =
      fun u => f u^2 * Real.exp (t*u) := by
    funext u
    rw [mul_pow, hexp]
  have hsq : IntegrableOn (fun u => (f u * Real.exp (t*u/2))^2) (Iio 0) := by
    rw [hsquare]
    refine hf.mono' (by fun_prop) ?_
    filter_upwards [ae_restrict_mem measurableSet_Iio] with u hu
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)]
    exact mul_le_of_le_one_right (sq_nonneg _) (Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos ht.le hu.le))
  have heval : (∫ u in Iio (0 : ℝ), Real.exp (t*u)) = 1/t := by
    rw [← integral_Iic_eq_integral_Iio, integral_exp_mul_Iic ht 0]
    simp only [mul_zero, Real.exp_zero]
  have he : IntegrableOn (fun u => Real.exp (t*u/2)^2) (Iio 0) := by
    simp_rw [hexp]
    exact Integrable.of_integral_ne_zero (by rw [heval]; positivity)
  have hcs := abs_integral_mul_le_sqrt
    (f := fun u => f u * Real.exp (t*u/2))
    (g := fun u => Real.exp (t*u/2))
    (μ := volume.restrict (Iio 0)) (by fun_prop) (by fun_prop) hsq he
  have hp : (fun u => f u * Real.exp (t*u/2) * Real.exp (t*u/2)) =
      fun u => f u * Real.exp (t*u) := by
    funext u
    rw [mul_assoc, ← sq, hexp]
  rw [hp, hsquare] at hcs
  simp_rw [hexp] at hcs
  rw [heval] at hcs
  have hmass := integral_exp_mul_Iio_le_of_terminal_mass hf
    (fun u _ => sq_nonneg (f u)) hbound ht
  calc
    _ ≤ Real.sqrt ((∫ u in Iio 0, f u^2 * Real.exp (t*u)) * (1/t)) := hcs
    _ ≤ Real.sqrt ((C/t)*(1/t)) := Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_right hmass (by positivity))
    _ = Real.sqrt C / t := by
      rw [show C/t*(1/t) = C/t^2 by ring, Real.sqrt_div hC,
        Real.sqrt_sq_eq_abs, abs_of_pos ht]

end GaloisForLFunctions.HTGeometry
