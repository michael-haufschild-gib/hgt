import GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap.FiniteMellinShift

/-!
# Finite Mellin rectangles at complex logarithmic frequencies

An imaginary clock shift twists the Mellin transform by an exponential.
Its norm consumes only part of the vertical decay, leaving the real-clock
rectangle estimate applicable with the reduced decay exponent.
-/

open Complex Set MeasureTheory
open GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap

/-- A bounded imaginary clock shift consumes only the corresponding vertical decay. -/
theorem norm_finite_complex_mellin_shift_le {F : ℂ → ℂ} {d T a r C : ℝ}
    {z : ℂ} {N : ℕ} (hd : 0 ≤ d) (hT : 0 ≤ T) (hz : 0 ≤ z.re)
    (hr : |z.im| ≤ r) (hra : r ≤ a) (hC : 0 ≤ C)
    (hF : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T → AnalyticAt ℂ F u)
    (hb : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
      ‖F u‖ ≤ C * (1 + |u.im|) ^ N * Real.exp (-(a * |u.im|))) :
    ‖∫ t : ℝ in (-T)..T, Complex.exp (z * ((t : ℂ) * I)) * F ((t : ℂ) * I)‖ ≤
      2 * T * C * (1 + T) ^ N * Real.exp (-(d * z.re)) +
        2 * d * C * (1 + T) ^ N * Real.exp (-((a - r) * T)) := by
  let Fv : ℂ → ℂ := fun u => Complex.exp ((z.im : ℂ) * I * u) * F u
  have hFv : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T → AnalyticAt ℂ Fv u := by
    intro u hleft hright hheight
    exact (by fun_prop : AnalyticAt ℂ (fun u : ℂ => Complex.exp ((z.im : ℂ) * I * u)) u).mul
      (hF u hleft hright hheight)
  have hb' : ∀ u : ℂ, -d ≤ u.re → u.re ≤ 0 → |u.im| ≤ T →
      ‖Fv u‖ ≤ C * (1 + |u.im|) ^ N * Real.exp (-((a - r) * |u.im|)) := by
    intro u hleft hright hheight
    have hphase : -(z.im * u.im) ≤ r * |u.im| := by
      calc
        _ ≤ |z.im * u.im| := neg_le_abs _
        _ = |z.im| * |u.im| := abs_mul _ _
        _ ≤ _ := mul_le_mul_of_nonneg_right hr (abs_nonneg _)
    have hnorm : ‖Complex.exp ((z.im : ℂ) * I * u)‖ = Real.exp (-(z.im * u.im)) := by
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re, Complex.mul_im]
    dsimp only [Fv]
    rw [norm_mul, hnorm]
    calc
      _ ≤ Real.exp (r * |u.im|) *
          (C * (1 + |u.im|) ^ N * Real.exp (-(a * |u.im|))) :=
        mul_le_mul (Real.exp_le_exp.mpr hphase) (hb u hleft hright hheight)
          (norm_nonneg _) (Real.exp_nonneg _)
      _ = (C * (1 + |u.im|) ^ N) *
          (Real.exp (r * |u.im|) * Real.exp (-(a * |u.im|))) := by ring
      _ = _ := by rw [← Real.exp_add]; congr 2; ring
  have h := norm_finite_mellin_shift_le hd hT hz (sub_nonneg.mpr hra) hC hFv hb'
  have heq : (fun t : ℝ => Complex.exp ((z.re : ℂ) * ((t : ℂ) * I)) * Fv ((t : ℂ) * I)) =
      fun t : ℝ => Complex.exp (z * ((t : ℂ) * I)) * F ((t : ℂ) * I) := by
    funext t
    dsimp only [Fv]
    rw [← mul_assoc, ← Complex.exp_add]
    rw [← add_mul, Complex.re_add_im]
  rw [heq] at h
  exact h

#print axioms norm_finite_complex_mellin_shift_le
end GaloisForLFunctions.ArithmeticScatteringHolography.ModularBootstrap
