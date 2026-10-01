import GaloisForLFunctions.HTGeometry.BesselOrderPolyaRealZeros
import GaloisForLFunctions.RHTower.DeBruijnHeatFlowRealZeros

/-!
# The Pólya–Bessel kernel in the de Bruijn heat class

The kernel `g_a(x) = e^{−a cosh x}` (`a > 0`) is the symmetric model of the leading theta term of
Riemann's `Φ`. Its transform `∫ g_a(x) e^{izx} dx = 2 K_{iz}(a)` has only real zeros (Pólya's
theorem, `HTGeometry.im_eq_zero_of_modifiedBesselKOrder_I_mul_eq_zero`).

**Theorems.**
- `superExpKernel_polyaKernel`: `g_a` belongs to the de Bruijn heat class `SuperExpKernel`.
- `polyaKernel_mul_cosh_pow_zeros_real`: for every `λ > 0` and `j`, the transform of
  `g_a(x) cosh(λx)^j` has only real zeros.
- `polyaKernel_heat_zeros_real`: for every `t > 0`, the transform of `g_a(x) e^{t x²}` has only real
  zeros. So the de Bruijn–Newman constant of the Pólya–Bessel kernel is `≤ 0`, whereas for
  Riemann's kernel it is `≥ 0` (Newman's theorem in the corpus).
-/

open Complex MeasureTheory Set

namespace RHTower.DeBruijn

noncomputable section

/-- The Pólya–Bessel kernel `e^{−a cosh x}`. -/
def polyaKernel (a x : ℝ) : ℝ := Real.exp (-(a * Real.cosh x))

theorem superExpKernel_polyaKernel {a : ℝ} (ha : 0 < a) : SuperExpKernel (polyaKernel a) where
  continuous := by unfold polyaKernel; fun_prop
  even := fun x => by simp [polyaKernel, Real.cosh_neg]
  nonneg := fun x => (Real.exp_pos _).le
  pos_zero := Real.exp_pos _
  decay := by
    refine ⟨1, a / 2, 1, 0, zero_le_one, by positivity, one_pos, le_rfl, fun x => ?_⟩
    rw [one_mul, zero_mul, add_zero, polyaKernel, one_mul]
    apply Real.exp_le_exp.mpr
    have h : Real.exp |x| / 2 ≤ Real.cosh x := by
      rw [← Real.cosh_abs, Real.cosh_eq]
      linarith [Real.exp_pos (-|x|)]
    nlinarith

/-- The transform of the Pólya–Bessel kernel is `2 K_{iz}(a)`. -/
theorem cosTransform_polyaKernel {a : ℝ} (ha : 0 < a) (w : ℂ) :
    cosTransform (polyaKernel a) w =
      2 * GaloisForLFunctions.HTGeometry.modifiedBesselKOrder a (I * w) := by
  set F : ℝ → ℂ := fun x => (polyaKernel a x : ℂ) * Complex.exp (I * w * x) with hF
  have hint : Integrable F := by
    have hg := superExpKernel_polyaKernel ha
    exact hg.integrable w
  -- reflect the negative half-line
  have hrefl : ∫ x in Iic (0 : ℝ), F x = ∫ x in Ioi (0 : ℝ), F (-x) := by
    have h := integral_comp_neg_Ioi (0 : ℝ) F
    simp only [neg_zero] at h
    exact h.symm
  have hsplit : ∫ x, F x = (∫ x in Iic (0 : ℝ), F x) + ∫ x in Ioi (0 : ℝ), F x := by
    have h := MeasureTheory.integral_add_compl (measurableSet_Iic (a := (0 : ℝ))) hint
    simpa [Set.compl_Iic] using h.symm
  have hnegint : IntegrableOn (fun x => F (-x)) (Ioi 0) := by
    have := hint.comp_neg
    exact this.integrableOn
  have hpoint : ∀ x : ℝ, F (-x) + F x =
      2 * GaloisForLFunctions.HTGeometry.besselOrderKernel a (I * w) x := by
    intro x
    simp only [hF, polyaKernel, GaloisForLFunctions.HTGeometry.besselOrderKernel,
      Complex.ofReal_exp, Complex.ofReal_neg, Complex.ofReal_mul, Complex.ofReal_cosh,
      Complex.cosh]
    ring_nf
  change ∫ x, F x = _
  rw [hsplit, hrefl, ← integral_add hnegint hint.integrableOn,
    GaloisForLFunctions.HTGeometry.modifiedBesselKOrder, ← MeasureTheory.integral_const_mul]
  exact setIntegral_congr_fun measurableSet_Ioi fun x _ => hpoint x

/-- Every zero of the transform of the Pólya–Bessel kernel is real. -/
theorem polyaKernel_cosTransform_zeros_real {a : ℝ} (ha : 0 < a) {w : ℂ}
    (hw : cosTransform (polyaKernel a) w = 0) : w.im = 0 := by
  rw [cosTransform_polyaKernel ha] at hw
  exact GaloisForLFunctions.HTGeometry.im_eq_zero_of_modifiedBesselKOrder_I_mul_eq_zero ha
    ((mul_eq_zero.mp hw).resolve_left two_ne_zero)

/-- **Cosh-power multiples stay real-rooted.** -/
theorem polyaKernel_mul_cosh_pow_zeros_real {a : ℝ} (ha : 0 < a) {lam : ℝ} (hlam : 0 < lam)
    (j : ℕ) {w : ℂ}
    (hw : cosTransform (fun x => polyaKernel a x * Real.cosh (lam * x) ^ j) w = 0) :
    w.im = 0 := by
  have h := (superExpKernel_polyaKernel ha).zeros_mul_cosh_pow (D := 0)
    (fun w hw => by rw [polyaKernel_cosTransform_zeros_real ha hw]; simp) hlam j w hw
  have : max (0 - (j : ℝ) * lam ^ 2) 0 = 0 := max_eq_right (by nlinarith [sq_nonneg lam])
  rw [this] at h
  exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm h (sq_nonneg _))

/-- **The Pólya–Bessel kernel has de Bruijn–Newman constant `≤ 0`.** -/
theorem polyaKernel_heat_zeros_real {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : 0 < t) {w : ℂ}
    (hw : cosTransform (fun x => polyaKernel a x * Real.exp (t * x ^ 2)) w = 0) : w.im = 0 :=
  cosTransform_heat_zeros_real (superExpKernel_polyaKernel ha) (D := 0)
    (fun w hw => by rw [polyaKernel_cosTransform_zeros_real ha hw]; simp) (by linarith) ht w hw

end

end RHTower.DeBruijn
