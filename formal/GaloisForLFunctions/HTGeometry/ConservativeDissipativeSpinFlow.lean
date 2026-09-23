import GaloisForLFunctions.HTGeometry.ConservativeDissipativeSpin
import GaloisForLFunctions.Bottcher.MartyCriterion
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric

set_option autoImplicit false

/-!
# Exact stereographic Landau–Lifshitz evolution

The spin energy mechanism of Schaffer–Exl (arXiv:2609.04530) acts on the
existing stereographic sphere in the Böttcher/Montel corpus. Multiplication
by `exp ((-a² - I)t)` in the chart gives an actual global solution of the
established cross-product spin field for a constant north-directed energy
gradient. The trajectory preserves unit spin length, has exact exponential
chart-radius damping, and inherits its exact round speed from Marty's
conformality theorem.
-/
open scoped Matrix RealInnerProductSpace
namespace GaloisForLFunctions.HTGeometry.SchafferExl
noncomputable section

/-- Complex generator of damped precession in the existing stereographic chart. -/
def spinPlaneRate (a : ℝ) : ℂ := ((-a ^ (2 : ℕ) : ℝ) : ℂ) - Complex.I

theorem spinPlaneRate_re (a : ℝ) : (spinPlaneRate a).re = -a ^ (2 : ℕ) := by
  change -a ^ (2 : ℕ) - 0 = -a ^ (2 : ℕ)
  ring

theorem spinPlaneRate_im (a : ℝ) : (spinPlaneRate a).im = -1 := by
  change (0 : ℝ) - 1 = -1
  ring

/-- Exact global chart flow, with the paper's nonnegative damping constructed as a square. -/
def spinPlaneFlow (a : ℝ) (z : ℂ) (t : ℝ) : ℂ :=
  Complex.exp (spinPlaneRate a * (t : ℂ)) * z

/-- The real-time chart evolution solves its scalar complex linear equation. -/
theorem hasDerivAt_spinPlaneFlow (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinPlaneFlow a z) (spinPlaneRate a * spinPlaneFlow a z t) t := by
  have ht : HasDerivAt (fun s : ℝ => (s : ℂ)) (1 : ℂ) t := Complex.ofRealCLM.hasDerivAt
  have h := ((ht.const_mul (spinPlaneRate a)).cexp).mul_const z
  apply h.congr_deriv
  simp only [spinPlaneFlow]
  ring

theorem spinPlaneFlow_zero (a : ℝ) (z : ℂ) : spinPlaneFlow a z 0 = z := by
  simp [spinPlaneFlow]

/-- The chart evolution is an exact group for arbitrary real times. -/
theorem spinPlaneFlow_add (a : ℝ) (z : ℂ) (s t : ℝ) :
    spinPlaneFlow a z (s + t) = spinPlaneFlow a (spinPlaneFlow a z s) t := by
  simp only [spinPlaneFlow, Complex.ofReal_add, mul_add, Complex.exp_add]
  ring

/-- Precession changes phase only; the chart radius has exact exponential damping. -/
theorem spinPlaneFlow_norm (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinPlaneFlow a z t‖ = Real.exp (-a ^ (2 : ℕ) * t) * ‖z‖ := by
  simp only [spinPlaneFlow, norm_mul, Complex.norm_exp, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, spinPlaneRate_re, mul_zero, sub_zero]

/-- Exact squared-radius damping in the stereographic coordinate. -/
theorem spinPlaneFlow_norm_sq (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinPlaneFlow a z t‖ ^ (2 : ℕ) = Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z‖ ^ (2 : ℕ) := by
  rw [spinPlaneFlow_norm, mul_pow]
  have h : Real.exp (-a ^ (2 : ℕ) * t) ^ (2 : ℕ) = Real.exp (-2 * a ^ (2 : ℕ) * t) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [h]

/-- Actual sphere trajectory obtained through the existing Böttcher stereographic map. -/
def spinSphereFlow (a : ℝ) (z : ℂ) (t : ℝ) : EuclideanSpace ℝ (Fin 3) :=
  _root_.Bottcher.stereo (spinPlaneFlow a z t)

/-- The established Landau–Lifshitz field in the Euclidean three-dimensional norm. -/
def spinSphereField (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (spinField m.ofLp (![0, 0, 1]) a)

/-- Explicit north-gradient precession and double-cross damping components. -/
theorem spinSphereField_components (a : ℝ) (m : EuclideanSpace ℝ (Fin 3)) :
    spinSphereField a m =
      !₂[m 1 + a ^ (2 : ℕ) * m 2 * m 0, -m 0 + a ^ (2 : ℕ) * m 2 * m 1,
        -a ^ (2 : ℕ) * (m 0 ^ (2 : ℕ) + m 1 ^ (2 : ℕ))] := by
  ext i
  fin_cases i <;> simp [spinSphereField, spinField, cross_apply] <;> ring

/-- The constructed trajectory preserves unit spin length at every real time. -/
theorem spinSphereFlow_norm (a : ℝ) (z : ℂ) (t : ℝ) : ‖spinSphereFlow a z t‖ = 1 :=
  _root_.Bottcher.norm_stereo_eq_one _

theorem spinSphereFlow_zero (a : ℝ) (z : ℂ) : spinSphereFlow a z 0 = _root_.Bottcher.stereo z := by
  rw [spinSphereFlow, spinPlaneFlow_zero]

/-- The actual global sphere trajectory solves the paper's Landau–Lifshitz equation. -/
theorem hasDerivAt_spinSphereFlow (a : ℝ) (z : ℂ) (t : ℝ) :
    HasDerivAt (spinSphereFlow a z) (spinSphereField a (spinSphereFlow a z t)) t := by
  let w := spinPlaneFlow a z
  have hw := hasDerivAt_spinPlaneFlow a z t
  have hu : HasDerivAt (fun s => (w s).re) (-a ^ (2 : ℕ) * (w t).re + (w t).im) t := by
    apply (Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hw).congr_deriv
    change (spinPlaneRate a * w t).re = _
    rw [Complex.mul_re, spinPlaneRate_re, spinPlaneRate_im]
    ring
  have hv : HasDerivAt (fun s => (w s).im) (-(w t).re - a ^ (2 : ℕ) * (w t).im) t := by
    apply (Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hw).congr_deriv
    change (spinPlaneRate a * w t).im = _
    rw [Complex.mul_im, spinPlaneRate_re, spinPlaneRate_im]
    ring
  have hn : ∀ s, ‖w s‖ ^ (2 : ℕ) = (w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ) := by
    intro s
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  have hD : HasDerivAt (fun s => 1 + ((w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ)))
      (-2 * a ^ (2 : ℕ) * ((w t).re ^ (2 : ℕ) + (w t).im ^ (2 : ℕ))) t := by
    apply ((hasDerivAt_const t (1 : ℝ)).add ((hu.pow 2).add (hv.pow 2))).congr_deriv
    ring
  have hd : 1 + ((w t).re ^ (2 : ℕ) + (w t).im ^ (2 : ℕ)) ≠ 0 := by positivity
  have hst : spinSphereFlow a z = fun s =>
      (!₂[2 * (w s).re / (1 + ((w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ))),
        2 * (w s).im / (1 + ((w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ))),
        ((w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ) - 1) / (1 + ((w s).re ^ (2 : ℕ) + (w s).im ^ (2 : ℕ)))]
        : EuclideanSpace ℝ (Fin 3)) := by
    funext s
    unfold spinSphereFlow
    change _root_.Bottcher.stereo (w s) = _
    rw [_root_.Bottcher.stereo, hn]
  have hc := _root_.Bottcher.hasDerivAt_euclidean3
    ((hu.const_mul 2).div hD hd) ((hv.const_mul 2).div hD hd)
    ((((hu.pow 2).add (hv.pow 2)).sub_const (1 : ℝ)).div hD hd)
  rw [hst]
  apply hc.congr_deriv
  rw [spinSphereField_components]
  ext i
  fin_cases i <;> simp <;> field_simp <;> ring

/-- Existing Marty conformality gives the exact speed of the genuine spin evolution. -/
theorem spinSphereFlow_speed (a : ℝ) (z : ℂ) (t : ℝ) :
    ‖spinSphereField a (spinSphereFlow a z t)‖ =
      2 * ‖spinPlaneRate a * spinPlaneFlow a z t‖ / (1 + ‖spinPlaneFlow a z t‖ ^ (2 : ℕ)) := by
  obtain ⟨V, hV, hn⟩ := _root_.Bottcher.hasDerivAt_stereo_path (hasDerivAt_spinPlaneFlow a z t)
  have he := (hasDerivAt_spinSphereFlow a z t).unique hV
  rw [← he] at hn
  exact hn

/-- The spin energy has a closed expression in the exponentially damped chart radius. -/
theorem spinSphereFlow_energy (a : ℝ) (z : ℂ) (t : ℝ) :
    spinSphereFlow a z t (2 : Fin 3) =
      (Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z‖ ^ (2 : ℕ) - 1) /
        (1 + Real.exp (-2 * a ^ (2 : ℕ) * t) * ‖z‖ ^ (2 : ℕ)) := by
  simp [spinSphereFlow, _root_.Bottcher.stereo, spinPlaneFlow_norm_sq]

end
end GaloisForLFunctions.HTGeometry.SchafferExl
