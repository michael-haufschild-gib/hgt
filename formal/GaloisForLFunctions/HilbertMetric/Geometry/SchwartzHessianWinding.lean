import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzBonnetCharts
import GaloisForLFunctions.HilbertMetric.Geometry.WeightedKelvinWirtinger
import GaloisForLFunctions.RHTower.WindingHomotopy
import GaloisForLFunctions.RHTower.WindingArgumentPrinciple

/-!
# Winding of the explicit trace-free Hessian

The nonvanishing Hessian symbol has zero winding on every inverted circle,
since its domain contracts through the entire plane. Multiplication by the
fourth angular power produces winding four.
-/

open scoped ContDiff ComplexConjugate
namespace GaloisForLFunctions.HilbertMetric.Geometry.SchwartzHessianWinding
open GaloisForLFunctions.HTGeometry.GaussBonnet
open SeparableHessian SchwartzBonnetCharts BonnetSupport
open Complex
noncomputable section

/-- Complex coordinate of the actual trace-free Euclidean Hessian. -/
def hessianSymbol (z : ℂ) : ℂ :=
  ((px (px dampedSeedSchwartz) (z.re, z.im) -
    py (py dampedSeedSchwartz) (z.re, z.im) : ℝ) : ℂ) +
      2 * (py (px dampedSeedSchwartz) (z.re, z.im) : ℂ) * I

theorem hessianSymbol_continuous : Continuous hessianSymbol := by
  have hf : ContDiff ℝ ∞ (dampedSeedSchwartz : ℝ × ℝ → ℝ) := dampedSeedSchwartz.smooth ⊤
  have hxx := (contDiff_px (contDiff_px hf)).continuous.comp Complex.equivRealProdCLM.continuous
  have hyy := (contDiff_py (contDiff_py hf)).continuous.comp Complex.equivRealProdCLM.continuous
  have hxy := (contDiff_py (contDiff_px hf)).continuous.comp Complex.equivRealProdCLM.continuous
  exact (Complex.continuous_ofReal.comp (hxx.sub hyy)).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp hxy)).mul continuous_const)

/-- The symbol never vanishes, including where one of its real coordinates vanishes. -/
theorem hessianSymbol_ne_zero (z : ℂ) : hessianSymbol z ≠ 0 := by
  intro h
  have hr : px (px dampedSeedSchwartz) (z.re, z.im) =
      py (py dampedSeedSchwartz) (z.re, z.im) := by
    simpa [hessianSymbol, sub_eq_zero] using congrArg Complex.re h
  have hi : py (px dampedSeedSchwartz) (z.re, z.im) = 0 := by
    simpa [hessianSymbol] using congrArg Complex.im h
  apply south_radius_not_scalar (z.re, z.im)
  apply (radius_scalar_iff (dampedSeedSchwartz.smooth ⊤) amplitude_pos.ne' _).mpr
  exact ⟨hr, hi⟩

private theorem exp_loop_closed :
    Complex.exp (I * ((0 : ℝ) : ℂ)) = Complex.exp (I * ((2 * Real.pi : ℝ) : ℂ)) := by
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show I * ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi * I by push_cast; ring,
    Complex.exp_two_pi_mul_I]

/-- Inverted circular samples of the genuine Hessian symbol. -/
def inverseHessianLoop (r θ : ℝ) : ℂ :=
  hessianSymbol (((r : ℂ) * Complex.exp (I * (θ : ℂ)))⁻¹)

private theorem inverse_loop (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.IsLoop (inverseHessianLoop r) 0 (2 * Real.pi) := by
  refine ⟨?_, fun θ => hessianSymbol_ne_zero _, ?_⟩
  · apply hessianSymbol_continuous.comp
    exact (continuous_const.mul (Complex.continuous_exp.comp
      (continuous_const.mul Complex.continuous_ofReal))).inv₀
      (fun θ => mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _))
  · unfold inverseHessianLoop
    rw [exp_loop_closed]

/-- The inverted Hessian phase has winding zero at every nonzero radius. -/
theorem inverseHessianLoop_winding (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.windingNumber (inverseHessianLoop r) 0 (2 * Real.pi) = 0 := by
  let H : ℝ → ℝ → ℂ := fun s θ =>
    hessianSymbol (((1 - s : ℝ) : ℂ) * (((r : ℂ) * Complex.exp (I * (θ : ℂ)))⁻¹))
  have hcont : Continuous (fun p : ℝ × ℝ => H p.1 p.2) := by
    apply hessianSymbol_continuous.comp
    apply Continuous.mul
    · exact Complex.continuous_ofReal.comp (continuous_const.sub continuous_fst)
    · exact (continuous_const.mul (Complex.continuous_exp.comp
        (continuous_const.mul (Complex.continuous_ofReal.comp continuous_snd)))).inv₀
        (fun p => mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _))
  have hw := _root_.RHTower.windingNumber_of_homotopic (a := 0) (b := 2 * Real.pi) H hcont
    (fun s θ => hessianSymbol_ne_zero _)
    (fun s => congrArg (fun w : ℂ => hessianSymbol
      (((1 - s : ℝ) : ℂ) * ((r : ℂ) * w)⁻¹)) exp_loop_closed)
    (γ₀ := inverseHessianLoop r) (γ₁ := fun _ => hessianSymbol 0)
    (fun θ => by simp [H, inverseHessianLoop]) (fun θ => by simp [H])
  exact hw.trans (_root_.RHTower.windingNumber_const (hessianSymbol_ne_zero 0) _ _)

/-- The angular factor occurring in the weighted Kelvin Hessian transformation. -/
def fourthTwistedLoop (r θ : ℝ) : ℂ :=
  Complex.exp (I * (θ : ℂ)) ^ 4 * inverseHessianLoop r θ

/-- The fourth angular twist has exactly winding four, independent of the radius. -/
theorem fourthTwistedLoop_winding (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.windingNumber (fourthTwistedLoop r) 0 (2 * Real.pi) = 4 := by
  have he : _root_.RHTower.IsLoop (fun θ : ℝ => Complex.exp (I * (θ : ℂ))) 0
      (2 * Real.pi) := ⟨by fun_prop, fun θ => Complex.exp_ne_zero _, exp_loop_closed⟩
  have hp : _root_.RHTower.IsLoop (fun θ : ℝ => Complex.exp (I * (θ : ℂ)) ^ 4) 0
      (2 * Real.pi) := ⟨he.continuous.pow 4, fun θ => pow_ne_zero 4 (he.nonzero θ), by rw [he.closed]⟩
  change _root_.RHTower.windingNumber
    (fun θ => Complex.exp (I * (θ : ℂ)) ^ 4 * inverseHessianLoop r θ) 0 (2 * Real.pi) = 4
  rw [_root_.RHTower.windingNumber_mul hp (inverse_loop r hr),
    inverseHessianLoop_winding r hr, add_zero,
    _root_.RHTower.windingNumber_pow he 4, _root_.RHTower.windingNumber_circle]
  norm_num

/-- The actual smooth weighted Kelvin potential on the real plane. -/
def invertedPotential (p : ℝ × ℝ) : ℝ :=
  ‖(Complex.mk p.1 p.2 : ℂ)‖ ^ 2 *
    SchwartzInversion.kelvin complexPotential (Complex.mk p.1 p.2)

theorem invertedPotential_smooth : ContDiff ℝ ∞ invertedPotential :=
  ((contDiff_norm_sq ℂ).comp Complex.equivRealProdCLM.symm.contDiff).mul
    ((SchwartzInversion.kelvin_contDiff complexPotential).comp Complex.equivRealProdCLM.symm.contDiff)

private theorem complexLift_invertedPotential :
    WeightedKelvinWirtinger.complexLift invertedPotential =
      WeightedKelvinWirtinger.weightedKelvin
        (WeightedKelvinWirtinger.complexLift dampedSeedSchwartz) := by
  funext z
  change ((‖z‖ ^ 2 * SchwartzInversion.kelvin complexPotential z : ℝ) : ℂ) =
    z * (conj z * (dampedSeedSchwartz ((z⁻¹).re, (z⁻¹).im) : ℂ))
  by_cases hz : z = 0
  · subst z
    simp
  · rw [SchwartzInversion.kelvin_of_ne_zero _ hz]
    change ((‖z‖ ^ 2 * dampedSeedSchwartz ((z⁻¹).re, (z⁻¹).im) : ℝ) : ℂ) = _
    rw [Complex.ofReal_mul, Complex.sq_norm, ← Complex.mul_conj]
    ring

/-- Complex coordinate of the actual inverted real Hessian. -/
def invertedHessianSymbol (z : ℂ) : ℂ :=
  ((px (px invertedPotential) (z.re, z.im) -
    py (py invertedPotential) (z.re, z.im) : ℝ) : ℂ) +
      2 * (py (px invertedPotential) (z.re, z.im) : ℂ) * I

/-- The exact transformation law concerns the actual Hessians of both explicit real potentials. -/
theorem invertedHessianSymbol_eq {z : ℂ} (hz : z ≠ 0) :
    invertedHessianSymbol z = z / conj z ^ 3 * hessianSymbol z⁻¹ := by
  have hs : ContDiff ℝ ∞ (WeightedKelvinWirtinger.complexLift dampedSeedSchwartz) :=
    Complex.ofRealCLM.contDiff.comp
      ((dampedSeedSchwartz.smooth ⊤).comp Complex.equivRealProdCLM.contDiff)
  have hf := WeightedKelvinWirtinger.four_dzbar_twice_complexLift invertedPotential_smooth z
  have hu := WeightedKelvinWirtinger.four_dzbar_twice_complexLift
    (dampedSeedSchwartz.smooth ⊤) z⁻¹
  change 4 * _root_.HTGeometry.dzbar (_root_.HTGeometry.dzbar
    (WeightedKelvinWirtinger.complexLift dampedSeedSchwartz)) z⁻¹ = hessianSymbol z⁻¹ at hu
  rw [complexLift_invertedPotential, WeightedKelvinWirtinger.dzbar_twice_weightedKelvin hs hz] at hf
  change 4 * (z / conj z ^ 3 * _) = invertedHessianSymbol z at hf
  calc
    invertedHessianSymbol z = 4 * (z / conj z ^ 3 * _root_.HTGeometry.dzbar
      (_root_.HTGeometry.dzbar (WeightedKelvinWirtinger.complexLift dampedSeedSchwartz)) z⁻¹) := hf.symm
    _ = z / conj z ^ 3 * (4 * _root_.HTGeometry.dzbar
      (_root_.HTGeometry.dzbar (WeightedKelvinWirtinger.complexLift dampedSeedSchwartz)) z⁻¹) := by ring
    _ = _ := by rw [hu]

/-- Weighted inversion creates no additional scalar Hessian away from its flat origin. -/
theorem invertedHessianSymbol_ne_zero {z : ℂ} (hz : z ≠ 0) : invertedHessianSymbol z ≠ 0 := by
  rw [invertedHessianSymbol_eq hz]
  exact mul_ne_zero (div_ne_zero hz (pow_ne_zero 3 ((map_ne_zero (starRingEnd ℂ)).mpr hz)))
    (hessianSymbol_ne_zero _)

private theorem inverse_factor_on_circle (r θ : ℝ) (hr : r ≠ 0) :
    ((r : ℂ) * Complex.exp (I * (θ : ℂ))) /
        conj ((r : ℂ) * Complex.exp (I * (θ : ℂ))) ^ 3 =
      (r : ℂ)⁻¹ ^ 2 * Complex.exp (I * (θ : ℂ)) ^ 4 := by
  have hc : conj (Complex.exp (I * (θ : ℂ))) = (Complex.exp (I * (θ : ℂ)))⁻¹ := by
    rw [← Complex.exp_conj]
    rw [show conj (I * (θ : ℂ)) = -(I * (θ : ℂ)) by simp, Complex.exp_neg]
  rw [map_mul, Complex.conj_ofReal, hc]
  have hr0 := Complex.ofReal_ne_zero.mpr hr
  have he0 := Complex.exp_ne_zero (I * (θ : ℂ))
  field_simp

/-- The actual inverted Hessian on a circle is a positive constant times its fourth angular twist. -/
theorem invertedHessianSymbol_circle (r θ : ℝ) (hr : r ≠ 0) :
    invertedHessianSymbol ((r : ℂ) * Complex.exp (I * (θ : ℂ))) =
      (r : ℂ)⁻¹ ^ 2 * fourthTwistedLoop r θ := by
  rw [invertedHessianSymbol_eq
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)),
    inverse_factor_on_circle r θ hr]
  change _ = (r : ℂ)⁻¹ ^ 2 * (Complex.exp (I * (θ : ℂ)) ^ 4 * inverseHessianLoop r θ)
  unfold inverseHessianLoop
  ring

/-- The actual trace-free Hessian of the smooth inverted potential has winding exactly four. -/
theorem invertedHessianSymbol_winding (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.windingNumber
      (fun θ : ℝ => invertedHessianSymbol ((r : ℂ) * Complex.exp (I * (θ : ℂ))))
      0 (2 * Real.pi) = 4 := by
  have hf : (fun θ : ℝ => invertedHessianSymbol ((r : ℂ) * Complex.exp (I * (θ : ℂ)))) =
      fun θ => (r : ℂ)⁻¹ ^ 2 * fourthTwistedLoop r θ :=
    funext (fun θ : ℝ => invertedHessianSymbol_circle r θ hr)
  have he : _root_.RHTower.IsLoop (fun θ : ℝ => Complex.exp (I * (θ : ℂ))) 0
      (2 * Real.pi) := ⟨by fun_prop, fun θ => Complex.exp_ne_zero _, exp_loop_closed⟩
  have hi := inverse_loop r hr
  have ht : _root_.RHTower.IsLoop (fourthTwistedLoop r) 0 (2 * Real.pi) :=
    ⟨(he.continuous.pow 4).mul hi.continuous,
      fun θ => mul_ne_zero (pow_ne_zero 4 (he.nonzero θ)) (hi.nonzero θ),
      by change _ * _ = _ * _; rw [he.closed, hi.closed]⟩
  have hc : _root_.RHTower.IsLoop (fun _ : ℝ => (r : ℂ)⁻¹ ^ 2) 0 (2 * Real.pi) :=
    ⟨continuous_const, fun _ => pow_ne_zero 2 (inv_ne_zero (Complex.ofReal_ne_zero.mpr hr)), rfl⟩
  rw [hf, _root_.RHTower.windingNumber_mul hc ht,
    _root_.RHTower.windingNumber_const (hc.nonzero 0),
    fourthTwistedLoop_winding r hr, zero_add]

#print axioms invertedHessianSymbol_eq
#print axioms invertedHessianSymbol_ne_zero
#print axioms invertedHessianSymbol_winding
#print axioms hessianSymbol_ne_zero
#print axioms inverseHessianLoop_winding
#print axioms fourthTwistedLoop_winding
end
end GaloisForLFunctions.HilbertMetric.Geometry.SchwartzHessianWinding
