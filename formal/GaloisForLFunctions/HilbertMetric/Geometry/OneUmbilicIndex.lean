import GaloisForLFunctions.HilbertMetric.Geometry.SchwartzHessianWinding
import GaloisForLFunctions.HilbertMetric.Geometry.NorthSupportRotation
import GaloisForLFunctions.HilbertMetric.Geometry.PrincipalLinePhase
import GaloisForLFunctions.HilbertMetric.Geometry.OneUmbilicSupport

/-!
# Index two of the unique umbilic

The actual north radius symbol is a positive scalar multiple of the
weighted Kelvin Hessian. Its winding is four. A unit principal direction
has square equal to the normalized radius symbol, so the unoriented
principal line has index two.
-/

open Complex Filter Topology
open scoped ComplexConjugate ContDiff
namespace GaloisForLFunctions.HilbertMetric.Geometry.OneUmbilicIndex
open BonnetSupport BonnetSurface StereographicFrame SeparableHessian
open SchwartzBonnetCharts SchwartzHessianWinding NorthSupportRotation PrincipalLinePhase
open GaloisForLFunctions.HTGeometry.GaussBonnet
noncomputable section

private def northSupportReal : ℝ × ℝ → ℝ := northSupportPlane dampedSeedSchwartz amplitude

private theorem northSupportReal_eq : northSupportReal = support invertedPotential amplitude := by
  funext p
  have hn : ‖(Complex.mk p.1 p.2 : ℂ)‖ ^ 2 = p.1 ^ 2 + p.2 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  change 1 + amplitude * (‖(Complex.mk p.1 p.2 : ℂ)‖ ^ 2 /
      (1 + ‖(Complex.mk p.1 p.2 : ℂ)‖ ^ 2) *
      SchwartzInversion.kelvin SchwartzBonnetCharts.complexPotential (Complex.mk p.1 p.2)) =
    1 + amplitude * (invertedPotential p * inverseDenominator p)
  unfold invertedPotential inverseDenominator denominator
  rw [hn]
  ring

/-- The trace-free radius symbol of the actual north support chart. -/
def northRadiusSymbol (z : ℂ) : ℂ :=
  symbol (radiusXX northSupportReal (z.re, z.im))
    (radiusXY northSupportReal (z.re, z.im)) (radiusYY northSupportReal (z.re, z.im))

/-- Exact identification of the geometric radius symbol with the actual inverted Hessian. -/
theorem northRadiusSymbol_eq (z : ℂ) :
    northRadiusSymbol z = ((amplitude * denominator (z.re, z.im) / 4 : ℝ) : ℂ) *
      invertedHessianSymbol z := by
  obtain ⟨hx, hy, hxy⟩ := radius_decomposition invertedPotential_smooth amplitude (z.re, z.im)
  simp only [northRadiusSymbol, northSupportReal_eq, symbol, hx, hy, hxy, invertedHessianSymbol]
  push_cast
  ring

/-- The actual north radius is nonscalar at every nonzero coordinate. -/
theorem northRadiusSymbol_ne_zero {z : ℂ} (hz : z ≠ 0) : northRadiusSymbol z ≠ 0 := by
  rw [northRadiusSymbol_eq]
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr
    (div_pos (mul_pos amplitude_pos (denominator_pos _)) (by norm_num)).ne')
      (invertedHessianSymbol_ne_zero hz)

private theorem denominator_circle (r θ : ℝ) :
    denominator (((r : ℂ) * exp (I * (θ : ℂ))).re, ((r : ℂ) * exp (I * (θ : ℂ))).im) =
      1 + r ^ 2 := by
  have hn : ‖(r : ℂ) * exp (I * (θ : ℂ))‖ ^ 2 = r ^ 2 := by
    rw [norm_mul, Complex.norm_exp]
    simp only [Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, mul_zero, sub_zero, Real.exp_zero, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [Complex.sq_norm, Complex.normSq_apply] at hn
  unfold denominator
  nlinarith only [hn]

private theorem invertedHessianSymbol_continuous : Continuous invertedHessianSymbol := by
  have hxx := (contDiff_px (contDiff_px invertedPotential_smooth)).continuous.comp
    Complex.equivRealProdCLM.continuous
  have hyy := (contDiff_py (contDiff_py invertedPotential_smooth)).continuous.comp
    Complex.equivRealProdCLM.continuous
  have hxy := (contDiff_py (contDiff_px invertedPotential_smooth)).continuous.comp
    Complex.equivRealProdCLM.continuous
  exact (Complex.continuous_ofReal.comp (hxx.sub hyy)).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp hxy)).mul continuous_const)

private theorem exp_loop_closed :
    exp (I * ((0 : ℝ) : ℂ)) = exp (I * ((2 * Real.pi : ℝ) : ℂ)) := by
  rw [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  rw [show I * ((2 * Real.pi : ℝ) : ℂ) = 2 * Real.pi * I by push_cast; ring,
    Complex.exp_two_pi_mul_I]

/-- The actual north radius symbol winds four times around its isolated scalar point. -/
theorem northRadiusSymbol_winding (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.windingNumber
      (fun θ : ℝ => northRadiusSymbol ((r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) = 4 := by
  let c : ℂ := ((amplitude * (1 + r ^ 2) / 4 : ℝ) : ℂ)
  have hc : c ≠ 0 := Complex.ofReal_ne_zero.mpr
    (div_pos (mul_pos amplitude_pos (by positivity : 0 < 1 + r ^ 2)) (by norm_num)).ne'
  have he : (fun θ : ℝ => northRadiusSymbol ((r : ℂ) * exp (I * (θ : ℂ)))) =
      fun θ : ℝ => c * invertedHessianSymbol ((r : ℂ) * exp (I * (θ : ℂ))) := by
    funext θ
    rw [northRadiusSymbol_eq, denominator_circle]
  have hi : _root_.RHTower.IsLoop
      (fun θ : ℝ => invertedHessianSymbol ((r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) := by
    refine ⟨invertedHessianSymbol_continuous.comp (by fun_prop), ?_, ?_⟩
    · intro θ
      exact invertedHessianSymbol_ne_zero
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _))
    · rw [exp_loop_closed]
  rw [he, _root_.RHTower.windingNumber_mul
    (⟨continuous_const, fun _ => hc, rfl⟩ : _root_.RHTower.IsLoop (fun _ : ℝ => c) 0 (2 * Real.pi)) hi,
    _root_.RHTower.windingNumber_const hc, invertedHessianSymbol_winding r hr, zero_add]

private theorem winding_normalize {γ : ℝ → ℂ} {a b : ℝ}
    (hγ : _root_.RHTower.IsLoop γ a b) :
    _root_.RHTower.windingNumber (fun t => γ t / (‖γ t‖ : ℂ)) a b =
      _root_.RHTower.windingNumber γ a b := by
  have hn (t : ℝ) : ‖γ t‖ ≠ 0 := norm_ne_zero_iff.mpr (hγ.nonzero t)
  have hδ : _root_.RHTower.IsLoop (fun t => (‖γ t‖ : ℂ)⁻¹) a b :=
    ⟨(Complex.continuous_ofReal.comp hγ.continuous.norm).inv₀
      (fun t => Complex.ofReal_ne_zero.mpr (hn t)),
      fun t => inv_ne_zero (Complex.ofReal_ne_zero.mpr (hn t)), by rw [hγ.closed]⟩
  have hL : Continuous (fun t => -(Real.log ‖γ t‖ : ℂ)) :=
    (Complex.continuous_ofReal.comp (hγ.continuous.norm.log hn)).neg
  have hExp (t : ℝ) : exp (-(Real.log ‖γ t‖ : ℂ)) = (‖γ t‖ : ℂ)⁻¹ := by
    rw [Complex.exp_neg, ← Complex.ofReal_exp, Real.exp_log (norm_pos_iff.mpr (hγ.nonzero t))]
  have hzero : _root_.RHTower.windingNumber (fun t => (‖γ t‖ : ℂ)⁻¹) a b = 0 :=
    (_root_.RHTower.windingNumber_eq_zero_iff hδ hL hExp).mpr (by rw [hγ.closed])
  change _root_.RHTower.windingNumber (fun t => γ t * (‖γ t‖ : ℂ)⁻¹) a b = _
  rw [_root_.RHTower.windingNumber_mul hγ hδ, hzero, add_zero]

/-- The actual squared unit principal-direction phase. -/
def principalPhase (z : ℂ) : ℂ := northRadiusSymbol z / (‖northRadiusSymbol z‖ : ℂ)

theorem principalPhase_norm {z : ℂ} (hz : z ≠ 0) : ‖principalPhase z‖ = 1 := by
  rw [principalPhase, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (norm_nonneg _), div_self (norm_ne_zero_iff.mpr (northRadiusSymbol_ne_zero hz))]

/-- Normalization to the actual squared unit direction preserves winding four. -/
theorem principalPhase_winding (r : ℝ) (hr : r ≠ 0) :
    _root_.RHTower.windingNumber
      (fun θ : ℝ => principalPhase ((r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) = 4 := by
  have hc : Continuous northRadiusSymbol := by
    have he : northRadiusSymbol = fun z =>
        ((amplitude * denominator (z.re, z.im) / 4 : ℝ) : ℂ) * invertedHessianSymbol z :=
      funext northRadiusSymbol_eq
    rw [he]
    apply Continuous.mul
    · apply Complex.continuous_ofReal.comp
      unfold denominator
      fun_prop
    · exact invertedHessianSymbol_continuous
  have hγ : _root_.RHTower.IsLoop
      (fun θ : ℝ => northRadiusSymbol ((r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) :=
    ⟨hc.comp (by fun_prop),
      fun θ => northRadiusSymbol_ne_zero
        (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) (Complex.exp_ne_zero _)),
      by rw [exp_loop_closed]⟩
  change _root_.RHTower.windingNumber
    (fun θ : ℝ => northRadiusSymbol ((r : ℂ) * exp (I * (θ : ℂ))) /
      (‖northRadiusSymbol ((r : ℂ) * exp (I * (θ : ℂ)))‖ : ℂ)) 0 (2 * Real.pi) = 4
  rw [winding_normalize hγ, northRadiusSymbol_winding r hr]

/-- Index of the unoriented principal line: half the degree of its squared unit direction. -/
def principalLineIndex (r : ℝ) : ℝ :=
  (_root_.RHTower.windingNumber
    (fun θ : ℝ => principalPhase ((r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) : ℝ) / 2

/-- The isolated umbilic has principal-line index two on every positive-radius circle. -/
theorem principalLineIndex_eq_two (r : ℝ) (hr : 0 < r) : principalLineIndex r = 2 := by
  rw [principalLineIndex, principalPhase_winding r hr.ne']
  norm_num

/-- Actual north normal and surface charts in real coordinates. -/
def actualNorthNormal (p : ℝ × ℝ) : Space := Bottcher.stereoInvExtended (Complex.mk p.1 p.2)

def actualNorthSurface (p : ℝ × ℝ) : Space :=
  SmoothSupportCompactification.north dampedSeedSchwartz amplitude (Complex.mk p.1 p.2)

private theorem actualNorthNormal_fderiv (p : ℝ × ℝ) :
    fderiv ℝ actualNorthNormal p = halfTurn.comp (fderiv ℝ normal p) := by
  have he : actualNorthNormal = fun q => halfTurn (normal q) := funext (fun q => (halfTurn_normal q).symm)
  rw [he]
  exact (halfTurn.hasFDerivAt.comp p ((normal_smooth.differentiable (by simp) p).hasFDerivAt)).fderiv

/-- Squared phase of the actual larger-radius principal direction is exactly the north radius phase. -/
theorem actual_principal_direction_iff_phase {z v : ℂ} (hz : z ≠ 0) (hv : ‖v‖ = 1) :
    fderiv ℝ actualNorthSurface (z.re, z.im) (v.re, v.im) =
      eigenPlus (radiusXX northSupportReal (z.re, z.im))
        (radiusXY northSupportReal (z.re, z.im)) (radiusYY northSupportReal (z.re, z.im)) •
          fderiv ℝ actualNorthNormal (z.re, z.im) (v.re, v.im) ↔
      v ^ 2 = northRadiusSymbol z / (‖northRadiusSymbol z‖ : ℂ) := by
  have hρ : ContDiff ℝ ∞ northSupportReal := northSupportPlane_smooth dampedSeedSchwartz amplitude
  have he := north_fderiv_eq_halfTurn_surface dampedSeedSchwartz (z.re, z.im)
  change fderiv ℝ actualNorthSurface (z.re, z.im) =
    halfTurn.comp (fderiv ℝ (surface northSupportReal) (z.re, z.im)) at he
  rw [he, actualNorthNormal_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ← map_smul]
  have hC : Function.Injective halfTurn :=
    Function.LeftInverse.injective halfTurn_involutive
  rw [hC.eq_iff]
  exact surface_principal_plus_iff_phase hρ (z.re, z.im) (northRadiusSymbol_ne_zero hz) hv

/-- The normal used in the principal-direction calculation is an actual unit normal. -/
theorem actualNorthNormal_unit (p : ℝ × ℝ) : ‖actualNorthNormal p‖ = 1 :=
  SphericalChartRecovery.norm_stereoInvExtended _

theorem actualNorthNormal_orthogonal (p w : ℝ × ℝ) :
    inner ℝ (actualNorthNormal p) (fderiv ℝ actualNorthSurface p w) = 0 := by
  have hn : actualNorthNormal p = halfTurn (normal p) := (halfTurn_normal p).symm
  have hd := north_fderiv_eq_halfTurn_surface dampedSeedSchwartz p
  change fderiv ℝ actualNorthSurface p = halfTurn.comp (fderiv ℝ (surface northSupportReal) p) at hd
  rw [hn, hd, ContinuousLinearMap.comp_apply, halfTurn_inner_move, halfTurn_involutive]
  have hρ : ContDiff ℝ ∞ northSupportReal := northSupportPlane_smooth dampedSeedSchwartz amplitude
  rw [surface_fderiv_apply hρ]
  obtain ⟨hx, hy⟩ := surface_normal hρ p
  simp only [inner_add_right, inner_smul_right, hx, hy, mul_zero, add_zero]

/-- The squared phase gives an actual scalar Gauss derivative along that principal direction. -/
theorem actual_principal_gauss {z v : ℂ} (hz : z ≠ 0) (hv : ‖v‖ = 1)
    (hphase : v ^ 2 = northRadiusSymbol z / (‖northRadiusSymbol z‖ : ℂ)) :
    ∃ κ : ℝ, fderiv ℝ actualNorthNormal (z.re, z.im) (v.re, v.im) =
      κ • fderiv ℝ actualNorthSurface (z.re, z.im) (v.re, v.im) := by
  let lam := eigenPlus (radiusXX northSupportReal (z.re, z.im))
    (radiusXY northSupportReal (z.re, z.im)) (radiusYY northSupportReal (z.re, z.im))
  have he := (actual_principal_direction_iff_phase hz hv).mpr hphase
  change fderiv ℝ actualNorthSurface (z.re, z.im) (v.re, v.im) =
    lam • fderiv ℝ actualNorthNormal (z.re, z.im) (v.re, v.im) at he
  have hlam : lam ≠ 0 := by
    intro h
    rw [h, zero_smul] at he
    have hi := north_plane_fderiv_injective dampedSeedSchwartz (z.re, z.im)
    change Function.Injective (fderiv ℝ actualNorthSurface (z.re, z.im)) at hi
    have hp : (v.re, v.im) = (0 : ℝ × ℝ) := hi (he.trans (map_zero _).symm)
    have hv0 : v = 0 := Complex.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp)
    rw [hv0, norm_zero] at hv
    exact zero_ne_one hv
  refine ⟨lam⁻¹, ?_⟩
  rw [he, smul_smul, inv_mul_cancel₀ hlam, one_smul]

/-- The concrete compact strictly convex smooth sphere has one umbilic, and its principal index is two. -/
theorem unique_umbilic_index_two :
    (∃! v : CompactifiedSupportSphere.Sphere,
      OneUmbilicSupport.scalarGaussOf OneUmbilicSupport.explicitSurface v) ∧
      ∀ r : ℝ, 0 < r → principalLineIndex r = 2 :=
  ⟨OneUmbilicSupport.existsUnique_actual_scalarGauss, principalLineIndex_eq_two⟩

#print axioms northRadiusSymbol_ne_zero
#print axioms northRadiusSymbol_winding
#print axioms principalPhase_norm
#print axioms principalPhase_winding
#print axioms principalLineIndex_eq_two
#print axioms actual_principal_direction_iff_phase
#print axioms actualNorthNormal_unit
#print axioms actualNorthNormal_orthogonal
#print axioms actual_principal_gauss
#print axioms unique_umbilic_index_two
end
end GaloisForLFunctions.HilbertMetric.Geometry.OneUmbilicIndex
