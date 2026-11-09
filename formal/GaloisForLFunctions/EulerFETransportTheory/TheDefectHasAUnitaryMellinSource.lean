import GaloisForLFunctions.EulerFETransportTheory.FiniteEnergyDefectsHaveCanonicalBoundaries
import GaloisForLFunctions.HTGeometry.HalfLineMellinUnitary
import GaloisForLFunctions.RHTower.HeatEchoCompleted
import GaloisForLFunctions.RHTower.UnitModulusL2Multiplier
import GaloisForLFunctions.RHTower.SoninL2Model
import GaloisForLFunctions.RHTower.L2FourierReflection
import GaloisForLFunctions.HTGeometry.GammaAnalyticOffPoles

/-!
# The Gamma–Mellin source of the functional-equation defect

Reflection and duplication factor the defect kernel through a constant-modulus Gamma
multiplier. Its Mellin synthesis is a scaled unitary onto the positive-half-line `L²` space.
-/

open Complex MeasureTheory Filter Topology Set
open RHTower.HamburgerStability
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace GaloisForLFunctions.EulerFETransportTheory

/-- The multiplier whose Gamma integral recovers the defect's inverse sine kernel. -/
def defectMellinMultiplier (t : ℝ) : ℂ :=
  (2 : ℂ) ^ linePt (2 * t) * Gamma (linePt (2 * t) / 2) /
    ((Real.sqrt Real.pi : ℂ) * Gamma ((1 - linePt (2 * t)) / 2))

private theorem gamma_quarter_ne_zero (t : ℝ) :
    Gamma (linePt (2 * t) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num [linePt])

private theorem gamma_reflected_quarter_ne_zero (t : ℝ) :
    Gamma ((1 - linePt (2 * t)) / 2) ≠ 0 :=
  Complex.Gamma_ne_zero_of_re_pos (by norm_num [linePt])

private theorem reflected_quarter_eq_conj (t : ℝ) :
    (1 - linePt (2 * t)) / 2 = star (linePt (2 * t) / 2) := by
  apply Complex.ext <;> simp [linePt] <;> ring

/-- The Gamma quotient has no loss of energy: its modulus is exactly `√2/√π`. -/
theorem norm_defectMellinMultiplier (t : ℝ) :
    ‖defectMellinMultiplier t‖ = Real.sqrt 2 / Real.sqrt Real.pi := by
  have hg := norm_ne_zero_iff.mpr (gamma_quarter_ne_zero t)
  have hconj : Gamma ((1 - linePt (2 * t)) / 2) =
      (starRingEnd ℂ) (Gamma (linePt (2 * t) / 2)) := by
    rw [reflected_quarter_eq_conj]
    exact Complex.Gamma_conj _
  rw [defectMellinMultiplier, norm_div, norm_mul, norm_mul,
    hconj, Complex.norm_conj,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [Complex.norm_cpow_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  have harg : (2 : ℂ).arg = 0 := by
    exact Complex.arg_ofReal_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)
  simp only [harg, zero_mul, Real.exp_zero, div_one]
  have hre : (linePt (2 * t)).re = (1 / 2 : ℝ) := by simp [linePt]
  rw [hre, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num, ← Real.sqrt_eq_rpow]
  field_simp

/-- Duplication and reflection recover the exact multiplier of the Hamburger kernel. -/
theorem defectMellinMultiplier_mul_gamma (t : ℝ) :
    defectMellinMultiplier t * Gamma (1 - linePt (2 * t)) =
      1 / Complex.sin ((Real.pi : ℂ) * (linePt (2 * t) / 2)) := by
  let s := linePt (2 * t)
  have hs0 : 0 < s.re := by norm_num [s, linePt]
  have hs2 : s.re < 2 := by norm_num [s, linePt]
  have hS : (Real.sqrt Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have hG : Gamma ((1 - s) / 2) ≠ 0 := gamma_reflected_quarter_ne_zero t
  have hsin : Complex.sin ((Real.pi : ℂ) * (s / 2)) ≠ 0 := by
    have h := _root_.RHTower.sin_pi_mul_half_ne_zero hs0 hs2
    rwa [show (Real.pi : ℂ) * s / 2 = (Real.pi : ℂ) * (s / 2) by ring] at h
  have hdup := _root_.RHTower.gamma_duplication_one_sub (s := s)
  have href := _root_.RHTower.sin_mul_gamma_half hs0 hs2
  rw [show (Real.pi : ℂ) * s / 2 = (Real.pi : ℂ) * (s / 2) by ring] at href
  have hsq : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  change (2 : ℂ) ^ s * Gamma (s / 2) /
      ((Real.sqrt Real.pi : ℂ) * Gamma ((1 - s) / 2)) * Gamma (1 - s) =
    1 / Complex.sin ((Real.pi : ℂ) * (s / 2))
  generalize hq : Complex.sin ((Real.pi : ℂ) * (s / 2)) = q at *
  field_simp [hS, hG, hsin]
  apply (mul_left_injective₀ hS)
  linear_combination Gamma ((1 - s) / 2) * href -
    (Gamma (s / 2) * q) * hdup +
    -Gamma ((1 - s) / 2) * hsq

/-- The normalized Gamma multiplier, of modulus one at every real frequency. -/
def defectMellinPhase (t : ℝ) : ℂ :=
  (Real.sqrt Real.pi / Real.sqrt 2 : ℂ) * defectMellinMultiplier t

theorem norm_defectMellinPhase (t : ℝ) : ‖defectMellinPhase t‖ = 1 := by
  rw [defectMellinPhase, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _),
    abs_of_nonneg (Real.sqrt_nonneg _), norm_defectMellinMultiplier]
  have hπ := (Real.sqrt_pos.mpr Real.pi_pos).ne'
  have h2 := (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  field_simp

theorem measurable_defectMellinMultiplier : Measurable defectMellinMultiplier := by
  have hs : Measurable (fun t : ℝ => linePt (2 * t)) := by
    unfold linePt
    fun_prop
  unfold defectMellinMultiplier
  simp_rw [Complex.cpow_def_of_ne_zero (by norm_num : (2 : ℂ) ≠ 0)]
  exact ((measurable_const.mul hs).cexp.mul
    (_root_.HTGeometry.measurable_Gamma.comp (hs.div_const 2))).div
      (measurable_const.mul
        (_root_.HTGeometry.measurable_Gamma.comp ((measurable_const.sub hs).div_const 2)))

private def defectMellinUnitPhase :
    GaloisForLFunctions.RHTower.UnitModulusL2Phase ℝ (volume : Measure ℝ) where
  toFun := defectMellinPhase
  aestronglyMeasurable :=
    (measurable_const.mul measurable_defectMellinMultiplier).aestronglyMeasurable
  norm_eq_one := Eventually.of_forall norm_defectMellinPhase

/-- The normalized source transform: Gamma phase, frequency reflection and dilation,
followed by inverse half-line Mellin synthesis. -/
def normalizedDefectMellinSource : DefectL2 ≃ₗᵢ[ℂ] HalfLineL2 :=
  defectMellinUnitPhase.mulUnitary.trans
    (((Lp.fourierTransformₗᵢ ℝ ℂ).trans (Lp.fourierTransformₗᵢ ℝ ℂ)).trans
      ((_root_.RHTower.dilationUnitary Real.pi Real.pi_pos).trans
        halfLineMellinUnitary.symm))

/-- The half-line source with the normalization of the actual Hamburger defect. -/
def defectMellinSource : DefectL2 →L[ℂ] HalfLineL2 :=
  ((Real.sqrt 2 * Real.pi : ℂ)⁻¹) •
    normalizedDefectMellinSource.toLinearIsometry.toContinuousLinearMap

theorem norm_defectMellinSource (g : DefectL2) :
    ‖defectMellinSource g‖ = (Real.sqrt 2 * Real.pi)⁻¹ * ‖g‖ := by
  change ‖(Real.sqrt 2 * Real.pi : ℂ)⁻¹ • normalizedDefectMellinSource g‖ = _
  rw [norm_smul, normalizedDefectMellinSource.norm_map, norm_inv, norm_mul,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _), abs_of_pos Real.pi_pos]

theorem norm_sq_defectMellinSource (g : DefectL2) :
    ‖defectMellinSource g‖ ^ 2 = (2 * Real.pi ^ 2)⁻¹ * ‖g‖ ^ 2 := by
  rw [norm_defectMellinSource, mul_pow, inv_pow, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]

/-- The exact spectral formula, with the sign and scale of the existing Mellin unitary. -/
theorem mellin_defectMellinSource (g : DefectL2) :
    (halfLineMellinUnitary (defectMellinSource g) : ℝ → ℂ) =ᵐ[volume]
      fun ξ => (1 / 2 : ℂ) * g (-Real.pi * ξ) * defectMellinMultiplier (-Real.pi * ξ) := by
  let f : DefectL2 := defectMellinUnitPhase.mulUnitary g
  let r : DefectL2 := _root_.RHTower.l2Reflection f
  let d : DefectL2 := _root_.RHTower.dilation Real.pi Real.pi_pos r
  let c : ℂ := (Real.sqrt 2 * Real.pi : ℂ)⁻¹
  have hm : halfLineMellinUnitary (defectMellinSource g) = c • d := by
    change halfLineMellinUnitary (c • halfLineMellinUnitary.symm
      (_root_.RHTower.dilationUnitary Real.pi Real.pi_pos
        ((Lp.fourierTransformₗᵢ ℝ ℂ) ((Lp.fourierTransformₗᵢ ℝ ℂ) f)))) = c • d
    rw [map_smul, LinearIsometryEquiv.apply_symm_apply, _root_.RHTower.l2_fourier_fourier]
    rfl
  have hr : (r : ℝ → ℂ) =ᵐ[volume] fun x => f (-x) :=
    Lp.coeFn_compMeasurePreserving f (Measure.measurePreserving_neg (volume : Measure ℝ))
  have hp := defectMellinUnitPhase.mulUnitary_ae g
  have hrπ := (_root_.RHTower.realMul_quasiMeasurePreserving
    Real.pi Real.pi_ne_zero).ae hr
  have hpπ := (_root_.RHTower.realMul_quasiMeasurePreserving
    (-Real.pi) (neg_ne_zero.mpr Real.pi_ne_zero)).ae hp
  have hS : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
  have hπ : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hsq2 : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hsqπ : (Real.sqrt Real.pi : ℂ) ^ 2 = (Real.pi : ℂ) := by
    exact_mod_cast Real.sq_sqrt Real.pi_pos.le
  have hc : c * (Real.sqrt Real.pi : ℂ) *
      ((Real.sqrt Real.pi : ℂ) / (Real.sqrt 2 : ℂ)) = (1 / 2 : ℂ) := by
    dsimp [c]
    field_simp
    linear_combination 2 * hsqπ - (Real.pi : ℂ) * hsq2
  rw [hm]
  filter_upwards [Lp.coeFn_smul c d,
    _root_.RHTower.dilation_ae Real.pi Real.pi_pos r, hrπ, hpπ] with ξ hs hd hr hp
  change (c • d : DefectL2) ξ = _ at hs
  rw [hs]
  change c * d ξ = _
  change d ξ = (Real.sqrt Real.pi : ℂ) * r (Real.pi * ξ) at hd
  change r (Real.pi * ξ) = f (-(Real.pi * ξ)) at hr
  change f (-Real.pi * ξ) = defectMellinPhase (-Real.pi * ξ) * g (-Real.pi * ξ) at hp
  rw [hd, hr, ← neg_mul, hp, defectMellinPhase]
  calc
    _ = (c * (Real.sqrt Real.pi : ℂ) *
        ((Real.sqrt Real.pi : ℂ) / (Real.sqrt 2 : ℂ))) *
          g (-Real.pi * ξ) * defectMellinMultiplier (-Real.pi * ξ) := by ring
    _ = _ := by rw [hc]

/-- Every half-line finite-energy source has a unique defect preimage. -/
theorem defectMellinSource_bijective : Function.Bijective defectMellinSource := by
  have hc : (Real.sqrt 2 * Real.pi : ℂ) ≠ 0 := by
    exact mul_ne_zero (by exact_mod_cast (Real.sqrt_pos.mpr
      (by norm_num : (0 : ℝ) < 2)).ne') (by exact_mod_cast Real.pi_ne_zero)
  constructor
  · intro g h heq
    apply normalizedDefectMellinSource.injective
    exact (smul_right_injective _ (inv_ne_zero hc)) heq
  · intro ψ
    refine ⟨normalizedDefectMellinSource.symm ((Real.sqrt 2 * Real.pi : ℂ) • ψ), ?_⟩
    change (Real.sqrt 2 * Real.pi : ℂ)⁻¹ •
      normalizedDefectMellinSource
        (normalizedDefectMellinSource.symm ((Real.sqrt 2 * Real.pi : ℂ) • ψ)) = ψ
    rw [LinearIsometryEquiv.apply_symm_apply, smul_smul, inv_mul_cancel₀ hc, one_smul]

end GaloisForLFunctions.EulerFETransportTheory

#print axioms GaloisForLFunctions.EulerFETransportTheory.defectMellinMultiplier_mul_gamma
#print axioms GaloisForLFunctions.EulerFETransportTheory.mellin_defectMellinSource
#print axioms GaloisForLFunctions.EulerFETransportTheory.norm_sq_defectMellinSource
#print axioms GaloisForLFunctions.EulerFETransportTheory.defectMellinSource_bijective
