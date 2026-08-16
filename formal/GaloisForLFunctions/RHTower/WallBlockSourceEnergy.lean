import GaloisForLFunctions.RHTower.WallForcedProfileWindow
import GaloisForLFunctions.RHTower.WallBlockSliceProfile

/-!
# The energy of the block source

The source of the one-block equation is the angular transform of the profile, halved and rotated by
`−i/2`.  Its frequency energy is therefore `π/2` times the physical energy: the Plancherel factor
`2π` divided by four.  This is the card's `(12)` in the form the window estimate consumes, and it is
the only place the source's normalisation enters the constant.
-/

open Complex MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [CompleteSpace X]

omit [CompleteSpace X] in
/-- The block source is the angular transform of the profile, halved and rotated. -/
theorem blockSource_eq_angularTransform {g : ℝ → X} {m : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (t : ℝ) :
    blockSource g m t = (-(Complex.I) / 2 : ℂ) • vectorAngularTransform g t := by
  rw [blockSource, vectorAngularTransform]
  congr 1
  have hext : (∫ L in Icc m (m + 1), Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L)
      = ∫ L : ℝ, Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L :=
    setIntegral_eq_integral_of_forall_compl_eq_zero
      (fun L hL => by rw [hsupp L hL, smul_zero])
  rw [hext]
  refine integral_congr_ae (Filter.Eventually.of_forall fun L => ?_)
  have hcomm : -(Complex.I) * (L : ℂ) * (t : ℂ) = -(Complex.I) * (t : ℂ) * (L : ℂ) := by ring
  show Complex.exp (-(Complex.I) * (L : ℂ) * (t : ℂ)) • g L
      = Complex.exp (-(Complex.I) * (t : ℂ) * (L : ℂ)) • g L
  rw [hcomm]

omit [CompleteSpace X] in
theorem norm_blockSource {g : ℝ → X} {m : ℝ}
    (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) (t : ℝ) :
    ‖blockSource g m t‖ = (1 / 2) * ‖vectorAngularTransform g t‖ := by
  rw [blockSource_eq_angularTransform hsupp, norm_smul]
  congr 1
  rw [norm_div, norm_neg, Complex.norm_I]
  norm_num

/-- **`(12)` for the block source.**  Its frequency energy is `π/2` times the physical energy: the
Plancherel factor `2π` halved twice by the factor `−i/2`. -/
theorem integral_norm_sq_blockSource {g : ℝ → X} {m : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫ t : ℝ, ‖blockSource g m t‖ ^ 2) = (Real.pi / 2) * ∫ L : ℝ, ‖g L‖ ^ 2 := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hpar := integral_norm_sq_vectorAngularTransform_eq hg1 hg2
  have hrw : (fun t : ℝ => ‖blockSource g m t‖ ^ 2)
      = fun t : ℝ => (1 / 4 : ℝ) * ‖vectorAngularTransform g t‖ ^ 2 := by
    funext t
    rw [norm_blockSource hsupp]
    ring
  rw [hrw, integral_const_mul, hpar]
  ring

open scoped ENNReal

/-- The block source is square integrable on the line. -/
theorem integrable_norm_sq_blockSource {g : ℝ → X} {m : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    Integrable (fun t : ℝ => ‖blockSource g m t‖ ^ 2) (volume : Measure ℝ) := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hbase := integrable_norm_sq_vectorAngularTransform hg1 hg2
  have hrw : (fun t : ℝ => ‖blockSource g m t‖ ^ 2)
      = fun t : ℝ => (1 / 4 : ℝ) * ‖vectorAngularTransform g t‖ ^ 2 := by
    funext t
    rw [norm_blockSource hsupp]
    ring
  rw [hrw]
  exact hbase.const_mul _

/-- The extended frequency energy of the block source. -/
theorem lintegral_enorm_sq_blockSource {g : ℝ → X} {m : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫⁻ t : ℝ, ‖blockSource g m t‖ₑ ^ 2)
      = ENNReal.ofReal ((Real.pi / 2) * ∫ L : ℝ, ‖g L‖ ^ 2) := by
  rw [lintegral_enorm_sq_eq_ofReal_integral (integrable_norm_sq_blockSource hg2 hsupp),
    integral_norm_sq_blockSource hg2 hsupp]

omit [CompleteSpace X] in
/-- The block source is measurable, being a parametrised Fourier integral. -/
theorem aestronglyMeasurable_blockSource {g : ℝ → X} {m : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    AEStronglyMeasurable (fun t : ℝ => blockSource g m t) (volume : Measure ℝ) := by
  have hrw : (fun t : ℝ => blockSource g m t)
      = fun t : ℝ => (-(Complex.I) / 2 : ℂ) • vectorAngularTransform g t := by
    funext t
    exact blockSource_eq_angularTransform hsupp t
  rw [hrw]
  refine AEStronglyMeasurable.const_smul ?_ _
  have hjoint : AEStronglyMeasurable (Function.uncurry fun (t : ℝ) (x : ℝ) =>
      Complex.exp (-(Complex.I) * (t : ℂ) * (x : ℂ)) • g x)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
    have hph : Continuous fun p : ℝ × ℝ =>
        Complex.exp (-(Complex.I) * (p.1 : ℂ) * (p.2 : ℂ)) := by fun_prop
    exact hph.aestronglyMeasurable.smul (hg2.aestronglyMeasurable.comp_snd)
  exact hjoint.integral_prod_right'

/-- **The `L¹` mass of the block source on the window costs one half power of the window.** -/
theorem sq_lintegral_enorm_blockSource_window_le {g : ℝ → X} {m Y : ℝ}
    (hg2 : MemLp g 2 (volume : Measure ℝ)) (hsupp : ∀ L : ℝ, L ∉ Icc m (m + 1) → g L = 0) :
    (∫⁻ t in uIoc (0 : ℝ) Y, ‖blockSource g m t‖ₑ) ^ 2
      ≤ ENNReal.ofReal |Y| * ENNReal.ofReal ((Real.pi / 2) * ∫ L : ℝ, ‖g L‖ ^ 2) := by
  have hg1 : Integrable g := integrable_zeroExtension hg2 hsupp
  have hmeas : AEMeasurable (fun t : ℝ => ‖blockSource g m t‖ₑ)
      (volume.restrict (uIoc (0 : ℝ) Y)) :=
    ((aestronglyMeasurable_blockSource hg2 hsupp).restrict).enorm
  have hCS := GaloisForLFunctions.HTGeometry.sq_lintegral_le_measure_mul hmeas
  refine hCS.trans ?_
  have hvol : volume (uIoc (0 : ℝ) Y) = ENNReal.ofReal |Y| := by
    rw [Real.volume_uIoc, sub_zero]
  have hsub : (∫⁻ t in uIoc (0 : ℝ) Y, ‖blockSource g m t‖ₑ ^ 2)
      ≤ ∫⁻ t : ℝ, ‖blockSource g m t‖ₑ ^ 2 := setLIntegral_le_lintegral _ _
  rw [hvol]
  exact mul_le_mul' le_rfl (hsub.trans (le_of_eq (lintegral_enorm_sq_blockSource hg2 hsupp)))

end GaloisForLFunctions.RHTower
