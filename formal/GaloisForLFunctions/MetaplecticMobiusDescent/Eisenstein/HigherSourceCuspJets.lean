import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.BesselFourierSmoothness
import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.HigherCuspWirtingerJets

/-!
# Higher cusp reflection for the actual cubic source

The residual cubic source is jointly smooth in positive cusp coordinates, as are all its fixed
hyperbolic translates. Its normalized pure Wirtinger jets therefore obey the exact cusp
reflection law at every order. The absolute reflection scale is independent of that order.
-/

open Complex Set Filter
open scoped ContDiff Topology ComplexConjugate MatrixGroups
open HTGeometry
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

/-- Hyperbolic coordinate changes are smooth throughout the positive-height half-space. -/
theorem contDiffOn_mobiusCoordinates (g : SL(2, ℂ)) :
    ContDiffOn ℝ ∞ (mobiusCoordinates g) (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  intro p hp
  have hd : mobiusCoordinateDenominator g p ≠ 0 :=
    (mobiusCoordinateDenominator_pos g p hp.1).ne'
  have hlin : ContDiff ℝ ∞ (fun q : ℝ × ℂ => g 1 0 * q.2 + g 1 1) :=
    (contDiff_const.mul contDiff_snd).add contDiff_const
  have hre := Complex.reCLM.contDiff.comp hlin
  have him := Complex.imCLM.contDiff.comp hlin
  have hden : ContDiff ℝ ∞ (mobiusCoordinateDenominator g) := by
    change ContDiff ℝ ∞ (fun q : ℝ × ℂ =>
      (g 1 0 * q.2 + g 1 1).re * (g 1 0 * q.2 + g 1 1).re +
      (g 1 0 * q.2 + g 1 1).im * (g 1 0 * q.2 + g 1 1).im +
      Complex.normSq (g 1 0) * q.1 ^ 2)
    exact ((hre.mul hre).add (him.mul him)).add (contDiff_const.mul (contDiff_fst.pow 2))
  have hinv : ContDiffAt ℝ ∞ (fun q => (mobiusCoordinateDenominator g q)⁻¹) p :=
    hden.contDiffAt.inv hd
  have hheight : ContDiffAt ℝ ∞
      (fun q : ℝ × ℂ => q.1 / mobiusCoordinateDenominator g q) p := by
    simpa only [div_eq_mul_inv] using contDiffAt_fst.mul hinv
  have hnum : ContDiffAt ℝ ∞ (fun q : ℝ × ℂ =>
      (g 0 0 * q.2 + g 0 1) * star (g 1 0 * q.2 + g 1 1) +
        g 0 0 * star (g 1 0) * (q.1 : ℂ) ^ 2) p := by
    exact (((contDiff_const.mul contDiff_snd).add contDiff_const).mul
      (Complex.conjCLE.contDiff.comp hlin) |>.add
      (contDiff_const.mul ((Complex.ofRealCLM.contDiff.comp contDiff_fst).pow 2))).contDiffAt
  apply ContDiffAt.contDiffWithinAt
  apply hheight.prodMk
  simpa only [Complex.ofReal_inv, div_eq_mul_inv, Function.comp_def,
    Complex.ofRealCLM_apply] using
    hnum.mul (Complex.ofRealCLM.contDiff.contDiffAt.comp p hinv)

/-- Every fixed cusp translate of the actual residual source is smooth to all orders. -/
theorem cubicSourceResidualFunction_translate_coordinate_contDiffOn (g : SL(2, ℂ)) :
    ContDiffOn ℝ ∞ (fun p : ℝ × ℂ => cubicSourceResidualFunction (g • cuspCoordinateLift p))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) := by
  have hcomp := cubicSourceResidualFunction_coordinate_contDiffOn.comp
    (contDiffOn_mobiusCoordinates g)
    (fun p hp => ⟨mobiusCoordinates_height_pos g p hp.1, mem_univ _⟩)
  apply hcomp.congr
  intro p hp
  exact congrArg cubicSourceResidualFunction (mobiusCoordinates_lift g p hp.1).symm

/-- The normalized higher cusp law for any source smooth in the translated cusp coordinates. -/
theorem coordinate_cusp_normalized_iterated_wirtinger_rule
    (f : HyperbolicSpace → ℂ) (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v)
    (hf : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ => f (g • cuspCoordinateLift q))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ))) (n : ℕ) :
    (v : ℂ) ^ n * iteratedDzbar (n + 1)
        (fun z => f (upperPoint (z + g 0 0 / g 1 0) v hv)) 0 =
      (-conj (g 1 0) / g 1 0) ^ (n + 1) /
          ((‖g 1 0‖ ^ 2 * v ^ 2 : ℝ) : ℂ) *
        (((1 / (‖g 1 0‖ ^ 2 * v) : ℝ) : ℂ) ^ n *
          iteratedDz (n + 1)
            (fun z => f (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
            (-g 1 1 / g 1 0)) := by
  have hpos : 0 < 1 / (‖g 1 0‖ ^ 2 * v) := by positivity
  have he : (fun z => f (g • cuspCoordinateLift
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z))) =
      fun z => f (upperPoint (z + g 0 0 / g 1 0) v hv) := by
    funext z
    rw [show cuspCoordinateLift (inverseCuspCoordinates (g 1 0) (g 1 1) v z) =
      upperPoint (inverseCuspCoordinates (g 1 0) (g 1 1) v z).2
        (inverseCuspCoordinates (g 1 0) (g 1 1) v z).1
        (inverseCuspCoordinates_height_pos _ _ _ _ hc hv) from cuspCoordinateLift_positive _ _ _,
      ← inverse_cusp_action g hc v hv z, smul_inv_smul]
  have hr := inverse_cusp_normalized_iterated_wirtinger_rule
    (g 1 0) (g 1 1) v hc hv (isOpen_Ioi.prod isOpen_univ)
    ⟨hpos, mem_univ _⟩ hf n
  rw [he] at hr
  simpa only [cuspCoordinateLift_positive _ _ hpos] using hr

/-- All normalized pure jets of the actual cubic residual source reflect at every finite cusp. -/
theorem cubicSourceResidualFunction_normalized_cusp_jets
    (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) (n : ℕ) :
    (v : ℂ) ^ n * iteratedDzbar (n + 1)
        (fun z => cubicSourceResidualFunction (upperPoint (z + g 0 0 / g 1 0) v hv)) 0 =
      (-conj (g 1 0) / g 1 0) ^ (n + 1) /
          ((‖g 1 0‖ ^ 2 * v ^ 2 : ℝ) : ℂ) *
        (((1 / (‖g 1 0‖ ^ 2 * v) : ℝ) : ℂ) ^ n *
          iteratedDz (n + 1)
            (fun z => cubicSourceResidualFunction
              (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity)))
            (-g 1 1 / g 1 0)) :=
  coordinate_cusp_normalized_iterated_wirtinger_rule cubicSourceResidualFunction g hc v hv
    (cubicSourceResidualFunction_translate_coordinate_contDiffOn g) n

/-- The conjugate source used in cubic Gauss twists obeys the same all-order reflection law. -/
theorem conjugate_cubicSourceResidualFunction_normalized_cusp_jets
    (g : SL(2, ℂ)) (hc : g 1 0 ≠ 0) (v : ℝ) (hv : 0 < v) (n : ℕ) :
    (v : ℂ) ^ n * iteratedDzbar (n + 1)
        (fun z => conj (cubicSourceResidualFunction (upperPoint (z + g 0 0 / g 1 0) v hv))) 0 =
      (-conj (g 1 0) / g 1 0) ^ (n + 1) /
          ((‖g 1 0‖ ^ 2 * v ^ 2 : ℝ) : ℂ) *
        (((1 / (‖g 1 0‖ ^ 2 * v) : ℝ) : ℂ) ^ n *
          iteratedDz (n + 1)
            (fun z => conj (cubicSourceResidualFunction
              (g • upperPoint z (1 / (‖g 1 0‖ ^ 2 * v)) (by positivity))))
            (-g 1 1 / g 1 0)) := by
  have hf : ContDiffOn ℝ ∞ (fun q : ℝ × ℂ =>
      conj (cubicSourceResidualFunction (g • cuspCoordinateLift q)))
      (Ioi (0 : ℝ) ×ˢ (univ : Set ℂ)) :=
    Complex.conjCLE.contDiff.comp_contDiffOn
      (cubicSourceResidualFunction_translate_coordinate_contDiffOn g)
  exact coordinate_cusp_normalized_iterated_wirtinger_rule
    (fun w : HyperbolicSpace => conj (cubicSourceResidualFunction w)) g hc v hv hf n

private lemma iteratedDz_const_mul {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (a : ℂ) (n : ℕ) :
    iteratedDz n (fun z => a * f z) = fun z => a * iteratedDz n f z := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [iteratedDz, ih]
      funext z
      have hd := ((contDiff_iteratedDz hf n).differentiable (by simp) z).hasFDerivAt.const_mul a
      rw [dz_eq_of_hasFDerivAt hd, wirtingerHol_smul]
      rfl

private lemma conjugate_cubicSource_horizontal_contDiff
    (g : SL(2, ℂ)) (v : ℝ) (hv : 0 < v) :
    ContDiff ℝ ∞ (fun z => conj (cubicSourceResidualFunction (g • upperPoint z v hv))) := by
  have hcoord := Complex.conjCLE.contDiff.comp_contDiffOn
    (cubicSourceResidualFunction_translate_coordinate_contDiffOn g)
  have hs : ContDiff ℝ ∞ (fun z => conj (cubicSourceResidualFunction
      (g • cuspCoordinateLift (v, z)))) := by
    apply contDiff_iff_contDiffAt.2
    intro z
    have hm : (v, z) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set ℂ) := ⟨hv, mem_univ z⟩
    exact (hcoord.contDiffAt ((isOpen_Ioi.prod isOpen_univ).mem_nhds hm)).comp z
      (contDiffAt_const.prodMk contDiffAt_id)
  simpa only [cuspCoordinateLift_positive v _ hv] using hs

/-- Normalized pure antiholomorphic jets of the actual source, centered at a finite cusp. -/
def higherSourceBarProfile (n : ℕ) (z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ n * iteratedDzbar (n + 1)
    (fun w => conj (cubicSourceResidualFunction (cuspCoordinateLift (v, w + z)))) 0

/-- Normalized pure holomorphic jets of the three actual cusp representatives. -/
def higherSourceZFamily (n : ℕ) (j : Fin 3) (z : ℂ) (v : ℝ) : ℂ :=
  (v : ℂ) ^ n * iteratedDz (n + 1)
    (fun w => conj (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative j) • cuspCoordinateLift (v, w)))) z

/-- The higher cusp multiplier changes only its unit phase with derivative order. -/
def SourceCuspDatum.jetMultiplier (d : SourceCuspDatum) (n : ℕ) : ℂ :=
  conj (extendedComplexCharacter d.gamma) *
    (-conj (d.matrix 1 0) / d.matrix 1 0) ^ (n + 1) / (d.heightScale : ℂ)

lemma SourceCuspDatum.jetMultiplier_norm (d : SourceCuspDatum) (n : ℕ) :
    ‖d.jetMultiplier n‖ = d.heightScale⁻¹ := by
  have hc : d.matrix 1 0 ≠ 0 := d.lower_ne_zero
  have hphase : ‖-conj (d.matrix 1 0) / d.matrix 1 0‖ = 1 :=
    norm_cuspAngularPhase (d.matrix 1 0) hc
  rw [SourceCuspDatum.jetMultiplier, norm_div, norm_mul, Complex.norm_conj,
    norm_extendedComplexCharacter, norm_pow, hphase,
    one_pow, one_mul, Complex.norm_of_nonneg d.heightScale_pos.le, one_div]

/-- Every higher pure source jet reflects into the same three cusp representatives. -/
theorem SourceCuspDatum.reflection_higher (d : SourceCuspDatum) (n : ℕ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile n d.point v =
      d.jetMultiplier n / (v : ℂ) ^ 2 *
        higherSourceZFamily n d.index d.dualPoint ((d.heightScale * v)⁻¹) := by
  have hv0 : 0 < (d.heightScale * v)⁻¹ := inv_pos.2 (mul_pos d.heightScale_pos hv)
  have he (w : HyperbolicSpace) :
      conj (cubicSourceResidualFunction (d.matrix • w)) =
        conj (extendedComplexCharacter d.gamma) *
          conj (cubicSourceResidualFunction (integralComplexMatrix (cuspRepresentative d.index) • w)) := by
    rw [SourceCuspDatum.matrix, mul_smul, cubicSourceResidualFunction_automorphy, map_mul]
  have hs : ContDiff ℝ ∞ (fun z => conj (cubicSourceResidualFunction
      (integralComplexMatrix (cuspRepresentative d.index) •
        upperPoint z ((d.heightScale * v)⁻¹) hv0))) :=
    conjugate_cubicSource_horizontal_contDiff _ _ hv0
  have hr := conjugate_cubicSourceResidualFunction_normalized_cusp_jets
    d.matrix d.lower_ne_zero v hv n
  have hz : (1 / (‖d.matrix 1 0‖ ^ 2 * v) : ℝ) = (d.heightScale * v)⁻¹ := by
    rw [SourceCuspDatum.heightScale, one_div]
  simp only [hz] at hr
  simp_rw [he] at hr
  rw [iteratedDz_const_mul hs] at hr
  change (v : ℂ) ^ n * iteratedDzbar (n + 1)
      (fun w => conj (cubicSourceResidualFunction (cuspCoordinateLift (v, w + d.point)))) 0 = _
  simp only [cuspCoordinateLift_positive _ _ hv, SourceCuspDatum.point]
  rw [hr]
  simp only [higherSourceZFamily, cuspCoordinateLift_positive _ _ hv0]
  simp only [SourceCuspDatum.jetMultiplier, SourceCuspDatum.heightScale, SourceCuspDatum.dualPoint,
    Complex.ofReal_mul, Complex.ofReal_pow, div_eq_mul_inv, mul_inv_rev]
  ring

/-- The directional and real-Fréchet definitions of both Wirtinger derivatives agree. -/
lemma horizontalWirtinger_eq_dz {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℝ f z) :
    horizontalWirtingerZ f z = dz f z ∧ horizontalWirtingerBar f z = dzbar f z := by
  have hline (direction : ℂ) : HasDerivAt (fun t : ℝ => f (z + (t : ℂ) * direction))
      (fderiv ℝ f z direction) 0 := by
    have hi : HasDerivAt (fun t : ℝ => z + (t : ℂ) * direction) direction 0 := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := (0 : ℝ))).mul_const direction).const_add z
    have hh : HasFDerivAt f (fderiv ℝ f z) (z + (0 : ℂ) * direction) := by
      simpa only [zero_mul, add_zero] using hf.hasFDerivAt
    exact hh.comp_hasDerivAt 0 hi
  have h1 := (hline 1).deriv
  have hI := (hline Complex.I).deriv
  simp only [mul_one] at h1
  constructor
  · rw [horizontalWirtingerZ, h1, hI, dz, wirtingerHol]
    ring
  · rw [horizontalWirtingerBar, h1, hI, dzbar, wirtingerAntihol]
    ring

/-- Order one recovers the original antiholomorphic cusp profile. -/
theorem higherSourceBarProfile_zero (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceBarProfile 0 z v =
      cuspBarProfile (fun w => conj (cubicSourceResidualFunction w)) z v := by
  have hf : ContDiff ℝ ∞ (fun w => conj (cubicSourceResidualFunction (upperPoint w v hv))) := by
    simpa only [one_smul] using conjugate_cubicSource_horizontal_contDiff 1 v hv
  have hshift : DifferentiableAt ℝ
      (fun w => conj (cubicSourceResidualFunction (upperPoint (w + z) v hv))) 0 :=
    (hf.comp (contDiff_id.add contDiff_const)).differentiable (by simp) 0
  simp only [higherSourceBarProfile, pow_zero, one_mul, iteratedDzbar,
    cuspBarProfile, cuspCoordinateLift_positive _ _ hv]
  rw [← (horizontalWirtinger_eq_dz hshift).2]
  exact horizontalWirtingerBar_translate
    (fun w : ℂ => conj (cubicSourceResidualFunction (upperPoint w v hv))) z

/-- Order one recovers the original holomorphic cusp family. -/
theorem higherSourceZFamily_zero (j : Fin 3) (z : ℂ) (v : ℝ) (hv : 0 < v) :
    higherSourceZFamily 0 j z v = sourceCuspZFamily j z v := by
  have hf := conjugate_cubicSource_horizontal_contDiff
    (integralComplexMatrix (cuspRepresentative j)) v hv
  simp only [higherSourceZFamily, pow_zero, one_mul, iteratedDz, sourceCuspZFamily,
    cuspZProfile, cuspCoordinateLift_positive _ _ hv]
  exact (horizontalWirtinger_eq_dz (hf.differentiable (by simp) z)).1.symm

/-- The order-one phase agrees exactly with the existing cusp multiplier. -/
lemma SourceCuspDatum.jetMultiplier_zero (d : SourceCuspDatum) :
    d.jetMultiplier 0 = d.multiplier := by
  have hc : d.matrix 1 0 ≠ 0 := d.lower_ne_zero
  have hconj : conj (d.matrix 1 0) ≠ 0 := by
    simpa only [Complex.star_def] using star_ne_zero.mpr hc
  have hn : ((‖d.matrix 1 0‖ ^ 2 : ℝ) : ℂ) = d.matrix 1 0 * conj (d.matrix 1 0) := by
    rw [← Complex.normSq_eq_norm_sq, Complex.mul_conj]
  simp only [SourceCuspDatum.jetMultiplier, SourceCuspDatum.multiplier,
    SourceCuspDatum.heightScale, zero_add, pow_one, Complex.star_def]
  rw [hn]
  field_simp [hc, hconj]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
