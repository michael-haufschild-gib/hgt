import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerPrimitiveOrbitWords
import GaloisForLFunctions.RenormalizedIntersectionTheory.GaussMayerRealEigenbasis

/-! Translation lengths of the actual Gauss pair matrices, measured in the
Poincaré metric on the upper half-plane. -/

open Matrix
open scoped MatrixGroups UpperHalfPlane
open GaloisForLFunctions.RenormalizedIntersectionTheory
open MayerHyperbolic MayerGaussCoding MayerPairMultiplier MayerOrbitWords MayerPrimitiveCycles
open MayerCycleIndex MayerRealEigenbasis
set_option autoImplicit false
noncomputable section
namespace GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolicLength

/-- The actual pair matrix, regarded as a real determinant-one matrix. -/
def pairElement (ps : List (ℕ × ℕ)) : SL(2, ℝ) :=
  ⟨fun i j => (actualPairedMatrix ps i j : ℝ), by
    have h := actualPairedMatrix_det ps
    rw [Matrix.det_fin_two] at h ⊢
    exact_mod_cast h⟩

/-- A representative of the actual primitive integral conjugacy class. -/
def orbitElement (c : Orbit) : SL(2, ℝ) := pairElement (representative c).val

/-- Translation length defined by the actual displacement infimum. -/
def orbitTranslationLength (c : Orbit) : ℝ :=
  sInf (Set.range (fun z : ℍ => dist z (orbitElement c • z)))

private theorem diagonal_action (l : ℝ) (hl : 0 < l) (z : ℍ) :
    diagonalElement l l⁻¹ (mul_inv_cancel₀ hl.ne') • z =
      (⟨l^2,sq_pos_of_pos hl⟩ : {x : ℝ // 0 < x}) • z := by
  apply UpperHalfPlane.ext
  rw [UpperHalfPlane.coe_specialLinearGroup_apply,UpperHalfPlane.coe_pos_real_smul]
  change ((l : ℂ)*(z : ℂ)+0)/(0*(z : ℂ)+(l⁻¹ : ℝ)) = (l^2 : ℝ) • (z : ℂ)
  simp only [add_zero,zero_mul,zero_add,Complex.ofReal_inv,div_inv_eq_mul]
  rw [Algebra.smul_def]
  change (l : ℂ)*(z : ℂ)*(l : ℂ) = ((l^2 : ℝ) : ℂ)*(z : ℂ)
  rw [Complex.ofReal_pow]
  ring

private theorem diagonal_minimum (l : ℝ) (hl : 1 < l) :
    IsLeast (Set.range (fun z : ℍ =>
      dist z (diagonalElement l l⁻¹ (mul_inv_cancel₀ (zero_lt_one.trans hl).ne') • z)))
      (2*Real.log l) := by
  have hl0 := zero_lt_one.trans hl
  have hlog0 : 0 ≤ 2*Real.log l := mul_nonneg (by norm_num) (Real.log_pos hl).le
  have him (z : ℍ) :
      Real.log ((diagonalElement l l⁻¹ (mul_inv_cancel₀ hl0.ne') • z).im) =
        2*Real.log l+Real.log z.im := by
    rw [diagonal_action l hl0 z,UpperHalfPlane.pos_real_im,
      Real.log_mul (ne_of_gt (sq_pos_of_pos hl0)) z.im_ne_zero,Real.log_pow]
    norm_num
  have hd (z : ℍ) : dist (Real.log z.im)
      (Real.log ((diagonalElement l l⁻¹ (mul_inv_cancel₀ hl0.ne') • z).im)) =
        2*Real.log l := by
    rw [him,Real.dist_eq,show Real.log z.im-(2*Real.log l+Real.log z.im) =
      -(2*Real.log l) by ring,abs_neg,abs_of_nonneg hlog0]
  refine ⟨⟨UpperHalfPlane.I,?_⟩,?_⟩
  · change dist UpperHalfPlane.I
      (diagonalElement l l⁻¹ (mul_inv_cancel₀ hl0.ne') • UpperHalfPlane.I) = 2*Real.log l
    rw [UpperHalfPlane.dist_of_re_eq,hd]
    rw [diagonal_action l hl0 UpperHalfPlane.I,
      UpperHalfPlane.pos_real_re,UpperHalfPlane.I_re,mul_zero]
  · rintro t ⟨z,rfl⟩
    rw [← hd z]
    exact UpperHalfPlane.dist_log_im_le _ _

private theorem minimum_of_eigenbasis (A : SL(2, ℝ)) (l : ℝ)
    (hl : 1 < l) (hc : A 1 0 ≠ 0)
    (hroot : l^2-(A 0 0+A 1 1)*l+1=0) :
    IsLeast (Set.range (fun z : ℍ => dist z (A • z))) (2*Real.log l) := by
  have hl0 := zero_lt_one.trans hl
  have hp := mul_inv_cancel₀ hl0.ne'
  have ht : l+l⁻¹=A 0 0+A 1 1 := by
    apply mul_right_cancel₀ hl0.ne'
    rw [add_mul,inv_mul_cancel₀ hl0.ne']
    nlinarith only [hroot]
  have hμ : l⁻¹ < 1 := (inv_lt_one₀ hl0).mpr hl
  have hg : l-l⁻¹ ≠ 0 := (sub_pos.mpr (hμ.trans hl)).ne'
  obtain ⟨C,hC⟩ := exists_eigenbasis A l l⁻¹ hp ht hc hg
  have hdist (z : ℍ) : dist (C • z) (A • (C • z)) =
      dist z (diagonalElement l l⁻¹ hp • z) := by
    rw [← mul_smul,hC,mul_smul,dist_smul]
  have hm := diagonal_minimum l hl
  obtain ⟨z,hz⟩ := hm.1
  refine ⟨⟨C • z,(hdist z).trans hz⟩,?_⟩
  rintro t ⟨u,rfl⟩
  change 2*Real.log l ≤ dist u (A • u)
  have hu : C • (C⁻¹ • u)=u := smul_inv_smul C u
  rw [← hu,hdist]
  exact hm.2 ⟨C⁻¹ • u,rfl⟩

/-- Every nonempty actual pair word attains its sharp hyperbolic displacement bound. -/
theorem pairElement_minimum_displacement (ps : List (ℕ × ℕ)) (hps : ps ≠ []) :
    IsLeast (Set.range (fun z : ℍ => dist z (pairElement ps • z)))
      (2*Real.log (pairMultiplier ps)) := by
  apply minimum_of_eigenbasis (pairElement ps) (pairMultiplier ps)
    (pairMultiplier_gt_one ps hps)
  · have h := lowerLeft_ne_zero (actualPairedMatrix ps)
      (by simpa only [Matrix.det_fin_two] using actualPairedMatrix_det ps)
      (actualPairedMatrix_trace_gt_two ps hps)
    change (actualPairedMatrix ps 1 0 : ℝ) ≠ 0
    exact_mod_cast h
  · have h := (expandingMultiplier_spec (actualPairedMatrix_trace_gt_two ps hps)).2
    simpa only [pairElement,pairMultiplier,Int.cast_add] using h

/-- The primitive-cycle multiplier gives the least actual displacement. -/
theorem orbitElement_minimum_displacement (c : Orbit) :
    IsLeast (Set.range (fun z : ℍ => dist z (orbitElement c • z)))
      (2*Real.log (multiplier c)) := by
  simpa only [orbitElement,multiplier] using
    pairElement_minimum_displacement (representative c).val (representative c).property.1

/-- The displacement infimum is twice the logarithm of the expanding multiplier. -/
theorem orbitTranslationLength_eq (c : Orbit) :
    orbitTranslationLength c = 2*Real.log (multiplier c) :=
  (orbitElement_minimum_displacement c).csInf_eq

theorem orbitTranslationLength_pos (c : Orbit) : 0 < orbitTranslationLength c := by
  rw [orbitTranslationLength_eq]
  exact mul_pos (by norm_num) (Real.log_pos (multiplier_gt_one c))

#print axioms pairElement_minimum_displacement
#print axioms orbitElement_minimum_displacement
#print axioms orbitTranslationLength_eq
#print axioms orbitTranslationLength_pos

end GaloisForLFunctions.RenormalizedIntersectionTheory.MayerHyperbolicLength
