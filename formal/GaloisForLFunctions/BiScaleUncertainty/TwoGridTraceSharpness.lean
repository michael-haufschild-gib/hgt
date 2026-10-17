import GaloisForLFunctions.BiScaleUncertainty.TwoGridTraceStability

/-!
# Attained arithmetic interpolation constants

The range of the reduced product's positive square supplies actual extremizers.
Both endpoint constants are attained by nonzero square-summable joint data.
-/

noncomputable section
open MeasureTheory Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear

theorem coprimeProjector_mul_reduced (d e : ℕ) :
    coprimeProjector d * reducedCoprimeProduct d e = reducedCoprimeProduct d e := by
  simp only [reducedCoprimeProduct, mul_sub, ← mul_assoc,
    coprimeProjector_mul_self, coprimeProjector_mul_lcm]

theorem coprimeLcmProjector_mul_reduced (d e : ℕ) :
    coprimeProjector (coprimeLcm d e) * reducedCoprimeProduct d e = 0 := by
  simp only [reducedCoprimeProduct, mul_sub, coprimeLcmProjector_mul_product,
    coprimeProjector_mul_self, sub_self]

private theorem exists_twoGrid_angle_vectors (d e : ℕ)
    (hg : ¬2 ≤ Nat.gcd (d + 2) (e + 2)) :
    ∃ x y : Velocity, coprimeProjector d x = x ∧ coprimeProjector e y = y ∧
      coprimeProjector (coprimeLcm d e) y = 0 ∧ y ≠ 0 ∧
      ‖x‖ ^ 2 = ‖y‖ ^ 2 ∧
      ⟪x, y⟫ = Real.sqrt (coprimeAngleSquare d e) * ‖y‖ ^ 2 := by
  let T := reducedCoprimeProduct d e
  let U := reducedCoprimeProduct e d
  let A := U * T
  let c := coprimeAngleSquare d e
  have hc : 0 < c := by
    dsimp [c, coprimeAngleSquare]
    rw [if_neg hg]
    split_ifs <;> norm_num
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hsq := Real.sq_sqrt hc.le
  have hA : A ≠ 0 := by
    simpa only [A, U, T, reducedCoprimeProduct_star] using
      (CStarRing.star_mul_self_ne_zero_iff (reducedCoprimeProduct d e)).2
        (reducedCoprimeProduct_ne_zero d e hg)
  have hex : ∃ z : Velocity, A z ≠ 0 := by
    by_contra h
    apply hA
    apply ContinuousLinearMap.ext
    simpa using h
  obtain ⟨z, hz⟩ := hex
  have hquad : A * A = c • A := by
    calc
      A * A = (U * T * U) * T := by simp only [A, mul_assoc]
      _ = (U * U) * T := by rw [reducedCoprimeProduct_star_product]
      _ = c • A := by
        rw [reducedCoprimeProduct_square, coprimeAngleSquare_comm e d, smul_mul_assoc]
  let y := A z
  let x := (Real.sqrt c)⁻¹ • T y
  have hqy : coprimeProjector e y = y := by
    change (coprimeProjector e * U * T) z = (U * T) z
    rw [coprimeProjector_mul_reduced]
  have hry : coprimeProjector (coprimeLcm d e) y = 0 := by
    change (coprimeProjector (coprimeLcm d e) * U * T) z = 0
    rw [coprimeLcm_comm d e, coprimeLcmProjector_mul_reduced, zero_mul, zero_apply]
  have hpx : coprimeProjector d x = x := by
    dsimp only [x]
    rw [map_smul]
    congr 1
    exact congrArg (fun B : Velocity →L[ℝ] Velocity => B y) (coprimeProjector_mul_reduced d e)
  have hty : T y = coprimeProjector d y := by
    simp only [T, reducedCoprimeProduct, sub_apply, mul_apply_eq_comp, hqy, hry, sub_zero]
  have heig : A y = c • y :=
    congrArg (fun B : Velocity →L[ℝ] Velocity => B z) hquad
  have hnorm : ‖T y‖ ^ 2 = c * ‖y‖ ^ 2 := by
    have h := T.apply_norm_sq_eq_inner_adjoint_left y
    change ‖T y‖ ^ 2 = ⟪(star T * T) y, y⟫ at h
    have hstar : star T * T = A := by simp only [T, A, U, reducedCoprimeProduct_star]
    rw [hstar, heig, real_inner_smul_left, real_inner_self_eq_norm_sq] at h
    exact h
  have hinner : ⟪T y, y⟫ = ‖T y‖ ^ 2 := by
    rw [hty, ← real_inner_self_eq_norm_sq]
    have h := (coprimeProjector d).adjoint_inner_right (coprimeProjector d y) y
    rw [coprimeProjector_adjoint, coprimeProjector_apply,
      coprimeProjection_idempotent] at h
    exact h.symm
  refine ⟨x, y, hpx, hqy, hry, hz, ?_, ?_⟩
  · dsimp only [x]
    rw [norm_smul, mul_pow, Real.norm_eq_abs, sq_abs, inv_pow, hsq, hnorm]
    field_simp
  · dsimp only [x]
    rw [real_inner_smul_left, hinner, hnorm]
    have hinv : (Real.sqrt c)⁻¹ * c = Real.sqrt c := by
      rw [← hsq]
      field_simp
    rw [← mul_assoc, hinv]

private theorem coefficients_norm_sq_of_fixed (d : ℕ) (x : Velocity)
    (hx : coprimeProjector d x = x) :
    2 * ‖coprimeCoefficients d x‖ ^ 2 = ‖x‖ ^ 2 := by
  rw [← norm_sq_coprimeExtension, ← coprimeProjection_eq_extension]
  exact congrArg (fun q : Velocity => ‖q‖ ^ 2) hx

private theorem twoGrid_extremizers_of_vectors (d e : ℕ) (x y : Velocity)
    (hx : coprimeProjector d x = x) (hy : coprimeProjector e y = y)
    (hr : coprimeProjector (coprimeLcm d e) y = 0) (hn : y ≠ 0)
    (he : ‖x‖ ^ 2 = ‖y‖ ^ 2)
    (hi : ⟪x, y⟫ = Real.sqrt (coprimeAngleSquare d e) * ‖y‖ ^ 2) :
    (∃ v : TwoGridData d e, 0 < twoGridMass d e v ∧
      ‖twoGridExtension d e v‖ ^ 2 =
        (2 - 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v) ∧
    (∃ v : TwoGridData d e, 0 < twoGridMass d e v ∧
      ‖twoGridExtension d e v‖ ^ 2 =
        (2 + 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v) := by
  have hex : coprimeExtension d (coprimeCoefficients d x) = x := by
    rw [← coprimeProjection_eq_extension]
    exact hx
  have hey : coprimeExtension e (coprimeCoefficients e y) = y := by
    rw [← coprimeProjection_eq_extension]
    exact hy
  have hmem (a : TraceData) : (a, coprimeCoefficients e y) ∈ twoGridDataSpace d e := by
    change coprimeProjector (coprimeLcm d e) (coprimeExtensionL e _) = 0
    rw [coprimeExtensionL_apply, hey, hr]
  let vp : TwoGridData d e := ⟨(coprimeCoefficients d x, coprimeCoefficients e y), hmem _⟩
  let vm : TwoGridData d e := ⟨(-coprimeCoefficients d x, coprimeCoefficients e y), hmem _⟩
  have hm : twoGridMass d e vp = ‖y‖ ^ 2 := by
    have h1 := coefficients_norm_sq_of_fixed d x hx
    have h2 := coefficients_norm_sq_of_fixed e y hy
    dsimp only [twoGridMass, vp]
    nlinarith only [h1, h2, he]
  have hmm : twoGridMass d e vm = ‖y‖ ^ 2 := by
    simpa only [twoGridMass, vm, vp, norm_neg] using hm
  have hpos : 0 < ‖y‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hn)
  have hep : twoGridExtension d e vp = x + y := by
    rw [twoGridExtension_apply]
    change coprimeExtension d _ + coprimeExtension e _ = _
    rw [hex, hey]
  have hem : twoGridExtension d e vm = -x + y := by
    rw [twoGridExtension_apply]
    change coprimeExtension d (-coprimeCoefficients d x) + coprimeExtension e _ = _
    rw [← coprimeExtensionL_apply d, map_neg, coprimeExtensionL_apply, hex, hey]
  constructor
  · refine ⟨vm, by rw [hmm]; exact hpos, ?_⟩
    rw [hem, hmm, norm_add_sq_real, norm_neg, inner_neg_left, he, hi]
    ring
  · refine ⟨vp, by rw [hm]; exact hpos, ?_⟩
    rw [hep, hm, norm_add_sq_real, he, hi]
    ring

/-- Both sharp arithmetic bounds are attained by actual nonzero union data. -/
theorem twoGridExtension_sharp (d e : ℕ) :
    (∃ v : TwoGridData d e, 0 < twoGridMass d e v ∧
      ‖twoGridExtension d e v‖ ^ 2 =
        (2 - 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v) ∧
    (∃ v : TwoGridData d e, 0 < twoGridMass d e v ∧
      ‖twoGridExtension d e v‖ ^ 2 =
        (2 + 2 * Real.sqrt (coprimeAngleSquare d e)) * twoGridMass d e v) := by
  by_cases hg : 2 ≤ Nat.gcd (d + 2) (e + 2)
  · let v : TwoGridData d e := ⟨(lp.single 2 0 (1 : ℝ), 0),
      (mem_twoGridDataSpace_iff d e _ _).2 (by simp)⟩
    have hc : Real.sqrt (coprimeAngleSquare d e) = 0 := by
      simp [coprimeAngleSquare, hg]
    have hm : twoGridMass d e v = 1 := by
      simp [twoGridMass, v, norm_sq_traceData, lp.single_apply]
    have he := twoGridExtension_stability d e v
    rw [hc] at he
    norm_num at he
    have heq := le_antisymm he.2 he.1
    constructor <;> refine ⟨v, by rw [hm]; norm_num, ?_⟩ <;> simpa [hc] using heq
  · obtain ⟨x, y, hx, hy, hr, hn, he, hi⟩ := exists_twoGrid_angle_vectors d e hg
    exact twoGrid_extremizers_of_vectors d e x y hx hy hr hn he hi

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
