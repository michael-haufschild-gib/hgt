import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddFourRankEight
import GaloisForLFunctions.RHTower.PrimeArchThetaFirstMoment
import GaloisForLFunctions.RHTower.CothInfra
import GaloisForLFunctions.HTGeometry.HankelSuccessorSchurStrict

/-!
# Strict positivity of the eighth theta section

The seam certificate pays the negative part of the native odd fibre. The
aperture weight increases strictly relative to the seam weight, leaving a
positive tail for every nonzero vector. This removes the possible radical
of the odd block; the even block is already a strict seventh-section block.
-/

noncomputable section
open MeasureTheory Set Matrix
open RHTower RHTower.ThetaCuspOddFourPieces
open RHTower.ThetaCuspOddFourNativeBulk
open RHTower.ThetaCuspOddCentral RHTower.ThetaCuspOddCentralTail

namespace GaloisForLFunctions.ThetaCuspSections

private theorem mul_sinh_lt_mul_sinh {y Y : ℝ} (hy : 0 < y) (hY : y < Y) :
    Y * Real.sinh y < y * Real.sinh Y := by
  let d := Y - y
  have hd : 0 < d := sub_pos.mpr hY
  have heq : Y = y + d := by dsimp only [d]; ring
  have h1 : 0 ≤ y * Real.sinh y * (Real.cosh d - 1) :=
    mul_nonneg (mul_nonneg hy.le (Real.sinh_pos_iff.mpr hy).le)
      (sub_nonneg.mpr (Real.one_le_cosh d))
  have h2 : 0 ≤ y * Real.cosh y * (Real.sinh d - d) :=
    mul_nonneg (mul_nonneg hy.le (Real.cosh_pos y).le)
      (sub_nonneg.mpr (Real.self_le_sinh_iff.mpr hd.le))
  have h3 : 0 < d * (y * Real.cosh y - Real.sinh y) :=
    mul_pos hd (sub_pos.mpr (RHTower.sinh_lt_mul_cosh hy))
  rw [heq, Real.sinh_add]
  nlinarith only [h1, h2, h3]

private theorem strict_aperture_weight {a rc r : ℝ}
    (ha : 0 < a) (hc : 0 < rc) (hr : rc < r) :
    (Real.sinh (a * rc) / rc) * r ^ 2 < r * Real.sinh (a * r) := by
  have h := mul_sinh_lt_mul_sinh (mul_pos ha hc)
    (mul_lt_mul_of_pos_left hr ha)
  have hscaled : r * Real.sinh (a * rc) < rc * Real.sinh (a * r) := by
    by_contra hn
    have hp := mul_nonneg ha.le (sub_nonneg.mpr (le_of_not_gt hn))
    nlinarith only [h, hp]
  have hmul := mul_lt_mul_of_pos_left hscaled (hc.trans hr)
  rw [div_mul_eq_mul_div, div_lt_iff₀ hc]
  nlinarith only [hmul]

private theorem log_six_div_pi_pos : 0 < Real.log (6 / Real.pi) :=
  Real.log_pos (by rw [lt_div_iff₀ Real.pi_pos]; linarith [Real.pi_lt_d2])

/-- The complete odd native fibre is strictly positive beyond scale six.
The lower bound uses invertible central coordinates and the first theta atom. -/
theorem oddFour_fibre_pos_of_log_six {r : ℝ}
    (hr : Real.log (6 / Real.pi) < r) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    0 < thetaCuspOddFourFibreForm r v := by
  have hr0 : 0 < r := log_six_div_pi_pos.trans hr
  let q := thetaCuspSingleAtomReflectionScale 1 (r / 2)
  have hq : 6 ≤ q := by
    have he := Real.exp_lt_exp.mpr hr
    rw [Real.exp_log (by positivity : (0 : ℝ) < 6 / Real.pi),
      div_lt_iff₀ Real.pi_pos] at he
    dsimp only [q, thetaCuspSingleAtomReflectionScale]
    simp only [Nat.cast_one, one_pow, mul_one, show 2 * (r / 2) = r by ring]
    linarith only [he]
  have hqpos : 0 < q := by linarith only [hq]
  have hq0 : q ≠ 0 := hqpos.ne'
  have hy : coordinates q v ≠ 0 := by
    intro hz
    have he := centralBasis_coordinates' hq0 v
    rw [hz, Matrix.mulVec_zero] at he
    exact hv he.symm
  have hyi : ∃ i : Fin 4, coordinates q v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hy (funext h)
  obtain ⟨i, hi⟩ := hyi
  have hsum : 0 < ∑ j : Fin 4, coordinates q v j ^ 2 := by
    exact lt_of_lt_of_le (sq_pos_of_ne_zero hi)
      (Finset.single_le_sum (fun j _ => sq_nonneg (coordinates q v j)) (Finset.mem_univ i))
  have hf : 0 < thetaCuspSourceTerm (r / 2) 1 :=
    thetaCuspSourceTerm_one_pos_of_pos (by positivity)
  have hbound := native_oddFour_coercive hq (coordinates q v)
  dsimp only at hbound
  change (8 * q * thetaCuspSourceTerm (r / 2) 1 ^ 2) / 24 *
      (∑ j : Fin 4, coordinates q v j ^ 2) ≤ _ at hbound
  rw [centralBasis_coordinates' hq0] at hbound
  have hpos : 0 < (8 * q * thetaCuspSourceTerm (r / 2) 1 ^ 2) / 24 *
      (∑ j : Fin 4, coordinates q v j ^ 2) := by positivity
  have hout := hpos.trans_le hbound
  have heq : thetaCuspOddFourFibreForm r v =
      ∑ i : Fin 4, ∑ j : Fin 4, v i * v j * (-1 : ℝ) ^ (i.val + j.val + 1) *
        thetaCuspNativeReflectionJet (2 * (i.val + j.val + 1)) (r / 2) := by
    unfold thetaCuspOddFourFibreForm
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show 2 * (i.val + j.val) + 2 = 2 * (i.val + j.val + 1) by ring,
      signedJet_even_eq]
    ring
  rw [heq]
  exact hout

private def apertureFibre (a : ℝ) (v : Fin 4 → ℝ) (r : ℝ) : ℝ :=
  r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v

private theorem apertureFibre_eq_sum (a : ℝ) (v : Fin 4 → ℝ) (r : ℝ) :
    apertureFibre a v r = ∑ i : Fin 4, ∑ j : Fin 4, (v i * v j) *
      (r * Real.sinh (a * r) * thetaCuspNativeSignedJet (r / 2) (2 * (i.val + j.val) + 2)) := by
  simp only [apertureFibre, thetaCuspOddFourFibreForm, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem apertureFibre_integrable {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (v : Fin 4 → ℝ) : IntegrableOn (apertureFibre a v) (Ioi 0) := by
  change IntegrableOn (fun r => apertureFibre a v r) (Ioi 0)
  simp_rw [apertureFibre_eq_sum]
  exact integrable_finsetSum Finset.univ fun i _ =>
    integrable_finsetSum Finset.univ fun j _ =>
      (integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha
        (2 * (i.val + j.val) + 2)).const_mul (v i * v j)

private theorem oddFour_form_eq_integral {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2)
    (v : Fin 4 → ℝ) :
    star v ⬝ᵥ (thetaCuspCenterMixedOddFour a *ᵥ v) =
      ∫ r in Ioi 0, apertureFibre a v r := by
  have hint (i j : Fin 4) := (integrableOn_thetaCuspWeightedNativeSignedJet ha0.le ha
    (2 * (i.val + j.val) + 2)).const_mul (v i * v j)
  simp_rw [apertureFibre_eq_sum]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun j _ => hint i j))]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum, thetaCuspCenterMixedOddFour, star_trivial]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum Finset.univ (fun j _ => hint i j)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, thetaCuspCenterMixedSignedJet_eq_integral_nativeSignedJet ha0.le ha]
  ring

private theorem seam_comparison {a : ℝ} (ha : 0 < a) {r : ℝ} (hr : 0 < r)
    (v : Fin 4 → ℝ) :
    (Real.sinh (a * Real.log (5 / Real.pi)) / Real.log (5 / Real.pi)) *
      thetaCuspOddFourSeamSplitIntegrand (Real.log (5 / Real.pi)) r v ≤
        apertureFibre a v r := by
  let rc := Real.log (5 / Real.pi)
  let c := Real.sinh (a * rc) / rc
  have hrc : 0 < rc := log_five_div_pi_pos
  change c * (r ^ 2 * (if r ≤ rc then min (thetaCuspOddFourFibreForm r v) 0
    else thetaCuspOddFourFibreForm r v)) ≤ r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v
  have hw0 : 0 ≤ r * Real.sinh (a * r) :=
    mul_nonneg hr.le (Real.sinh_pos_iff.mpr (mul_pos ha hr)).le
  split_ifs with hle
  · have hw : r * Real.sinh (a * r) ≤ c * r ^ 2 := by
      have h := aperture_weight_le ha.le hr.le hle
      dsimp only [c]
      rw [div_mul_eq_mul_div, le_div_iff₀ hrc]
      nlinarith only [h, hr]
    calc c * (r ^ 2 * min (thetaCuspOddFourFibreForm r v) 0)
        = (c * r ^ 2) * min (thetaCuspOddFourFibreForm r v) 0 := by ring
      _ ≤ (r * Real.sinh (a * r)) * min (thetaCuspOddFourFibreForm r v) 0 :=
        mul_le_mul_of_nonpos_right hw (min_le_right _ _)
      _ ≤ r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v :=
        mul_le_mul_of_nonneg_left (min_le_left _ _) hw0
  · have hgt : rc < r := lt_of_not_ge hle
    have hw := (strict_aperture_weight ha hrc hgt).le
    have hf := oddFour_fibre_nonneg_beyond_logFive hgt v
    calc c * (r ^ 2 * thetaCuspOddFourFibreForm r v)
        = (c * r ^ 2) * thetaCuspOddFourFibreForm r v := by ring
      _ ≤ r * Real.sinh (a * r) * thetaCuspOddFourFibreForm r v :=
        mul_le_mul_of_nonneg_right hw hf

private theorem seam_comparison_strict {a : ℝ} (ha : 0 < a) {r : ℝ}
    (hr : Real.log (6 / Real.pi) < r) {v : Fin 4 → ℝ} (hv : v ≠ 0) :
    (Real.sinh (a * Real.log (5 / Real.pi)) / Real.log (5 / Real.pi)) *
      thetaCuspOddFourSeamSplitIntegrand (Real.log (5 / Real.pi)) r v <
        apertureFibre a v r := by
  have h56 : Real.log (5 / Real.pi) ≤ Real.log (6 / Real.pi) :=
    Real.log_le_log (by positivity)
      (div_le_div_of_nonneg_right (by norm_num) Real.pi_pos.le)
  have h5 : Real.log (5 / Real.pi) < r := h56.trans_lt hr
  have hw := strict_aperture_weight ha log_five_div_pi_pos h5
  have hp := mul_lt_mul_of_pos_right hw (oddFour_fibre_pos_of_log_six hr hv)
  simpa only [thetaCuspOddFourSeamSplitIntegrand, if_neg (not_le.mpr h5),
    apertureFibre, mul_assoc] using hp

/-- Strict aperture weighting preserves a positive part of the native tail,
so the fourth odd block has no radical. -/
theorem thetaCuspCenterMixedOddFour_posDef {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    (thetaCuspCenterMixedOddFour a).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (thetaCuspCenterMixedOddFour_isHermitian a) ?_
  intro v hv
  rw [oddFour_form_eq_integral ha0 ha]
  let rc := Real.log (5 / Real.pi)
  let c := Real.sinh (a * rc) / rc
  let S := fun r => thetaCuspOddFourSeamSplitIntegrand rc r v
  let D := fun r => apertureFibre a v r - c * S r
  let μ := volume.restrict (Ioi (0 : ℝ))
  have hc : 0 < c := div_pos (Real.sinh_pos_iff.mpr (mul_pos ha0 log_five_div_pi_pos))
    log_five_div_pi_pos
  have hiA : Integrable (apertureFibre a v) μ := apertureFibre_integrable ha0 ha v
  have hiS : Integrable S μ := integrableOn_thetaCuspOddFourSeamSplitIntegrand rc v
  have hiD : Integrable D μ := hiA.sub (hiS.const_mul c)
  have hD : 0 ≤ᵐ[μ] D := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    exact sub_nonneg.mpr (seam_comparison ha0 hr v)
  let R := Real.log (6 / Real.pi) + 1
  have hR : 0 < R := by dsimp only [R]; linarith only [log_six_div_pi_pos]
  have hsupport : Ioo R (R + 1) ⊆ Function.support D := by
    intro r hr
    have h6 : Real.log (6 / Real.pi) < r := by
      dsimp only [R] at hr
      linarith only [hr.1]
    exact (sub_pos.mpr (seam_comparison_strict ha0 h6 hv)).ne'
  have hmass : μ (Ioo R (R + 1)) = 1 := by
    rw [Measure.restrict_apply measurableSet_Ioo,
      inter_eq_left.mpr (show Ioo R (R + 1) ⊆ Ioi 0 from fun r hr => hR.trans hr.1),
      Real.volume_Ioo]
    simp
  have hmeasure : 0 < μ (Function.support D) := by
    have hm := measure_mono (μ := μ) hsupport
    rw [hmass] at hm
    exact lt_of_lt_of_le (by norm_num : (0 : ENNReal) < 1) hm
  have hpos : 0 < ∫ r, D r ∂μ :=
    (integral_pos_iff_support_of_nonneg_ae hD hiD).mpr hmeasure
  have heq : ∫ r, D r ∂μ = (∫ r, apertureFibre a v r ∂μ) - c * ∫ r, S r ∂μ := by
    rw [integral_sub hiA (hiS.const_mul c), integral_const_mul]
  have hs : 0 ≤ ∫ r, S r ∂μ := oddFour_seamSplit_logFive v
  rw [heq] at hpos
  exact lt_of_lt_of_le hpos (sub_le_self _ (mul_nonneg hc.le hs))

/-- The actual signed center-mixed Hankel section of size eight is strictly
positive at every critical aperture. -/
theorem thetaCuspCenterMixedSignedHankel_eight_posDef
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    (thetaCuspCenterMixedSignedHankel a 8).PosDef := by
  let e : Fin 4 → Fin 8 := fun i => ⟨2 * i.val, by omega⟩
  let o : Fin 4 → Fin 8 := fun i => ⟨2 * i.val + 1, by omega⟩
  let e7 : Fin 4 → Fin 7 := fun i => ⟨2 * i.val, by omega⟩
  have he7inj : Function.Injective e7 := by
    intro i j hij
    apply Fin.ext
    have h := congrArg Fin.val hij
    simp only [e7] at h
    omega
  have hEven : ((thetaCuspCenterMixedSignedHankel a 8).submatrix e e).PosDef := by
    have h7 := (thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha).submatrix he7inj
    have hEq : (thetaCuspCenterMixedSignedHankel a 8).submatrix e e =
        (thetaCuspCenterMixedSignedHankel a 7).submatrix e7 e7 := by ext i j; rfl
    rw [hEq]
    exact h7
  have hOdd : (thetaCuspCenterMixedOddFour a).PosDef := thetaCuspCenterMixedOddFour_posDef ha0 ha
  have hOddEq : (thetaCuspCenterMixedSignedHankel a 8).submatrix o o =
      thetaCuspCenterMixedOddFour a := by
    ext i j
    simp only [submatrix_apply, thetaCuspCenterMixedSignedHankel, thetaCuspCenterMixedOddFour, o]
    congr 1
    omega
  have hHerm : (thetaCuspCenterMixedSignedHankel a 8).IsHermitian := by
    rw [Matrix.IsHermitian]
    ext i j
    simp [thetaCuspCenterMixedSignedHankel, add_comm]
  have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
  have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
  have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
  have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
  have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
  have ho5 := thetaCuspCenterMixedSignedJet_odd a 5
  have ho6 := thetaCuspCenterMixedSignedJet_odd a 6
  norm_num at ho0 ho1 ho2 ho3 ho4 ho5 ho6
  have hSplit (v : Fin 8 → ℝ) :
      star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a 8 *ᵥ v) =
        star (v ∘ e) ⬝ᵥ
          ((thetaCuspCenterMixedSignedHankel a 8).submatrix e e *ᵥ (v ∘ e)) +
        star (v ∘ o) ⬝ᵥ (thetaCuspCenterMixedOddFour a *ᵥ (v ∘ o)) := by
    rw [← hOddEq]
    simp [dotProduct, mulVec, Fin.sum_univ_succ,
      thetaCuspCenterMixedSignedHankel, e, o, ho0, ho1, ho2, ho3, ho4, ho5, ho6]
    ring
  have hCover (v : Fin 8 → ℝ) (he : v ∘ e = 0) (ho : v ∘ o = 0) : v = 0 := by
    funext i
    fin_cases i
    · simpa [e, Function.comp_def] using congrFun he (0 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (0 : Fin 4)
    · simpa [e, Function.comp_def] using congrFun he (1 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (1 : Fin 4)
    · simpa [e, Function.comp_def] using congrFun he (2 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (2 : Fin 4)
    · simpa [e, Function.comp_def] using congrFun he (3 : Fin 4)
    · simpa [o, Function.comp_def] using congrFun ho (3 : Fin 4)
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm fun v hv => ?_
  rw [hSplit]
  by_cases he : v ∘ e = 0
  · have ho : v ∘ o ≠ 0 := fun hz => hv (hCover v he hz)
    exact add_pos_of_nonneg_of_pos (hEven.posSemidef.dotProduct_mulVec_nonneg _)
      (hOdd.dotProduct_mulVec_pos ho)
  · exact add_pos_of_pos_of_nonneg (hEven.dotProduct_mulVec_pos he)
      (hOdd.posSemidef.dotProduct_mulVec_nonneg _)

/-- The seventh native successor integral is strictly positive. -/
theorem thetaCuspNativeSuccessorIntegral_seven_pos
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    0 < ∫ r : ℝ in Ioi 0, r * Real.sinh (a * r) * thetaCuspNativeSuccessorSource a 7 (r / 2) := by
  rw [← thetaCuspCenterMixedSuccessorSchur_eq_integral_native ha0.le ha]
  exact (HTGeometry.finiteHankelMatrix_succ_posDef_iff_schur_pos
    (thetaCuspCenterMixedSignedHankel_seven_posDef ha0 ha)).mp
      (thetaCuspCenterMixedSignedHankel_eight_posDef ha0 ha)

end GaloisForLFunctions.ThetaCuspSections
