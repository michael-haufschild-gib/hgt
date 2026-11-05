import GaloisForLFunctions.ThetaCuspSections.FifthEvenCompleteTail
import GaloisForLFunctions.ThetaCuspSections.StrictEighthSection
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCenterTailRepresentation
/-!
# Strict positivity of the ninth theta section

The complete fifth even tail is positive at every nonnegative cutoff.
Its strictly positive aperture weight gives the fifth even mixed section;
the known fourth odd block completes the parity decomposition of rank nine.
-/
noncomputable section
open MeasureTheory Set Matrix
open _root_.RHTower
namespace GaloisForLFunctions.ThetaCuspSections
open FifthCompleteTail

/-- The fifth even block of the signed center-mixed jet hierarchy. -/
def thetaCuspCenterMixedEvenFive (a : ℝ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
 thetaCuspCenterMixedSignedJet a (2*(i.val+j.val))

private def evenTailApertureForm (a : ℝ) (v : Fin 5 → ℝ) (r : ℝ) : ℝ :=
 thetaCuspCenterTailWeight a r*(star v ⬝ᵥ (nativeTailMatrix r *ᵥ v))

private theorem evenTailApertureForm_eq_sum (a : ℝ) (v : Fin 5 → ℝ) (r : ℝ) :
 evenTailApertureForm a v r=∑ i : Fin 5, ∑ j : Fin 5,
  (v i*v j)*(thetaCuspCenterTailWeight a r*thetaCuspNativeSignedJetTail (2*(i.val+j.val)) r) := by
 simp only [evenTailApertureForm,dotProduct,mulVec,nativeTailMatrix,
  thetaCuspNativeSignedJetTail,star_trivial,Finset.mul_sum]
 exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))

private theorem evenTailApertureForm_integrable {a : ℝ} (ha0 : 0<a) (ha : a<1/2)
 (v : Fin 5 → ℝ) : IntegrableOn (evenTailApertureForm a v) (Ioi 0) := by
 change IntegrableOn (fun r => evenTailApertureForm a v r) (Ioi 0)
 simp_rw [evenTailApertureForm_eq_sum]
 exact integrable_finsetSum Finset.univ (fun i _ =>
  integrable_finsetSum Finset.univ (fun j _ =>
   (integrableOn_thetaCuspCenterTailWeight_mul_tail ha0.le ha (2*(i.val+j.val))).const_mul _))

private theorem evenFive_form_eq_integral {a : ℝ} (ha0 : 0<a) (ha : a<1/2)
 (v : Fin 5 → ℝ) :
 star v ⬝ᵥ (thetaCuspCenterMixedEvenFive a *ᵥ v)=∫ r in Ioi 0, evenTailApertureForm a v r := by
 have hi (i j : Fin 5) :=
  (integrableOn_thetaCuspCenterTailWeight_mul_tail ha0.le ha (2*(i.val+j.val))).const_mul (v i*v j)
 simp_rw [evenTailApertureForm_eq_sum]
 rw [integral_finsetSum Finset.univ (fun i _ =>
  integrable_finsetSum Finset.univ (fun j _ => hi i j))]
 simp only [dotProduct,mulVec,thetaCuspCenterMixedEvenFive,star_trivial,Finset.mul_sum]
 apply Finset.sum_congr rfl
 intro i hi'
 rw [integral_finsetSum Finset.univ (fun j _ => hi i j)]
 apply Finset.sum_congr rfl
 intro j hj
 rw [integral_const_mul,thetaCuspCenterMixedSignedJet_eq_integral_tail ha0.le ha]
 ring

/-- Strict native tails pay the fifth even mixed section at every critical aperture. -/
theorem thetaCuspCenterMixedEvenFive_posDef {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
 (thetaCuspCenterMixedEvenFive a).PosDef := by
 have hHerm : (thetaCuspCenterMixedEvenFive a).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp only [Matrix.conjTranspose_apply,star_trivial,thetaCuspCenterMixedEvenFive,Nat.add_comm]
 refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm fun v hv => ?_
 rw [evenFive_form_eq_integral ha0 ha]
 let μ := volume.restrict (Ioi (0:ℝ))
 have hi : Integrable (evenTailApertureForm a v) μ := evenTailApertureForm_integrable ha0 ha v
 have hp (r : ℝ) (hr : 0<r) : 0<evenTailApertureForm a v r :=
  mul_pos (thetaCuspCenterTailWeight_pos ha0 hr)
   ((nativeTailMatrix_posDef hr.le).dotProduct_mulVec_pos hv)
 have hn : 0≤ᵐ[μ] evenTailApertureForm a v := by
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact (hp r hr).le
 have hs : Ioo (1:ℝ) 2⊆Function.support (evenTailApertureForm a v) := by
  intro r hr
  exact (hp r ((by norm_num : (0:ℝ)<1).trans hr.1)).ne'
 have hm : μ (Ioo (1:ℝ) 2)=1 := by
  rw [Measure.restrict_apply measurableSet_Ioo,
   inter_eq_left.mpr (show Ioo (1:ℝ) 2⊆Ioi 0 from
    fun r hr => (by norm_num : (0:ℝ)<1).trans hr.1),Real.volume_Ioo]
  norm_num
 have hmeasure : 0<μ (Function.support (evenTailApertureForm a v)) := by
  have hmono := measure_mono (μ := μ) hs
  rw [hm] at hmono
  exact lt_of_lt_of_le (by norm_num : (0:ENNReal)<1) hmono
 exact (integral_pos_iff_support_of_nonneg_ae hn hi).mpr hmeasure

/-- The actual ninth signed center-mixed Hankel section is strict at every critical aperture. -/
theorem thetaCuspCenterMixedSignedHankel_nine_posDef {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
 (thetaCuspCenterMixedSignedHankel a 9).PosDef := by
 let e : Fin 5 → Fin 9 := fun i => ⟨2*i.val,by omega⟩
 let o : Fin 4 → Fin 9 := fun i => ⟨2*i.val+1,by omega⟩
 have hEven : ((thetaCuspCenterMixedSignedHankel a 9).submatrix e e).PosDef := by
  have he : (thetaCuspCenterMixedSignedHankel a 9).submatrix e e=thetaCuspCenterMixedEvenFive a := by
   ext i j
   simp only [submatrix_apply,thetaCuspCenterMixedSignedHankel,thetaCuspCenterMixedEvenFive,e]
   congr 1
   omega
  rw [he]
  exact thetaCuspCenterMixedEvenFive_posDef ha0 ha
 have hOdd := thetaCuspCenterMixedOddFour_posDef ha0 ha
 have hOddEq : (thetaCuspCenterMixedSignedHankel a 9).submatrix o o=thetaCuspCenterMixedOddFour a := by
  ext i j
  simp only [submatrix_apply,thetaCuspCenterMixedSignedHankel,thetaCuspCenterMixedOddFour,o]
  congr 1
  omega
 have hHerm : (thetaCuspCenterMixedSignedHankel a 9).IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [thetaCuspCenterMixedSignedHankel,add_comm]
 have ho0 := thetaCuspCenterMixedSignedJet_odd a 0
 have ho1 := thetaCuspCenterMixedSignedJet_odd a 1
 have ho2 := thetaCuspCenterMixedSignedJet_odd a 2
 have ho3 := thetaCuspCenterMixedSignedJet_odd a 3
 have ho4 := thetaCuspCenterMixedSignedJet_odd a 4
 have ho5 := thetaCuspCenterMixedSignedJet_odd a 5
 have ho6 := thetaCuspCenterMixedSignedJet_odd a 6
 have ho7 := thetaCuspCenterMixedSignedJet_odd a 7
 norm_num at ho0 ho1 ho2 ho3 ho4 ho5 ho6 ho7
 have hSplit (v : Fin 9 → ℝ) :
   star v ⬝ᵥ (thetaCuspCenterMixedSignedHankel a 9 *ᵥ v)=
    star (v∘e) ⬝ᵥ ((thetaCuspCenterMixedSignedHankel a 9).submatrix e e *ᵥ (v∘e))+
    star (v∘o) ⬝ᵥ (thetaCuspCenterMixedOddFour a *ᵥ (v∘o)) := by
  rw [← hOddEq]
  simp [dotProduct,mulVec,Fin.sum_univ_succ,thetaCuspCenterMixedSignedHankel,
   e,o,ho0,ho1,ho2,ho3,ho4,ho5,ho6,ho7]
  ring
 have hCover (v : Fin 9 → ℝ) (he : v∘e=0) (ho : v∘o=0) : v=0 := by
  funext i
  fin_cases i
  · simpa [e,Function.comp_def] using congrFun he (0:Fin 5)
  · simpa [o,Function.comp_def] using congrFun ho (0:Fin 4)
  · simpa [e,Function.comp_def] using congrFun he (1:Fin 5)
  · simpa [o,Function.comp_def] using congrFun ho (1:Fin 4)
  · simpa [e,Function.comp_def] using congrFun he (2:Fin 5)
  · simpa [o,Function.comp_def] using congrFun ho (2:Fin 4)
  · simpa [e,Function.comp_def] using congrFun he (3:Fin 5)
  · simpa [o,Function.comp_def] using congrFun ho (3:Fin 4)
  · simpa [e,Function.comp_def] using congrFun he (4:Fin 5)
 refine Matrix.PosDef.of_dotProduct_mulVec_pos hHerm fun v hv => ?_
 rw [hSplit]
 by_cases he : v∘e=0
 · have ho : v∘o≠0 := fun hz => hv (hCover v he hz)
   exact add_pos_of_nonneg_of_pos (hEven.posSemidef.dotProduct_mulVec_nonneg _)
    (hOdd.dotProduct_mulVec_pos ho)
 · exact add_pos_of_pos_of_nonneg (hEven.dotProduct_mulVec_pos he)
    (hOdd.posSemidef.dotProduct_mulVec_nonneg _)

/-- The eighth native successor integral is strictly positive. -/
theorem thetaCuspNativeSuccessorIntegral_eight_pos {a : ℝ} (ha0 : 0<a) (ha : a<1/2) :
 0<∫ r in Ioi 0, r*Real.sinh (a*r)*thetaCuspNativeSuccessorSource a 8 (r/2) := by
 rw [← thetaCuspCenterMixedSuccessorSchur_eq_integral_native ha0.le ha]
 exact (HTGeometry.finiteHankelMatrix_succ_posDef_iff_schur_pos
  (thetaCuspCenterMixedSignedHankel_eight_posDef ha0 ha)).mp
   (thetaCuspCenterMixedSignedHankel_nine_posDef ha0 ha)

end GaloisForLFunctions.ThetaCuspSections
