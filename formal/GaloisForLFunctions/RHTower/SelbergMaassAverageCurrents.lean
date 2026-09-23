import GaloisForLFunctions.RHTower.SelbergMaassCongruenceAverage
import GaloisForLFunctions.RHTower.SelbergMaassCurrentCurvature

/-!
# Exact currents of the original congruence mean and remainder

The literal Maass congruence family splits into its full modular average and
its complete zero-sum remainder. Its pair energy separates into centered pair
squares and mean/remainder bracket squares. The phase currents add before
squaring, retaining their interference. These identities preserve the complete
regularized curvature numerator, its nodal locus, and the zero-average case.
Mixed brackets obey the original common Maass conservation equation.

No quantitative quarter comparison or Xi occurrence is asserted here.
-/

open Complex Set Filter Topology UpperHalfPlane
open scoped ContDiff
namespace GaloisForLFunctions.RHTower.SelbergMaassAverageCurrents
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassTraceEnergy
open SelbergMaassSourceCurrents SelbergMaassPairPhaseEnergy
noncomputable section

private theorem sum_difference_normSq {ι : Type*} [Fintype ι] (a : ι → ℂ) (ha : ∑ i, a i=0) :
    (∑ i, ∑ j, normSq (a j-a i))=2*(Fintype.card ι:ℝ)*∑ i, normSq (a i) := by
  have hz (i : ι) : (∑ j, (a j*(starRingEnd ℂ) (a i)).re)=0 := by
    rw [← Complex.re_sum,← Finset.sum_mul,ha,zero_mul]
    rfl
  simp only [normSq_sub,Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,hz,
    mul_zero,sub_zero,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  ring

/-- A finite family split into its constant mean and zero-sum remainder retains
an exact positive mixed-bracket term in its pair-current energy. -/
theorem finite_mean_pair_decomposition {ι : Type*} [Fintype ι]
    (m n : ℂ) (a b : ι → ℂ) (ha : ∑ i, a i=0) (hb : ∑ i, b i=0) :
    (1/2:ℝ)*∑ i, ∑ j, normSq ((m+a i)*(n+b j)-(m+a j)*(n+b i))=
      (1/2:ℝ)*∑ i, ∑ j, normSq (a i*b j-a j*b i)+
        (Fintype.card ι:ℝ)*∑ i, normSq (m*b i-n*a i) := by
  let H : ι → ℂ := fun i => m*b i-n*a i
  let J : ι → ι → ℂ := fun i j => a i*b j-a j*b i
  have hH : ∑ i, H i=0 := by
    simp only [H,Finset.sum_sub_distrib,← Finset.mul_sum,ha,hb,mul_zero,sub_self]
  have hrow (i : ι) : ∑ j, J i j=0 := by
    simp only [J,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,ha,hb,mul_zero,zero_mul,sub_self]
  have hcol (j : ι) : ∑ i, J i j=0 := by
    simp only [J,Finset.sum_sub_distrib,← Finset.mul_sum,← Finset.sum_mul,ha,hb,mul_zero,zero_mul,sub_self]
  have hcross1 : (∑ i, ∑ j, (H j*(starRingEnd ℂ) (J i j)).re)=0 := by
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [← Complex.re_sum,← Finset.mul_sum,← map_sum,hcol,map_zero,mul_zero]
    rfl
  have hcross2 : (∑ i, ∑ j, (H i*(starRingEnd ℂ) (J i j)).re)=0 := by
    apply Finset.sum_eq_zero
    intro i _
    rw [← Complex.re_sum,← Finset.mul_sum,← map_sum,hrow,map_zero,mul_zero]
    rfl
  have hcross : (∑ i, ∑ j, ((H j-H i)*(starRingEnd ℂ) (J i j)).re)=0 := by
    simp_rw [sub_mul,Complex.sub_re,Finset.sum_sub_distrib]
    rw [hcross1,hcross2,sub_self]
  have he (i j : ι) : (m+a i)*(n+b j)-(m+a j)*(n+b i)=H j-H i+J i j := by
    dsimp [H,J]
    ring
  simp_rw [he,normSq_add,Finset.sum_add_distrib,← Finset.mul_sum]
  rw [hcross,mul_zero,add_zero,sum_difference_normSq H hH]
  change (1/2:ℝ)*(2*(Fintype.card ι:ℝ)*(∑ i, normSq (H i))+
    ∑ i, ∑ j, normSq (J i j))= _
  dsimp [H,J]
  ring

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)

def meanField : ℂ → ℂ := sourceMean N f ∘ ofComplex

def centeredField (q : Deck N) : ℂ → ℂ := centeredComponent N f q ∘ ofComplex

theorem meanField_smooth (z : ℍ) : ContDiffAt ℝ 2 (meanField N f) (z:ℂ) :=
  (sourceMean_smooth N f).contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem centeredField_smooth (q : Deck N) (z : ℍ) : ContDiffAt ℝ 2 (centeredField N f q) (z:ℂ) :=
  (centeredComponent_eigenfunction N f q).1.contDiffAt (isOpen_upperHalfPlaneSet.mem_nhds z.im_pos)

theorem field_mean_decomposition (q : Deck N) (z : ℂ) :
    field N f q z=meanField N f z+centeredField N f q z := by
  simp only [field,meanField,centeredField,centeredComponent,Function.comp_apply]
  ring

theorem meanField_dir (v : ℂ) (z : ℍ) :
    dir v (meanField N f) (z:ℂ)=(Fintype.card (Deck N):ℂ)⁻¹*∑ q : Deck N, dir v (field N f q) (z:ℂ) := by
  have hs : ContDiffAt ℝ 2 (fun w => ∑ q : Deck N, field N f q w) (z:ℂ) :=
    ContDiffAt.sum (fun q _ => field_smooth N f q z)
  change fderiv ℝ (fun w => (Fintype.card (Deck N):ℂ)⁻¹ • ∑ q : Deck N, field N f q w) (z:ℂ) v= _
  rw [fderiv_fun_const_smul (hs.differentiableAt (by norm_num)),smul_apply]
  change (Fintype.card (Deck N):ℂ)⁻¹*dir v (fun w => ∑ q : Deck N, field N f q w) (z:ℂ)= _
  rw [dir_sum Finset.univ (fun q _ => (field_smooth N f q z).differentiableAt (by norm_num))]

theorem centeredField_dir (q : Deck N) (v : ℂ) (z : ℍ) :
    dir v (centeredField N f q) (z:ℂ)=dir v (field N f q) (z:ℂ)-dir v (meanField N f) (z:ℂ) := by
  change fderiv ℝ (fun w => field N f q w-meanField N f w) (z:ℂ) v= _
  rw [fderiv_fun_sub ((field_smooth N f q z).differentiableAt (by norm_num))
    ((meanField_smooth N f z).differentiableAt (by norm_num)),sub_apply]
  rfl

theorem sum_centeredField (z : ℂ) : ∑ q : Deck N, centeredField N f q z=0 :=
  sum_centeredComponent N f (ofComplex z)

theorem sum_centeredField_dir (v : ℂ) (z : ℍ) : ∑ q : Deck N, dir v (centeredField N f q) (z:ℂ)=0 := by
  simp_rw [centeredField_dir,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,meanField_dir]
  rw [← mul_assoc,mul_inv_cancel₀ (by exact_mod_cast Fintype.card_ne_zero : (Fintype.card (Deck N):ℂ)≠0),one_mul,sub_self]

/-- Exact pair-energy separation of the original Maass source. The mixed mean
and complement currents retain a nonnegative contribution with the full deck cardinality. -/
theorem pairEnergy_mean_decomposition (v : ℂ) (z : ℍ) :
    pairEnergy N f v (z:ℂ)=
      (1/2:ℝ)*∑ q : Deck N, ∑ r : Deck N,
        normSq (bracket (centeredField N f q) (centeredField N f r) v (z:ℂ))+
      (Fintype.card (Deck N):ℝ)*∑ q : Deck N,
        normSq (bracket (meanField N f) (centeredField N f q) v (z:ℂ)) := by
  have h := finite_mean_pair_decomposition (meanField N f (z:ℂ)) (dir v (meanField N f) (z:ℂ))
    (fun q : Deck N => centeredField N f q (z:ℂ))
    (fun q : Deck N => dir v (centeredField N f q) (z:ℂ))
    (sum_centeredField N f (z:ℂ)) (sum_centeredField_dir N f v z)
  have hd (q : Deck N) : dir v (meanField N f) (z:ℂ)+dir v (centeredField N f q) (z:ℂ)=
      dir v (field N f q) (z:ℂ) := by rw [centeredField_dir]; ring
  simp only [hd,← field_mean_decomposition] at h
  simpa only [pairEnergy,bracket,mul_comm (centeredField N f _ (z:ℂ))] using h

/-- Constant and zero-sum components have no omitted linear Hermitian cross
terms. Their individual phase currents still add before the phase is squared. -/
theorem finite_mean_hermitian_decomposition {ι : Type*} [Fintype ι]
    (m n : ℂ) (a b : ι → ℂ) (ha : ∑ i, a i=0) (hb : ∑ i, b i=0) :
    (∑ i, (n+b i)*(starRingEnd ℂ) (m+a i))=
      (Fintype.card ι:ℂ)*n*(starRingEnd ℂ) m+∑ i, b i*(starRingEnd ℂ) (a i) := by
  have h1 : (∑ i, n*(starRingEnd ℂ) (a i))=0 := by
    rw [← Finset.mul_sum,← map_sum,ha,map_zero,mul_zero]
  have h2 : (∑ i, b i*(starRingEnd ℂ) m)=0 := by
    rw [← Finset.sum_mul,hb,zero_mul]
  simp only [map_add,mul_add,add_mul,Finset.sum_add_distrib,h1,h2,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,add_zero,zero_add]
  ring

theorem hermitianPairing_mean_decomposition (v : ℂ) (z : ℍ) :
    (∑ q : Deck N, dir v (field N f q) (z:ℂ)*(starRingEnd ℂ) (field N f q (z:ℂ)))=
      (Fintype.card (Deck N):ℂ)*dir v (meanField N f) (z:ℂ)*(starRingEnd ℂ) (meanField N f (z:ℂ))+
      ∑ q : Deck N, dir v (centeredField N f q) (z:ℂ)*(starRingEnd ℂ) (centeredField N f q (z:ℂ)) := by
  have h := finite_mean_hermitian_decomposition (meanField N f (z:ℂ)) (dir v (meanField N f) (z:ℂ))
    (fun q : Deck N => centeredField N f q (z:ℂ))
    (fun q : Deck N => dir v (centeredField N f q) (z:ℂ))
    (sum_centeredField N f (z:ℂ)) (sum_centeredField_dir N f v z)
  have hd (q : Deck N) : dir v (meanField N f) (z:ℂ)+dir v (centeredField N f q) (z:ℂ)=
      dir v (field N f q) (z:ℂ) := by rw [centeredField_dir]; ring
  simpa only [hd,← field_mean_decomposition] using h

def meanPhaseCurrent (v z : ℂ) : ℝ :=
  (dir v (meanField N f) z*(starRingEnd ℂ) (meanField N f z)).im

def centeredPhaseCurrent (v z : ℂ) : ℝ :=
  ∑ q : Deck N, (dir v (centeredField N f q) z*(starRingEnd ℂ) (centeredField N f q z)).im

/-- The complete original phase current keeps the interference between its
mean and centered contributions. -/
theorem phaseCurrent_mean_decomposition (v : ℂ) (z : ℍ) :
    phaseCurrent N f v (z:ℂ)=
      (Fintype.card (Deck N):ℝ)*meanPhaseCurrent N f v (z:ℂ)+centeredPhaseCurrent N f v (z:ℂ) := by
  have h := congrArg Complex.im (hermitianPairing_mean_decomposition N f v z)
  simpa only [phaseCurrent,meanPhaseCurrent,centeredPhaseCurrent,Complex.im_sum,
    Complex.add_im,mul_assoc,Complex.mul_im,Complex.natCast_re,Complex.natCast_im,
    zero_mul,zero_add,add_zero] using h

/-- The full multiplied radial energy retains centered pair squares, positive
mixed brackets and the square of the sum of both phase currents, even at nodes. -/
theorem radialResidual_mean_decomposition (v : ℂ) (z : ℍ) :
    density N f z*SelbergMaassTraceRadial.radialResidual N f v
      (SelbergMaassTraceRadial.radialSlope N f v z) z=
      (1/2:ℝ)*∑ q : Deck N, ∑ r : Deck N,
        normSq (bracket (centeredField N f q) (centeredField N f r) v (z:ℂ))+
      (Fintype.card (Deck N):ℝ)*∑ q : Deck N,
        normSq (bracket (meanField N f) (centeredField N f q) v (z:ℂ))+
      ((Fintype.card (Deck N):ℝ)*meanPhaseCurrent N f v (z:ℂ)+centeredPhaseCurrent N f v (z:ℂ))^(2 : ℕ) := by
  rw [density_mul_radialResidual,pairEnergy_mean_decomposition,phaseCurrent_mean_decomposition]

/-- The mixed source currents supply an exact nonnegative lower part of the
full original pair energy, with the deck cardinality preserved. -/
theorem mixed_brackets_le_pairEnergy (v : ℂ) (z : ℍ) :
    (Fintype.card (Deck N):ℝ)*∑ q : Deck N,
      normSq (bracket (meanField N f) (centeredField N f q) v (z:ℂ)) ≤ pairEnergy N f v (z:ℂ) := by
  rw [pairEnergy_mean_decomposition]
  have hp : 0 ≤ (1/2:ℝ)*∑ q : Deck N, ∑ r : Deck N,
      normSq (bracket (centeredField N f q) (centeredField N f r) v (z:ℂ)) := by
    exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ =>
      Finset.sum_nonneg (fun _ _ => normSq_nonneg _)))
  linarith

private theorem eigenfunction_planar_equation {F : ℍ → ℂ} (hF : IsMaassEigenfunction lam F) (z : ℍ) :
    dir 1 (dir 1 (F ∘ ofComplex)) (z:ℂ)+dir Complex.I (dir Complex.I (F ∘ ofComplex)) (z:ℂ)=
      ((-(lam/z.im^(2 : ℕ)):ℝ):ℂ)*F z := by
  have hz : (z.im:ℂ)≠0 := Complex.ofReal_ne_zero.mpr z.im_pos.ne'
  have he := hF.2 z
  change -(z.im:ℂ)^(2 : ℕ)*(dir 1 (dir 1 (F ∘ ofComplex)) (z:ℂ)+
    dir Complex.I (dir Complex.I (F ∘ ofComplex)) (z:ℂ))=(lam:ℂ)*F z at he
  apply mul_left_cancel₀ (pow_ne_zero 2 hz)
  push_cast
  field_simp
  linear_combination -he

/-- Each mixed mean/remainder bracket is conserved by the original common
Maass equation; no amplitude division or vanishing of quotient periods is used. -/
theorem mixed_current_conservation (q : Deck N) (z : ℍ) :
    dir 1 (bracket (meanField N f) (centeredField N f q) 1) (z:ℂ)+
      dir Complex.I (bracket (meanField N f) (centeredField N f q) Complex.I) (z:ℂ)=0 := by
  rw [bracket_divergence (meanField_smooth N f z) (centeredField_smooth N f q z)]
  have hm := eigenfunction_planar_equation (sourceMean_eigenfunction N f) z
  have hq := eigenfunction_planar_equation (centeredComponent_eigenfunction N f q) z
  change dir 1 (dir 1 (meanField N f)) (z:ℂ)+dir Complex.I (dir Complex.I (meanField N f)) (z:ℂ)=
    ((-(lam/z.im^(2 : ℕ)):ℝ):ℂ)*sourceMean N f z at hm
  change dir 1 (dir 1 (centeredField N f q)) (z:ℂ)+dir Complex.I (dir Complex.I (centeredField N f q)) (z:ℂ)=
    ((-(lam/z.im^(2 : ℕ)):ℝ):ℂ)*centeredComponent N f q z at hq
  rw [hm,hq]
  simp only [meanField,centeredField,Function.comp_apply,ofComplex_apply]
  ring

/-- The common-zero locus is preserved exactly by the complete mean and
centered-source decomposition. -/
theorem field_zero_iff_mean_centered (z : ℂ) :
    (∀ q : Deck N, field N f q z=0) ↔
      meanField N f z=0 ∧ ∀ q : Deck N, centeredField N f q z=0 := by
  constructor
  · intro h
    have hm : meanField N f z=0 := by
      change (Fintype.card (Deck N):ℂ)⁻¹*(∑ q : Deck N, field N f q z)=0
      simp only [h,Finset.sum_const_zero,mul_zero]
    refine ⟨hm,fun q => ?_⟩
    have hh := field_mean_decomposition N f q z
    rw [h q,hm,zero_add] at hh
    exact hh.symm
  · rintro ⟨hm,h⟩ q
    rw [field_mean_decomposition,hm,h q,add_zero]

/-- The complete directional current numerator in mean and centered coordinates. -/
def meanSplitCurrentEnergy (v z : ℂ) : ℝ :=
  (1/2:ℝ)*∑ q : Deck N, ∑ r : Deck N,
    normSq (bracket (centeredField N f q) (centeredField N f r) v z)+
  (Fintype.card (Deck N):ℝ)*∑ q : Deck N,
    normSq (bracket (meanField N f) (centeredField N f q) v z)+
  ((Fintype.card (Deck N):ℝ)*meanPhaseCurrent N f v z+centeredPhaseCurrent N f v z)^(2 : ℕ)

theorem meanSplitCurrentEnergy_eq (v : ℂ) (z : ℍ) :
    meanSplitCurrentEnergy N f v (z:ℂ)=pairEnergy N f v (z:ℂ)+phaseCurrent N f v (z:ℂ)^(2 : ℕ) := by
  rw [pairEnergy_mean_decomposition,phaseCurrent_mean_decomposition]
  rfl

/-- Full original curvature retains the exact averaged-source currents in both
directions and the entire regulator-gradient term. -/
theorem curvature_mean_decomposition (e : Ioi (0:ℝ)) (z : ℍ) :
    SelbergMaassTraceRegularized.radius N f e (z:ℂ)^(3 : ℕ)*
      SelbergMaassWeakCurvature.curvatureWeight N f e (z:ℂ)=
        meanSplitCurrentEnergy N f 1 (z:ℂ)+meanSplitCurrentEnergy N f Complex.I (z:ℂ)+
          (e:ℝ)^(2 : ℕ)*gradientDensity N f (z:ℂ) := by
  rw [SelbergMaassCurrentCurvature.radius_cube_mul_curvatureWeight,
    SelbergMaassCurrentCurvature.currentEnergy,meanSplitCurrentEnergy_eq,meanSplitCurrentEnergy_eq]
  ring

/-- Both families of mixed conserved brackets give a source-derived lower
part of the complete regularized curvature numerator. -/
theorem mixed_brackets_le_curvature (e : Ioi (0:ℝ)) (z : ℍ) :
    (Fintype.card (Deck N):ℝ)*
      ((∑ q : Deck N, normSq (bracket (meanField N f) (centeredField N f q) 1 (z:ℂ)))+
        ∑ q : Deck N, normSq (bracket (meanField N f) (centeredField N f q) Complex.I (z:ℂ))) ≤
      SelbergMaassTraceRegularized.radius N f e (z:ℂ)^(3 : ℕ)*
        SelbergMaassWeakCurvature.curvatureWeight N f e (z:ℂ) := by
  have h1 := mixed_brackets_le_pairEnergy N f 1 z
  have hI := mixed_brackets_le_pairEnergy N f Complex.I z
  rw [SelbergMaassCurrentCurvature.radius_cube_mul_curvatureWeight,
    SelbergMaassCurrentCurvature.currentEnergy]
  have he : 0 ≤ (e:ℝ)^(2 : ℕ)*gradientDensity N f (z:ℂ) :=
    mul_nonneg (sq_nonneg _) (gradientDensity_nonneg N f _)
  nlinarith [sq_nonneg (phaseCurrent N f 1 (z:ℂ)),sq_nonneg (phaseCurrent N f Complex.I (z:ℂ))]

/-- If the actual average is zero, the centered family is the entire original
source, not a source from which any nonzero component was removed. -/
theorem centeredField_eq_of_mean_zero (hm : sourceMean N f=0) (q : Deck N) :
    centeredField N f q=field N f q := by
  funext z
  change field N f q z-sourceMean N f (ofComplex z)=field N f q z
  rw [hm,Pi.zero_apply,sub_zero]

/-- The mean channel's mixed currents vanish in the zero-average case;
all original current information is retained by the centered source. -/
theorem mixed_bracket_zero_of_mean_zero (hm : sourceMean N f=0) (q : Deck N) (v z : ℂ) :
    bracket (meanField N f) (centeredField N f q) v z=0 := by
  have h0 : meanField N f=(fun _ => (0:ℂ)) := by
    funext w
    simp [meanField,hm]
  rw [bracket,h0]
  simp [dir]

end
end GaloisForLFunctions.RHTower.SelbergMaassAverageCurrents
