/-
Hyperbolic differential isometries adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.SmoothCutoffsOnTheCubicQuotient

/-!
# Hyperbolic invariance of Dirichlet energy density

Translations, diagonal matrices, and inversion have derivatives scaled by
height ratios. Bruhat decomposition propagates this to every special linear
matrix. The dual norm identity then gives invariance of scalar energy density.
-/

noncomputable section
open Filter MeasureTheory
open scoped BigOperators Classical Topology InnerProductSpace ENNReal MatrixGroups
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

def euclideanAction (g : SL(2,ℂ)) (p : EuclideanSpatial) : EuclideanSpatial :=
  hyperbolicEuclideanCoordinates (g•euclideanToHyperbolic p)

lemma euclideanAction_positive (g : SL(2,ℂ)) (p : EuclideanSpatial) :
    0<euclideanAction g p 2 := by
  change 0<hyperbolicHeight (g•euclideanToHyperbolic p)
  exact hyperbolicHeight_pos _

lemma euclideanAction_mul (g h : SL(2,ℂ)) :
    euclideanAction (g*h)=euclideanAction g ∘ euclideanAction h := by
  funext p
  simp only [euclideanAction,Function.comp_apply,euclideanToHyperbolic_coordinates,mul_smul]

lemma euclideanAction_translation (b : ℂ) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexTranslation b) p=p+euclideanHorizontalTranslation b := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexTranslation_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j <;> simp [euclideanHorizontalTranslation]

lemma euclideanAction_diagonal (b : ℂ) (hb : b≠0) (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction (complexDiagonal b hb) p=euclideanComplexDilation b p := by
  rw [euclideanAction,euclideanToHyperbolic_positive _ hp,complexDiagonal_action,
    hyperbolicEuclideanCoordinates_upperPoint]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b p
  apply (WithLp.equiv 2 (Fin 3→ℝ)).injective
  funext j
  fin_cases j
  · simpa [Complex.mul_re] using h0.symm
  · simpa [Complex.mul_im,add_comm] using h1.symm
  · exact h2.symm

lemma euclideanAction_weyl (p : EuclideanSpatial) (hp : 0<p 2) :
    euclideanAction complexWeyl p=euclideanWeylAction p := by
  have hn : ‖p‖≠0 := norm_ne_zero_iff.mpr (euclideanUpperHalf_ne_zero p hp)
  have hnc : (‖p‖:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hn
  have hq : 0<euclideanWeylAction p 2 := by
    rw [(euclideanWeylAction_apply p).2.2]
    exact mul_pos (sq_pos_of_ne_zero (one_div_ne_zero hn)) hp
  have h := congrArg hyperbolicEuclideanCoordinates
    (show euclideanToHyperbolic (euclideanWeylAction p)=
      complexWeyl•euclideanToHyperbolic p from by
      rw [euclideanToHyperbolic_positive _ hq,euclideanToHyperbolic_positive _ hp,complexWeyl_action]
      obtain ⟨h0,h1,h2⟩ := euclideanWeylAction_apply p
      apply upperPoint_congr
      · rw [h0,h1,euclidean_complex_norm_sq]
        simp only [Complex.ofReal_neg,Complex.ofReal_mul,Complex.ofReal_pow,Complex.ofReal_div,
          Complex.ofReal_one,Complex.star_def,map_add,map_mul,Complex.conj_ofReal,Complex.conj_I]
        field_simp
        ring
      · rw [h2,euclidean_complex_norm_sq]
        field_simp)
  simpa only [hyperbolicEuclideanCoordinates_toHyperbolic _ hq,euclideanAction] using h.symm

lemma euclideanWeylReflection_norm (u : EuclideanSpatial) : ‖euclideanWeylReflection u‖=‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanWeylReflection_apply u
  simp only [Fin.sum_univ_three,h0,h1,h2,neg_sq]

lemma euclideanComplexDilation_norm (b : ℂ) (u : EuclideanSpatial) :
    ‖euclideanComplexDilation b u‖=Complex.normSq b*‖u‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Complex.normSq_nonneg _) (norm_nonneg _))).mp
  have h : (b^2).re^2+(b^2).im^2=(Complex.normSq b)^2 := by
    simpa [Complex.normSq_apply,sq] using map_pow Complex.normSq b 2
  rw [mul_pow,EuclideanSpace.real_norm_sq_eq,EuclideanSpace.real_norm_sq_eq]
  obtain ⟨h0,h1,h2⟩ := euclideanComplexDilation_apply b u
  simp only [Fin.sum_univ_three,h0,h1,h2]
  calc
    _ = ((b^2).re^2+(b^2).im^2)*((u 0)^2+(u 1)^2)+(Complex.normSq b)^2*(u 2)^2 := by ring
    _ = _ := by rw [h]; ring

lemma euclideanInversionDeriv_norm (p u : EuclideanSpatial) :
    ‖euclideanInversionDeriv p u‖=(1/‖p‖)^2*‖u‖ := by
  unfold euclideanInversionDeriv
  rw [_root_.smul_apply,norm_smul,Real.norm_of_nonneg (sq_nonneg _)]
  simp only [LinearIsometryEquiv.coe_coe'',LinearIsometryEquiv.norm_map]

/-- The derivative preserves the hyperbolic norm `‖u‖ / height`. -/
def HyperbolicDifferentialIsometry (g : SL(2,ℂ)) : Prop :=
  ∀p : EuclideanSpatial,0<p 2 → ∃A : EuclideanSpatial→L[ℝ]EuclideanSpatial,
    HasFDerivAt (euclideanAction g) A p ∧
    ∀u,‖A u‖*p 2=‖u‖*euclideanAction g p 2

lemma hyperbolicDifferentialIsometry_mul (g h : SL(2,ℂ))
    (hg : HyperbolicDifferentialIsometry g) (hh : HyperbolicDifferentialIsometry h) :
    HyperbolicDifferentialIsometry (g*h) := by
  intro p hp
  obtain ⟨B,hB,hBn⟩ := hh p hp
  obtain ⟨A,hA,hAn⟩ := hg (euclideanAction h p) (euclideanAction_positive h p)
  refine ⟨A.comp B,?_,?_⟩
  · rw [euclideanAction_mul]
    exact hA.comp p hB
  · intro u
    rw [euclideanAction_mul]
    change ‖A (B u)‖*p 2=‖u‖*euclideanAction g (euclideanAction h p) 2
    apply (mul_right_inj' (euclideanAction_positive h p).ne').mp
    calc
      _ = (‖A (B u)‖*euclideanAction h p 2)*p 2 := by ring
      _ = (‖B u‖*euclideanAction g (euclideanAction h p) 2)*p 2 := by rw [hAn]
      _ = (‖B u‖*p 2)*euclideanAction g (euclideanAction h p) 2 := by ring
      _ = _ := by rw [hBn]; ring

lemma hyperbolicDifferentialIsometry_translation (b : ℂ) :
    HyperbolicDifferentialIsometry (complexTranslation b) := by
  intro p hp
  refine ⟨ContinuousLinearMap.id ℝ _,?_,?_⟩
  · apply ((hasFDerivAt_id p).add_const (euclideanHorizontalTranslation b)).congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_translation b q hq
  · intro u
    rw [euclideanAction_translation b p hp]
    simp [euclideanHorizontalTranslation]

lemma hyperbolicDifferentialIsometry_diagonal (b : ℂ) (hb : b≠0) :
    HyperbolicDifferentialIsometry (complexDiagonal b hb) := by
  intro p hp
  refine ⟨euclideanComplexDilation b,?_,?_⟩
  · apply (euclideanComplexDilation b).hasFDerivAt.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_diagonal b hb q hq
  · intro u
    rw [euclideanComplexDilation_norm,euclideanAction_diagonal b hb p hp,
      (euclideanComplexDilation_apply b p).2.2]
    ring

lemma hyperbolicDifferentialIsometry_weyl : HyperbolicDifferentialIsometry complexWeyl := by
  intro p hp
  refine ⟨euclideanWeylReflection.comp (euclideanInversionDeriv p),?_,?_⟩
  · have h := euclideanWeylReflection.hasFDerivAt.comp p
      (euclideanInversion_hasFDerivAt p (euclideanUpperHalf_ne_zero p hp))
    apply h.congr_of_eventuallyEq
    filter_upwards [(by fun_prop : Continuous (fun p : EuclideanSpatial => p 2)).continuousAt.eventually_const_lt hp]
      with q hq
    exact euclideanAction_weyl q hq
  · intro u
    change ‖euclideanWeylReflection (euclideanInversionDeriv p u)‖*p 2=_
    rw [euclideanWeylReflection_norm,euclideanInversionDeriv_norm,euclideanAction_weyl p hp,
      (euclideanWeylAction_apply p).2.2]
    ring

/-- Every complex special linear matrix acts by hyperbolic differential isometries. -/
theorem hyperbolicDifferentialIsometry (g : SL(2,ℂ)) : HyperbolicDifferentialIsometry g := by
  by_cases hc : g 1 0=0
  · obtain ⟨ha,hg⟩ := complex_bruhat_zero g hc
    rw [hg]
    exact hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_diagonal _ ha)
      (hyperbolicDifferentialIsometry_translation _)
  · rw [complex_bruhat_nonzero g hc]
    exact hyperbolicDifferentialIsometry_mul _ _
      (hyperbolicDifferentialIsometry_mul _ _
        (hyperbolicDifferentialIsometry_mul _ _ (hyperbolicDifferentialIsometry_translation _)
          (hyperbolicDifferentialIsometry_diagonal _ (inv_ne_zero hc)))
        hyperbolicDifferentialIsometry_weyl)
      (hyperbolicDifferentialIsometry_translation _)


lemma norm_comp_scaled_isometry (A : EuclideanSpatial→L[ℝ]EuclideanSpatial) (r : ℝ)
    (hr : 0<r) (hA : ∀u,‖A u‖=r*‖u‖) (φ : EuclideanSpatial→L[ℝ]ℝ) :
    ‖φ.comp A‖=r*‖φ‖ := by
  let iso : EuclideanSpatial→ₗᵢ[ℝ]EuclideanSpatial :=
    { toLinearMap := (r⁻¹ • A).toLinearMap
      norm_map' := fun u => by
        change ‖r⁻¹ • A u‖=‖u‖
        rw [norm_smul,Real.norm_of_nonneg (inv_nonneg.mpr hr.le),hA]
        field_simp }
  let equiv : EuclideanSpatial≃ₗᵢ[ℝ]EuclideanSpatial :=
    LinearIsometryEquiv.ofSurjective iso ((LinearMap.injective_iff_surjective).mp iso.injective)
  have he : A=r • (equiv : EuclideanSpatial→L[ℝ]EuclideanSpatial) := by
    apply ContinuousLinearMap.ext
    intro u
    change A u=r • (r⁻¹ • A u)
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  rw [he,ContinuousLinearMap.comp_smul,norm_smul,Real.norm_of_nonneg hr.le,
    ContinuousLinearMap.opNorm_comp_linearIsometryEquiv]

/-- Pullback preserves squared cotangent norm weighted by squared height. -/
lemma hyperbolic_cotangent_energy_comp (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p)) :
    (p 2)^2*‖fderiv ℝ (F ∘ euclideanAction g) p‖^2=
      (euclideanAction g p 2)^2*‖fderiv ℝ F (euclideanAction g p)‖^2 := by
  obtain ⟨A,hA,hAn⟩ := hyperbolicDifferentialIsometry g p hp
  rw [(hF.hasFDerivAt.comp p hA).fderiv]
  have hn : ∀u,‖A u‖=(euclideanAction g p 2/p 2)*‖u‖ := by
    intro u
    calc
      ‖A u‖=(‖u‖*euclideanAction g p 2)/p 2 := (eq_div_iff hp.ne').2 (hAn u)
      _ = _ := by ring
  rw [norm_comp_scaled_isometry A _ (div_pos (euclideanAction_positive g p) hp) hn]
  field_simp

def euclideanScalarDirichletDensity (F : EuclideanSpatial→ℝ) (p : EuclideanSpatial) : ℝ :=
  (p 2)^2*‖fderiv ℝ F p‖^2

lemma euclideanScalarDirichletDensity_invariant (g : SL(2,ℂ)) (F : EuclideanSpatial→ℝ)
    (p : EuclideanSpatial) (hp : 0<p 2) (hF : DifferentiableAt ℝ F (euclideanAction g p))
    (hinv : F ∘ euclideanAction g=F) :
    euclideanScalarDirichletDensity F (euclideanAction g p)=euclideanScalarDirichletDensity F p := by
  have h := hyperbolic_cotangent_energy_comp g F p hp hF
  rw [hinv] at h
  exact h.symm

#print axioms hyperbolicDifferentialIsometry
#print axioms hyperbolic_cotangent_energy_comp
#print axioms euclideanScalarDirichletDensity_invariant
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
