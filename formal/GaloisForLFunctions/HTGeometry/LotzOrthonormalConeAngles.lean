import GaloisForLFunctions.HTGeometry.LotzStellarSolidAngles

/-!
# Exact solid angles for orthonormal cones and their signed subdivisions

Reflection symmetry and Gaussian independence give the symbolic angle
`(1/2)^dimension` for every orthonormal basis cone. Lotz's general signed
stellar relation then determines the total angle of all replacement cones,
including arbitrary nonzero ray coordinates and the exterior correction.
-/

noncomputable section
namespace GaloisForLFunctions.HTGeometry
open MeasureTheory ProbabilityTheory Module Set
open scoped BigOperators
attribute [local instance] Classical.propDecidable

/-- Reflection symmetry and atomlessness split the standard real Gaussian into equal half-lines. -/
theorem lotz_gaussianReal_halfline : (gaussianReal 0 1).real (Ici 0) = 1/2 := by
  letI := nullSingletonClass_gaussianReal (μ := 0) (v := 1) one_ne_zero
  have hs : (gaussianReal 0 1) (Ici 0) = (gaussianReal 0 1) (Iic 0) := by
    calc
      _ = ((gaussianReal 0 1).map (fun x => -x)) (Ici 0) := by
        rw [gaussianReal_map_neg,neg_zero]
      _ = _ := by
        rw [Measure.map_apply (by fun_prop) measurableSet_Ici]
        congr 1
        ext x
        simp
  have hinter : Iic (0 : ℝ) ∩ Ici 0 = {0} := by
    ext x
    simp only [mem_inter_iff,mem_Iic,mem_Ici,mem_singleton_iff]
    exact le_antisymm_iff.symm
  have h := measureReal_union_add_inter (μ := gaussianReal 0 1)
    (s := Iic 0) (t := Ici 0) measurableSet_Ici
  rw [Iic_union_Ici,hinter] at h
  have hsreal := congrArg ENNReal.toReal hs
  change (gaussianReal 0 1).real (Ici 0) = (gaussianReal 0 1).real (Iic 0) at hsreal
  have hz : (gaussianReal 0 1).real {0}=0 := by simp [Measure.real]
  rw [probReal_univ,hz,add_zero] at h
  linarith

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [DecidableEq ι] in
/-- Every orthonormal basis cone has exactly the same solid angle in every finite dimension. -/
theorem lotzGaussian_orthonormal_cone (b : OrthonormalBasis ι ℝ E) :
    lotzGaussianConeVal (lotzProperBasisCone b.toBasis) = (1/2 : ℝ)^Fintype.card ι := by
  unfold lotzGaussianConeVal Measure.real
  have hm : Measurable (fun x : ι → ℝ => ∑ i,x i • b i) := by fun_prop
  have hpre : (fun x : ι → ℝ => ∑ i,x i • b i) ⁻¹' (lotzBasisCone b.toBasis : Set E) =
      Set.pi Set.univ (fun _ => Ici (0 : ℝ)) := by
    ext x
    change (∑ i,x i • b i) ∈ lotzBasisCone b.toBasis ↔ ∀ i ∈ Set.univ, x i ∈ Ici 0
    rw [lotzBasisCone_mem]
    have he : (∑ i,x i • b i) = b.toBasis.equivFun.symm x := by
      simpa only [OrthonormalBasis.coe_toBasis] using (b.toBasis.equivFun_symm_apply x).symm
    rw [he,LinearEquiv.apply_symm_apply]
    simp
  change ((stdGaussian E) (lotzBasisCone b.toBasis : Set E)).toReal = _
  rw [stdGaussian_eq_map_pi_orthonormalBasis b,
    Measure.map_apply hm (isClosed_lotzBasisCone b.toBasis).measurableSet,hpre,Measure.pi_pi]
  simp only [ENNReal.toReal_prod]
  change (∏ _ : ι,(gaussianReal 0 1).real (Ici 0)) = _
  simp only [lotz_gaussianReal_halfline,Finset.prod_const,Finset.card_univ]

variable [Nonempty ι]

/-- Signed replacement-cone angles have a symbolic exact total, determined solely by dimension and ray signs. -/
theorem lotz_orthonormal_stellar_angle_total (b : OrthonormalBasis ι ℝ E) (a : ι → ℝˣ) :
    (∑ j, (if 0 < (a j : ℝ) then (1 : ℝ) else -1)*
      lotzGaussianConeVal (lotzProperBasisCone (lotzStellarBasis b.toBasis a j))) =
      (1/2 : ℝ)^Fintype.card ι - (if ∀ j,(a j : ℝ)<0 then (1 : ℝ) else 0) := by
  have h := lotz_signed_stellar_solid_angle b.toBasis a
  rw [lotzGaussian_orthonormal_cone] at h
  linarith

end GaloisForLFunctions.HTGeometry
