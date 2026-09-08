import GaloisForLFunctions.HTGeometry.FokasLenellsRightJost

/-!
# Left Fokas–Lenells Jost solutions and global interaction bounds

The interaction density is even because the nonlocal reduction includes
both `q′(x)` and `q′(-x)`. The same variable-coefficient Grönwall argument
therefore controls the negative ray. Integrable reverse transport constructs
a left asymptotic matrix of determinant one.

The resulting left Jost function solves equation (2.2), tends to the identity
at the left endpoint as specified after (2.3), and satisfies the determinant
identity (2.61) of Yan–Zhang–Zhu, arXiv:2607.19649v1. These results hold for
every Schwartz potential and every positive real spectral parameter `exp κ`.
No boundary limit, invertibility or smallness condition is assumed.
-/

open Complex Matrix MeasureTheory Filter Topology
open scoped Matrix.Norms.Elementwise
namespace GaloisForLFunctions.HTGeometry.FokasLenells
noncomputable section


/-- Reverse-space coupling makes the dominating interaction density even. -/
theorem scatteringDensity_even (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    scatteringDensity q κ (-x) = scatteringDensity q κ x := by
  simp [scatteringDensity, reflectedDerivative, RHTower.negSchwartz'_apply,
    SchwartzMap.derivCLM_apply, add_comm]

def reversedInteractionSolution (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector)
    (x : ℝ) : SpectralVector := interactionSolution q κ v (-x)

def reversedInteractionDerivative (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector)
    (x : ℝ) : SpectralVector := -interactionDerivative q κ v (-x)

theorem reversedInteractionSolution_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    HasDerivAt (reversedInteractionSolution q κ v) (reversedInteractionDerivative q κ v x) x := by
  change HasDerivAt (fun y : ℝ => interactionSolution q κ v (-y))
    (-interactionRate q κ (-x) (interactionSolution q κ v (-x))) x
  have h := (interactionSolution_hasDerivAt q κ v (-x)).scomp x (hasDerivAt_id x).neg
  simpa only [Function.comp_def, neg_one_smul] using h

theorem reversedInteractionSolution_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) : Continuous (reversedInteractionSolution q κ v) :=
  (interactionSolution_continuous q κ v).comp (f := fun x : ℝ => -x) continuous_neg

theorem reversedInteractionDerivative_continuous (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) : Continuous (reversedInteractionDerivative q κ v) :=
  ((interactionDerivative_continuous q κ v).comp (f := fun x : ℝ => -x) continuous_neg).neg

theorem reversedInteractionDerivative_bound (q : SchwartzMap ℝ ℂ) (κ x : ℝ)
    (v : SpectralVector) :
    ‖reversedInteractionDerivative q κ v x‖ ≤
      scatteringDensity q κ x*‖reversedInteractionSolution q κ v x‖ := by
  have h := interactionRate_bound q κ (-x) (interactionSolution q κ v (-x))
  simpa only [reversedInteractionDerivative, norm_neg, interactionDerivative,
    reversedInteractionSolution, scatteringDensity_even] using h

theorem reversedInteractionSolution_integral (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    reversedInteractionSolution q κ v x =
      v + ∫ s in (0:ℝ)..x, reversedInteractionDerivative q κ v s := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun y _ => reversedInteractionSolution_hasDerivAt q κ v y)
    ((reversedInteractionDerivative_continuous q κ v).intervalIntegrable 0 x)
  have hz : reversedInteractionSolution q κ v 0 = v := by
    simp [reversedInteractionSolution, interactionSolution_initial]
  rw [hz] at h
  simpa only [add_comm] using (sub_eq_iff_eq_add.mp h.symm)

/-- The same total mass controls the negative ray. -/
theorem interactionSolution_negative_bound (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    ‖interactionSolution q κ v (-|x|)‖ ≤ ‖v‖*Real.exp (scatteringMass q κ) := by
  have hS := (reversedInteractionSolution_continuous q κ v).norm
  have hk := scatteringDensity_continuous q κ
  have hD := (reversedInteractionDerivative_continuous q κ v).norm
  change ‖reversedInteractionSolution q κ v |x|‖ ≤ _
  apply le_mul_exp_of_le_add_integral_of_mass_le (A := 0) (B := |x|)
    (S := fun y => ‖reversedInteractionSolution q κ v y‖) (k := scatteringDensity q κ)
    (abs_nonneg x) hS.continuousOn hk.continuousOn
    (fun y _ => scatteringDensity_nonneg q κ y) (norm_nonneg v)
  · intro y hy
    calc
      ‖reversedInteractionSolution q κ v y‖ =
          ‖v + ∫ s in (0:ℝ)..y, reversedInteractionDerivative q κ v s‖ := by
        rw [reversedInteractionSolution_integral]
      _ ≤ ‖v‖ + ‖∫ s in (0:ℝ)..y, reversedInteractionDerivative q κ v s‖ := norm_add_le _ _
      _ ≤ ‖v‖ + ∫ s in (0:ℝ)..y, ‖reversedInteractionDerivative q κ v s‖ :=
        add_le_add le_rfl (intervalIntegral.norm_integral_le_integral_norm hy.1)
      _ ≤ ‖v‖ + ∫ s in (0:ℝ)..y,
          scatteringDensity q κ s*‖reversedInteractionSolution q κ v s‖ := by
        apply add_le_add le_rfl
        exact intervalIntegral.integral_mono_on hy.1 (hD.intervalIntegrable 0 y)
          ((hk.mul hS).intervalIntegrable 0 y)
          (fun s _ => reversedInteractionDerivative_bound q κ s v)
  · intro y hy
    rw [intervalIntegral.integral_of_le hy.1]
    exact setIntegral_le_integral (scatteringDensity_integrable q κ)
      (Filter.Eventually.of_forall (scatteringDensity_nonneg q κ))
  · exact ⟨abs_nonneg x, le_rfl⟩

theorem interactionSolution_global_bound (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) (x : ℝ) :
    ‖interactionSolution q κ v x‖ ≤ ‖v‖*Real.exp (scatteringMass q κ) := by
  by_cases hx : 0 ≤ x
  · simpa only [abs_of_nonneg hx] using interactionSolution_positive_bound q κ v x
  · have hx' : x ≤ 0 := le_of_not_ge hx
    simpa only [abs_of_nonpos hx', neg_neg] using interactionSolution_negative_bound q κ v x

theorem reversedInteractionDerivative_integrableOn_Ioi (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) :
    IntegrableOn (reversedInteractionDerivative q κ v) (Set.Ioi 0) := by
  have hmajor := ((scatteringDensity_integrable q κ).const_mul
    (‖v‖*Real.exp (scatteringMass q κ))).integrableOn (s := Set.Ioi 0)
  apply hmajor.mono' (reversedInteractionDerivative_continuous q κ v).aestronglyMeasurable
  filter_upwards with x
  calc
    ‖reversedInteractionDerivative q κ v x‖ ≤
        scatteringDensity q κ x*‖reversedInteractionSolution q κ v x‖ :=
      reversedInteractionDerivative_bound _ _ _ _
    _ ≤ scatteringDensity q κ x*(‖v‖*Real.exp (scatteringMass q κ)) :=
      mul_le_mul_of_nonneg_left (interactionSolution_global_bound q κ v (-x))
        (scatteringDensity_nonneg q κ x)
    _ = _ := mul_comm _ _

def leftAsymptoticVector (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v : SpectralVector) :
    SpectralVector := v + ∫ x in Set.Ioi (0:ℝ), reversedInteractionDerivative q κ v x

theorem reversedInteractionSolution_tendsto_right (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) :
    Tendsto (reversedInteractionSolution q κ v) atTop (𝓝 (leftAsymptoticVector q κ v)) := by
  have h := tendsto_of_hasDerivAt_of_integrableOn_Ioi (a := 0)
    (fun x _ => reversedInteractionSolution_hasDerivAt q κ v x)
    (reversedInteractionDerivative_integrableOn_Ioi q κ v)
  simpa only [reversedInteractionSolution, neg_zero, interactionSolution_initial,
    leftAsymptoticVector] using h

theorem interactionSolution_tendsto_left (q : SchwartzMap ℝ ℂ) (κ : ℝ)
    (v : SpectralVector) :
    Tendsto (interactionSolution q κ v) atBot (𝓝 (leftAsymptoticVector q κ v)) := by
  have h := (reversedInteractionSolution_tendsto_right q κ v).comp
    (tendsto_neg_atBot_atTop : Tendsto (fun x : ℝ => -x) atBot atTop)
  simpa only [Function.comp_def, reversedInteractionSolution, neg_neg] using h

theorem leftAsymptoticVector_wedge (q : SchwartzMap ℝ ℂ) (κ : ℝ) (v w : SpectralVector) :
    (leftAsymptoticVector q κ v).1*(leftAsymptoticVector q κ w).2 -
      (leftAsymptoticVector q κ v).2*(leftAsymptoticVector q κ w).1 = v.1*w.2-v.2*w.1 := by
  have hv := interactionSolution_tendsto_left q κ v
  have hw := interactionSolution_tendsto_left q κ w
  have h := (hv.fst_nhds.mul hw.snd_nhds).sub (hv.snd_nhds.mul hw.fst_nhds)
  simp only [interactionSolution_wedge] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

def leftAsymptoticMatrix (q : SchwartzMap ℝ ℂ) (κ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(leftAsymptoticVector q κ (1,0)).1, (leftAsymptoticVector q κ (0,1)).1;
     (leftAsymptoticVector q κ (1,0)).2, (leftAsymptoticVector q κ (0,1)).2]

theorem interactionFundamentalMatrix_tendsto_left (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (interactionFundamentalMatrix q κ) atBot (𝓝 (leftAsymptoticMatrix q κ)) := by
  have hc : Continuous (fun p : SpectralVector × SpectralVector =>
      (!![p.1.1,p.2.1;p.1.2,p.2.2] : Matrix (Fin 2) (Fin 2) ℂ)) := by fun_prop
  exact (hc.tendsto _).comp ((interactionSolution_tendsto_left q κ (1,0)).prodMk_nhds
    (interactionSolution_tendsto_left q κ (0,1)))

theorem leftAsymptoticMatrix_det (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    (leftAsymptoticMatrix q κ).det = 1 := by
  have h := leftAsymptoticVector_wedge q κ (1,0) (0,1)
  simpa [leftAsymptoticMatrix, Matrix.det_fin_two, mul_comm] using h

theorem leftAsymptoticMatrix_mul_inverse (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    leftAsymptoticMatrix q κ*(leftAsymptoticMatrix q κ)⁻¹ = 1 := by
  apply Matrix.mul_nonsing_inv
  rw [leftAsymptoticMatrix_det]
  exact isUnit_one

/-- The fundamental matrix normalized at the left infinite endpoint. -/
def leftJostMatrix (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  spatialFundamentalMatrix q (κ:ℂ) x*(leftAsymptoticMatrix q κ)⁻¹

def leftJostFrame (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  interactionFundamentalMatrix q κ x*(leftAsymptoticMatrix q κ)⁻¹

theorem leftJostFrame_tendsto_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (leftJostFrame q κ) atBot (𝓝 1) := by
  have h := (interactionFundamentalMatrix_tendsto_left q κ).mul_const
    ((leftAsymptoticMatrix q κ)⁻¹)
  rwa [leftAsymptoticMatrix_mul_inverse] at h

theorem leftJostFrame_eq_diagonal_mul (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    leftJostFrame q κ x = diagonalFrame ((Real.exp κ)^2) x*leftJostMatrix q κ x := by
  unfold leftJostFrame leftJostMatrix
  rw [← Matrix.mul_assoc]
  congr 1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalFrame, interactionFundamentalMatrix, spatialFundamentalMatrix,
      interactionSolution, rotatingFrame, Matrix.mul_apply, Fin.sum_univ_two]

theorem leftJostMatrix_det (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    (leftJostMatrix q κ x).det = 1 := by
  rw [leftJostMatrix, Matrix.det_mul, spatialFundamentalMatrix_det,
    Matrix.det_nonsing_inv, leftAsymptoticMatrix_det]
  simp

/-- Constant linear combinations preserve the spatial system without any invertibility premise. -/
theorem spatialMatrixCombination_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (a : ℂ)
    (C : Matrix (Fin 2) (Fin 2) ℂ) (x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => (spatialFundamentalMatrix q a y*C) i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp a)*
        (spatialFundamentalMatrix q a x*C)) i j) x := by
  have h := ((spatialFundamentalMatrix_entry_hasDerivAt q a x i 0).mul_const (C 0 j)).fun_add
    ((spatialFundamentalMatrix_entry_hasDerivAt q a x i 1).mul_const (C 1 j))
  rw [← Matrix.mul_assoc]
  simpa only [Matrix.mul_apply, Fin.sum_univ_two] using h

theorem leftJostMatrix_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => leftJostMatrix q κ y i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp (κ:ℂ))*
        leftJostMatrix q κ x) i j) x :=
  spatialMatrixCombination_entry_hasDerivAt q (κ:ℂ) _ x i j

/-- The left-normalized Jost function, in the phase convention of equation (2.2). -/
def leftJostFunction (q : SchwartzMap ℝ ℂ) (κ x : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  leftJostMatrix q κ x*diagonalFrame ((Real.exp κ)^2) x

theorem leftJostFunction_norm_sub_one (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    ‖leftJostFunction q κ x-1‖ = ‖leftJostFrame q κ x-1‖ := by
  have hleft : diagonalFrame (-((Real.exp κ)^2)) x*leftJostFrame q κ x =
      leftJostMatrix q κ x := by
    rw [leftJostFrame_eq_diagonal_mul, ← Matrix.mul_assoc, diagonalFrame_neg_inverse, one_mul]
  have he : leftJostFunction q κ x-1 =
      diagonalFrame (-((Real.exp κ)^2)) x*(leftJostFrame q κ x-1)*
        diagonalFrame ((Real.exp κ)^2) x := by
    rw [mul_sub, sub_mul, mul_one, hleft, diagonalFrame_neg_inverse]
    rfl
  rw [he, diagonalFrame_conjugation_norm]

theorem leftJostFunction_tendsto_one (q : SchwartzMap ℝ ℂ) (κ : ℝ) :
    Tendsto (leftJostFunction q κ) atBot (𝓝 1) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have h := tendsto_iff_norm_sub_tendsto_zero.mp (leftJostFrame_tendsto_one q κ)
  simpa only [leftJostFunction_norm_sub_one] using h

theorem leftJostFunction_det (q : SchwartzMap ℝ ℂ) (κ x : ℝ) :
    (leftJostFunction q κ x).det = 1 := by
  rw [leftJostFunction, Matrix.det_mul, leftJostMatrix_det, diagonalFrame_det, one_mul]

theorem leftJostFunction_entry_hasDerivAt (q : SchwartzMap ℝ ℂ) (κ x : ℝ) (i j : Fin 2) :
    HasDerivAt (fun y => leftJostFunction q κ y i j)
      ((spatialLax (deriv q x) (deriv (fun y : ℝ => q (-y)) x) (Complex.exp (κ:ℂ))*
          leftJostFunction q κ x -
        leftJostFunction q κ x*spatialLax 0 0 (Complex.exp (κ:ℂ))) i j) x := by
  fin_cases j
  · have he : (fun y => leftJostFunction q κ y i 0) =
        fun y => leftJostMatrix q κ y i 0*FDNLS.staggerPhase ((Real.exp κ)^2) y := by
      funext y
      simp [leftJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((leftJostMatrix_entry_hasDerivAt q κ x i 0).fun_mul
      (FDNLS.hasDerivAt_staggerPhase ((Real.exp κ)^2) x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [leftJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, ← Complex.ofReal_exp] <;> ring
  · have he : (fun y => leftJostFunction q κ y i 1) =
        fun y => leftJostMatrix q κ y i 1*FDNLS.staggerPhase (-((Real.exp κ)^2)) y := by
      funext y
      simp [leftJostFunction, diagonalFrame, Matrix.mul_apply, Fin.sum_univ_two]
    refine (((leftJostMatrix_entry_hasDerivAt q κ x i 1).fun_mul
      (FDNLS.hasDerivAt_staggerPhase (-((Real.exp κ)^2)) x)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall (fun y => congrFun he y))).congr_deriv ?_
    fin_cases i <;>
      simp [leftJostFunction, diagonalFrame, spatialLax, Matrix.mul_apply, Matrix.vecMul,
        dotProduct, Fin.sum_univ_two, ← Complex.ofReal_exp] <;> ring

end
end GaloisForLFunctions.HTGeometry.FokasLenells
