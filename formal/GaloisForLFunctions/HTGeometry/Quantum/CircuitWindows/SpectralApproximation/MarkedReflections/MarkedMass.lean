import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpectralApproximation.MarkedReflections.PositiveDiagonal

/-! # Exact spectral-torus distance when every marked weight is at most one half -/
open Matrix Finset
open scoped Matrix.Norms.L2Operator ComplexConjugate
namespace GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
open private diagonal_overlap from GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SharpOccupation.UnitaryDiagonal
open StaticLocalLaboratoryComplexityGrowthLaw
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Marked spectral mass seen by the ith coordinate. -/
def rowWeight (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (i : I) : ℝ :=
  ∑ j∈M, ‖(V:Mat I) i j‖^2

def markSign (M : Finset I) (j : I) : ℂ := if j∈M then -1 else 1

def reflection (V : Matrix.unitaryGroup I ℂ) (M : Finset I) : Mat I :=
  (V:Mat I)*diagonal (markSign M)*star (V:Mat I)

omit [Nonempty I] in
private theorem diagonal_sum (V : Matrix.unitaryGroup I ℂ) (f : I → ℂ) (i : I) :
    ((V:Mat I)*diagonal f*star (V:Mat I)) i i = ∑ j, (‖(V:Mat I) i j‖^2:ℝ)*f j := by
  rw [Matrix.mul_apply]
  apply sum_congr rfl
  intro j _
  rw [Matrix.mul_diagonal,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_apply]
  change (V:Mat I) i j*f j*conj ((V:Mat I) i j)=_
  rw [show (V:Mat I) i j*f j*conj ((V:Mat I) i j)=((V:Mat I) i j*conj ((V:Mat I) i j))*f j by ring,
    Complex.mul_conj',Complex.ofReal_pow]

omit [Nonempty I] in
theorem reflection_diagonal (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (i : I) :
    reflection V M i i=((1-2*rowWeight V M i:ℝ):ℂ) := by
  let w (j : I) : ℂ := (‖(V:Mat I) i j‖^2:ℝ)
  have hu : ∑ j, w j=1 := by
    have h := diagonal_sum V (fun _ => 1) i
    simpa only [diagonal_one,mul_one,(Unitary.mem_iff.mp V.property).2,Matrix.one_apply_eq,w] using h.symm
  have hs (j : I) : w j*markSign M j=w j-2*(if j∈M then w j else 0) := by
    by_cases hj : j∈M
    · simp only [markSign,hj,if_true,mul_neg,mul_one]
      ring
    · simp [markSign,hj]
  rw [reflection,diagonal_sum]
  change ∑ j, w j*markSign M j=_
  simp only [hs,sum_sub_distrib,hu,←mul_sum,sum_ite_mem,univ_inter,rowWeight,Complex.ofReal_sub,
    Complex.ofReal_one,Complex.ofReal_mul,Complex.ofReal_ofNat,Complex.ofReal_sum,w]

omit [Fintype I] [Nonempty I] in
private theorem sign_norm (M : Finset I) (j : I) : ‖markSign M j‖=1 := by
  by_cases hj : j∈M <;> simp [markSign,hj]

theorem marked_minority_floor (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (hm : M.Nonempty)
    (half : ∀ i, rowWeight V M i≤1/2) (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    Real.sqrt 2 ≤ ‖diagonal f-reflection V M‖ := by
  obtain ⟨j,hj⟩ := hm
  apply minority_floor V _ (sign_norm M) j (if_pos hj) _ f hf
  exact fun i => ⟨_,by linarith only [half i],reflection_diagonal V M i⟩

/-- A fit by spectral phases forces every marked weight to lie near an endpoint. -/
theorem weight_dichotomy (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (f : I → ℂ)
    (hf : ∀ i, ‖f i‖=1) (i : I) :
    let e := ‖diagonal f-reflection V M‖
    rowWeight V M i ≤ e^2/4 ∨ 1-e^2/4 ≤ rowWeight V M i := by
  intro e
  have hu : reflection V M ∈ unitary (Mat I) :=
    mul_mem (mul_mem V.property (mem_unitaryGroup_diagonal_general _ (sign_norm M)))
      (Unitary.star_mem V.property)
  have hb := diagonal_overlap f hf (reflection V M) hu i
  have h := Complex.re_le_norm (f i*conj (reflection V M i i))
  rw [norm_mul,hf,one_mul,Complex.norm_conj,reflection_diagonal,Complex.norm_real,Real.norm_eq_abs] at h
  change 2-2*_ ≤ e^2 at hb
  rw [reflection_diagonal V M i] at hb
  by_cases hs : 0 ≤ 1-2*rowWeight V M i
  · rw [abs_of_nonneg hs] at h
    exact Or.inl (by linarith only [h,hb])
  · rw [abs_of_neg (lt_of_not_ge hs)] at h
    exact Or.inr (by linarith only [h,hb])

/-- Below distance √2 at least one energy level has marked weight at
least 1 − e²/4. For a marked ray this is squared eigenstate fidelity. -/
theorem marked_witness (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (hm : M.Nonempty)
    (f : I → ℂ) (hf : ∀ i, ‖f i‖=1) :
    let e := ‖diagonal f-reflection V M‖
    Real.sqrt 2 ≤ e ∨ ∃ i, 1-e^2/4 ≤ rowWeight V M i := by
  intro e
  by_cases he : Real.sqrt 2 ≤ e
  · exact Or.inl he
  right
  obtain ⟨i,hi⟩ : ∃ i, 1/2 < rowWeight V M i := by
    by_contra! h
    exact he (marked_minority_floor V M hm h f hf)
  have hn : 0 ≤ e := norm_nonneg _
  have hs : e^2 < 2 := by
    nlinarith only [mul_pos (sub_pos.mpr (lt_of_not_ge he))
      (add_pos_of_pos_of_nonneg (Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2)) hn),
      Real.sq_sqrt (by norm_num : (0:ℝ)≤2)]
  exact ⟨i,(weight_dichotomy V M f hf i).resolve_left (by change ¬_ ≤ e^2/4; linarith only [hi,hs])⟩

/-- The scalar quarter turn lies within √2 of every marked reflection. -/
theorem imaginary_distance_le (V : Matrix.unitaryGroup I ℂ) (M : Finset I) :
    ‖diagonal (fun _ : I => Complex.I)-reflection V M‖ ≤ Real.sqrt 2 := by
  have hz : diagonal (fun _ : I => Complex.I)=(V:Mat I)*diagonal (fun _ => Complex.I)*star (V:Mat I) := by
    simp only [←smul_one_eq_diagonal_const,Matrix.mul_smul,mul_one,Matrix.smul_mul,(Unitary.mem_iff.mp V.property).2]
  change ‖diagonal (fun _ : I => Complex.I)-(V:Mat I)*diagonal (markSign M)*star (V:Mat I)‖ ≤ _
  conv_lhs => rw [hz]
  rw [←Matrix.sub_mul,←Matrix.mul_sub,l2_opNorm_unitary_conj_eq V.property,Matrix.diagonal_sub,
    Matrix.l2_opNorm_diagonal]
  apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
  intro i
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Complex.sq_norm]
  by_cases hi : i∈M <;> norm_num [markSign,hi,Complex.normSq_apply,Complex.sub_re,Complex.sub_im]

/-- The imaginary scalar realizes the exact distance, at time zero,
whenever every level gives the nonempty marked space at most half its mass. -/
theorem exact_minor_distance (V : Matrix.unitaryGroup I ℂ) (M : Finset I) (hm : M.Nonempty)
    (half : ∀ i, rowWeight V M i≤1/2) :
    IsLeast {r : ℝ | ∃ f : I → ℂ, (∀ i, ‖f i‖=1) ∧ r=‖diagonal f-reflection V M‖} (Real.sqrt 2) := by
  refine ⟨⟨fun _ => Complex.I,fun _ => Complex.norm_I,?_⟩,?_⟩
  · exact le_antisymm (marked_minority_floor V M hm half _ fun _ => Complex.norm_I)
      (imaginary_distance_le V M)
  · rintro r ⟨f,hf,rfl⟩
    exact marked_minority_floor V M hm half f hf

#print axioms marked_witness
#print axioms exact_minor_distance
end
end GaloisForLFunctions.HTGeometry.SpectralApproximation.MarkedReflections
