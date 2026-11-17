import GaloisForLFunctions.HTGeometry.HermitianInertia

/-!
# Complex inertia from real test families

Real and imaginary coordinate forms split the complex quadratic form. Real definite families therefore bound complex inertia.
-/

open Matrix
open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.HilbertMetric
open HTGeometry
variable {ι : Type*} [Fintype ι]

/-- A real matrix's complex quadratic form splits into its real and imaginary coordinate forms. -/
theorem hermQuad_real_matrix_split (A : Matrix ι ι ℝ) (z : ι → ℂ) :
    hermQuad (A.map Complex.ofReal) z =
      hermQuad (A.map Complex.ofReal) (fun i => ((z i).re : ℂ)) +
      hermQuad (A.map Complex.ofReal) (fun i => ((z i).im : ℂ)) := by
  simp only [hermQuad, dotProduct, Matrix.mulVec, Matrix.map_apply, Pi.star_apply,
    Complex.star_def, Finset.mul_sum, Complex.re_sum, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, zero_mul, add_zero, sub_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Complex synthesis of a real vector family. -/
def complexRealFamilySynthesis {n : ℕ} (v : Fin n → ι → ℝ) :
    (Fin n → ℂ) →ₗ[ℂ] (ι → ℂ) where
  toFun c := ∑ i, c i • (fun j => (v i j : ℂ))
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul,
    mul_smul, Finset.smul_sum]

omit [Fintype ι] in
private theorem complexRealFamilySynthesis_re {n : ℕ} (v : Fin n → ι → ℝ)
    (c : Fin n → ℂ) :
    (fun j => ((complexRealFamilySynthesis v c j).re : ℂ)) =
      complexRealFamilySynthesis v (fun i => ((c i).re : ℂ)) := by
  funext j
  simp [complexRealFamilySynthesis, Complex.mul_re]

omit [Fintype ι] in
private theorem complexRealFamilySynthesis_im {n : ℕ} (v : Fin n → ι → ℝ)
    (c : Fin n → ℂ) :
    (fun j => ((complexRealFamilySynthesis v c j).im : ℂ)) =
      complexRealFamilySynthesis v (fun i => ((c i).im : ℂ)) := by
  funext j
  simp [complexRealFamilySynthesis, Complex.mul_im]

/-- A real strictly negative family remains strictly negative for all nonzero complex coefficients. -/
theorem complex_negative_family_of_real (A : Matrix ι ι ℝ) {n : ℕ} (v : Fin n → ι → ℝ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      hermQuad (A.map Complex.ofReal) (complexRealFamilySynthesis v (fun i => (c i : ℂ))) < 0) :
    ∀ c : Fin n → ℂ, c ≠ 0 →
      hermQuad (A.map Complex.ofReal) (complexRealFamilySynthesis v c) < 0 := by
  intro c hc
  have hnonpos (d : Fin n → ℝ) :
      hermQuad (A.map Complex.ofReal) (complexRealFamilySynthesis v (fun i => (d i : ℂ))) ≤ 0 := by
    by_cases hd : d = 0
    · subst d
      simp [complexRealFamilySynthesis, hermQuad]
    · exact (hv d hd).le
  have hne : (fun i => (c i).re) ≠ 0 ∨ (fun i => (c i).im) ≠ 0 := by
    by_contra h
    push Not at h
    apply hc
    funext i
    exact Complex.ext (congrFun h.1 i) (congrFun h.2 i)
  rw [hermQuad_real_matrix_split, complexRealFamilySynthesis_re, complexRealFamilySynthesis_im]
  rcases hne with h | h
  · exact add_neg_of_neg_of_nonpos (hv _ h) (hnonpos _)
  · exact add_neg_of_nonpos_of_neg (hnonpos _) (hv _ h)

/-- Real strictly negative test families give a lower bound on the complex negative inertia. -/
theorem le_hermNegIndex_of_real_family (A : Matrix ι ι ℝ) {n : ℕ} (v : Fin n → ι → ℝ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      hermQuad (A.map Complex.ofReal) (complexRealFamilySynthesis v (fun i => (c i : ℂ))) < 0) :
    n ≤ hermNegIndex (A.map Complex.ofReal) := by
  let T := complexRealFamilySynthesis v
  have hneg := complex_negative_family_of_real A v hv
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro c hc
    by_contra hc0
    have h := hneg c hc0
    have hz : T c = 0 := hc
    change hermQuad (A.map Complex.ofReal) (T c) < 0 at h
    rw [hz] at h
    simp [hermQuad] at h
  have hpos : IsPosDefOn (-(A.map Complex.ofReal)) (LinearMap.range T) := by
    rintro _ ⟨c, rfl⟩ hc
    rw [hermQuad_neg]
    exact neg_pos.mpr (hneg c (fun hc0 => hc (by rw [hc0, map_zero])))
  have hrank : Module.finrank ℂ (LinearMap.range T) = n := by
    rw [← Submodule.map_top, ((Submodule.equivMapOfInjective T hinj ⊤).symm).finrank_eq]
    simp
  rw [← hrank, hermNegIndex]
  exact finrank_le_posIndex hpos

/-- Real strictly positive test families give the same lower bound on complex positive inertia. -/
theorem le_hermPosIndex_of_real_family (A : Matrix ι ι ℝ) {n : ℕ} (v : Fin n → ι → ℝ)
    (hv : ∀ c : Fin n → ℝ, c ≠ 0 →
      0 < hermQuad (A.map Complex.ofReal) (complexRealFamilySynthesis v (fun i => (c i : ℂ)))) :
    n ≤ hermPosIndex (A.map Complex.ofReal) := by
  have hmap : (-A).map Complex.ofReal = -(A.map Complex.ofReal) := by
    ext i j
    simp
  have h := le_hermNegIndex_of_real_family (-A) v (by
    intro c hc
    rw [hmap, hermQuad_neg]
    exact neg_neg_of_pos (hv c hc))
  simpa only [hmap, hermNegIndex, neg_neg] using h

#print axioms complex_negative_family_of_real
#print axioms le_hermNegIndex_of_real_family
#print axioms le_hermPosIndex_of_real_family
end GaloisForLFunctions.HilbertMetric
