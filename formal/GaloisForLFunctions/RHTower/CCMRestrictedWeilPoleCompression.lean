import GaloisForLFunctions.RHTower.CCMRestrictedWeilFullPoleMatrix

/-!
# Exact parity diagonalization of the literal Weil pole matrix

Reflection and the complete sesquilinear form give the full two-dimensional
compression for arbitrary complex coefficients. Its positivity is equivalent
to `|C| ≤ A`, or positivity of both literal parity poles. The normalized
constrained ground's source-gap comparison now retains these exact entries.
No all-aperture sign or RH equivalence for this fixed family is asserted.
-/

open Complex
open scoped InnerProduct
noncomputable section
namespace RHTower

/-- Reflection exchanges the two literal real-exponential form vectors. -/
theorem ccmArchimedeanFormReflection_polar (a : SuzukiPositiveAperture) (s : ℝ) :
    ccmArchimedeanFormReflection a (ccmPolarFormVector a s) = ccmPolarFormVector a (-s) := by
  apply ccmArchimedeanFormToAperture_injective a
  apply Subtype.ext
  rw [ccmArchimedeanFormToAperture_reflection, ccmArchimedeanFormToAperture_polar,
    ccmArchimedeanFormToAperture_polar]
  exact l2Reflection_ccmPolarL2Vector a s

private theorem pole_matrix_reflection (a : SuzukiPositiveAperture) :
    ccmRestrictedWeilForm a (ccmPolarFormVector a (-1/2)) (ccmPolarFormVector a (-1/2)) =
      ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (1/2)) ∧
    ccmRestrictedWeilForm a (ccmPolarFormVector a (-1/2)) (ccmPolarFormVector a (1/2)) =
      ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (-1/2)) := by
  constructor
  · simpa only [ccmArchimedeanFormReflection_polar, neg_div] using
      ccmRestrictedWeilForm_reflection a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (1/2))
  · simpa only [ccmArchimedeanFormReflection_polar, neg_div, neg_neg] using
      ccmRestrictedWeilForm_reflection a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (-1/2))

private theorem form_combination (a : SuzukiPositiveAperture)
    (u v : CCMArchimedeanFormDomain a) (c d : ℂ) :
    ccmRestrictedWeilForm a (c • u+d • v) (c • u+d • v) =
      (starRingEnd ℂ) c*c*ccmRestrictedWeilForm a u u +
      (starRingEnd ℂ) c*d*ccmRestrictedWeilForm a u v +
      (starRingEnd ℂ) d*c*ccmRestrictedWeilForm a v u +
      (starRingEnd ℂ) d*d*ccmRestrictedWeilForm a v v := by
  simp only [ccmRestrictedWeilForm_eq_inner_sub_zeroBirmanSchwingerInner,
    map_add, map_smul, inner_add_left, inner_add_right,
    inner_smul_left (E:=CCMArchimedeanFormDomain a), inner_smul_right (E:=CCMArchimedeanFormDomain a)]
  ring

/-- The complete actual Weil form on the two-pole plane is the real symmetric
matrix with entries given by the exact prime–Gamma formulas. -/
theorem ccmWeilPoleCompression_quadratic (a : SuzukiPositiveAperture) (c d : ℂ) :
    ccmRestrictedWeilSourceQuadratic a
      (c • ccmPolarFormVector a (1/2)+d • ccmPolarFormVector a (-1/2)) =
      ccmWeilPoleDiagonal a*(‖c‖^2+‖d‖^2)+
        2*ccmWeilPoleCross a*((starRingEnd ℂ) c*d).re := by
  rw [← ccmRestrictedWeilForm_self_re_eq_source, form_combination,
    (pole_matrix_reflection a).1, (pole_matrix_reflection a).2]
  have hc : ccmRestrictedWeilForm a (ccmPolarFormVector a (1/2)) (ccmPolarFormVector a (-1/2)) =
      (ccmWeilPoleCross a:ℂ) := by
    rw [ccmRestrictedWeilForm_pole_cross_eq,ccmWeilPoleCross_eq]
  rw [hc]
  simp only [Complex.add_re, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.sq_norm, Complex.normSq_apply,
    ccmRestrictedWeilForm_self_re_eq_source, ccmWeilPoleDiagonal]
  ring

/-- Exact even/odd diagonalization, valid for arbitrary complex coefficients. -/
theorem ccmWeilPoleCompression_parity_decomposition (a : SuzukiPositiveAperture) (c d : ℂ) :
    ccmRestrictedWeilSourceQuadratic a
      (c • ccmPolarFormVector a (1/2)+d • ccmPolarFormVector a (-1/2)) =
      (ccmWeilPoleDiagonal a+ccmWeilPoleCross a)/2*‖c+d‖^2+
      (ccmWeilPoleDiagonal a-ccmWeilPoleCross a)/2*‖c-d‖^2 := by
  rw [ccmWeilPoleCompression_quadratic]
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  ring

/-- Either literal parity pole has the exact full-source energy `2(A+rC)`. -/
theorem ccmWeilPoleCompression_parity_energy (a : SuzukiPositiveAperture) {r : ℝ}
    (hr : r=1 ∨ r=-1) :
    ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a r) =
      2*(ccmWeilPoleDiagonal a+r*ccmWeilPoleCross a) := by
  rw [ccmPolarParityFormVector, ← one_smul ℂ (ccmPolarFormVector a (1/2)),
    ccmWeilPoleCompression_quadratic]
  rcases hr with rfl | rfl <;> simp <;> ring

/-- Positivity of the literal pole compression is precisely one real entry comparison.
This identity supplies no all-aperture positivity premise. -/
theorem ccmWeilPoleCompression_nonneg_iff (a : SuzukiPositiveAperture) :
    (∀ c d : ℂ, 0 ≤ ccmRestrictedWeilSourceQuadratic a
      (c • ccmPolarFormVector a (1/2)+d • ccmPolarFormVector a (-1/2))) ↔
      |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a := by
  constructor
  · intro h
    have hp := h 1 1
    have hm := h 1 (-1)
    rw [ccmWeilPoleCompression_quadratic] at hp hm
    norm_num at hp hm
    exact abs_le.mpr ⟨by linarith,by linarith⟩
  · intro h c d
    rw [ccmWeilPoleCompression_parity_decomposition]
    obtain ⟨hm,hp⟩ := abs_le.mp h
    exact add_nonneg (mul_nonneg (by linarith) (sq_nonneg _))
      (mul_nonneg (by linarith) (sq_nonneg _))

/-- Pole-compression positivity is equivalent to checking just its two parity vectors. -/
theorem ccmWeilPoleCompression_nonneg_iff_parity (a : SuzukiPositiveAperture) :
    |ccmWeilPoleCross a| ≤ ccmWeilPoleDiagonal a ↔
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a 1) ∧
      0 ≤ ccmRestrictedWeilSourceQuadratic a (ccmPolarParityFormVector a (-1)) := by
  rw [ccmWeilPoleCompression_parity_energy a (Or.inl rfl),
    ccmWeilPoleCompression_parity_energy a (Or.inr rfl)]
  constructor
  · intro h
    obtain ⟨hm,hp⟩ := abs_le.mp h
    constructor <;> nlinarith
  · rintro ⟨hp,hm⟩
    exact abs_le.mpr ⟨by nlinarith,by nlinarith⟩

/-- Every aperture has a normalized constrained parity ground whose source is bounded
by the actual unrestricted gap and the explicit prime–Gamma matrix entry. -/
theorem exists_normalized_polarGround_poleMatrix_gap (a : SuzukiPositiveAperture) :
    ∃ (u : CCMArchimedeanFormDomain a) (r : ℝ),
      (r=1 ∨ r=-1) ∧ IsPolarConstrained a u ∧
      ‖ccmArchimedeanFormToAperture a u‖=1 ∧
      ccmArchimedeanFormReflection a u=(r:ℂ) • u ∧
      ccmRestrictedWeilSourceQuadratic a u=ccmRestrictedWeilPolarGroundEnergy a ∧
      4*‖ccmPolarBoundarySourceFunctional a u‖^2 ≤
        (ccmRestrictedWeilPolarGroundEnergy a-ccmRestrictedWeilGroundEnergy a)*
          (2*(ccmWeilPoleDiagonal a+r*ccmWeilPoleCross a)-
            2*ccmRestrictedWeilGroundEnergy a*(2*Real.sinh a.1+2*a.1*r)) := by
  obtain ⟨u,r,hr,hu,hn,hpar,hQ,hgap,_⟩ := exists_normalized_polarGround_source_variance_gap a
  exact ⟨u,r,hr,hu,hn,hpar,hQ,by
    simpa only [ccmWeilPoleCompression_parity_energy a hr] using hgap⟩

end RHTower
