import GaloisForLFunctions.RHTower.MaassModelHilbertGenerators
import GaloisForLFunctions.RHTower.RealPrincipalSeriesCompactUnitarity
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# The actual Maass inner product

Differentiating the original quotient unitary action proves the raising/lowering
adjoint relation and compact-generator symmetry. Distinct K-types are orthogonal;
two-sided recurrence identifies the entire pullback form with the canonical
complementary-series form times the actual spherical norm squared.
-/

open UpperHalfPlane MeasureTheory
namespace GaloisForLFunctions.RHTower.MaassModelQuotientL2
noncomputable section
variable (N : ℕ) (lam : SelbergExceptionalEigenvalue)
  (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam.1)


def modelInner : ComplexHermitianForm SphericalKFiniteModel :=
  pullbackComplexHermitianForm (innerₛₗ ℂ) (modelToLp N lam f)

@[simp] theorem modelInner_apply (v w : SphericalKFiniteModel) :
    modelInner N lam f v w = inner ℂ (modelToLp N lam f v) (modelToLp N lam f w) := rfl

theorem modelInner_positiveDefinite : IsPositiveDefiniteHermitian (modelInner N lam f) := by
  constructor
  · exact ⟨fun v w => @inner_conj_symm ℂ _ _ _ _ (modelToLp N lam f w) (modelToLp N lam f v)⟩
  · intro v hv
    rw [modelInner_apply]
    apply (re_inner_self_pos (𝕜 := ℂ)).2
    intro h
    apply hv
    apply modelToLp_injective N lam f
    simpa only [map_zero] using h

private theorem unitary_inner_derivative (p : ℝ → SL2R) (hp : p 0 = 1)
    (v w v' w' : Lp ℂ 2 (integralSubgroupQuotientMeasure
      (CongruenceSubgroup.Gamma (N+1))))
    (hv : HasDerivAt (fun t => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N+1)) (p t) v) v' 0)
    (hw : HasDerivAt (fun t => integralSubgroupUnitary
      (CongruenceSubgroup.Gamma (N+1)) (p t) w) w' 0) :
    inner ℂ v w' + inner ℂ v' w = 0 := by
  have h := hv.inner ℂ hw
  simp only [hp, integralSubgroupUnitary_one, integralSubgroupUnitary_inner] at h
  exact h.unique (hasDerivAt_const 0 (inner ℂ v w))

theorem modelInner_H_symmetric (v w : SphericalKFiniteModel) :
    modelInner N lam f (sphericalPrincipalH v) w =
      modelInner N lam f v (sphericalPrincipalH w) := by
  have h := unitary_inner_derivative N
    (fun t => (realSphericalRotation t : SL2R))
    (by simp only [realSphericalRotation_zero, OneMemClass.coe_one]) _ _ _ _
    (modelToLp_rotation_hasDerivAt N lam f v) (modelToLp_rotation_hasDerivAt N lam f w)
  simp only [LinearMap.smul_apply, map_smul, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h
  simp only [modelInner_apply]
  have hmul : Complex.I * (inner ℂ (modelToLp N lam f (sphericalPrincipalH v))
      (modelToLp N lam f w) - inner ℂ (modelToLp N lam f v)
      (modelToLp N lam f (sphericalPrincipalH w))) = 0 := by linear_combination -h
  exact sub_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left Complex.I_ne_zero)

theorem modelInner_invariant : IsSphericalPrincipalInvariant
    (2*lam.complementaryExponent) (modelInner N lam f) := by
  intro v w
  have hA := unitary_inner_derivative N
    (fun t => (realPositiveDiagonalBorel (-t) : SL2R))
    (by simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one]) _ _ _ _
    (modelToLp_diagonal_hasDerivAt N lam f v) (modelToLp_diagonal_hasDerivAt N lam f w)
  have hB := unitary_inner_derivative N
    (fun t => (realSphericalRotation (Real.pi/4) : SL2R) *
      (realPositiveDiagonalBorel (-t) : SL2R) * (realSphericalRotation (Real.pi/4) : SL2R)⁻¹)
    (by simp only [neg_zero, realPositiveDiagonalBorel_zero, OneMemClass.coe_one,
      mul_one, mul_inv_cancel]) _ _ _ _
    (modelToLp_quarterDiagonal_hasDerivAt N lam f v)
    (modelToLp_quarterDiagonal_hasDerivAt N lam f w)
  simp only [LinearMap.add_apply, map_add, inner_add_left, inner_add_right] at hA
  simp only [LinearMap.smul_apply, LinearMap.sub_apply, map_smul, map_sub,
    inner_smul_left, inner_smul_right, inner_sub_left, inner_sub_right, Complex.conj_I] at hB
  simp only [modelInner_apply]
  have hBi := congrArg (fun z : ℂ => Complex.I * z) hB
  simp only [mul_add, mul_neg, mul_sub, ← mul_assoc, Complex.I_mul_I, neg_one_mul,
    mul_zero] at hBi
  linear_combination hA/2 + hBi/2

/-- Distinct actual Maass K-types are orthogonal in the quotient Hilbert space. -/
theorem modelInner_single_orthogonal (m n : ℤ) (hmn : m ≠ n) :
    modelInner N lam f (Finsupp.single m 1) (Finsupp.single n 1) = 0 := by
  have h := modelInner_H_symmetric N lam f (Finsupp.single m 1) (Finsupp.single n 1)
  have hH (k : ℤ) : sphericalPrincipalH (Finsupp.single k 1) =
      (2*(k : ℂ)) • Finsupp.single k 1 := by
    simp only [sphericalPrincipalH_single, Finsupp.smul_single, smul_eq_mul]
  rw [hH m, hH n] at h
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply] at h
  have hc (k : ℤ) : (starRingEnd ℂ) (2*(k : ℂ)) = 2*(k : ℂ) := by
    simp only [map_mul, map_ofNat, map_intCast]
  rw [hc m] at h
  have hne : (m : ℂ) - (n : ℂ) ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hmn)
  apply (mul_eq_zero.mp (show ((m : ℂ)-(n : ℂ)) *
    modelInner N lam f (Finsupp.single m 1) (Finsupp.single n 1) = 0 by
      linear_combination h/2)).resolve_left hne

private theorem invariant_diagonal_step (s : ℝ)
    (B : ComplexHermitianForm SphericalKFiniteModel)
    (hB : IsSphericalPrincipalInvariant s B) (m : ℤ) :
    (((s : ℂ)-1-2*(m : ℂ))/2) * B (Finsupp.single (m+1) 1) (Finsupp.single (m+1) 1) =
      -(((s : ℂ)-1+2*((m+1 : ℤ) : ℂ))/2) * B (Finsupp.single m 1) (Finsupp.single m 1) := by
  have h := hB (Finsupp.single m 1) (Finsupp.single (m+1) 1)
  have hE : sphericalPrincipalE (s : ℂ) (Finsupp.single m 1) =
      (((s : ℂ)-1-2*(m : ℂ))/2) • Finsupp.single (m+1) 1 := by
    simp only [sphericalPrincipalE_single, Finsupp.smul_single, smul_eq_mul]
  have hF : sphericalPrincipalF (s : ℂ) (Finsupp.single (m+1) 1) =
      (((s : ℂ)-1+2*((m+1 : ℤ) : ℂ))/2) • Finsupp.single m 1 := by
    simp only [sphericalPrincipalF_single, Finsupp.smul_single, smul_eq_mul,
      add_sub_cancel_right]
  have hc : (starRingEnd ℂ) (((s : ℂ)-1-2*(m : ℂ))/2) =
      (((s : ℂ)-1-2*(m : ℂ))/2) := by simp [map_ofNat]
  rw [hE, hF] at h
  simpa only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, hc, neg_mul] using h

private theorem parameter_abs_lt : |2*lam.complementaryExponent| < 1 := by
  have h := lam.complementaryExponent_mem_Ioo
  exact abs_lt.mpr ⟨by linarith [h.1], by linarith [h.2]⟩

/-- Every actual diagonal norm is the canonical complementary norm times the spherical norm. -/
theorem modelInner_single_self (m : ℤ) :
    modelInner N lam f (Finsupp.single m 1) (Finsupp.single m 1) =
      modelInner N lam f (Finsupp.single 0 1) (Finsupp.single 0 1) *
        sphericalComplementaryHermitianForm (2*lam.complementaryExponent)
          (Finsupp.single m 1) (Finsupp.single m 1) := by
  let s := 2*lam.complementaryExponent
  let B := modelInner N lam f
  let C := sphericalComplementaryHermitianForm s
  let c := B (Finsupp.single 0 1) (Finsupp.single 0 1)
  change B (Finsupp.single m 1) (Finsupp.single m 1) =
    c * C (Finsupp.single m 1) (Finsupp.single m 1)
  have hB := invariant_diagonal_step s B (modelInner_invariant N lam f)
  have hC := invariant_diagonal_step s C
    (sphericalComplementaryHermitianForm_invariant s (parameter_abs_lt lam))
  induction m using Int.induction_on with
  | zero =>
      simp [C, sphericalComplementaryHermitianForm, complementaryKTypeWeight,
        complementaryNatWeight, c]
  | succ n ih =>
      apply mul_left_cancel₀ (sphericalPrincipalE_coefficient_ne_zero s (parameter_abs_lt lam) n)
      calc
        _ = -(((s : ℂ)-1+2*(((n : ℤ)+1 : ℤ) : ℂ))/2) *
            B (Finsupp.single (n : ℤ) 1) (Finsupp.single (n : ℤ) 1) := hB n
        _ = c * (-(((s : ℂ)-1+2*(((n : ℤ)+1 : ℤ) : ℂ))/2) *
            C (Finsupp.single (n : ℤ) 1) (Finsupp.single (n : ℤ) 1)) := by rw [ih]; ring
        _ = _ := by rw [← hC n]; ring
  | pred n ih =>
      have hb := hB (-(n : ℤ)-1)
      have hc := hC (-(n : ℤ)-1)
      simp only [sub_add_cancel] at hb hc
      apply mul_left_cancel₀ (neg_ne_zero.mpr
        (sphericalPrincipalF_coefficient_ne_zero s (parameter_abs_lt lam) (-(n : ℤ))))
      calc
        _ = (((s : ℂ)-1-2*((-(n : ℤ)-1 : ℤ) : ℂ))/2) *
            B (Finsupp.single (-(n : ℤ)) 1) (Finsupp.single (-(n : ℤ)) 1) := hb.symm
        _ = c * ((((s : ℂ)-1-2*((-(n : ℤ)-1 : ℤ) : ℂ))/2) *
            C (Finsupp.single (-(n : ℤ)) 1) (Finsupp.single (-(n : ℤ)) 1)) := by rw [ih]; ring
        _ = _ := by rw [hc]; ring

/-- The actual Maass pullback form equals the canonical complementary form with its actual scale. -/
theorem modelInner_eq_sphericalForm :
    modelInner N lam f =
      modelInner N lam f (Finsupp.single 0 1) (Finsupp.single 0 1) •
        sphericalComplementaryHermitianForm (2*lam.complementaryExponent) := by
  apply (Finsupp.basisSingleOne : Module.Basis ℤ ℂ SphericalKFiniteModel).ext
  intro m
  apply (Finsupp.basisSingleOne : Module.Basis ℤ ℂ SphericalKFiniteModel).ext
  intro n
  change modelInner N lam f (Finsupp.single m 1) (Finsupp.single n 1) =
    modelInner N lam f (Finsupp.single 0 1) (Finsupp.single 0 1) *
      sphericalComplementaryHermitianForm (2*lam.complementaryExponent)
        (Finsupp.single m 1) (Finsupp.single n 1)
  by_cases h : m = n
  · subst n
    exact modelInner_single_self N lam f m
  · rw [modelInner_single_orthogonal N lam f m n h]
    simp only [sphericalComplementaryHermitianForm, diagonalKTypeHermitianForm_single, h,
      if_false, mul_zero]

/-- The positive scaling constant is the squared norm of the actual spherical Maass vector. -/
theorem modelInner_spherical_scale :
    modelInner N lam f (Finsupp.single 0 1) (Finsupp.single 0 1) =
      (‖modelToLp N lam f (Finsupp.single 0 1)‖ ^ 2 : ℝ) := by
  rw [modelInner_apply, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

/-- The complete finite-vector norm identity for the actual Maass model map. -/
theorem modelToLp_norm_sq (v : SphericalKFiniteModel) :
    ‖modelToLp N lam f v‖ ^ 2 = ‖modelToLp N lam f (Finsupp.single 0 1)‖ ^ 2 *
      (sphericalComplementaryHermitianForm (2*lam.complementaryExponent) v v).re := by
  have h := congrArg (fun B : ComplexHermitianForm SphericalKFiniteModel => (B v v).re)
    (modelInner_eq_sphericalForm N lam f)
  rw [modelInner_spherical_scale] at h
  have he := @norm_sq_eq_re_inner ℂ _ _ _ _ (modelToLp N lam f v)
  change ‖modelToLp N lam f v‖ ^ 2 = (inner ℂ (modelToLp N lam f v) (modelToLp N lam f v)).re at he
  rw [he]
  simpa only [modelInner_apply, LinearMap.smul_apply, smul_eq_mul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero] using h

end
end GaloisForLFunctions.RHTower.MaassModelQuotientL2
