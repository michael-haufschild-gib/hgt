import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicCuspNormalization

/-!
# Physical retraction dynamics on the normalization defect

The two-variable polynomial flow is exactly pullback along the physical
retraction. It preserves the cusp algebra and descends to its actual vector
quotient. Every quotient basis class u^n c has eigenvalue q^(n+1). The induced
maps form a semigroup with identity at one and zero map at zero.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set Polynomial Module


def cubicInnerPolynomialFlow (q : ℝ) : Polynomial ℝ →ₐ[ℝ] Polynomial ℝ :=
  Polynomial.aeval (Polynomial.C q*Polynomial.X)

def cubicPolynomialFlow (q : ℝ) : Polynomial (Polynomial ℝ) →ₐ[ℝ] Polynomial (Polynomial ℝ) :=
  Polynomial.aevalTower (Polynomial.CAlgHom.comp (cubicInnerPolynomialFlow q))
    (Polynomial.C (Polynomial.C q)*Polynomial.X)

theorem cubicInnerPolynomialFlow_monomial (q r : ℝ) (n : ℕ) :
    cubicInnerPolynomialFlow q (Polynomial.monomial n r)=Polynomial.monomial n (r*q^n) := by
  simp only [cubicInnerPolynomialFlow,Polynomial.aeval_monomial,Polynomial.algebraMap_eq,
    mul_pow,← map_pow]
  rw [← mul_assoc,← map_mul,Polynomial.C_mul_X_pow_eq_monomial]

theorem cubicInnerPolynomialFlow_evaluation (q x : ℝ) (p : Polynomial ℝ) :
    (cubicInnerPolynomialFlow q p).eval x=p.eval (q*x) := by
  induction p using Polynomial.induction_on' with
  | add p r hp hr => simpa only [map_add,Polynomial.eval_add] using congrArg₂ (·+·) hp hr
  | monomial n r =>
    rw [cubicInnerPolynomialFlow_monomial]
    simp only [Polynomial.eval_monomial,mul_pow]
    ring

theorem cubicPolynomialFlow_monomial (q : ℝ) (n : ℕ) (p : Polynomial ℝ) :
    cubicPolynomialFlow q (Polynomial.monomial n p)=
      Polynomial.monomial n (cubicInnerPolynomialFlow q p*Polynomial.C (q^n)) := by
  rw [← Polynomial.C_mul_X_pow_eq_monomial,map_mul,map_pow]
  simp only [cubicPolynomialFlow,Polynomial.aevalTower_C,Polynomial.aevalTower_X,
    AlgHom.comp_apply,Polynomial.CAlgHom_apply,mul_pow,← map_pow]
  rw [← mul_assoc,← map_mul,Polynomial.C_mul_X_pow_eq_monomial]

theorem cubicPolynomialFlow_coefficient (q : ℝ) (P : Polynomial (Polynomial ℝ)) (n : ℕ) :
    (cubicPolynomialFlow q P).coeff n=
      cubicInnerPolynomialFlow q (P.coeff n)*Polynomial.C (q^n) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simp only [map_add,Polynomial.coeff_add,hP,hQ,add_mul]
  | monomial k p =>
    rw [cubicPolynomialFlow_monomial]
    by_cases hk : k=n
    · subst k; simp
    · simp [Polynomial.coeff_monomial,hk]

theorem cubicPolynomialFlow_preservesCusp (q : ℝ) :
    MapsTo (cubicPolynomialFlow q) cubicCuspAlgebra cubicCuspAlgebra := by
  intro P hP
  change (cubicPolynomialFlow q P).coeff 1=0
  change P.coeff 1=0 at hP
  rw [cubicPolynomialFlow_coefficient,hP,map_zero,zero_mul]

theorem cubicPolynomialFlow_observation (q : Icc (0:ℝ) 1) (P : Polynomial (Polynomial ℝ)) :
    cubicPolynomialObservation (cubicPolynomialFlow q P)=
      cubicSectionPullback q (cubicPolynomialObservation P) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ => simpa only [map_add] using congrArg₂ (·+·) hP hQ
  | monomial n p =>
    rw [cubicPolynomialFlow_monomial]
    ext g
    change Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 g.val)) (g.val 2)
      (Polynomial.monomial n (cubicInnerPolynomialFlow q p*Polynomial.C (q.val^n)))=
      Polynomial.eval₂ (Polynomial.evalRingHom (cubicDecayMode 0 (cubicFlow q g.val)))
        ((cubicFlow q g.val) 2) (Polynomial.monomial n p)
    simp only [Polynomial.eval₂_monomial,Polynomial.coe_evalRingHom,Polynomial.eval_mul,
      Polynomial.eval_C,cubicInnerPolynomialFlow_evaluation,cubicDecayMode_spectrum]
    have hc : (cubicFlow q g.val) 2=q.val*g.val 2 := by simp [cubicFlow,cubicCollapse]
    rw [hc]
    simp only [Fin.val_zero,zero_add,pow_one,mul_pow]
    ring

def cubicCuspDefectFlow (q : ℝ) :
    (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) →ₗ[ℝ]
      (Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :=
  cubicCuspAlgebra.toSubmodule.mapQ cubicCuspAlgebra.toSubmodule
    (cubicPolynomialFlow q).toLinearMap (cubicPolynomialFlow_preservesCusp q)

theorem cubicCuspDefectFlow_mk (q : ℝ) (P : Polynomial (Polynomial ℝ)) :
    cubicCuspDefectFlow q (Submodule.Quotient.mk P)=
      Submodule.Quotient.mk (cubicPolynomialFlow q P) := rfl

theorem cubicCuspDefectFlow_spectrum (q : ℝ) (n : ℕ) :
    cubicCuspDefectFlow q (cubicCuspDefectBasis n)=q^(n+1) • cubicCuspDefectBasis n := by
  apply cubicCuspDefectEquiv.injective
  rw [cubicCuspDefectBasis_apply,cubicCuspDefectFlow_mk,cubicCuspDefectEquiv_mk,map_smul,
    cubicCuspDefectEquiv_mk,Polynomial.C_mul_X_eq_monomial,Polynomial.coeff_monomial_same,
    cubicPolynomialFlow_coefficient]
  rw [Polynomial.coeff_monomial_same]
  have hi : cubicInnerPolynomialFlow q (Polynomial.X^n)=Polynomial.C (q^n)*Polynomial.X^n := by
    rw [map_pow]
    simp only [cubicInnerPolynomialFlow,Polynomial.aeval_X,mul_pow,← map_pow]
  rw [hi,pow_one]
  rw [Polynomial.smul_eq_C_mul]
  rw [pow_succ,map_mul]
  ring

theorem cubicCuspDefectFlow_one : cubicCuspDefectFlow 1=LinearMap.id := by
  apply cubicCuspDefectBasis.ext
  intro n
  simp [cubicCuspDefectFlow_spectrum]

theorem cubicCuspDefectFlow_zero : cubicCuspDefectFlow 0=0 := by
  apply cubicCuspDefectBasis.ext
  intro n
  simp [cubicCuspDefectFlow_spectrum]

theorem cubicCuspDefectFlow_mul (q r : ℝ) :
    (cubicCuspDefectFlow q).comp (cubicCuspDefectFlow r)=cubicCuspDefectFlow (q*r) := by
  apply cubicCuspDefectBasis.ext
  intro n
  simp only [LinearMap.comp_apply,cubicCuspDefectFlow_spectrum,map_smul,← mul_smul,mul_pow,mul_comm]

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
