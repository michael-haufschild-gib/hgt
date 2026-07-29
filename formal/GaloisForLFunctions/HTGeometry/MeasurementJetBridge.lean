import GaloisForLFunctions.HTGeometry.FiniteResolutionMeasurement
import GaloisForLFunctions.HTGeometry.PolynomialJetEvaluation

/-!
# Bridge between the coefficient measurement operator and polynomial jet evaluation

The concrete finite measurement operator `measCLM` (on the coefficient space `Fin N → ℝ`) and the
polynomial evaluation `sampleEval` (on `MvPolynomial`) are the *same* operator in two coordinate
systems: `measCLM = sampleEval ∘ lawEmbed`, where `lawEmbed` sends a coefficient vector to the
polynomial law `∑_k c_k X^{e_k}`.  This connects the finite-resolution measurement theorem
(`measCLM_eventually_injMod_pos`) to the hypertranscendence characterization
(`jetEval_injective_iff`): the measurement injectivity hypothesis is exactly HT of the underlying jet
on the law window.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

/-- Coefficient-to-law embedding: `c ↦ ∑_k c_k · X^{e_k}`, sending the measurement coefficient space
into the polynomial law window with monomial exponents `e`. -/
noncomputable def lawEmbed {n N : ℕ} (e : Fin N → (Fin n →₀ ℕ)) :
    (Fin N → ℝ) →ₗ[ℝ] MvPolynomial (Fin n) ℝ where
  toFun c := ∑ k, MvPolynomial.C (c k) * MvPolynomial.monomial (e k) 1
  map_add' c c' := by simp [Finset.sum_add_distrib, add_mul, map_add]
  map_smul' a c := by simp only [Pi.smul_apply, smul_eq_mul, Finset.smul_sum, map_mul, MvPolynomial.smul_eq_C_mul, RingHom.id_apply, mul_assoc]

/-- **Measurement/evaluation bridge.**  The concrete coefficient-space measurement operator `measCLM`
equals the polynomial evaluation `sampleEval` precomposed with the monomial embedding `lawEmbed`, when
the jet-sample values are `y j i = g i (E j)`.  This threads the finite-resolution measurement theorem
to the hypertranscendence characterization `jetEval_injective_iff`. -/
theorem measCLM_eq_sampleEval_lawEmbed {n m N : ℕ} (e : Fin N → (Fin n →₀ ℕ))
    (g : Fin n → (ℝ → ℝ)) (E : Fin m → ℝ) (c : Fin N → ℝ) :
    measCLM (fun k i => (e k) i) (fun j i => g i (E j)) c = sampleEval g E (lawEmbed e c) := by
  ext j
  simp only [measCLM, _root_.sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, Finset.sum_apply, sampleEval_apply,
    jetEval_apply, lawEmbed, LinearMap.coe_mk, AddHom.coe_mk, map_sum, map_mul, eval_C,
    eval_monomial, one_mul]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  rw [Finsupp.prod_fintype _ _ (fun i => pow_zero _)]
  simp only [Pi.smul_apply, smul_eq_mul]

end GaloisForLFunctions.HTGeometry
