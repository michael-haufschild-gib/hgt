import GaloisForLFunctions.HTGeometry.DifferentialPrincipalIdeal
import GaloisForLFunctions.HTGeometry.LocalizationDerivationMap
import GaloisForLFunctions.HTGeometry.ParameterizedPicardVessiotSystem

/-!
# Parameterized Picard--Vessiot quotients with normalized Casoratian

When the companion determinant has square one, the differential orbit of
`det(Y)^2 - 1` generates a proper `σ`-`δ` ideal in the universal PPV coordinate ring.  Properness
comes from identity-jet evaluation.  Extending that ideal to a maximal proper `σ`-`δ` ideal
produces a PPV quotient whose fundamental determinant has square one, without any no-new-constants
hypothesis.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open GaloisForLFunctions
open scoped Differential

variable {K : Type*} [Field K] [Differential K] {n : ℕ}

/-- Identity matrix, regarded as a point of the matrix-coordinate differential scheme. -/
def ppvIdentityPoint (n : ℕ) : Fin n × Fin n → K :=
  fun q => (1 : Matrix (Fin n) (Fin n) K) q.1 q.2

/-- Evaluate every fundamental entry at the identity matrix and all its positive jets at zero. -/
def ppvIdentityPolynomialEval (K : Type*) [Field K] [Differential K] (n : ℕ) :
    DifferentialPolynomial (Fin n × Fin n) K →ₐ[K] K :=
  differentialPolynomialEvalOver (ppvIdentityPoint (K := K) n)

theorem ppvIdentityPolynomialEval_jetFundamentalMatrix (n : ℕ) :
    (jetFundamentalMatrix K n).map (ppvIdentityPolynomialEval K n).toRingHom = 1 := by
  ext i j
  simp [jetFundamentalMatrix, ppvIdentityPolynomialEval, ppvIdentityPoint]

theorem ppvIdentityPolynomialEval_jetFundamentalDet (n : ℕ) :
    ppvIdentityPolynomialEval K n ((jetFundamentalMatrix K n).det) = 1 := by
  change (ppvIdentityPolynomialEval K n).toRingHom ((jetFundamentalMatrix K n).det) = 1
  rw [RingHom.map_det (ppvIdentityPolynomialEval K n).toRingHom (jetFundamentalMatrix K n),
    RingHom.mapMatrix_apply, ppvIdentityPolynomialEval_jetFundamentalMatrix, Matrix.det_one]

/-- Identity-jet evaluation extends through determinant localization. -/
def ppvIdentityEval (K : Type*) [Field K] [Differential K] (n : ℕ) :
    ppvLocalization K n →+* K :=
  IsLocalization.Away.lift ((jetFundamentalMatrix K n).det)
    (g := (ppvIdentityPolynomialEval K n).toRingHom)
    (by
      have h := ppvIdentityPolynomialEval_jetFundamentalDet (K := K) n
      change (ppvIdentityPolynomialEval K n).toRingHom
        ((jetFundamentalMatrix K n).det) = 1 at h
      rw [h]
      exact isUnit_one)

@[simp] theorem ppvIdentityEval_algebraMap
    (P : DifferentialPolynomial (Fin n × Fin n) K) :
    ppvIdentityEval K n (algebraMap _ (ppvLocalization K n) P) =
      ppvIdentityPolynomialEval K n P := by
  exact IsLocalization.Away.lift_eq _ _ _

theorem ppvIdentityEval_ppvFundamental :
    (ppvFundamental K n).map (ppvIdentityEval K n) = 1 := by
  ext i j
  change ppvIdentityEval K n
      (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (jetFundamentalMatrix K n i j)) = (1 : Matrix (Fin n) (Fin n) K) i j
  rw [ppvIdentityEval_algebraMap]
  exact congrFun (congrFun (ppvIdentityPolynomialEval_jetFundamentalMatrix (K := K) n) i) j

theorem ppvIdentityEval_det_ppvFundamental :
    ppvIdentityEval K n (ppvFundamental K n).det = 1 := by
  rw [RingHom.map_det (ppvIdentityEval K n) (ppvFundamental K n),
    RingHom.mapMatrix_apply, ppvIdentityEval_ppvFundamental, Matrix.det_one]

theorem ppvIdentityEval_commutesDeriv (x : ppvLocalization K n) :
    ppvIdentityEval K n (Differential.deriv x) =
      Differential.deriv (ppvIdentityEval K n x) := by
  apply localization_ringHom_derivation_commutes_of_base
    (Submonoid.powers ((jetFundamentalMatrix K n).det))
    (ppvLocalizationDerivation K n) Differential.deriv (ppvIdentityEval K n) _ x
  intro P
  rw [ppvLocalizationDerivation_algebraMap, ppvIdentityEval_algebraMap,
    ppvIdentityEval_algebraMap]
  exact differentialPolynomialEvalOver_derivation (ppvIdentityPoint (K := K) n) P

/-- Relation normalizing the square of the generic Casoratian. -/
def ppvFundamentalDetSqRelation (K : Type*) [Field K] [Differential K] (n : ℕ) :
    ppvLocalization K n :=
  (ppvFundamental K n).det ^ 2 - 1

theorem ppvIdentityEval_fundamentalDetSqRelation :
    ppvIdentityEval K n (ppvFundamentalDetSqRelation K n) = 0 := by
  simp [ppvFundamentalDetSqRelation, ppvIdentityEval_det_ppvFundamental]

theorem ppvFundamentalDetSqRelation_ideal_ne_top :
    derivationIterateIdeal (ppvFundamentalDetSqRelation K n) ≠ ⊤ :=
  derivationIterateIdeal_ne_top_of_ringHom (ppvIdentityEval K n)
    ppvIdentityEval_commutesDeriv ppvIdentityEval_fundamentalDetSqRelation

theorem ppvSigma_det_ppvFundamental
    (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    ppvSigma σ hσ A A' hAA' hA'A (ppvFundamental K n).det =
      ppvBaseMap K n A.det * (ppvFundamental K n).det := by
  change (ppvSigma σ hσ A A' hAA' hA'A).toRingHom
    (ppvFundamental K n).det = _
  rw [RingHom.map_det (ppvSigma σ hσ A A' hAA' hA'A).toRingHom (ppvFundamental K n),
    RingHom.mapMatrix_apply]
  have hfund : (ppvFundamental K n).map (ppvSigma σ hσ A A' hAA' hA'A).toRingHom =
      A.map (ppvBaseMap K n) * ppvFundamental K n := by
    ext i j
    exact ppvSigma_ppvFundamental σ hσ A A' hAA' hA'A i j
  rw [hfund, Matrix.det_mul, RingHom.map_det (ppvBaseMap K n) A, RingHom.mapMatrix_apply]

theorem ppvSigma_fundamentalDetSqRelation_fixed_of_det_sq
    (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hdet : A.det ^ 2 = 1) :
    ppvSigma σ hσ A A' hAA' hA'A (ppvFundamentalDetSqRelation K n) =
      ppvFundamentalDetSqRelation K n := by
  rw [ppvFundamentalDetSqRelation, map_sub, map_pow, map_one,
    ppvSigma_det_ppvFundamental, mul_pow, ← map_pow, hdet, map_one, one_mul]

/-- The Casoratian-square relation generates a proper doubly stable ideal whenever the companion
determinant has square one. -/
theorem ppvFundamentalDetSqRelation_isSigmaDeltaIdeal
    (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hdet : A.det ^ 2 = 1) :
    IsSigmaDeltaIdeal (ppvSigma σ hσ A A' hAA' hA'A)
      (derivationIterateIdeal (ppvFundamentalDetSqRelation K n)) :=
  isSigmaDeltaIdeal_derivationIterateIdeal_of_fixed
    (ppvSigma_commutes σ hσ A A' hAA' hA'A)
    (ppvSigma_fundamentalDetSqRelation_fixed_of_det_sq σ hσ A A' hAA' hA'A hdet)

/-- A parameterized PV quotient can be chosen with normalized Casoratian square. -/
theorem exists_parameterizedPicardVessiot_system_fundamentalDetSqOne
    (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hdet : A.det ^ 2 = 1) :
    ∃ (M : Ideal (ppvLocalization K n))
      (hM : IsSigmaDeltaIdeal (ppvSigma σ hσ A A' hAA' hA'A) M) (_ : M ≠ ⊤)
      (hM' : IsSigmaIdeal (ppvSigma σ hσ A A' hAA' hA'A).symm M),
      @IsSigmaDeltaSimple ((ppvLocalization K n) ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv (ppvSigma σ hσ A A' hAA' hA'A) M hM.1 hM') ∧
      @CommutesDeriv ((ppvLocalization K n) ⧸ M) _ (quotientDifferential M hM.2)
        (sigmaQuotientEquiv (ppvSigma σ hσ A A' hAA' hA'A) M hM.1 hM') ∧
      (∀ i j, sigmaQuotientEquiv (ppvSigma σ hσ A A' hAA' hA'A) M hM.1 hM'
          (Ideal.Quotient.mk M (ppvFundamental K n i j)) =
        ((((A.map (ppvBaseMap K n)).map (Ideal.Quotient.mk M)) *
          ((ppvFundamental K n).map (Ideal.Quotient.mk M))) i j)) ∧
      IsUnit ((ppvFundamental K n).map (Ideal.Quotient.mk M)).det ∧
      ((ppvFundamental K n).map (Ideal.Quotient.mk M)).det ^ 2 = 1 := by
  let I := derivationIterateIdeal (ppvFundamentalDetSqRelation K n)
  have hI := ppvFundamentalDetSqRelation_isSigmaDeltaIdeal σ hσ A A' hAA' hA'A hdet
  have hIne : I ≠ ⊤ := ppvFundamentalDetSqRelation_ideal_ne_top
  obtain ⟨M, hM, hMne, hM', hIM, hsimple, hcomm⟩ :=
    exists_sigmaDeltaSimple_quotient (ppvSigma σ hσ A A' hAA' hA'A)
      (ppvSigma_commutes σ hσ A A' hAA' hA'A) I hI hIne
  refine ⟨M, hM, hMne, hM', hsimple, hcomm, ?_, ?_, ?_⟩
  · intro i j
    rw [sigmaQuotientEquiv_mk, ppvSigma_ppvFundamental]
    simp [Matrix.mul_apply]
  · have hu := isUnit_det_ppvFundamental.map (Ideal.Quotient.mk M)
    rw [RingHom.map_det (Ideal.Quotient.mk M) (ppvFundamental K n),
      RingHom.mapMatrix_apply] at hu
    exact hu
  · have hrel : ppvFundamentalDetSqRelation K n ∈ M :=
      hIM (iterate_deriv_mem_derivationIterateIdeal _ 0)
    have hzero := Ideal.Quotient.eq_zero_iff_mem.mpr hrel
    rw [ppvFundamentalDetSqRelation, map_sub, map_pow, map_one] at hzero
    rw [RingHom.map_det (Ideal.Quotient.mk M) (ppvFundamental K n),
      RingHom.mapMatrix_apply] at hzero
    exact sub_eq_zero.mp hzero

end

end GaloisForLFunctions.HTGeometry
