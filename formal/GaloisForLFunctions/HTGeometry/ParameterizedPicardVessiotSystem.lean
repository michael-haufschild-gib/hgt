import GaloisForLFunctions.HTGeometry.LocalizationDerivationExt
import GaloisForLFunctions.HTGeometry.DifferenceAwayLocalization

/-!
# Concrete parameterized Picard--Vessiot systems

The differential coordinate ring of a fundamental matrix is the polynomial ring in every formal
jet of its entries.  Inverting the determinant of its zeroth-jet matrix produces the parameterized
coordinate ring of `GLₙ`.  This file constructs its total derivation and difference automorphism,
proves that they commute, and takes a maximal `σ`-`δ` quotient.  Thus every invertible linear
difference system over a differential field has a parameterized Picard--Vessiot quotient; no
pre-existing extension ring or simplicity premise is required.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {B A S : Type*} [CommRing B] [CommRing A] [CommRing S]
  [Algebra B A] [Algebra A S] [Algebra B S] [IsScalarTower B A S]

private def derivationIntoLocalization (D : Derivation B A A) : Derivation B A S :=
  let f : A →ₗ[B] S :=
    { toFun := algebraMap A S
      map_add' := map_add _
      map_smul' := by
        intro b a
        simp only [Algebra.smul_def, map_mul]
        rw [IsScalarTower.algebraMap_apply B A S]
        simp }
  Derivation.mk' (f.comp D.toLinearMap) (by
    intro a b
    change algebraMap A S (D (a * b)) =
      a • algebraMap A S (D b) + b • algebraMap A S (D a)
    rw [Derivation.leibniz, map_add]
    simp [Algebra.smul_def])

variable {K : Type*} [Field K] {n : ℕ}

/-- Zeroth jets of the generic fundamental matrix. -/
def jetFundamentalMatrix (K : Type*) [CommRing K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (DifferentialPolynomial (Fin n × Fin n) K) :=
  fun i j => MvPolynomial.X ((i, j), 0)

/-- The generic zeroth-jet determinant is nonzero. -/
theorem jetFundamentalMatrix_det_ne_zero :
    (jetFundamentalMatrix K n).det ≠ 0 := by
  classical
  set e : ((Fin n × Fin n) × ℕ) → K := fun q =>
    if q.2 = 0 ∧ q.1.1 = q.1.2 then 1 else 0 with he
  have hmap : (jetFundamentalMatrix K n).map (MvPolynomial.eval e) =
      (1 : Matrix (Fin n) (Fin n) K) := by
    refine Matrix.ext fun i j => ?_
    simp [jetFundamentalMatrix, Matrix.map_apply, Matrix.one_apply, he]
  have heval : MvPolynomial.eval e ((jetFundamentalMatrix K n).det) = 1 := by
    rw [RingHom.map_det (MvPolynomial.eval e) (jetFundamentalMatrix K n),
      RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  intro hzero
  rw [hzero, map_zero] at heval
  exact zero_ne_one heval

/-- Differential-polynomial coordinate ring localized at the zeroth-jet determinant. -/
abbrev ppvLocalization (K : Type*) [Field K] (n : ℕ) : Type _ :=
  Localization.Away ((jetFundamentalMatrix K n).det)

theorem powers_jetFundamentalDet_le_nonZeroDivisors :
    Submonoid.powers ((jetFundamentalMatrix K n).det) ≤
      nonZeroDivisors (DifferentialPolynomial (Fin n × Fin n) K) := by
  rintro x ⟨k, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  exact pow_ne_zero k jetFundamentalMatrix_det_ne_zero

instance : Nontrivial (ppvLocalization K n) := by
  have hinj : Function.Injective
      (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)) :=
    IsLocalization.injective (M := Submonoid.powers ((jetFundamentalMatrix K n).det)) _
      powers_jetFundamentalDet_le_nonZeroDivisors
  exact ⟨⟨algebraMap _ _ 0, algebraMap _ _ 1, fun h => zero_ne_one (hinj h)⟩⟩

local instance ppvLocalizationIntAlgebra : Algebra ℤ (ppvLocalization K n) :=
  Ring.toIntAlgebra _

/-- Base-field embedding into the parameterized coordinate ring. -/
def ppvBaseMap (K : Type*) [Field K] (n : ℕ) : K →+* ppvLocalization K n :=
  (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)).comp
    (MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K)

/-- Generic invertible fundamental matrix in the localized differential coordinate ring. -/
def ppvFundamental (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (ppvLocalization K n) :=
  (jetFundamentalMatrix K n).map
    (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n))

theorem isUnit_algebraMap_jetFundamentalDet :
    IsUnit (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
      ((jetFundamentalMatrix K n).det)) :=
  IsLocalization.map_units
    (M := Submonoid.powers ((jetFundamentalMatrix K n).det)) _
    ⟨_, Submonoid.mem_powers _⟩

theorem isUnit_det_ppvFundamental : IsUnit ((ppvFundamental K n).det) := by
  have h : (ppvFundamental K n).det =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        ((jetFundamentalMatrix K n).det) := by
    rw [ppvFundamental, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h]
  exact isUnit_algebraMap_jetFundamentalDet

variable [Differential K]

/-- Quotient-rule extension of the total jet derivation. -/
def ppvLocalizationDerivation (K : Type*) [Field K] [Differential K] (n : ℕ) :
    Derivation ℤ (ppvLocalization K n) (ppvLocalization K n) :=
  localizationDerivation (K := ℤ)
    (A := DifferentialPolynomial (Fin n × Fin n) K) (S := ppvLocalization K n)
    (Submonoid.powers ((jetFundamentalMatrix K n).det))
    (derivationIntoLocalization (jetCoordDeriv K n))

instance : Differential (ppvLocalization K n) where
  deriv := ppvLocalizationDerivation K n

@[simp] theorem ppvLocalizationDerivation_algebraMap
    (f : DifferentialPolynomial (Fin n × Fin n) K) :
    ppvLocalizationDerivation K n
        (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n) f) =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (jetCoordDeriv K n f) := by
  rw [ppvLocalizationDerivation, localizationDerivation_algebraMap]
  rfl

@[simp] theorem ppvLocalization_deriv_algebraMap
    (f : DifferentialPolynomial (Fin n × Fin n) K) :
    Differential.deriv
        (algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n) f) =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K) (ppvLocalization K n)
        (jetCoordDeriv K n f) :=
  ppvLocalizationDerivation_algebraMap f

/-- The difference action sends the generic zeroth-jet matrix to `A` times that matrix. -/
theorem sigmaJetCoordHom_jetFundamentalMatrix (σ : K ≃+* K)
    (A : Matrix (Fin n) (Fin n) K) (i j : Fin n) :
    sigmaJetCoordHom σ A (jetFundamentalMatrix K n i j) =
      ((A.map (MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K)) *
        jetFundamentalMatrix K n) i j := by
  simp [jetFundamentalMatrix, systemRow, Matrix.mul_apply, Matrix.map_apply]

/-- The zeroth-jet determinant is a semi-invariant of the difference action. -/
theorem sigmaJetCoordHom_jetFundamentalDet (σ : K ≃+* K)
    (A : Matrix (Fin n) (Fin n) K) :
    sigmaJetCoordHom σ A ((jetFundamentalMatrix K n).det) =
      MvPolynomial.C A.det * (jetFundamentalMatrix K n).det := by
  have hmap : (jetFundamentalMatrix K n).map (sigmaJetCoordHom σ A) =
      (A.map (MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K)) *
        jetFundamentalMatrix K n :=
    Matrix.ext fun i j => sigmaJetCoordHom_jetFundamentalMatrix σ A i j
  calc
    sigmaJetCoordHom σ A ((jetFundamentalMatrix K n).det) =
        ((jetFundamentalMatrix K n).map (sigmaJetCoordHom σ A)).det :=
      RingHom.map_det _ _
    _ = ((A.map (MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K)) *
        jetFundamentalMatrix K n).det := by rw [hmap]
    _ = MvPolynomial.C A.det * (jetFundamentalMatrix K n).det := by
      rw [Matrix.det_mul]
      congr 1
      rw [RingHom.map_det
        (MvPolynomial.C : K →+* DifferentialPolynomial (Fin n × Fin n) K) A,
        RingHom.mapMatrix_apply]

/-- Difference automorphism on the determinant-localized differential coordinate ring. -/
def ppvSigma (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    ppvLocalization K n ≃+* ppvLocalization K n :=
  sigmaAwayEquiv (S := ppvLocalization K n)
    (sigmaJetCoordEquiv σ hσ A A' hAA' hA'A) ((jetFundamentalMatrix K n).det)
    (by
      have hdet : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hAA'
      rw [sigmaJetCoordEquiv_apply, sigmaJetCoordHom_jetFundamentalDet, map_mul]
      exact ((hdet.map MvPolynomial.C).map _).mul isUnit_algebraMap_jetFundamentalDet)
    (by
      have hdet' : IsUnit (A'.map (σ.symm : K →+* K)).det := by
        have h1 : (A'.map (σ.symm : K →+* K)).det = (σ.symm : K →+* K) A'.det := by
          rw [RingHom.map_det (σ.symm : K →+* K) A', RingHom.mapMatrix_apply]
        rw [h1]
        exact (Matrix.isUnit_det_of_right_inverse hA'A).map (σ.symm : K →+* K)
      change IsUnit (algebraMap _ _
        (sigmaJetCoordHom σ.symm (A'.map (σ.symm : K →+* K))
          ((jetFundamentalMatrix K n).det)))
      rw [sigmaJetCoordHom_jetFundamentalDet, map_mul]
      exact ((hdet'.map MvPolynomial.C).map _).mul isUnit_algebraMap_jetFundamentalDet)

@[simp] theorem ppvSigma_algebraMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (f : DifferentialPolynomial (Fin n × Fin n) K) :
    ppvSigma σ hσ A A' hAA' hA'A (algebraMap _ _ f) =
      algebraMap _ _ (sigmaJetCoordEquiv σ hσ A A' hAA' hA'A f) := by
  exact sigmaAwayEquiv_algebraMap _ _ _ _ _

/-- The parameterized difference action restricts to the given action on the base field. -/
theorem ppvSigma_ppvBaseMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (x : K) :
    ppvSigma σ hσ A A' hAA' hA'A (ppvBaseMap K n x) = ppvBaseMap K n (σ x) := by
  rw [show ppvBaseMap K n x =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K)
        (ppvLocalization K n) (MvPolynomial.C x) from rfl,
    show ppvBaseMap K n (σ x) =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K)
        (ppvLocalization K n) (MvPolynomial.C (σ x)) from rfl]
  simpa only [sigmaJetCoordEquiv_apply, sigmaJetCoordHom_C] using
    ppvSigma_algebraMap σ hσ A A' hAA' hA'A (MvPolynomial.C x)

/-- The localized total derivation restricts to the derivation on the base field. -/
theorem ppvBaseMap_deriv (x : K) :
    Differential.deriv (ppvBaseMap K n x) = ppvBaseMap K n (Differential.deriv x) := by
  rw [show ppvBaseMap K n x =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K)
        (ppvLocalization K n) (MvPolynomial.C x) from rfl,
    show ppvBaseMap K n (Differential.deriv x) =
      algebraMap (DifferentialPolynomial (Fin n × Fin n) K)
        (ppvLocalization K n) (MvPolynomial.C (Differential.deriv x)) from rfl]
  simpa only [GaloisForLFunctions.differentialPolynomialOverDerivation_C] using
    ppvLocalization_deriv_algebraMap (n := n) (MvPolynomial.C x)

/-- Base compatibility survives every two-sided stable quotient. -/
theorem sigmaQuotientEquiv_ppvBaseMap (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (M : Ideal (ppvLocalization K n))
    (hM : IsSigmaIdeal (ppvSigma σ hσ A A' hAA' hA'A) M)
    (hM' : IsSigmaIdeal (ppvSigma σ hσ A A' hAA' hA'A).symm M)
    (x : K) :
    sigmaQuotientEquiv (ppvSigma σ hσ A A' hAA' hA'A) M hM hM'
        (Ideal.Quotient.mk M (ppvBaseMap K n x)) =
      Ideal.Quotient.mk M (ppvBaseMap K n (σ x)) := by
  rw [sigmaQuotientEquiv_mk, ppvSigma_ppvBaseMap]

/-- Base derivation compatibility survives every differential quotient. -/
theorem quotientDifferential_ppvBaseMap_deriv (M : Ideal (ppvLocalization K n))
    (hM : ∀ y ∈ M, Differential.deriv y ∈ M) (x : K) :
    letI : Differential ((ppvLocalization K n) ⧸ M) := quotientDifferential M hM
    Differential.deriv (Ideal.Quotient.mk M (ppvBaseMap K n x)) =
      Ideal.Quotient.mk M (ppvBaseMap K n (Differential.deriv x)) := by
  rw [quotientDifferential_deriv_mk, ppvBaseMap_deriv]

/-- Every differential PPV quotient is canonically a differential algebra over its base field. -/
theorem ppvQuotientDifferentialAlgebra
    (M : Ideal (ppvLocalization K n))
    (hM : ∀ y ∈ M, Differential.deriv y ∈ M) :
    letI : Differential ((ppvLocalization K n) ⧸ M) := quotientDifferential M hM
    DifferentialAlgebra K ((ppvLocalization K n) ⧸ M) := by
  letI : Differential ((ppvLocalization K n) ⧸ M) := quotientDifferential M hM
  constructor
  intro x
  exact quotientDifferential_ppvBaseMap_deriv M hM x

/-- The generic matrix solves the localized system. -/
theorem ppvSigma_ppvFundamental (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (i j : Fin n) :
    ppvSigma σ hσ A A' hAA' hA'A (ppvFundamental K n i j) =
      ((A.map (ppvBaseMap K n)) * ppvFundamental K n) i j := by
  simp [ppvFundamental, jetFundamentalMatrix, sigmaJetCoordEquiv_apply,
    systemRow, Matrix.mul_apply, Matrix.map_apply, ppvBaseMap]

/-- The localized difference automorphism commutes with the quotient-rule derivation. -/
theorem ppvSigma_commutes (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    CommutesDeriv (ppvSigma σ hσ A A' hAA' hA'A) := by
  intro z
  apply localization_commutes_of_base
    (Submonoid.powers ((jetFundamentalMatrix K n).det))
    (ppvLocalizationDerivation K n) (ppvSigma σ hσ A A' hAA' hA'A) _ z
  intro f
  rw [ppvLocalizationDerivation_algebraMap, ppvSigma_algebraMap,
    ppvSigma_algebraMap, ppvLocalizationDerivation_algebraMap,
    sigmaJetCoordEquiv_commutes]

/-- Every invertible differential difference system has a parameterized Picard--Vessiot quotient. -/
theorem exists_parameterizedPicardVessiot_system (σ : K ≃+* K)
    (hσ : ∀ a : K, σ (Differential.deriv a) = Differential.deriv (σ a))
    (A A' : Matrix (Fin n) (Fin n) K) (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
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
      IsUnit ((ppvFundamental K n).map (Ideal.Quotient.mk M)).det :=
  exists_parameterizedPicardVessiot_of_fundamentalMatrix
    (ppvSigma σ hσ A A' hAA' hA'A)
    (ppvSigma_commutes σ hσ A A' hAA' hA'A)
    (A.map (ppvBaseMap K n)) (ppvFundamental K n)
    (ppvSigma_ppvFundamental σ hσ A A' hAA' hA'A)
    isUnit_det_ppvFundamental

end

end GaloisForLFunctions.HTGeometry
