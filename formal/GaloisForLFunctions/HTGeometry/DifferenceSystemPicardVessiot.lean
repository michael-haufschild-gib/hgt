import GaloisForLFunctions.HTGeometry.DifferenceAwayLocalization

/-!
# Existence of a Picard--Vessiot ring for a linear difference system

Putting the previous layers together: the coordinate ring of a fundamental matrix, localized at its
determinant, is a difference ring carrying an invertible formal fundamental solution of the system
`σ Y = A Y`; quotienting by a maximal `σ`-ideal makes it `σ`-simple without destroying the
fundamental matrix.  The result is a Picard--Vessiot ring: a `σ`-simple difference ring, generated
over the base by the entries of an invertible fundamental matrix and the inverse of its
determinant, whose constants form a field.

This is the foundation on which a difference Galois group can be defined, and it exists in neither
mathlib nor the rest of this repository.
-/

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The abstract existence statement -/

/-- **Existence of a Picard--Vessiot quotient of a difference ring with a fundamental matrix.**
A nontrivial difference ring carrying an invertible fundamental solution matrix of a linear system
has a `σ`-simple quotient in which the matrix is still an invertible fundamental solution, and the
constants of that quotient form a field. -/
theorem exists_picardVessiot_of_fundamentalMatrix
    {S : Type*} [CommRing S] [Nontrivial S] (τ : S ≃+* S)
    {n : ℕ} (B Y : Matrix (Fin n) (Fin n) S)
    (hY : ∀ i j, τ (Y i j) = (B * Y) i j) (hdet : IsUnit Y.det) :
    ∃ (M : Ideal S) (hM : IsSigmaIdeal τ M) (_ : M ≠ ⊤) (hM' : IsSigmaIdeal τ.symm M),
      IsSigmaSimple (sigmaQuotientEquiv τ M hM hM') ∧
      IsField (sigmaConstantsSubring (sigmaQuotientEquiv τ M hM hM')) ∧
      (∀ i j, sigmaQuotientEquiv τ M hM hM' (Ideal.Quotient.mk M (Y i j))
        = ((B.map (Ideal.Quotient.mk M)) * (Y.map (Ideal.Quotient.mk M))) i j) ∧
      IsUnit (Y.map (Ideal.Quotient.mk M)).det := by
  classical
  have hbot : IsSigmaIdeal τ (⊥ : Ideal S) := isSigmaIdeal_bot τ
  have hbotne : (⊥ : Ideal S) ≠ ⊤ := bot_ne_top
  obtain ⟨M, hIM, hM, hMne, hmax⟩ := exists_maximal_isSigmaIdeal τ (⊥ : Ideal S) hbot hbotne
  have hM' : IsSigmaIdeal τ.symm M := isSigmaIdeal_symm_of_maximal hM hMne hmax
  have hsimple : IsSigmaSimple (sigmaQuotientEquiv τ M hM hM') :=
    isSigmaSimple_quotient_of_maximal hM hMne hmax
  haveI : Nontrivial (S ⧸ M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hMne
  refine ⟨M, hM, hMne, hM', hsimple,
    isField_sigmaConstantsSubring_of_isSigmaSimple hsimple, ?_, ?_⟩
  · intro i j
    have hmk : sigmaQuotientEquiv τ M hM hM' (Ideal.Quotient.mk M (Y i j))
        = Ideal.Quotient.mk M (τ (Y i j)) := rfl
    rw [hmk, hY i j]
    simp [Matrix.mul_apply, Matrix.map_apply, map_sum]
  · have hmap : (Y.map (Ideal.Quotient.mk M)).det = Ideal.Quotient.mk M Y.det := by
      rw [RingHom.map_det (Ideal.Quotient.mk M) Y, RingHom.mapMatrix_apply]
    rw [hmap]
    exact hdet.map (Ideal.Quotient.mk M)

/-! ### The concrete Picard--Vessiot ring of an invertible system -/

variable {K : Type*} [Field K] {n : ℕ}

/-- The determinant of the generic matrix is a nonzero polynomial: it takes the value one at the
identity matrix. -/
theorem fundamentalMatrix_det_ne_zero :
    (fundamentalMatrix K n).det ≠ 0 := by
  classical
  set e : Fin n × Fin n → K := fun p => if p.1 = p.2 then 1 else 0 with he
  have hmap : (fundamentalMatrix K n).map (MvPolynomial.eval e)
      = (1 : Matrix (Fin n) (Fin n) K) := by
    refine Matrix.ext fun i j => ?_
    simp [fundamentalMatrix, Matrix.map_apply, Matrix.one_apply, he]
  have heval : MvPolynomial.eval e ((fundamentalMatrix K n).det) = 1 := by
    rw [RingHom.map_det (MvPolynomial.eval e) (fundamentalMatrix K n),
      RingHom.mapMatrix_apply, hmap, Matrix.det_one]
  intro hzero
  rw [hzero, map_zero] at heval
  exact zero_ne_one heval

/-- The `σ`-action on the coordinate ring, as an explicit ring homomorphism on the inverse side. -/
theorem sigmaCoordEquiv_symm_apply (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (p : MvPolynomial (Fin n × Fin n) K) :
    (sigmaCoordEquiv σ A A' hAA' hA'A).symm p =
      sigmaCoordHom σ.symm (A'.map (σ.symm : K →+* K)) p := rfl

variable (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)

/-- The coordinate ring of a fundamental matrix, localized at its determinant. -/
abbrev pvLocalization (K : Type*) [Field K] (n : ℕ) : Type _ :=
  Localization.Away ((fundamentalMatrix K n).det)

theorem powers_fundamentalDet_le_nonZeroDivisors :
    Submonoid.powers ((fundamentalMatrix K n).det) ≤
      nonZeroDivisors (MvPolynomial (Fin n × Fin n) K) := by
  rintro x ⟨k, rfl⟩
  refine mem_nonZeroDivisors_of_ne_zero ?_
  exact pow_ne_zero k fundamentalMatrix_det_ne_zero

instance : Nontrivial (pvLocalization K n) := by
  have hinj : Function.Injective
      (algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)) :=
    IsLocalization.injective (M := Submonoid.powers ((fundamentalMatrix K n).det)) _
      powers_fundamentalDet_le_nonZeroDivisors
  exact ⟨⟨algebraMap _ _ 0, algebraMap _ _ 1, fun h => zero_ne_one (hinj h)⟩⟩

/-- The base field embedded in the localized coordinate ring. -/
def pvBaseMap (K : Type*) [Field K] (n : ℕ) : K →+* pvLocalization K n :=
  (algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)).comp
    (MvPolynomial.C : K →+* MvPolynomial (Fin n × Fin n) K)

/-- The formal fundamental solution matrix inside the localized coordinate ring. -/
def pvFundamental (K : Type*) [Field K] (n : ℕ) :
    Matrix (Fin n) (Fin n) (pvLocalization K n) :=
  (fundamentalMatrix K n).map
    (algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n))

theorem isUnit_algebraMap_fundamentalDet :
    IsUnit (algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)
      ((fundamentalMatrix K n).det)) :=
  IsLocalization.map_units (M := Submonoid.powers ((fundamentalMatrix K n).det)) _
    ⟨_, Submonoid.mem_powers _⟩

theorem isUnit_det_pvFundamental : IsUnit ((pvFundamental K n).det) := by
  have h : (pvFundamental K n).det =
      algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)
        ((fundamentalMatrix K n).det) := by
    rw [pvFundamental, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [h]
  exact isUnit_algebraMap_fundamentalDet

/-- The `σ`-action of an invertible system on the localized coordinate ring. -/
def pvSigma (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    pvLocalization K n ≃+* pvLocalization K n :=
  sigmaAwayEquiv (S := pvLocalization K n) (sigmaCoordEquiv σ A A' hAA' hA'A)
    ((fundamentalMatrix K n).det)
    (by
      have hdet : IsUnit A.det := Matrix.isUnit_det_of_right_inverse hAA'
      have hval : (sigmaCoordEquiv σ A A' hAA' hA'A) ((fundamentalMatrix K n).det)
          = MvPolynomial.C A.det * (fundamentalMatrix K n).det := sigmaCoordHom_det σ A
      rw [hval, map_mul]
      exact ((hdet.map MvPolynomial.C).map _).mul isUnit_algebraMap_fundamentalDet)
    (by
      have hdet' : IsUnit (A'.map (σ.symm : K →+* K)).det := by
        have h1 : (A'.map (σ.symm : K →+* K)).det = (σ.symm : K →+* K) A'.det := by
          rw [RingHom.map_det (σ.symm : K →+* K) A', RingHom.mapMatrix_apply]
        rw [h1]
        exact (Matrix.isUnit_det_of_right_inverse hA'A).map (σ.symm : K →+* K)
      have hval : (sigmaCoordEquiv σ A A' hAA' hA'A).symm ((fundamentalMatrix K n).det)
          = MvPolynomial.C ((A'.map (σ.symm : K →+* K)).det) * (fundamentalMatrix K n).det :=
        sigmaCoordHom_det σ.symm (A'.map (σ.symm : K →+* K))
      rw [hval, map_mul]
      exact ((hdet'.map MvPolynomial.C).map _).mul isUnit_algebraMap_fundamentalDet)

/-- **The formal fundamental matrix solves the system.** -/
theorem pvSigma_pvFundamental (hAA' : A * A' = 1) (hA'A : A' * A = 1) (i j : Fin n) :
    pvSigma σ A A' hAA' hA'A (pvFundamental K n i j) =
      ((A.map (pvBaseMap K n)) * pvFundamental K n) i j := by
  have hmk : pvSigma σ A A' hAA' hA'A
      (algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)
        (MvPolynomial.X (i, j)))
      = algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)
        (sigmaCoordHom σ A (MvPolynomial.X (i, j))) :=
    sigmaAwayEquiv_algebraMap _ _ _ _ _
  simp only [pvFundamental, Matrix.map_apply, fundamentalMatrix]
  rw [hmk, sigmaCoordHom_X, map_sum]
  simp [Matrix.mul_apply, Matrix.map_apply, pvBaseMap, fundamentalMatrix]

/-- **Existence of a Picard--Vessiot ring for an invertible linear difference system.**  There is a
`σ`-simple quotient of the localized coordinate ring in which the formal fundamental matrix is still
an invertible solution of the system, and whose constants form a field. -/
theorem exists_picardVessiot_system (hAA' : A * A' = 1) (hA'A : A' * A = 1) :
    ∃ (M : Ideal (pvLocalization K n))
      (hM : IsSigmaIdeal (pvSigma σ A A' hAA' hA'A) M) (_ : M ≠ ⊤)
      (hM' : IsSigmaIdeal (pvSigma σ A A' hAA' hA'A).symm M),
      IsSigmaSimple (sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM') ∧
      IsField (sigmaConstantsSubring
        (sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM')) ∧
      (∀ i j, sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM'
          (Ideal.Quotient.mk M (pvFundamental K n i j))
        = (((A.map (pvBaseMap K n)).map (Ideal.Quotient.mk M)) *
            ((pvFundamental K n).map (Ideal.Quotient.mk M))) i j) ∧
      IsUnit ((pvFundamental K n).map (Ideal.Quotient.mk M)).det :=
  exists_picardVessiot_of_fundamentalMatrix (pvSigma σ A A' hAA' hA'A)
    (A.map (pvBaseMap K n)) (pvFundamental K n)
    (pvSigma_pvFundamental σ A A' hAA' hA'A) isUnit_det_pvFundamental


end

end GaloisForLFunctions.HTGeometry
