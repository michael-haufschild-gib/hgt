import GaloisForLFunctions.HTGeometry.DifferenceSystemPicardVessiot
import GaloisForLFunctions.HTGeometry.DifferenceNoNewConstants

/-!
# The Picard--Vessiot ring of a difference system has no new constants

Assembling the two halves: the localized coordinate ring of a fundamental matrix is a finite-type
algebra over the base, its quotient by a maximal `σ`-ideal is `σ`-simple, and a `σ`-simple
finite-type extension of a difference field with algebraically closed constants has exactly the
constants of the base.

So the Picard--Vessiot ring of any invertible linear difference system is a `σ`-simple difference
ring, containing an invertible fundamental solution matrix, whose constants are exactly those of
the base field.  That is the full defining property of a Picard--Vessiot ring.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K] {n : ℕ}

theorem algebraMap_pvLocalization (x : K) :
    algebraMap K (pvLocalization K n) x =
      algebraMap (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n) (MvPolynomial.C x) := by
  rw [IsScalarTower.algebraMap_apply K (MvPolynomial (Fin n × Fin n) K) (pvLocalization K n)]
  rfl

theorem pvSigma_algebraMap (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1) (x : K) :
    pvSigma σ A A' hAA' hA'A (algebraMap K (pvLocalization K n) x)
      = algebraMap K (pvLocalization K n) (σ x) := by
  rw [algebraMap_pvLocalization, algebraMap_pvLocalization]
  rw [pvSigma]
  rw [sigmaAwayEquiv_algebraMap]
  congr 1
  exact sigmaCoordHom_C σ A x

/-- **The Picard--Vessiot ring of an invertible linear difference system has no new constants.**
Its constants are exactly the constants of the base field, provided those are infinite and
algebraically closed. -/
theorem exists_picardVessiot_no_new_constants (σ : K ≃+* K) (A A' : Matrix (Fin n) (Fin n) K)
    (hAA' : A * A' = 1) (hA'A : A' * A = 1)
    (hinf : ((differenceConstants σ : Subfield K) : Set K).Infinite)
    (hclosed : ∀ g : K[X], g.Monic → 0 < g.natDegree → g.map (σ : K →+* K) = g →
      ∃ a : K, σ a = a ∧ g.IsRoot a) :
    ∃ (M : Ideal (pvLocalization K n))
      (hM : IsSigmaIdeal (pvSigma σ A A' hAA' hA'A) M) (_ : M ≠ ⊤)
      (hM' : IsSigmaIdeal (pvSigma σ A A' hAA' hA'A).symm M),
      IsSigmaSimple (sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM') ∧
      (∀ i j, sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM'
          (Ideal.Quotient.mk M (pvFundamental K n i j))
        = (((A.map (pvBaseMap K n)).map (Ideal.Quotient.mk M)) *
            ((pvFundamental K n).map (Ideal.Quotient.mk M))) i j) ∧
      IsUnit ((pvFundamental K n).map (Ideal.Quotient.mk M)).det ∧
      (∀ x : (pvLocalization K n) ⧸ M,
        sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM' x = x →
          ∃ a : K, σ a = a ∧ x = algebraMap K ((pvLocalization K n) ⧸ M) a) := by
  classical
  obtain ⟨M, hM, hMne, hM', hsimple, hfield, hfund, hdet⟩ :=
    exists_picardVessiot_system σ A A' hAA' hA'A
  refine ⟨M, hM, hMne, hM', hsimple, hfund, hdet, ?_⟩
  haveI : Nontrivial ((pvLocalization K n) ⧸ M) := by
    rw [← not_subsingleton_iff_nontrivial, Ideal.Quotient.subsingleton_iff]
    exact hMne
  haveI : Algebra.FiniteType K ((pvLocalization K n) ⧸ M) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K M) Ideal.Quotient.mk_surjective
  have hcompat : ∀ x : K,
      sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM'
          (algebraMap K ((pvLocalization K n) ⧸ M) x)
        = algebraMap K ((pvLocalization K n) ⧸ M) (σ x) := by
    intro x
    have hmk : ∀ y : K, algebraMap K ((pvLocalization K n) ⧸ M) y
        = Ideal.Quotient.mk M (algebraMap K (pvLocalization K n) y) := fun _ => rfl
    rw [hmk, hmk, sigmaQuotientEquiv_mk, pvSigma_algebraMap]
  intro x hx
  exact exists_eq_algebraMap_of_isSigmaSimple σ
    (sigmaQuotientEquiv (pvSigma σ A A' hAA' hA'A) M hM hM') hcompat hsimple hinf hclosed hx

end

end GaloisForLFunctions.HTGeometry
