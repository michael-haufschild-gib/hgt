import GaloisForLFunctions.HTGeometry.PureCriticalFactorizationCount
import Mathlib.RingTheory.Etale.Finite
import Mathlib.RingTheory.Polynomial.UniversalFactorizationRing
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

/-- The pure cyclic polynomial with its monic degree certificate. -/
noncomputable def pureCriticalMonicDegreeEq (K : Type*) [Field K] (m n : ℕ)
    (hL : 0 < m + n) : Polynomial.MonicDegreeEq K (m + n) :=
  Polynomial.MonicDegreeEq.mk (pureCriticalCyclicPolynomial (K := K) (m + n))
    (pureCriticalCyclicPolynomial_monic hL)
    (pureCriticalCyclicPolynomial_natDegree (m + n))

/-- Universal algebra of monic degree-`m`/degree-`n` factorizations of `1+X^(m+n)`. -/
abbrev PureCriticalFactorizationAlgebra (K : Type*) [Field K] (m n : ℕ)
    (hL : 0 < m + n) :=
  Polynomial.UniversalFactorizationRing m n rfl (pureCriticalMonicDegreeEq K m n hL)

/-- Pairs of monic factors of prescribed degrees whose product is `P`. -/
abbrev MonicFactorization (P : K[X]) (m n : ℕ) :=
  {q : Polynomial.MonicDegreeEq K m × Polynomial.MonicDegreeEq K n // q.1.1 * q.2.1 = P}

/-- A monic factorization is determined by, and determines, its first monic divisor. -/
noncomputable def monicFactorizationEquivMonicDivisor
    {P : K[X]} (hP : P.Monic) (hdeg : P.natDegree = m + n) :
    MonicFactorization P m n ≃ {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} := by
  let f : MonicFactorization P m n →
      {A : K[X] // A.Monic ∧ A ∣ P ∧ A.natDegree = m} :=
    fun q => ⟨q.1.1.1, q.1.1.monic, ⟨q.1.2.1, q.2.symm⟩, q.1.1.natDegree⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro q r hqr
    have hfirst : q.1.1.1 = r.1.1.1 := by
      change (f q).1 = (f r).1
      exact congrArg Subtype.val hqr
    apply Subtype.ext
    apply Prod.ext
    · exact Subtype.ext hfirst
    · apply Subtype.ext
      have hmul : q.1.1.1 * q.1.2.1 = q.1.1.1 * r.1.2.1 := by
        rw [q.2, hfirst, r.2]
      exact (mul_left_cancel₀ q.1.1.monic.ne_zero hmul)
  · rintro ⟨A, hAmonic, hAdvd, hAdeg⟩
    obtain ⟨B, hAB⟩ := hAdvd
    have hAimd : A.IsMonicOfDegree m := ⟨hAdeg, hAmonic⟩
    have hPimd : P.IsMonicOfDegree (m + n) := ⟨hdeg, hP⟩
    have hBimd : B.IsMonicOfDegree n := by
      apply hAimd.of_mul_left
      rwa [← hAB]
    let AA : Polynomial.MonicDegreeEq K m :=
      Polynomial.MonicDegreeEq.mk A hAmonic hAdeg
    let BB : Polynomial.MonicDegreeEq K n :=
      Polynomial.MonicDegreeEq.mk B hBimd.monic hBimd.natDegree_eq
    refine ⟨⟨(AA, BB), ?_⟩, ?_⟩
    · exact hAB.symm
    · apply Subtype.ext
      rfl

theorem nat_card_pureCriticalMonicFactorization [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hL : 0 < m + n) :
    Nat.card (MonicFactorization (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) =
      criticalHorizonMultiplicity m n := by
  classical
  rw [Nat.card_congr (monicFactorizationEquivMonicDivisor
    (pureCriticalCyclicPolynomial_monic hL)
    (pureCriticalCyclicPolynomial_natDegree (m + n)))]
  simpa [criticalHorizonMultiplicity] using
    (nat_card_monic_divisors_pureCritical (K := K) (m := m) (n := n) hL)

theorem pureCriticalFactorizationAlgebra_isCoprime [CharZero K]
    {m n : ℕ} (hL : 0 < m + n) :
    IsCoprime
      (Polynomial.UniversalFactorizationRing.factor₁ m n rfl
        (pureCriticalMonicDegreeEq K m n hL)).1
      (Polynomial.UniversalFactorizationRing.factor₂ m n rfl
        (pureCriticalMonicDegreeEq K m n hL)).1 := by
  let A := PureCriticalFactorizationAlgebra K m n hL
  let f : A[X] :=
    (Polynomial.UniversalFactorizationRing.factor₁ m n rfl
      (pureCriticalMonicDegreeEq K m n hL)).1
  let g : A[X] :=
    (Polynomial.UniversalFactorizationRing.factor₂ m n rfl
      (pureCriticalMonicDegreeEq K m n hL)).1
  have hsep : ((pureCriticalCyclicPolynomial (K := K) (m + n)).map
      (algebraMap K A)).Separable :=
    (pureCriticalCyclicPolynomial_separable hL).map
  have hmul : f * g = (pureCriticalCyclicPolynomial (K := K) (m + n)).map
      (algebraMap K A) := by
    exact Polynomial.UniversalFactorizationRing.factor₁_mul_factor₂ m n rfl
      (pureCriticalMonicDegreeEq K m n hL)
  exact (hmul ▸ hsep).isCoprime

theorem pureCriticalFactorizationAlgebra_jacobian_isUnit [CharZero K]
    {m n : ℕ} (hL : 0 < m + n) :
    IsUnit (Polynomial.UniversalFactorizationRing.presentation m n rfl
      (pureCriticalMonicDegreeEq K m n hL)).jacobian := by
  rw [Polynomial.UniversalFactorizationRing.jacobian_resentation]
  apply IsUnit.mul
  · exact (isUnit_one.neg).pow _
  · rw [Polynomial.isUnit_resultant_iff_isCoprime
      (Polynomial.UniversalFactorizationRing.factor₁ m n rfl
        (pureCriticalMonicDegreeEq K m n hL)).monic]
    exact pureCriticalFactorizationAlgebra_isCoprime hL

theorem pureCriticalFactorizationAlgebra_etale [CharZero K]
    {m n : ℕ} (hL : 0 < m + n) :
    Algebra.Etale K (PureCriticalFactorizationAlgebra K m n hL) := by
  let P : Algebra.SubmersivePresentation K
      (PureCriticalFactorizationAlgebra K m n hL) (Fin m ⊕ Fin n) (Fin (m + n)) :=
    { toPreSubmersivePresentation :=
        Polynomial.UniversalFactorizationRing.presentation m n rfl
          (pureCriticalMonicDegreeEq K m n hL)
      jacobian_isUnit := pureCriticalFactorizationAlgebra_jacobian_isUnit hL }
  have : Algebra.IsStandardSmoothOfRelativeDimension 0 K
      (PureCriticalFactorizationAlgebra K m n hL) :=
    ⟨_, _, _, inferInstance, P, by
      simp [Algebra.Presentation.dimension]⟩
  infer_instance

/-- The pure factorization algebra is a product of one copy of `K` per occupation state. -/
theorem finrank_pureCriticalFactorizationAlgebra [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hL : 0 < m + n) :
    Module.finrank K (PureCriticalFactorizationAlgebra K m n hL) =
      criticalHorizonMultiplicity m n := by
  let A := PureCriticalFactorizationAlgebra K m n hL
  letI : Algebra.Etale K A := pureCriticalFactorizationAlgebra_etale hL
  letI : IsArtinianRing A := isArtinian_of_tower K inferInstance
  letI : Fintype (PrimeSpectrum A) := Fintype.ofFinite _
  let e : A ≃ₐ[K] (PrimeSpectrum A → K) :=
    Algebra.FormallyEtale.equivPiOfIsSepClosed K A
  calc
    Module.finrank K A = Module.finrank K (PrimeSpectrum A → K) :=
      LinearEquiv.finrank_eq e.toLinearEquiv
    _ = Fintype.card (PrimeSpectrum A) := by
      rw [Module.finrank_pi]
    _ = Nat.card (PrimeSpectrum A) :=
      (Nat.card_eq_fintype_card : Nat.card (PrimeSpectrum A) =
        Fintype.card (PrimeSpectrum A)).symm
    _ = Nat.card (A →ₐ[K] K) :=
      (Nat.card_congr (Algebra.IsFiniteSplit.algHomEquivPrimeSpectrum K A)).symm
    _ = Nat.card (MonicFactorization
        (pureCriticalCyclicPolynomial (K := K) (m + n)) m n) := by
      apply Nat.card_congr
      refine (Polynomial.UniversalFactorizationRing.homEquiv K m n rfl
        (pureCriticalMonicDegreeEq K m n hL)).trans ?_
      apply Equiv.subtypeEquivRight
      intro q
      simp [pureCriticalMonicDegreeEq]
    _ = criticalHorizonMultiplicity m n :=
      nat_card_pureCriticalMonicFactorization hL

end GaloisForLFunctions.HTGeometry
