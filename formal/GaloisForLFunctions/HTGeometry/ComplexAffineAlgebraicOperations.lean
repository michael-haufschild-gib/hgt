import GaloisForLFunctions.HTGeometry.ComplexAffineAlgebraicNoetherian

namespace GaloisForLFunctions.HTGeometry

open Set

noncomputable section

/-- Every ideal zero locus is a complex affine algebraic set. -/
theorem isComplexAffineAlgebraic_zeroLocus {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    IsComplexAffineAlgebraic (MvPolynomial.zeroLocus ℂ I) :=
  ⟨I, rfl⟩

theorem isComplexAffineAlgebraic_empty {n : ℕ} :
    IsComplexAffineAlgebraic (∅ : Set (Fin n → ℂ)) := by
  refine ⟨⊤, ?_⟩
  exact MvPolynomial.zeroLocus_top.symm

theorem isComplexAffineAlgebraic_univ {n : ℕ} :
    IsComplexAffineAlgebraic (Set.univ : Set (Fin n → ℂ)) := by
  refine ⟨⊥, ?_⟩
  exact MvPolynomial.zeroLocus_bot.symm

/-- Intersections of complex affine algebraic sets are algebraic. -/
theorem IsComplexAffineAlgebraic.inter {n : ℕ}
    {S T : Set (Fin n → ℂ)}
    (hS : IsComplexAffineAlgebraic S) (hT : IsComplexAffineAlgebraic T) :
    IsComplexAffineAlgebraic (S ∩ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  refine ⟨I ⊔ J, ?_⟩
  ext x
  change (I ≤ RingHom.ker (MvPolynomial.aeval x) ∧
      J ≤ RingHom.ker (MvPolynomial.aeval x)) ↔
    I ⊔ J ≤ RingHom.ker (MvPolynomial.aeval x)
  exact sup_le_iff.symm

/-- Finite unions of complex affine algebraic sets are algebraic. -/
theorem IsComplexAffineAlgebraic.union {n : ℕ}
    {S T : Set (Fin n → ℂ)}
    (hS : IsComplexAffineAlgebraic S) (hT : IsComplexAffineAlgebraic T) :
    IsComplexAffineAlgebraic (S ∪ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  refine ⟨I * J, ?_⟩
  ext x
  change (I ≤ RingHom.ker (MvPolynomial.aeval x) ∨
      J ≤ RingHom.ker (MvPolynomial.aeval x)) ↔
    I * J ≤ RingHom.ker (MvPolynomial.aeval x)
  exact (Ideal.IsPrime.mul_le (RingHom.ker_isPrime _)).symm

/-- The common zero set of a finite polynomial family is algebraic. -/
theorem isComplexAffineAlgebraic_zeroLocus_family {n m : ℕ}
    (P : Fin m → MvPolynomial (Fin n) ℂ) :
    IsComplexAffineAlgebraic {x | ∀ i, MvPolynomial.eval x (P i) = 0} := by
  refine ⟨Ideal.span (Set.range P), ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp [MvPolynomial.aeval_def]

/-- A common zero set indexed by an arbitrary finite type is algebraic. -/
theorem isComplexAffineAlgebraic_zeroLocus_finite_family
    {n : ℕ} {ι : Type*} [Finite ι]
    (P : ι → MvPolynomial (Fin n) ℂ) :
    IsComplexAffineAlgebraic {x | ∀ i, MvPolynomial.eval x (P i) = 0} := by
  refine ⟨Ideal.span (Set.range P), ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp [MvPolynomial.aeval_def]

/-- A common zero set in an arbitrary coordinate type is affine algebraic. -/
theorem isComplexAffineAlgebraicSet_zeroLocus_family
    {σ ι : Type*} (P : ι → MvPolynomial σ ℂ) :
    IsComplexAffineAlgebraicSet {x | ∀ i, MvPolynomial.eval x (P i) = 0} := by
  refine ⟨Ideal.span (Set.range P), ?_⟩
  rw [MvPolynomial.zeroLocus_span]
  ext x
  simp [MvPolynomial.aeval_def]

theorem IsComplexAffineAlgebraicSet.inter {σ : Type*}
    {S T : Set (σ → ℂ)}
    (hS : IsComplexAffineAlgebraicSet S) (hT : IsComplexAffineAlgebraicSet T) :
    IsComplexAffineAlgebraicSet (S ∩ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  refine ⟨I ⊔ J, ?_⟩
  ext x
  change (I ≤ RingHom.ker (MvPolynomial.aeval x) ∧
      J ≤ RingHom.ker (MvPolynomial.aeval x)) ↔
    I ⊔ J ≤ RingHom.ker (MvPolynomial.aeval x)
  exact sup_le_iff.symm

theorem IsComplexAffineAlgebraicSet.union {σ : Type*}
    {S T : Set (σ → ℂ)}
    (hS : IsComplexAffineAlgebraicSet S) (hT : IsComplexAffineAlgebraicSet T) :
    IsComplexAffineAlgebraicSet (S ∪ T) := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨J, rfl⟩ := hT
  refine ⟨I * J, ?_⟩
  ext x
  change (I ≤ RingHom.ker (MvPolynomial.aeval x) ∨
      J ≤ RingHom.ker (MvPolynomial.aeval x)) ↔
    I * J ≤ RingHom.ker (MvPolynomial.aeval x)
  exact (Ideal.IsPrime.mul_le (RingHom.ker_isPrime _)).symm

/-- Every algebraic set in finitely many arbitrary coordinates has finite equations. -/
theorem IsComplexAffineAlgebraicSet.exists_fin_zeroLocus_family
    {σ : Type*} [Finite σ] {S : Set (σ → ℂ)}
    (hS : IsComplexAffineAlgebraicSet S) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial σ ℂ),
      S = {x | ∀ i, MvPolynomial.eval x (P i) = 0} := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨m, P, hP⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing I)
  refine ⟨m, P, ?_⟩
  rw [← hP, MvPolynomial.zeroLocus_span]
  ext x
  simp [MvPolynomial.aeval_def]

/-- Every complex affine algebraic set is cut out by a finite polynomial family. -/
theorem IsComplexAffineAlgebraic.exists_fin_zeroLocus_family {n : ℕ}
    {S : Set (Fin n → ℂ)} (hS : IsComplexAffineAlgebraic S) :
    ∃ (m : ℕ) (P : Fin m → MvPolynomial (Fin n) ℂ),
      S = {x | ∀ i, MvPolynomial.eval x (P i) = 0} := by
  obtain ⟨I, rfl⟩ := hS
  obtain ⟨m, P, hP⟩ := Submodule.fg_iff_exists_fin_generating_family.mp
    (Ideal.fg_of_isNoetherianRing I)
  refine ⟨m, P, ?_⟩
  rw [← hP, MvPolynomial.zeroLocus_span]
  ext x
  simp [MvPolynomial.aeval_def]

end

end GaloisForLFunctions.HTGeometry
