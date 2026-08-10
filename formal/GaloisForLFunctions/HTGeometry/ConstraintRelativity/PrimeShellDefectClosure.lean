import Mathlib
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.DefectClosure
import GaloisForLFunctions.RHTower.PrimeDilationTropicalBoundaryTomography

/-!
# The prime-shell instance of defect closure

The bounded prime-valuation source carries the radial shell reporters and the prime dilations.
Pulling a reporter back along a prime dilation is an algebra endomorphism of the reporter algebra,
so the prime dilations generate an acting monoid and the generic defect-closure theorem applies
verbatim.

The covariance failure of a radial shell under one prime dilation is the signed difference of two
adjacent winning facets, and iterating over a squarefree prime list produces the signed difference
of two adjacent simultaneous-winning faces.  Both therefore lie in the prime-dilation orbit algebra
of the shells: the whole finite face nerve is already present in the orbit algebra of the supplied
dilations, and the defect recursion stabilizes after one step.
-/

namespace HTGeometry.ConstraintRelativity

open RHTower RHTower.BoundedPrimeValuation

/-! ## Pullback along a self-map of the source -/

section Pullback

variable {k X : Type*} [CommSemiring k]

/-- Precomposition with a self-map of the source is a unital algebra endomorphism of the algebra
of reporters. -/
def pullbackAlgHom (g : X → X) : (X → k) →ₐ[k] (X → k) where
  toFun f := fun x => f (g x)
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

@[simp] theorem pullbackAlgHom_apply (g : X → X) (f : X → k) (x : X) :
    pullbackAlgHom (k := k) g f x = f (g x) := rfl

end Pullback

/-! ## The prime-dilation action on radial shell reporters -/

section PrimeShell

/-- Pullback of a reporter along one prime dilation of the bounded valuation source. -/
noncomputable def primeDilationPullback (p : Nat.Primes) :
    (BoundedPrimeValuation → ℤ) →ₐ[ℤ] (BoundedPrimeValuation → ℤ) :=
  pullbackAlgHom fun x => x.primeDilation p

@[simp] theorem primeDilationPullback_apply (p : Nat.Primes) (f : BoundedPrimeValuation → ℤ)
    (x : BoundedPrimeValuation) :
    primeDilationPullback p f x = f (x.primeDilation p) := rfl

/-- The acting monoid: all words in the supplied prime dilations. -/
noncomputable def primeDilationMonoid :
    Submonoid ((BoundedPrimeValuation → ℤ) →ₐ[ℤ] (BoundedPrimeValuation → ℤ)) :=
  Submonoid.closure (Set.range primeDilationPullback)

theorem primeDilationPullback_mem (p : Nat.Primes) :
    primeDilationPullback p ∈ primeDilationMonoid :=
  Submonoid.subset_closure ⟨p, rfl⟩

/-- The observable algebra of radial shell reporters. -/
noncomputable def shellAlgebra : Subalgebra ℤ (BoundedPrimeValuation → ℤ) :=
  Algebra.adjoin ℤ (Set.range fun m : ℕ => tropicalShellIndicator m)

theorem tropicalShellIndicator_mem_shellAlgebra (m : ℕ) :
    tropicalShellIndicator m ∈ shellAlgebra :=
  Algebra.subset_adjoin ⟨m, rfl⟩

/-- The orbit algebra of the radial shells under the prime dilations: the strongest positive
survivor of the defect recursion. -/
noncomputable def shellOrbitAlgebra : Subalgebra ℤ (BoundedPrimeValuation → ℤ) :=
  orbitClosure primeDilationMonoid shellAlgebra

theorem shellAlgebra_le_shellOrbitAlgebra : shellAlgebra ≤ shellOrbitAlgebra :=
  le_orbitClosure _ _

theorem tropicalShellIndicator_mem_shellOrbitAlgebra (m : ℕ) :
    tropicalShellIndicator m ∈ shellOrbitAlgebra :=
  shellAlgebra_le_shellOrbitAlgebra (tropicalShellIndicator_mem_shellAlgebra m)

/-- The orbit algebra is closed under one prime-dilation covariance defect. -/
theorem primeDifference_mem_shellOrbitAlgebra (p : Nat.Primes)
    {f : BoundedPrimeValuation → ℤ} (hf : f ∈ shellOrbitAlgebra) :
    primeDifference p f ∈ shellOrbitAlgebra := by
  have hT : primeDilationPullback p f ∈ shellOrbitAlgebra :=
    orbitClosure_invariant primeDilationMonoid shellAlgebra (primeDilationPullback_mem p) hf
  have hsub : primeDilationPullback p f - f ∈ shellOrbitAlgebra := sub_mem hT hf
  have heq : primeDifference p f = primeDilationPullback p f - f := by
    funext x
    rfl
  rwa [heq]

/-- The orbit algebra is closed under iterated prime-dilation covariance defects. -/
theorem iteratedPrimeDifference_mem_shellOrbitAlgebra (ps : List Nat.Primes)
    {f : BoundedPrimeValuation → ℤ} (hf : f ∈ shellOrbitAlgebra) :
    iteratedPrimeDifference ps f ∈ shellOrbitAlgebra := by
  induction ps with
  | nil => exact hf
  | cons p ps ih => exact primeDifference_mem_shellOrbitAlgebra p ih

/-- **Card `(7)`, prime-shell application.**  The prime-winning facet difference is exactly the
covariance failure of a radial shell, hence lies in the orbit algebra of the shells. -/
theorem facetDifference_mem_shellOrbitAlgebra (p : Nat.Primes) {m : ℕ} (hm : 0 < m) :
    (fun x => primeWinningFacetIndicator p (m - 1) x - primeWinningFacetIndicator p m x)
      ∈ shellOrbitAlgebra := by
  have heq : (fun x => primeWinningFacetIndicator p (m - 1) x - primeWinningFacetIndicator p m x)
      = primeDifference p (tropicalShellIndicator m) := by
    funext x
    exact (tropicalShellIndicator_primeDilation_sub x p hm).symm
  rw [heq]
  exact primeDifference_mem_shellOrbitAlgebra p (tropicalShellIndicator_mem_shellOrbitAlgebra m)

/-- **Card `(7)`, full face nerve.**  Every simultaneous-winning face difference of the radial
shells lies in the orbit algebra: iterated dilation defects expose the whole finite face
resolution, and nothing beyond the supplied dilations is needed to produce it. -/
theorem faceDifference_mem_shellOrbitAlgebra (ps : List Nat.Primes) (hne : ps ≠ [])
    (hnd : ps.Nodup) {m : ℕ} (hm : 0 < m) :
    (fun x => winningFaceIndicator ps.toFinset (m - 1) x - winningFaceIndicator ps.toFinset m x)
      ∈ shellOrbitAlgebra := by
  have hiter : iteratedPrimeDifference ps (tropicalShellIndicator m) ∈ shellOrbitAlgebra :=
    iteratedPrimeDifference_mem_shellOrbitAlgebra ps
      (tropicalShellIndicator_mem_shellOrbitAlgebra m)
  have heq : iteratedPrimeDifference ps (tropicalShellIndicator m)
      = (-1 : ℤ) ^ (ps.length - 1) •
        (fun x => winningFaceIndicator ps.toFinset (m - 1) x -
          winningFaceIndicator ps.toFinset m x) := by
    funext x
    exact iteratedPrimeDifference_tropicalShellIndicator ps hne hnd x hm
  rw [heq] at hiter
  have hsq : ((-1 : ℤ) ^ (ps.length - 1)) * ((-1 : ℤ) ^ (ps.length - 1)) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  have := Subalgebra.smul_mem shellOrbitAlgebra hiter ((-1 : ℤ) ^ (ps.length - 1))
  rwa [smul_smul, hsq, one_smul] at this

/-- **Card `(5)`, prime-shell instance.**  The radial defect recursion stabilizes at the first
step: every later stage is the prime-dilation orbit algebra, so the experiment generates new
observable distinctions but no new transformation. -/
theorem shell_defectIter_eq (n : ℕ) :
    defectIter primeDilationMonoid shellAlgebra (n + 1) = shellOrbitAlgebra :=
  defectIter_succ_eq _ _ n

/-- **Card `(3)`, prime-shell instance.**  Adjoining every radial covariance defect gives exactly
the orbit algebra of the supplied prime dilations. -/
theorem shell_defectClosure_eq :
    defectClosure primeDilationMonoid shellAlgebra = shellOrbitAlgebra :=
  defectClosure_eq_orbitClosure _ _

/-- **Card `(5)` and `(8)`, prime-shell instance.**  The transfinite radial defect recursion is
constant from stage one on, with value the prime-dilation orbit algebra of the shells.  Every
observable distinction the radial experiment produces — the facets, and the whole simultaneous
winning-face nerve — already lies in that algebra, and no stage introduces a transformation
outside the supplied dilations. -/
theorem shell_defectRecursion_eq
    (chain : Ordinal → Subalgebra ℤ (BoundedPrimeValuation → ℤ))
    (h0 : chain 0 = shellAlgebra)
    (hsucc : ∀ β, chain (β + 1) = defectClosure primeDilationMonoid (chain β))
    (hlim : ∀ β, Order.IsSuccLimit β → chain β = ⨆ γ : Set.Iio β, chain γ)
    (α : Ordinal) (hα : 1 ≤ α) : chain α = shellOrbitAlgebra :=
  eq_orbitClosure_of_defectRecursion primeDilationMonoid shellAlgebra chain h0 hsucc hlim α hα

end PrimeShell

end HTGeometry.ConstraintRelativity
