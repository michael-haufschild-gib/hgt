import GaloisForLFunctions.HTGeometry.DifferentialIndependence
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.RingTheory.Nullstellensatz

/-!
# Finite multivariate Hermite interpolation by Chinese remainders

The maximal ideals of two distinct points of affine space over a field are distinct and hence
coprime.  Their arbitrary powers remain coprime, so the polynomial Chinese remainder theorem
simultaneously realizes arbitrary residue classes modulo arbitrary finite point-ideal powers.

This is the algebraic interpolation layer required by affine finite-jet packet arguments.  It is
genuinely multivariate: the local residue class modulo the `m`-th power of a point ideal records
the full Taylor packet of total order strictly below `m`.
-/

open Set Function

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Distinct affine points have distinct vanishing ideals. -/
theorem vanishingIdeal_singleton_ne_of_ne
    {K σ : Type*} [Field K] {x y : σ → K} (hxy : x ≠ y) :
    MvPolynomial.vanishingIdeal K {x} ≠
      MvPolynomial.vanishingIdeal K {y} := by
  intro hideal
  apply hxy
  funext i
  have hmem : MvPolynomial.X i - MvPolynomial.C (x i) ∈
      MvPolynomial.vanishingIdeal K {x} := by
    rw [MvPolynomial.mem_vanishingIdeal_singleton_iff]
    simp
  rw [hideal, MvPolynomial.mem_vanishingIdeal_singleton_iff] at hmem
  have hmem' : y i - x i = 0 := by
    simpa using hmem
  exact (sub_eq_zero.mp hmem').symm

/-- Arbitrary powers of the maximal ideals of two distinct affine points are coprime. -/
theorem isCoprime_pow_vanishingIdeal_singleton
    {K σ : Type*} [Field K] {x y : σ → K} (hxy : x ≠ y) (m n : ℕ) :
    IsCoprime
      (MvPolynomial.vanishingIdeal K {x} ^ m)
      (MvPolynomial.vanishingIdeal K {y} ^ n) := by
  exact (Ideal.isCoprime_of_isMaximal
    (vanishingIdeal_singleton_ne_of_ne hxy)).pow

/-- **Finite multivariate Hermite CRT.**  At finitely many pairwise distinct affine points, one
multivariable polynomial realizes every prescribed local polynomial class modulo an arbitrary
power of the corresponding point ideal. -/
theorem exists_mvPolynomial_sub_mem_pow_vanishingIdeal_singleton
    {K σ ι : Type*} [Field K] [Finite ι]
    (w : ι → σ → K) (hw : Function.Injective w)
    (m : ι → ℕ) (target : ι → MvPolynomial σ K) :
    ∃ P : MvPolynomial σ K, ∀ i,
      P - target i ∈ MvPolynomial.vanishingIdeal K {w i} ^ m i := by
  let I : ι → Ideal (MvPolynomial σ K) := fun i =>
    MvPolynomial.vanishingIdeal K {w i} ^ m i
  have hI : Pairwise (IsCoprime on I) := by
    intro i j hij
    exact isCoprime_pow_vanishingIdeal_singleton (hw.ne hij) (m i) (m j)
  simpa only [I] using Ideal.exists_forall_sub_mem_ideal hI target

end

end GaloisForLFunctions.HTGeometry
