import GaloisForLFunctions.HTGeometry.CountableAlgebraicLocusDichotomy
import GaloisForLFunctions.HTGeometry.DirectionalKaehlerPolynomialLocus

/-!
# Complex affine directional finite-law dichotomy

The homogeneous equations for every finite directional Kähler locus are assembled into a
countable polynomial family.  The Baire alternative then gives an exact affine dichotomy: either
one finite jet order is dependent in every direction, or the complete algebraically independent
directional jet tower occurs on a dense residual set.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial Topology

variable {k K L ι : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra K L] [Algebra k L] [IsScalarTower k K L]
  [CharZero K] [Fintype ι]

/-- The order-`n` directional finite-law locus in affine law coordinates. -/
def directionalFiniteLawLocus
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) : Set (ι → k) :=
  {c | ¬ AlgebraicIndependent K
    (fun j : Fin (n + 1) => directionalJet δ c j x)}

/-- Every finite-law locus is the common zero set of a finite family of scalar polynomials. -/
theorem exists_directionalFiniteLawPolynomialFinset
    (δ : ι → Derivation k L L) (x : L) (n : ℕ) :
    ∃ P : Finset (MvPolynomial ι k),
      ∀ c : ι → k,
        (∀ p ∈ P, MvPolynomial.eval c p = 0) ↔
          c ∈ directionalFiniteLawLocus (K := K) δ x n := by
  classical
  obtain ⟨r, Q, hQ, hzero⟩ :=
    exists_directionalFiniteLawPolynomials (K := K) δ x n
  let P : Finset (MvPolynomial ι k) := Finset.univ.image Q
  refine ⟨P, ?_⟩
  intro c
  change (∀ p ∈ P, MvPolynomial.eval c p = 0) ↔
    ¬ AlgebraicIndependent K
      (fun j : Fin (n + 1) => directionalJet δ c j x)
  rw [← hzero c]
  constructor
  · intro hc j
    exact hc (Q j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  · intro hc p hp
    rcases Finset.mem_image.mp hp with ⟨j, hj, rfl⟩
    exact hc j

/-- The complex finite-law loci admit one countable family of finite polynomial presentations. -/
theorem exists_directionalFiniteLawPolynomialFamily
    {K L ι : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra K L] [Algebra ℂ L] [IsScalarTower ℂ K L]
    [CharZero K] [Fintype ι]
    (δ : ι → Derivation ℂ L L) (x : L) :
    ∃ P : ℕ → Finset (MvPolynomial ι ℂ),
      ∀ n, finitePolynomialZeroLocus (P n) =
        directionalFiniteLawLocus (K := K) δ x n := by
  choose P hP using fun n =>
    exists_directionalFiniteLawPolynomialFinset (K := K) δ x n
  refine ⟨P, ?_⟩
  intro n
  ext c
  exact hP n c

/-- **Complex affine directional dichotomy.**  Either one finite order is dependent in every law
direction, or directions whose complete jet towers are algebraically independent form a dense
residual subset of affine law-coordinate space. -/
theorem complexDirectionalFiniteLaw_collapse_or_denseResidual
    {K L ι : Type*} [Field K] [Field L]
    [Algebra ℂ K] [Algebra K L] [Algebra ℂ L] [IsScalarTower ℂ K L]
    [CharZero K] [Fintype ι]
    (δ : ι → Derivation ℂ L L) (x : L) :
    (∃ N, directionalFiniteLawLocus (K := K) δ x N = Set.univ) ∨
      (Dense {c : ι → ℂ |
        AlgebraicIndependent K (fun n : ℕ => directionalJet δ c n x)} ∧
        {c : ι → ℂ |
          AlgebraicIndependent K (fun n : ℕ => directionalJet δ c n x)} ∈
            residual (ι → ℂ)) := by
  obtain ⟨P, hP⟩ :=
    exists_directionalFiniteLawPolynomialFamily (K := K) δ x
  rcases finitePolynomialZeroLoci_collapse_or_denseResidual P with hcollapse | hgeneric
  · left
    obtain ⟨N, hN⟩ := hcollapse
    exact ⟨N, by rw [← hP N, hN]⟩
  · right
    have hset :
        {c : ι → ℂ | ∀ n, c ∉ finitePolynomialZeroLocus (P n)} =
          {c : ι → ℂ |
            AlgebraicIndependent K (fun n : ℕ => directionalJet δ c n x)} := by
      ext c
      change (∀ n, c ∉ finitePolynomialZeroLocus (P n)) ↔
        AlgebraicIndependent K (fun n : ℕ => directionalJet δ c n x)
      rw [algebraicIndependent_nat_iff_initialSegments]
      constructor
      · intro h n
        by_contra hdep
        apply h n
        rw [hP n]
        exact hdep
      · intro h n hc
        rw [hP n] at hc
        exact hc (h n)
    simpa [hset] using hgeneric

end

end GaloisForLFunctions.HTGeometry
