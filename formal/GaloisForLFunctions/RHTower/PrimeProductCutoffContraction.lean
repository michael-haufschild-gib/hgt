import GaloisForLFunctions.HTGeometry.KoszulCartanContraction
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

/-!
# Prime-product cutoffs admit a contraction after doubling

The degree `k` chains are the exterior power on finitely supported prime-labelled vectors.
A cutoff retains the span of atoms whose prime product is at most `N`; repeated vertices vanish
in the exterior power. The augmented boundary removes one vertex, so it preserves that cutoff.
Adjoining a prime `p` increases the product by at most `p`, and the Cartan identity provides a
chain contraction. In particular every reduced cycle at cutoff `N` bounds at cutoff `2 * N`.

The unweighted statement holds over any commutative ring. For the actual Dirichlet weights
`p ^ (-s)`, the contraction is `2 ^ s` times adjoining prime two, for every complex `s`.
Both versions include exterior degree zero, corresponding to the empty augmented face.

These are exact finite-support statements. They impose no convergence condition, bound no birth
counts or analytic completion, and supply no zeta-zero correspondence or location theorem.
-/

open scoped BigOperators
open GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

variable (R : Type*) [CommRing R]

/-- Exterior chains on the free module with prime-labelled basis. -/
abbrev PrimeChainSpace (k : ℕ) := ⋀[R]^k (Nat.Primes →₀ R)

/-- An ordered prime tuple gives an alternating chain atom. -/
def primeChainAtom {k : ℕ} (v : Fin k → Nat.Primes) : PrimeChainSpace R k :=
  exteriorPower.ιMulti R k (fun i => Finsupp.single (v i) 1)

/-- The span of atoms with multiplicative support at most the cutoff. -/
def primeChainCutoff (k N : ℕ) : Submodule R (PrimeChainSpace R k) :=
  Submodule.span R {x | ∃ v : Fin k → Nat.Primes,
    (∏ i, (v i : ℕ)) ≤ N ∧ x = primeChainAtom R v}

/-- The unweighted boundary functional sends every prime basis vector to one. -/
def primeChainAugmentation : (Nat.Primes →₀ R) →ₗ[R] R :=
  Finsupp.linearCombination R (fun _ => (1 : R))

@[simp] theorem primeChainAugmentation_single (p : Nat.Primes) :
    primeChainAugmentation R (Finsupp.single p 1) = 1 := by
  simp [primeChainAugmentation]

/-- The reduced boundary, including the map to the empty face. -/
abbrev primeChainBoundary (k : ℕ) : PrimeChainSpace R (k + 1) →ₗ[R] PrimeChainSpace R k :=
  physicalKoszulDifferential k (primeChainAugmentation R)

/-- Adjoin one prime as the first exterior vertex. -/
abbrev primeChainCone (k : ℕ) (p : Nat.Primes) :
    PrimeChainSpace R k →ₗ[R] PrimeChainSpace R (k + 1) :=
  wedgeLeft k (Finsupp.single p (1 : R))

theorem primeChainCone_atom {k : ℕ} (p : Nat.Primes) (v : Fin k → Nat.Primes) :
    primeChainCone R k p (primeChainAtom R v) = primeChainAtom R (Fin.cons p v) := by
  rw [primeChainAtom, wedgeLeft_ιMulti]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> simp

/-- Adjoining a prime has an explicit multiplicative cutoff cost. -/
theorem primeChainCone_cutoff (k N : ℕ) (p : Nat.Primes) :
    primeChainCutoff R k N ≤
      (primeChainCutoff R (k + 1) (p * N)).comap (primeChainCone R k p) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨v, hv, rfl⟩
  change primeChainCone R k p (primeChainAtom R v) ∈ primeChainCutoff R (k + 1) (p * N)
  rw [primeChainCone_atom]
  apply Submodule.subset_span
  refine ⟨Fin.cons p v, ?_, rfl⟩
  simpa only [Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ] using
    Nat.mul_le_mul_left (p : ℕ) hv

theorem primeChainBoundary_atom {k : ℕ} (v : Fin (k + 1) → Nat.Primes) :
    primeChainBoundary R k (primeChainAtom R v) =
      ∑ i : Fin (k + 1), ((-1 : ℤ) ^ (i : ℕ)) •
        primeChainAtom R (fun j => v (i.succAbove j)) := by
  unfold primeChainAtom primeChainBoundary
  rw [physicalKoszulDifferential_ιMulti]
  apply Finset.sum_congr rfl
  intro i _
  rw [primeChainAugmentation_single, one_smul]
  rfl

/-- Every contraction functional preserves the product cutoff: deletion only lowers it. -/
theorem primeChainDifferential_cutoff
    (phi : (Nat.Primes →₀ R) →ₗ[R] R) (k N : ℕ) :
    primeChainCutoff R (k + 1) N ≤
      (primeChainCutoff R k N).comap (physicalKoszulDifferential k phi) := by
  refine Submodule.span_le.mpr ?_
  rintro x ⟨v, hv, rfl⟩
  change physicalKoszulDifferential k phi (primeChainAtom R v) ∈ primeChainCutoff R k N
  rw [primeChainAtom, physicalKoszulDifferential_ιMulti]
  apply Submodule.sum_mem
  intro i _
  refine (primeChainCutoff R k N).toAddSubgroup.zsmul_mem ?_ _
  apply Submodule.smul_mem
  apply Submodule.subset_span
  refine ⟨fun j => v (i.succAbove j), ?_, rfl⟩
  calc
    (∏ j, (v (i.succAbove j) : ℕ)) ≤
        (v i : ℕ) * ∏ j, (v (i.succAbove j) : ℕ) := by
      simpa only [one_mul] using Nat.mul_le_mul_right
        (∏ j, (v (i.succAbove j) : ℕ)) (v i).property.one_lt.le
    _ = ∏ j, (v j : ℕ) := (Fin.prod_univ_succAbove (fun j => (v j : ℕ)) i).symm
    _ ≤ N := hv

theorem primeChainBoundary_cutoff (k N : ℕ) :
    primeChainCutoff R (k + 1) N ≤
      (primeChainCutoff R k N).comap (primeChainBoundary R k) :=
  primeChainDifferential_cutoff R (primeChainAugmentation R) k N

theorem primeChainBoundary_sq (k : ℕ) :
    (primeChainBoundary R k).comp (primeChainBoundary R (k + 1)) = 0 :=
  physicalKoszulDifferential_sq k (primeChainAugmentation R)

theorem primeChainCone_contracts (k : ℕ) (p : Nat.Primes) :
    (primeChainBoundary R (k + 1)).comp (primeChainCone R (k + 1) p) +
      (primeChainCone R k p).comp (primeChainBoundary R k) = LinearMap.id := by
  simpa only [primeChainAugmentation_single, one_smul] using
    koszul_cartan_succ k (primeChainAugmentation R) (Finsupp.single p (1 : R))

/-- Every reduced cycle has an explicit filling by twice its cutoff, over any commutative ring. -/
theorem primeChainCutoff_cycle_bounds_in_double (k N : ℕ)
    (x : ↥(primeChainCutoff R (k + 1) N ⊓ (primeChainBoundary R k).ker)) :
    ∃ y : primeChainCutoff R (k + 2) (2 * N),
      primeChainBoundary R (k + 1) y = (x : PrimeChainSpace R (k + 1)) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  refine ⟨⟨primeChainCone R (k + 1) p x, primeChainCone_cutoff R _ N p x.property.1⟩, ?_⟩
  have h := LinearMap.congr_fun (primeChainCone_contracts R k p) x
  have hx : primeChainBoundary R k x = 0 := x.property.2
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hx, map_zero, add_zero] using h

theorem primeChainCone_contracts_zero (p : Nat.Primes) :
    (primeChainBoundary R 0).comp (primeChainCone R 0 p) = LinearMap.id := by
  simpa only [primeChainAugmentation_single, one_smul] using
    koszul_cartan_zero_map (primeChainAugmentation R) (Finsupp.single p (1 : R))

/-- The same filling statement includes the augmented empty-face degree. -/
theorem primeChainCutoff_zero_bounds_in_double (N : ℕ)
    (x : primeChainCutoff R 0 N) :
    ∃ y : primeChainCutoff R 1 (2 * N),
      primeChainBoundary R 0 y = (x : PrimeChainSpace R 0) := by
  let p : Nat.Primes := ⟨2, Nat.prime_two⟩
  refine ⟨⟨primeChainCone R 0 p x, primeChainCone_cutoff R 0 N p x.property⟩, ?_⟩
  exact LinearMap.congr_fun (primeChainCone_contracts_zero R p) x

/-- Literal complex Dirichlet weights on the prime basis. -/
def dirichletPrimeChainFunctional (s : ℂ) : (Nat.Primes →₀ ℂ) →ₗ[ℂ] ℂ :=
  Finsupp.linearCombination ℂ (fun p : Nat.Primes => (p : ℂ) ^ (-s))

abbrev dirichletPrimeChainBoundary (k : ℕ) (s : ℂ) :
    PrimeChainSpace ℂ (k + 1) →ₗ[ℂ] PrimeChainSpace ℂ k :=
  physicalKoszulDifferential k (dirichletPrimeChainFunctional s)

/-- Invert the nonzero prime-two weight before adjoining the prime-two vertex. -/
def dirichletPrimeChainCone (k : ℕ) (s : ℂ) :
    PrimeChainSpace ℂ k →ₗ[ℂ] PrimeChainSpace ℂ (k + 1) :=
  (2 : ℂ) ^ s • primeChainCone ℂ k ⟨2, Nat.prime_two⟩

private theorem dirichletPrimeChainFunctional_two_unit (s : ℂ) :
    (2 : ℂ) ^ s * dirichletPrimeChainFunctional s
      (Finsupp.single (⟨2, Nat.prime_two⟩ : Nat.Primes) 1) = 1 := by
  simp only [dirichletPrimeChainFunctional, Finsupp.linearCombination_single, one_smul]
  change (2 : ℂ) ^ s * (2 : ℂ) ^ (-s) = 1
  rw [← Complex.cpow_add _ _ (two_ne_zero : (2 : ℂ) ≠ 0), add_neg_cancel,
    Complex.cpow_zero]

theorem dirichletPrimeChainBoundary_cutoff (s : ℂ) (k N : ℕ) :
    primeChainCutoff ℂ (k + 1) N ≤
      (primeChainCutoff ℂ k N).comap (dirichletPrimeChainBoundary k s) :=
  primeChainDifferential_cutoff ℂ (dirichletPrimeChainFunctional s) k N

theorem dirichletPrimeChainBoundary_sq (s : ℂ) (k : ℕ) :
    (dirichletPrimeChainBoundary k s).comp (dirichletPrimeChainBoundary (k + 1) s) = 0 :=
  physicalKoszulDifferential_sq k (dirichletPrimeChainFunctional s)

theorem dirichletPrimeChainCone_cutoff (s : ℂ) (k N : ℕ) :
    primeChainCutoff ℂ k N ≤
      (primeChainCutoff ℂ (k + 1) (2 * N)).comap (dirichletPrimeChainCone k s) := by
  intro x hx
  have h : primeChainCone ℂ k ⟨2, Nat.prime_two⟩ x ∈ primeChainCutoff ℂ (k + 1) (2 * N) :=
    primeChainCone_cutoff ℂ k N ⟨2, Nat.prime_two⟩ hx
  change (2 : ℂ) ^ s • primeChainCone ℂ k ⟨2, Nat.prime_two⟩ x ∈
    primeChainCutoff ℂ (k + 1) (2 * N)
  exact Submodule.smul_mem _ _ h

theorem dirichletPrimeChainCone_contracts (s : ℂ) (k : ℕ) :
    (dirichletPrimeChainBoundary (k + 1) s).comp (dirichletPrimeChainCone (k + 1) s) +
      (dirichletPrimeChainCone k s).comp (dirichletPrimeChainBoundary k s) = LinearMap.id :=
  koszul_contraction k (dirichletPrimeChainFunctional s)
    (Finsupp.single (⟨2, Nat.prime_two⟩ : Nat.Primes) 1)
    (dirichletPrimeChainFunctional_two_unit s)

/-- Dirichlet weighting preserves the explicit doubled-cutoff filling at every complex parameter. -/
theorem dirichletPrimeChainCutoff_cycle_bounds_in_double (s : ℂ) (k N : ℕ)
    (x : ↥(primeChainCutoff ℂ (k + 1) N ⊓ (dirichletPrimeChainBoundary k s).ker)) :
    ∃ y : primeChainCutoff ℂ (k + 2) (2 * N),
      dirichletPrimeChainBoundary (k + 1) s y = (x : PrimeChainSpace ℂ (k + 1)) := by
  refine ⟨⟨dirichletPrimeChainCone (k + 1) s x,
    dirichletPrimeChainCone_cutoff s _ N x.property.1⟩, ?_⟩
  have h := LinearMap.congr_fun (dirichletPrimeChainCone_contracts s k) x
  have hx : dirichletPrimeChainBoundary k s x = 0 := x.property.2
  simpa only [LinearMap.add_apply, LinearMap.comp_apply, LinearMap.id_apply,
    hx, map_zero, add_zero] using h

theorem dirichletPrimeChainCone_contracts_zero (s : ℂ) :
    (dirichletPrimeChainBoundary 0 s).comp (dirichletPrimeChainCone 0 s) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  have h := LinearMap.congr_fun
    (koszul_cartan_zero_map (dirichletPrimeChainFunctional s)
      (Finsupp.single (⟨2, Nat.prime_two⟩ : Nat.Primes) 1)) x
  simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
  change dirichletPrimeChainBoundary 0 s
    ((2 : ℂ) ^ s • primeChainCone ℂ 0 ⟨2, Nat.prime_two⟩ x) = x
  rw [map_smul, h, smul_smul, dirichletPrimeChainFunctional_two_unit, one_smul]

/-- The Dirichlet-weighted filling also covers the empty augmented face. -/
theorem dirichletPrimeChainCutoff_zero_bounds_in_double (s : ℂ) (N : ℕ)
    (x : primeChainCutoff ℂ 0 N) :
    ∃ y : primeChainCutoff ℂ 1 (2 * N),
      dirichletPrimeChainBoundary 0 s y = (x : PrimeChainSpace ℂ 0) := by
  refine ⟨⟨dirichletPrimeChainCone 0 s x,
    dirichletPrimeChainCone_cutoff s 0 N x.property⟩, ?_⟩
  exact LinearMap.congr_fun (dirichletPrimeChainCone_contracts_zero s) x

end RHTower
