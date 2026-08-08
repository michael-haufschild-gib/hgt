/-
# A symmetric integer polynomial of a full conjugate set is a rational integer

Let `β₁, …, β_d ∈ ℂ` be the complete root set of a monic `μ ∈ ℤ[X]` — that is,
`∏_j (X − β_j) = μ` after mapping `μ` into `ℂ[X]`.  For any **symmetric** polynomial
`φ ∈ ℤ[X₁, …, X_d]`, the value `φ(β₁, …, β_d)` is a rational integer.

The mechanism is the fundamental theorem of symmetric polynomials.  A symmetric `φ` is a genuine
integer polynomial `q` in the elementary symmetric functions `e₁, …, e_d`
(`MvPolynomial.esymmAlgHom_fin_bijective`).  Evaluated at the roots, `e_k(β)` is — up to sign — the
coefficient `μ.coeff (d − k)` (Vieta, `Multiset.prod_X_sub_C_coeff`), an integer because `μ ∈ ℤ[X]`.
Hence `φ(β) = q(e₁(β), …, e_d(β))` is `q` applied to integers, so it lies in `ℤ`.

This is the general symmetric-function integrality behind transcendence estimates over number fields:
it collapses any Galois-symmetric integer expression in a full conjugate orbit to a single honest
integer.  The field-trace statement `∑_{r} h(r) ∈ ℤ` (`ConjugateTraceIntegral`) is the power-sum
special case `φ = ∑_j h(Xⱼ)`; the weighted orbit sums that arise when a single-conjugate exponential
relation is producted into a symmetric one are the general case handled here.
-/
import Mathlib

open Polynomial MvPolynomial
open scoped Classical

namespace GaloisForLFunctions
namespace RHTower

/-- **A symmetric integer polynomial of a complete conjugate set is an integer.**  If `β : Fin d → ℂ`
enumerates the roots of a monic `μ ∈ ℤ[X]` (so `∏_j (X − β j) = μ.map (ℤ → ℂ)`) and `φ` is a symmetric
polynomial over `ℤ`, then `φ(β) ∈ ℤ`.  Proved by the fundamental theorem of symmetric polynomials:
`φ` is an integer polynomial in the elementary symmetric functions, whose values on the roots are the
integer coefficients of `μ` (Vieta). -/
theorem symmetric_aeval_conj_isInt {d : ℕ} (μ : ℤ[X]) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ))
    (φ : MvPolynomial (Fin d) ℤ) (hφ : φ.IsSymmetric) :
    ∃ m : ℤ, MvPolynomial.aeval β φ = (m : ℂ) := by
  set s : Multiset ℂ := Multiset.map β Finset.univ.val with hs
  have hscard : s.card = d := by simp [hs]
  set E : Fin d → ℤ := fun i => (-1 : ℤ) ^ ((i : ℕ) + 1) * μ.coeff (d - ((i : ℕ) + 1)) with hEdef
  -- Each elementary symmetric function of `β` is the integer `E i`.
  have hE : ∀ i : Fin d,
      MvPolynomial.aeval β (MvPolynomial.esymm (Fin d) ℤ ((i : ℕ) + 1)) = ((E i : ℤ) : ℂ) := by
    intro i
    have hn : ((i : ℕ) + 1 : ℕ) ≤ d := i.2
    have hk : d - ((i : ℕ) + 1) ≤ s.card := by rw [hscard]; omega
    have hprod : (Multiset.map (fun t => Polynomial.X - Polynomial.C t) s).prod
        = μ.map (Int.castRingHom ℂ) := by rw [hs, Multiset.map_map]; exact hβ
    have hcoeff := Multiset.prod_X_sub_C_coeff s hk
    rw [hprod, Polynomial.coeff_map, hscard] at hcoeff
    have hsub : d - (d - ((i : ℕ) + 1)) = (i : ℕ) + 1 := by omega
    rw [hsub] at hcoeff
    rw [aeval_esymm_eq_multiset_esymm (Fin d) ℤ ((i : ℕ) + 1) β]
    have hunit : ((-1 : ℂ)) ^ ((i : ℕ) + 1) * ((-1 : ℂ)) ^ ((i : ℕ) + 1) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    have hsol : s.esymm ((i : ℕ) + 1)
        = ((-1 : ℂ)) ^ ((i : ℕ) + 1) * ((Int.castRingHom ℂ) (μ.coeff (d - ((i : ℕ) + 1)))) := by
      rw [hcoeff, ← mul_assoc, hunit, one_mul]
    rw [hsol]
    simp only [hEdef, Int.coe_castRingHom]
    push_cast; ring
  -- Fundamental theorem of symmetric polynomials: `φ` is a polynomial in the `esymm`.
  obtain ⟨q, hq⟩ := (esymmAlgHom_fin_bijective ℤ d).2
    ⟨φ, (mem_symmetricSubalgebra φ).mpr hφ⟩
  have hφq : MvPolynomial.aeval (fun i : Fin d => MvPolynomial.esymm (Fin d) ℤ ((i : ℕ) + 1)) q = φ := by
    have h1 : ((esymmAlgHom (Fin d) ℤ d q : symmetricSubalgebra (Fin d) ℤ) : MvPolynomial (Fin d) ℤ)
        = φ := by rw [hq]
    rwa [esymmAlgHom_apply] at h1
  -- Evaluate at `β` and collapse to the integer `aeval E q`.
  refine ⟨MvPolynomial.aeval E q, ?_⟩
  rw [← hφq, ← AlgHom.comp_apply, comp_aeval]
  simp_rw [hE]
  rw [show (fun i : Fin d => ((E i : ℤ) : ℂ)) = fun i : Fin d => (Algebra.ofId ℤ ℂ) (E i) from rfl,
      ← comp_aeval, AlgHom.comp_apply]
  rfl

/-- **The subset-sum polynomial has integer coefficients.**  If `β : Fin d → ℂ` is the complete root
set of a monic `μ ∈ ℤ[X]`, then the polynomial whose roots are all the subset sums
`σ_T = ∑_{j ∈ T} β j` (`T` ranging over subsets of the index set) lifts to `ℤ[X]`.  Each coefficient is
a symmetric integer polynomial in the `β j` — the product `∏_T (X − ∑_{j∈T} X_j)` over `ℤ`-variables
is invariant under permuting the variables — hence lands in `ℤ` by `symmetric_aeval_conj_isInt`.  This
is the "composed sum stays integral" fact underlying the symmetrisation of a single-conjugate
exponential relation into a Galois-stable one. -/
theorem subsetSum_poly_lifts {d : ℕ} (μ : ℤ[X]) (β : Fin d → ℂ)
    (hβ : (Multiset.map (fun j => Polynomial.X - Polynomial.C (β j)) Finset.univ.val).prod
        = μ.map (Int.castRingHom ℂ)) :
    (∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
        (Polynomial.X - Polynomial.C (∑ j ∈ T, β j)))
      ∈ Polynomial.lifts (Int.castRingHom ℂ) := by
  set R : Polynomial (MvPolynomial (Fin d) ℤ) :=
    ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset,
      (Polynomial.X - Polynomial.C (∑ j ∈ T, MvPolynomial.X (R := ℤ) j)) with hR
  have hsym : ∀ n, (R.coeff n).IsSymmetric := by
    intro n σ
    have hmap : R.map (MvPolynomial.rename σ).toRingHom = R := by
      rw [hR, Polynomial.map_prod]
      refine Finset.prod_nbij' (fun T => T.image σ) (fun T => T.image σ.symm) ?_ ?_ ?_ ?_ ?_
      · intro T _; simp
      · intro T _; simp
      · intro T _; simp [Finset.image_image]
      · intro T _; simp [Finset.image_image]
      · intro T _
        rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sum]
        congr 2
        rw [Finset.sum_image (fun a _ b _ h => σ.injective h)]
        exact Finset.sum_congr rfl (fun j _ => by simp [MvPolynomial.rename_X])
    calc MvPolynomial.rename σ (R.coeff n)
        = (R.map (MvPolynomial.rename σ).toRingHom).coeff n := by rw [Polynomial.coeff_map]; rfl
      _ = R.coeff n := by rw [hmap]
  have hmapβ : R.map (MvPolynomial.aeval β).toRingHom
      = ∏ T ∈ (Finset.univ : Finset (Fin d)).powerset, (Polynomial.X - Polynomial.C (∑ j ∈ T, β j)) := by
    rw [hR, Polynomial.map_prod]
    refine Finset.prod_congr rfl (fun T _ => ?_)
    rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C, map_sum]
    congr 2
    exact Finset.sum_congr rfl (fun j _ => by simp)
  rw [← hmapβ, Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_map]
  obtain ⟨m, hm⟩ := symmetric_aeval_conj_isInt μ β hβ (R.coeff n) (hsym n)
  refine ⟨m, ?_⟩
  show (Int.castRingHom ℂ) m = MvPolynomial.aeval β (R.coeff n)
  rw [hm]; simp

end RHTower
end GaloisForLFunctions
