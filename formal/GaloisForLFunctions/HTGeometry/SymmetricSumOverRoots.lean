import Mathlib

/-!
# Integer polynomial sums over the complex roots of a monic integer polynomial

For a monic `h : ℤ[X]` and any `g : ℤ[X]`, the sum of `g` over the complex roots of `h`, counted with
multiplicity, is an integer.  The sum is a symmetric integer polynomial in the roots, hence an
integer polynomial in their elementary symmetric functions, which Vieta identifies with the
coefficients of `h`.

This is the integrality input of the Lindemann–Weierstrass argument: the quantity produced by the
analytic estimate is only useful once it is known to be a rational integer.

* `exists_index_of_multiset` — index a multiset of known cardinality by `Fin n`.
* `sumEvalPoly`, `isSymmetric_sumEvalPoly` — the symmetric polynomial `∑ᵢ g(Xᵢ)`.
* `sum_aeval_aroots_isInt` — the sum over the roots is an integer.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Finset MvPolynomial

/-- A multiset of cardinality `n` is the image of a family indexed by `Fin n`. -/
theorem exists_index_of_multiset {α : Type*} (s : Multiset α) (n : ℕ)
    (hcard : Multiset.card s = n) :
    ∃ ρ : Fin n → α, s = Multiset.map ρ (Finset.univ : Finset (Fin n)).val := by
  subst hcard
  have hlen : s.toList.length = Multiset.card s := Multiset.length_toList s
  refine ⟨fun i => s.toList.get (Fin.cast hlen.symm i), ?_⟩
  rw [Finset.val_univ_fin, Multiset.map_coe]
  conv_lhs => rw [← Multiset.coe_toList s]
  congr 1
  refine List.ext_getElem ?_ ?_
  · simp [hlen]
  · intro k hk1 hk2
    simp

/-- The symmetric polynomial `∑ᵢ g(Xᵢ)`. -/
noncomputable def sumEvalPoly (n : ℕ) (g : ℤ[X]) : MvPolynomial (Fin n) ℤ :=
  ∑ i : Fin n, Polynomial.aeval (MvPolynomial.X i) g

theorem isSymmetric_sumEvalPoly (n : ℕ) (g : ℤ[X]) : (sumEvalPoly n g).IsSymmetric := by
  intro e
  rw [sumEvalPoly, map_sum]
  have hcomp : ∀ i : Fin n,
      (MvPolynomial.rename e)
          (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) g)
        = Polynomial.aeval (MvPolynomial.X (e i) : MvPolynomial (Fin n) ℤ) g := by
    intro i
    have hEq : (MvPolynomial.rename (R := ℤ) e).comp
          (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))
        = Polynomial.aeval (MvPolynomial.X (e i) : MvPolynomial (Fin n) ℤ) :=
      Polynomial.algHom_ext_iff.mpr (by simp)
    exact congrArg (fun F : Polynomial ℤ →ₐ[ℤ] MvPolynomial (Fin n) ℤ => F g) hEq
  rw [Finset.sum_congr rfl fun i _ => hcomp i]
  exact Fintype.sum_equiv e _ _ fun i => rfl

theorem aeval_sumEvalPoly {n : ℕ} (g : ℤ[X]) (ρ : Fin n → ℂ) :
    MvPolynomial.aeval ρ (sumEvalPoly n g) = ∑ i : Fin n, Polynomial.aeval (ρ i) g := by
  rw [sumEvalPoly, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hEq : (MvPolynomial.aeval ρ).comp
        (Polynomial.aeval (MvPolynomial.X i : MvPolynomial (Fin n) ℤ))
      = Polynomial.aeval (ρ i) :=
    Polynomial.algHom_ext_iff.mpr (by simp)
  exact congrArg (fun F : Polynomial ℤ →ₐ[ℤ] ℂ => F g) hEq

/-- **The sum of an integer polynomial over the complex roots of a monic integer polynomial is an
integer.** -/
theorem sum_aeval_aroots_isInt {h : ℤ[X]} (hm : h.Monic) (g : ℤ[X]) :
    ∃ z : ℤ, ((h.aroots ℂ).map (fun r => Polynomial.aeval r g)).sum = (z : ℂ) := by
  classical
  set n := h.natDegree with hn
  have hmapmonic : (h.map (algebraMap ℤ ℂ)).Monic := Monic.map (algebraMap ℤ ℂ) hm
  have hmapdeg : (h.map (algebraMap ℤ ℂ)).natDegree = n := hm.natDegree_map (algebraMap ℤ ℂ)
  have hcardmap : Multiset.card (h.aroots ℂ) = (h.map (algebraMap ℤ ℂ)).natDegree := by
    rw [Polynomial.aroots]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  have hcard : Multiset.card (h.aroots ℂ) = n := by rw [hcardmap, hmapdeg]
  obtain ⟨ρ, hρ⟩ := exists_index_of_multiset (h.aroots ℂ) n hcard
  have hsum : ((h.aroots ℂ).map (fun r => Polynomial.aeval r g)).sum
      = ∑ i : Fin n, Polynomial.aeval (ρ i) g := by
    rw [hρ, Multiset.map_map]
    rfl
  obtain ⟨Q, hQ⟩ := MvPolynomial.esymmAlgHom_surjective (σ := Fin n) ℤ
    (le_of_eq (Fintype.card_fin n)) ⟨sumEvalPoly n g, isSymmetric_sumEvalPoly n g⟩
  have hQ' : MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) ℤ ((j : ℕ) + 1)) Q
      = sumEvalPoly n g := by
    have hv := congrArg Subtype.val hQ
    simpa [MvPolynomial.esymmAlgHom_apply] using hv
  set c : Fin n → ℤ := fun j => (-1) ^ ((j : ℕ) + 1) * h.coeff (n - ((j : ℕ) + 1)) with hc
  have hesymm : ∀ j : Fin n, ((h.aroots ℂ).esymm ((j : ℕ) + 1)) = ((c j : ℤ) : ℂ) := by
    intro j
    have hle : n - ((j : ℕ) + 1) ≤ (h.map (algebraMap ℤ ℂ)).natDegree := by
      rw [hmapdeg]; omega
    have hV := Polynomial.coeff_eq_esymm_roots_of_card
      (p := h.map (algebraMap ℤ ℂ)) hcardmap hle
    have hidx : (h.map (algebraMap ℤ ℂ)).natDegree - (n - ((j : ℕ) + 1)) = (j : ℕ) + 1 := by
      rw [hmapdeg]; omega
    rw [hmapmonic.leadingCoeff, one_mul, hidx] at hV
    have hco : (h.map (algebraMap ℤ ℂ)).coeff (n - ((j : ℕ) + 1))
        = ((h.coeff (n - ((j : ℕ) + 1)) : ℤ) : ℂ) := by
      simp [Polynomial.coeff_map]
    rw [hco] at hV
    rw [Polynomial.aroots, hc]
    push_cast
    rw [hV, ← mul_assoc, ← mul_pow]
    norm_num
  refine ⟨MvPolynomial.aeval c Q, ?_⟩
  have hcomp : (MvPolynomial.aeval ρ).comp
      (MvPolynomial.aeval (fun j : Fin n => MvPolynomial.esymm (Fin n) ℤ ((j : ℕ) + 1)))
      = MvPolynomial.aeval (fun j : Fin n => ((c j : ℤ) : ℂ)) := by
    refine MvPolynomial.algHom_ext fun j => ?_
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X]
    rw [MvPolynomial.aeval_esymm_eq_multiset_esymm (Fin n) ℤ ((j : ℕ) + 1) ρ, ← hρ, hesymm j]
  have hcast : (MvPolynomial.aeval (fun j : Fin n => ((c j : ℤ) : ℂ))) Q
      = ((MvPolynomial.aeval c Q : ℤ) : ℂ) := by
    have hEq : (MvPolynomial.aeval (fun j : Fin n => ((c j : ℤ) : ℂ)) :
          MvPolynomial (Fin n) ℤ →ₐ[ℤ] ℂ)
        = (Algebra.ofId ℤ ℂ).comp (MvPolynomial.aeval c) := by
      refine MvPolynomial.algHom_ext fun j => ?_
      simp
    rw [hEq]
    simp
  rw [hsum, ← aeval_sumEvalPoly g ρ, ← hQ', ← AlgHom.comp_apply, hcomp, hcast]

end GaloisForLFunctions.HTGeometry
