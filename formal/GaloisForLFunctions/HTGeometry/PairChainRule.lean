import GaloisForLFunctions.HTGeometry.PairDegree
import GaloisForLFunctions.HTGeometry.CascadeChainRule

/-!
# The chain rule and the degree of the two-coordinate law

On the low subalgebra the two-coordinate law is the finite sum `δ f = ∑_(l ≤ m) (δ X_l)·∂_l f`, by
the corpus's chain rule for the free rational coordinate field.

The newest jet has degree `deg_1 p_(m−1)` in the newest coordinate — the degree of the placed
polynomial in its *second* variable — so the law does not raise that degree exactly when every
`p_j` is at most linear in its second variable.  That is the equation `f' = a(z) + b(z)·f`: linear
first order with polynomial coefficients, strictly larger than the family whose law is univariate.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable {p : ℕ → MvPolynomial (Fin 2) ℂ}

/-! ## The low subalgebra sits in a finitely generated subfield -/

theorem algebraMap_pairPoly_mem_freeCoordinateField {j : ℕ} {S : Set ℕ}
    (h0 : j ∈ S) (h1 : j + 1 ∈ S) (q : MvPolynomial (Fin 2) ℂ) :
    algebraMap (MvPolynomial ℕ ℂ) CascadeField (pairPoly q j) ∈ freeCoordinateField ℂ ℕ S := by
  induction q using MvPolynomial.induction_on with
  | C a =>
      rw [pairPoly_C]
      have hc : algebraMap (MvPolynomial ℕ ℂ) CascadeField (MvPolynomial.C a)
          = algebraMap ℂ CascadeField a := rfl
      rw [hc]
      exact (freeCoordinateField ℂ ℕ S).algebraMap_mem a
  | add q r hq hr =>
      rw [pairPoly_add, map_add]
      exact add_mem hq hr
  | mul_X q i hq =>
      rw [pairPoly_mul_X, map_mul]
      refine mul_mem hq ?_
      have hi : (i : ℕ) = 0 ∨ (i : ℕ) = 1 := by omega
      have hmem : (j + (i : ℕ)) ∈ S := by
        rcases hi with hi | hi
        · rw [hi]; simpa using h0
        · rw [hi]; exact h1
      exact IntermediateField.subset_adjoin _ _ ⟨j + (i : ℕ), hmem, rfl⟩

theorem pairLowSub_le_freeCoordinateField (p : ℕ → MvPolynomial (Fin 2) ℂ) (m : ℕ)
    {f : CascadeField} (h : f ∈ pairLowSub p m) :
    f ∈ freeCoordinateField ℂ ℕ (↑(Finset.range (m + 1)) : Set ℕ) := by
  have hle : pairLowSub p m
      ≤ (freeCoordinateField ℂ ℕ (↑(Finset.range (m + 1)) : Set ℕ)).toSubalgebra := by
    rw [pairLowSub]
    refine Algebra.adjoin_le ?_
    rintro x (⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩)
    · have hm : fx j ∈ freeCoordinateField ℂ ℕ (↑(Finset.range (m + 1)) : Set ℕ) :=
        IntermediateField.subset_adjoin _ _
          ⟨j, by simp only [Finset.coe_range, Set.mem_Iio]; omega, rfl⟩
      simpa using hm
    · have hm : (pairFactor (p j) j)⁻¹
          ∈ freeCoordinateField ℂ ℕ (↑(Finset.range (m + 1)) : Set ℕ) :=
        inv_mem (algebraMap_pairPoly_mem_freeCoordinateField
          (by simp only [Finset.coe_range, Set.mem_Iio]; omega)
          (by simp only [Finset.coe_range, Set.mem_Iio]; omega) (p j))
      simpa using hm
  exact hle h

/-- **The chain rule of the two-coordinate law.** -/
theorem pairDerivation_eq_sum {m : ℕ} {f : CascadeField} (h : f ∈ pairLowSub p m) :
    pairDerivation p f = ∑ l ∈ Finset.range (m + 1), pairJet p l * fpderiv l f := by
  have hmem := pairLowSub_le_freeCoordinateField p m h
  have hchain := freeCoordinate_chainRule (Finset.range (m + 1)) (pairDerivation p) hmem
  rw [hchain]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [fpderiv_eq_freeCoordinateDerivation]
  congr 1
  exact pairDerivation_fx p l

/-! ## The newest jet's degree -/

theorem topDegLE_pairFactor_top (n : ℕ) (q : MvPolynomial (Fin 2) ℂ) :
    TopDegLE (n + 1) ((MvPolynomial.degreeOf 1 q : ℤ)) (pairFactor q n) := by
  have h := topDegLE_algebraMap (n + 1) (pairPoly q n)
  refine TopDegLE.mono ?_ h
  exact_mod_cast degreeOf_pairPoly_top n q

/-- **The newest jet carries the second-variable degree of the last placed polynomial.** -/
theorem topDegLE_pairJet_top (n : ℕ) :
    TopDegLE (n + 1) ((MvPolynomial.degreeOf 1 (p n) : ℤ)) (pairJet p (n + 1)) := by
  rw [pairJet_succ]
  have h1 : TopDegLE (n + 1) 0 (pairJet p n) :=
    TopFree.topDegLE (topFree_pairJet (by omega))
  have hmul := TopDegLE.mul h1 (topDegLE_pairFactor_top n (p n))
  simpa using hmul

/-! ## The law does not raise the newest degree -/

/-- **A two-coordinate product law that is at most linear in the upper variable does not raise the
degree in the newest coordinate.** -/
theorem TopDegLE.pairDerivation {n : ℕ} {d : ℤ} {f : CascadeField}
    (hp : MvPolynomial.degreeOf 1 (p n) ≤ 1)
    (hmem : f ∈ pairLowSub p (n + 1)) (hf : TopDegLE (n + 1) d f) :
    TopDegLE (n + 1) d (pairDerivation p f) := by
  rw [pairDerivation_eq_sum hmem]
  refine topDegLE_sum _ _ fun l hl => ?_
  have hlm : l ≤ n + 1 := by
    have := Finset.mem_range.mp hl
    omega
  rcases eq_or_lt_of_le hlm with rfl | hlt
  · -- the newest jet: its degree is paid for by the coordinate derivative's drop
    have hjet : TopDegLE (n + 1) ((MvPolynomial.degreeOf 1 (p n) : ℤ)) (pairJet p (n + 1)) :=
      topDegLE_pairJet_top n
    have hder : TopDegLE (n + 1) (d - 1) (fpderiv (n + 1) f) := TopDegLE.fpderiv_top hf
    have hmul := TopDegLE.mul hjet hder
    refine TopDegLE.mono ?_ hmul
    have : ((MvPolynomial.degreeOf 1 (p n) : ℕ) : ℤ) ≤ 1 := by exact_mod_cast hp
    omega
  · -- a lower jet is free of the newest coordinate
    have hjet : TopFree (n + 1) (pairJet p l) := topFree_pairJet hlt
    have hder : TopDegLE (n + 1) d (fpderiv l f) := TopDegLE.fpderiv_of_ne (by omega) hf
    have hmul := TopDegLE.mul (TopFree.topDegLE hjet) hder
    refine TopDegLE.mono ?_ hmul
    omega

end GaloisForLFunctions.HTGeometry
