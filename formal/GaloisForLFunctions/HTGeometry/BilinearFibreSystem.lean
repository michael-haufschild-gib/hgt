import GaloisForLFunctions.HTGeometry.UniversalFibreSystem

/-!
# The fibre's system in its bilinear form

Before elimination the compatibility equation is bilinear: the unknown jet and the unknown
reciprocal enter it linearly and only their product couples them.  Writing both as universal
polynomials over the unknown coefficients, the observation's conditions become the coefficients of
one polynomial identity, each of total degree at most two and of bidegree one in each group of
unknowns.

This is the form in which the count is the multihomogeneous Bezout number: eliminating to the jet
alone, as the square system does, raises the degrees and loses that structure.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K] {m n : ℕ}

/-- The universal unknown jet: a polynomial of degree below the first depth whose coefficients are
the first group of variables. -/
noncomputable def univA (K : Type*) [Field K] (m n : ℕ) :
    (MvPolynomial (Fin m ⊕ Fin n) K)[X] :=
  ∑ i : Fin m, Polynomial.C (MvPolynomial.X (Sum.inl i)) * Polynomial.X ^ (i : ℕ)

/-- The universal unknown reciprocal: the second group of variables. -/
noncomputable def univB (K : Type*) [Field K] (m n : ℕ) :
    (MvPolynomial (Fin m ⊕ Fin n) K)[X] :=
  ∑ j : Fin n, Polynomial.C (MvPolynomial.X (Sum.inr j)) * Polynomial.X ^ (j : ℕ)

/-- The `k`-th equation of the observation, before elimination: the `k`-th coefficient of the low
product against one. -/
noncomputable def bilinSysPoly (U V : K[X]) (m n k : ℕ) : MvPolynomial (Fin m ⊕ Fin n) K :=
  (criticalLowProduct (U.map (MvPolynomial.C : K →+* MvPolynomial (Fin m ⊕ Fin n) K))
      (V.map (MvPolynomial.C : K →+* MvPolynomial (Fin m ⊕ Fin n) K))
      (univA K m n) (univB K m n) - 1).coeff k

theorem univA_coeff (i : ℕ) :
    (univA K m n).coeff i
      = if h : i < m then MvPolynomial.X (Sum.inl ⟨i, h⟩) else 0 := by
  classical
  rw [univA, Polynomial.finsetSum_coeff]
  split_ifs with h
  · rw [Finset.sum_eq_single (⟨i, h⟩ : Fin m)]
    · simp
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
      exact fun hcon => hb (Fin.ext hcon.symm)
    · intro hcon
      exact absurd (Finset.mem_univ _) hcon
  · refine Finset.sum_eq_zero fun b _ => ?_
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg, mul_zero]
    intro hcon
    exact h (hcon ▸ b.2)

theorem degree_univA_lt : (univA K m n).degree < (m : ℕ) := by
  refine Polynomial.degree_lt_iff_coeff_zero _ _ |>.2 fun i hi => ?_
  rw [univA_coeff, dif_neg]
  intro hcon
  exact absurd hi (by exact_mod_cast (by omega : ¬ ((m : ℕ) : WithBot ℕ) ≤ (i : ℕ)))


/-! ## Specialising the bilinear system -/

section Specialise

variable {K : Type*} [Field K] {m n : ℕ}

/-- The jet determined by a point of affine space. -/
noncomputable def jetOfPoint (x : (Fin m ⊕ Fin n) → K) : K[X] :=
  ∑ i : Fin m, Polynomial.C (x (Sum.inl i)) * Polynomial.X ^ (i : ℕ)

/-- The reciprocal determined by a point of affine space. -/
noncomputable def recipOfPoint (x : (Fin m ⊕ Fin n) → K) : K[X] :=
  ∑ j : Fin n, Polynomial.C (x (Sum.inr j)) * Polynomial.X ^ (j : ℕ)

theorem map_univA (x : (Fin m ⊕ Fin n) → K) :
    (univA K m n).map (MvPolynomial.eval x) = jetOfPoint x := by
  rw [univA, jetOfPoint, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    MvPolynomial.eval_X]

theorem map_univB (x : (Fin m ⊕ Fin n) → K) :
    (univB K m n).map (MvPolynomial.eval x) = recipOfPoint x := by
  rw [univB, recipOfPoint, Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, Polynomial.map_X,
    MvPolynomial.eval_X]

theorem map_map_C (x : (Fin m ⊕ Fin n) → K) (P : K[X]) :
    (P.map (MvPolynomial.C : K →+* MvPolynomial (Fin m ⊕ Fin n) K)).map
        (MvPolynomial.eval x) = P := by
  rw [Polynomial.map_map]
  have hcomp : ((MvPolynomial.eval x).comp
      (MvPolynomial.C : K →+* MvPolynomial (Fin m ⊕ Fin n) K)) = RingHom.id K := by
    ext a
    simp
  rw [hcomp, Polynomial.map_id]

theorem map_criticalLowProduct {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    (U V A B : R[X]) :
    (criticalLowProduct U V A B).map φ
      = criticalLowProduct (U.map φ) (V.map φ) (A.map φ) (B.map φ) := by
  simp only [criticalLowProduct, Polynomial.map_add, Polynomial.map_mul]

/-- **Specialising the bilinear system at a point gives the observation's equation.** -/
theorem eval_bilinSysPoly (U V : K[X]) (x : (Fin m ⊕ Fin n) → K) (k : ℕ) :
    MvPolynomial.eval x (bilinSysPoly U V m n k)
      = (criticalLowProduct U V (jetOfPoint x) (recipOfPoint x) - 1).coeff k := by
  rw [bilinSysPoly, ← Polynomial.coeff_map, Polynomial.map_sub, Polynomial.map_one,
    map_criticalLowProduct, map_map_C, map_map_C, map_univA, map_univB]

end Specialise

end GaloisForLFunctions.HTGeometry
