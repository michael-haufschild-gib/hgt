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


/-! ## The system is bilinear -/

section Bidegree

variable {K : Type*} [Field K] {m n : ℕ}

/-- Every coefficient of a polynomial has degree at most `d` in a chosen variable. -/
def CoeffDegreeOfLE {σ : Type*} (s : σ) (P : (MvPolynomial σ K)[X]) (d : ℕ) : Prop :=
  ∀ k, ((P.coeff k).degreeOf s) ≤ d

theorem degreeOf_neg_le {σ : Type*} (i : σ) (p : MvPolynomial σ K) {d : ℕ}
    (h : p.degreeOf i ≤ d) : (-p).degreeOf i ≤ d := by
  rw [MvPolynomial.degreeOf_le_iff] at h ⊢
  intro t ht
  exact h t (by rwa [MvPolynomial.support_neg] at ht)

theorem CoeffDegreeOfLE.add {σ : Type*} {s : σ} {P Q : (MvPolynomial σ K)[X]} {d : ℕ}
    (hP : CoeffDegreeOfLE s P d) (hQ : CoeffDegreeOfLE s Q d) :
    CoeffDegreeOfLE s (P + Q) d := by
  intro k
  rw [Polynomial.coeff_add]
  exact le_trans (MvPolynomial.degreeOf_add_le _ _ _) (max_le (hP k) (hQ k))

theorem CoeffDegreeOfLE.sub {σ : Type*} {s : σ} {P Q : (MvPolynomial σ K)[X]} {d : ℕ}
    (hP : CoeffDegreeOfLE s P d) (hQ : CoeffDegreeOfLE s Q d) :
    CoeffDegreeOfLE s (P - Q) d := by
  intro k
  rw [sub_eq_add_neg, Polynomial.coeff_add, Polynomial.coeff_neg]
  exact le_trans (MvPolynomial.degreeOf_add_le _ _ _)
    (max_le (hP k) (degreeOf_neg_le _ _ (hQ k)))

theorem CoeffDegreeOfLE.mono {σ : Type*} {s : σ} {P : (MvPolynomial σ K)[X]} {d e : ℕ}
    (hP : CoeffDegreeOfLE s P d) (hde : d ≤ e) : CoeffDegreeOfLE s P e :=
  fun k => le_trans (hP k) hde

theorem CoeffDegreeOfLE.mul {σ : Type*} {s : σ} {P Q : (MvPolynomial σ K)[X]} {d e : ℕ}
    (hP : CoeffDegreeOfLE s P d) (hQ : CoeffDegreeOfLE s Q e) :
    CoeffDegreeOfLE s (P * Q) (d + e) := by
  classical
  intro k
  rw [Polynomial.coeff_mul]
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) (Finset.sup_le ?_)
  rintro ⟨i, j⟩ -
  exact le_trans (MvPolynomial.degreeOf_mul_le _ _ _) (Nat.add_le_add (hP i) (hQ j))

theorem coeffDegreeOfLE_map_C {σ : Type*} (s : σ) (W : K[X]) :
    CoeffDegreeOfLE s (W.map (MvPolynomial.C : K →+* MvPolynomial σ K)) 0 := by
  intro k
  rw [Polynomial.coeff_map, MvPolynomial.degreeOf_C]

theorem coeffDegreeOfLE_one {σ : Type*} (s : σ) :
    CoeffDegreeOfLE s (1 : (MvPolynomial σ K)[X]) 0 := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · rw [Polynomial.coeff_one_zero, MvPolynomial.degreeOf_one]
  · rw [Polynomial.coeff_one, if_neg (by omega), MvPolynomial.degreeOf_zero]

theorem univB_coeff (j : ℕ) :
    (univB K m n).coeff j = if h : j < n then MvPolynomial.X (Sum.inr ⟨j, h⟩) else 0 := by
  rw [univB, Polynomial.finsetSum_coeff]
  by_cases h : j < n
  · rw [dif_pos h, Finset.sum_eq_single (⟨j, h⟩ : Fin n)]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    · intro b _ hb
      have hjb : j ≠ (b : ℕ) := fun hj => hb (Fin.ext hj.symm)
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjb, mul_zero]
    · intro hmem
      exact absurd (Finset.mem_univ _) hmem
  · rw [dif_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    have hjb : j ≠ (b : ℕ) := fun hj => h (hj ▸ b.isLt)
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hjb, mul_zero]

theorem coeffDegreeOfLE_univA_inl (i : Fin m) :
    CoeffDegreeOfLE (Sum.inl i : Fin m ⊕ Fin n) (univA K m n) 1 := by
  intro k
  rw [univA_coeff]
  by_cases h : k < m
  · rw [dif_pos h]
    by_cases hik : (⟨k, h⟩ : Fin m) = i
    · rw [hik, MvPolynomial.degreeOf_X_self]
    · rw [MvPolynomial.degreeOf_X_of_ne (fun hc => hik (Sum.inl_injective hc).symm)]
      exact Nat.zero_le 1
  · rw [dif_neg h, MvPolynomial.degreeOf_zero]
    exact Nat.zero_le 1

theorem coeffDegreeOfLE_univA_inr (j : Fin n) :
    CoeffDegreeOfLE (Sum.inr j : Fin m ⊕ Fin n) (univA K m n) 0 := by
  intro k
  rw [univA_coeff]
  by_cases h : k < m
  · rw [dif_pos h, MvPolynomial.degreeOf_X_of_ne (by simp)]
  · rw [dif_neg h, MvPolynomial.degreeOf_zero]

theorem coeffDegreeOfLE_univB_inr (j : Fin n) :
    CoeffDegreeOfLE (Sum.inr j : Fin m ⊕ Fin n) (univB K m n) 1 := by
  intro k
  rw [univB_coeff]
  by_cases h : k < n
  · rw [dif_pos h]
    by_cases hjk : (⟨k, h⟩ : Fin n) = j
    · rw [hjk, MvPolynomial.degreeOf_X_self]
    · rw [MvPolynomial.degreeOf_X_of_ne (fun hc => hjk (Sum.inr_injective hc).symm)]
      exact Nat.zero_le 1
  · rw [dif_neg h, MvPolynomial.degreeOf_zero]
    exact Nat.zero_le 1

theorem coeffDegreeOfLE_univB_inl (i : Fin m) :
    CoeffDegreeOfLE (Sum.inl i : Fin m ⊕ Fin n) (univB K m n) 0 := by
  intro k
  rw [univB_coeff]
  by_cases h : k < n
  · rw [dif_pos h, MvPolynomial.degreeOf_X_of_ne (by simp)]
  · rw [dif_neg h, MvPolynomial.degreeOf_zero]

/-- **The system is linear in the jet unknowns.** -/
theorem degreeOf_bilinSysPoly_inl (U V : K[X]) (i : Fin m) (k : ℕ) :
    (bilinSysPoly U V m n k).degreeOf (Sum.inl i) ≤ 1 := by
  have hAB := (coeffDegreeOfLE_univA_inl (K := K) (n := n) i).mul (coeffDegreeOfLE_univB_inl (K := K) (n := n) i)
  have hAV := (coeffDegreeOfLE_univA_inl (K := K) (n := n) i).mul
    (coeffDegreeOfLE_map_C (Sum.inl i : Fin m ⊕ Fin n) V)
  have hUB := (coeffDegreeOfLE_map_C (Sum.inl i : Fin m ⊕ Fin n) U).mul
    (coeffDegreeOfLE_univB_inl (K := K) (n := n) i)
  have hsum : CoeffDegreeOfLE (Sum.inl i : Fin m ⊕ Fin n)
      (criticalLowProduct (U.map MvPolynomial.C) (V.map MvPolynomial.C)
        (univA K m n) (univB K m n) - 1) 1 := by
    rw [criticalLowProduct]
    exact (((hAB.mono (by omega)).add (hAV.mono (by omega))).add
      (hUB.mono (by omega))).sub
      ((coeffDegreeOfLE_one (K := K) (Sum.inl i : Fin m ⊕ Fin n)).mono (by omega))
  exact hsum k

/-- **The system is linear in the reciprocal unknowns.** -/
theorem degreeOf_bilinSysPoly_inr (U V : K[X]) (j : Fin n) (k : ℕ) :
    (bilinSysPoly U V m n k).degreeOf (Sum.inr j) ≤ 1 := by
  have hAB := (coeffDegreeOfLE_univA_inr (K := K) (m := m) j).mul (coeffDegreeOfLE_univB_inr (K := K) (m := m) j)
  have hAV := (coeffDegreeOfLE_univA_inr (K := K) (m := m) j).mul
    (coeffDegreeOfLE_map_C (Sum.inr j : Fin m ⊕ Fin n) V)
  have hUB := (coeffDegreeOfLE_map_C (Sum.inr j : Fin m ⊕ Fin n) U).mul
    (coeffDegreeOfLE_univB_inr (K := K) (m := m) j)
  have hsum : CoeffDegreeOfLE (Sum.inr j : Fin m ⊕ Fin n)
      (criticalLowProduct (U.map MvPolynomial.C) (V.map MvPolynomial.C)
        (univA K m n) (univB K m n) - 1) 1 := by
    rw [criticalLowProduct]
    exact (((hAB.mono (by omega)).add (hAV.mono (by omega))).add
      (hUB.mono (by omega))).sub
      ((coeffDegreeOfLE_one (K := K) (Sum.inr j : Fin m ⊕ Fin n)).mono (by omega))
  exact hsum k

end Bidegree


/-! ## The observation's equations in explicit bilinear form -/

section Explicit

variable {K : Type*} [Field K]

/-- **The compatibility defect, coefficient by coefficient.**  Each coefficient is a bilinear
expression in the two unknown coefficient vectors together with the observed packets. -/
theorem criticalLowProduct_sub_one_coeff (U V A B : K[X]) (k : ℕ) :
    (criticalLowProduct U V A B - 1).coeff k
      = ((∑ i ∈ Finset.range (k + 1), A.coeff i * B.coeff (k - i))
          + (∑ i ∈ Finset.range (k + 1), A.coeff i * V.coeff (k - i))
          + (∑ i ∈ Finset.range (k + 1), U.coeff i * B.coeff (k - i)))
        - (if k = 0 then 1 else 0) := by
  rw [criticalLowProduct, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_add,
    coeff_mul_range, coeff_mul_range, coeff_mul_range, Polynomial.coeff_one]

/-- **The scalar equations of a fibre point, at any pair of depths.**  Below the horizon the
compatibility equation reads, coefficient by coefficient, as a bilinear equation in the unknown low
coefficients of the jet and of the reciprocal. -/
theorem criticalFibre_coeff_eq {m n : ℕ} {U V : K[X]} (p : criticalFibre K m n U V) (k : ℕ)
    (hk : k < m + n) :
    ((∑ i ∈ Finset.range (k + 1), p.1.1.coeff i * p.1.2.coeff (k - i))
        + (∑ i ∈ Finset.range (k + 1), p.1.1.coeff i * V.coeff (k - i))
        + (∑ i ∈ Finset.range (k + 1), U.coeff i * p.1.2.coeff (k - i)))
      = (if k = 0 then 1 else 0) := by
  have hz := (Polynomial.X_pow_dvd_iff.1 p.2.2.2) k hk
  rw [criticalLowProduct_sub_one_coeff, sub_eq_zero] at hz
  exact hz

end Explicit

end GaloisForLFunctions.HTGeometry
