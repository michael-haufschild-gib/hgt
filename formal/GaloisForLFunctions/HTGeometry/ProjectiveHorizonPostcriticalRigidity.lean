import GaloisForLFunctions.HTGeometry.ProjectiveHorizonPureTailFiber

/-!
# One-step postcritical rigidity of the pure horizon fiber

At critical order `L-1`, the pure `(m,n)` horizon fiber is the set of factorizations
`X₀ Y₀ = 1+t^L`.  Add one raw coefficient `u t^L` and one reciprocal coefficient `v t^L`.
The coefficient of `t^L` in the new inverse error is exactly

`1 + u Y₀(0) + v X₀(0)`.

In particular, at `u=0` the first postcritical reciprocal coefficient is `-X₀(0)⁻¹`.  It
distinguishes pure-fiber factors with different constant terms.  This is the explicit algebraic
witness used by the paper theorem that one postcritical coefficient breaks the atomic critical
Galois ambiguity.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Product of the roots selected by a pure critical occupation state. -/
def criticalHorizonOccupationProduct
    {K : Type*} [CommMonoid K] {m n : ℕ}
    (root : Fin (m + n) → K) (S : criticalHorizonOccupationStates m n) : K :=
  ∏ i ∈ S.1, root i

/-- The monic factor whose roots are selected by a pure critical occupation state. -/
def criticalHorizonLeftFactorFromRoots
    {K : Type*} [CommRing K] {m n : ℕ}
    (root : Fin (m + n) → K) (S : criticalHorizonOccupationStates m n) : K[X] :=
  ∏ i ∈ S.1, (X - C (root i))

/-- The complementary monic factor of a pure critical occupation state. -/
def criticalHorizonRightFactorFromRoots
    {K : Type*} [CommRing K] {m n : ℕ}
    (root : Fin (m + n) → K) (S : criticalHorizonOccupationStates m n) : K[X] :=
  ∏ i ∈ S.1ᶜ, (X - C (root i))

/-- A selected root factor times its complementary factor is the full root product. -/
theorem criticalHorizonRootFactors_mul
    {K : Type*} [CommRing K] {m n : ℕ}
    (root : Fin (m + n) → K) (S : criticalHorizonOccupationStates m n) :
    criticalHorizonLeftFactorFromRoots root S *
        criticalHorizonRightFactorFromRoots root S =
      ∏ i : Fin (m + n), (X - C (root i)) := by
  classical
  simpa [criticalHorizonLeftFactorFromRoots,
    criticalHorizonRightFactorFromRoots] using
    (Finset.prod_mul_prod_compl S.1 (fun i ↦ X - C (root i)))

/-- The constant coefficient of a selected root factor is its signed root product. -/
theorem criticalHorizonLeftFactorFromRoots_coeff_zero
    {K : Type*} [CommRing K] {m n : ℕ}
    (root : Fin (m + n) → K) (S : criticalHorizonOccupationStates m n) :
    (criticalHorizonLeftFactorFromRoots root S).coeff 0 =
      (-1 : K) ^ m * criticalHorizonOccupationProduct root S := by
  rw [criticalHorizonLeftFactorFromRoots, Polynomial.coeff_zero_prod]
  simp only [Polynomial.coeff_sub, Polynomial.coeff_X_zero,
    Polynomial.coeff_C_zero, zero_sub]
  rw [Finset.prod_neg]
  simp [criticalHorizonOccupationProduct, S.2]

/-- Among nontrivial proper subsets of distinct nonzero roots, the occupation product is not
constant. -/
theorem exists_criticalHorizonOccupationProduct_ne
    {K : Type*} [CommGroupWithZero K] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (root : Fin (m + n) → K) (hroot : Function.Injective root)
    (hroot0 : ∀ i, root i ≠ 0) :
    ∃ S T : criticalHorizonOccupationStates m n,
      criticalHorizonOccupationProduct root S ≠
        criticalHorizonOccupationProduct root T := by
  classical
  have hL : 1 < m + n := by omega
  let a : Fin (m + n) := ⟨0, by omega⟩
  let b : Fin (m + n) := ⟨1, hL⟩
  have hab : a ≠ b := by
    intro h
    have := congrArg Fin.val h
    simp [a, b] at this
  let R : Finset (Fin (m + n)) := (Finset.univ.erase a).erase b
  have hbmem : b ∈ Finset.univ.erase a :=
    Finset.mem_erase.mpr ⟨hab.symm, Finset.mem_univ b⟩
  have hRcard : R.card = m + n - 2 := by
    simp only [R, Finset.card_erase_of_mem hbmem,
      Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
    omega
  have hmR : m - 1 ≤ R.card := by
    rw [hRcard]
    omega
  obtain ⟨U, hUR, hUcard⟩ := Finset.exists_subset_card_eq hmR
  have haU : a ∉ U := by
    intro ha
    have := hUR ha
    have ha' : a ∈ Finset.univ.erase a := (Finset.mem_erase.mp this).2
    exact (Finset.mem_erase.mp ha').1 rfl
  have hbU : b ∉ U := by
    intro hb
    exact (Finset.mem_erase.mp (hUR hb)).1 rfl
  have hprod : ∏ i ∈ U, root i ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i hi ↦ hroot0 i
  let S : criticalHorizonOccupationStates m n :=
    ⟨insert a U, by rw [Finset.card_insert_of_notMem haU, hUcard]; omega⟩
  let T : criticalHorizonOccupationStates m n :=
    ⟨insert b U, by rw [Finset.card_insert_of_notMem hbU, hUcard]; omega⟩
  refine ⟨S, T, ?_⟩
  intro heq
  have hmul : root a * (∏ i ∈ U, root i) =
      root b * (∏ i ∈ U, root i) := by
    change (∏ i ∈ insert a U, root i) =
      (∏ i ∈ insert b U, root i) at heq
    rw [Finset.prod_insert haU, Finset.prod_insert hbU] at heq
    exact heq
  exact hab (hroot (mul_right_cancel₀ hprod hmul))

/-- Distinct-root occupation states produce two selected factors with different constant
coefficients. -/
theorem exists_criticalHorizonLeftFactorFromRoots_coeff_zero_ne
    {K : Type*} [Field K] {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n)
    (root : Fin (m + n) → K) (hroot : Function.Injective root)
    (hroot0 : ∀ i, root i ≠ 0) :
    ∃ S T : criticalHorizonOccupationStates m n,
      (criticalHorizonLeftFactorFromRoots root S).coeff 0 ≠
        (criticalHorizonLeftFactorFromRoots root T).coeff 0 := by
  obtain ⟨S, T, hST⟩ :=
    exists_criticalHorizonOccupationProduct_ne hm hn root hroot hroot0
  refine ⟨S, T, ?_⟩
  rw [criticalHorizonLeftFactorFromRoots_coeff_zero,
    criticalHorizonLeftFactorFromRoots_coeff_zero]
  intro heq
  exact hST (mul_left_cancel₀ (pow_ne_zero m (neg_ne_zero.mpr one_ne_zero)) heq)

/-- The roots of `1 + X^L`, indexed without repetition. -/
noncomputable def pureCriticalRootEquiv
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K] [DecidableEq K]
    {L : ℕ} (hL : 0 < L) :
    Fin L ≃ (pureCriticalCyclicPolynomial (K := K) L).roots.toFinset := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_fin, Fintype.card_coe,
    Multiset.toFinset_card_of_nodup
      (Polynomial.nodup_roots (pureCriticalCyclicPolynomial_separable hL))]
  rw [← (IsAlgClosed.splits
    (pureCriticalCyclicPolynomial (K := K) L)).natDegree_eq_card_roots]
  simpa [pureCriticalCyclicPolynomial, add_comm] using
    (Polynomial.natDegree_X_pow_add_C (R := K) (n := L) (r := (1 : K))).symm

/-- The value of the canonical finite indexing of the roots of `1 + X^L`. -/
noncomputable def pureCriticalRootLabeling
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {L : ℕ} (hL : 0 < L) : Fin L → K := by
  classical
  exact fun i ↦ pureCriticalRootEquiv (K := K) hL i

theorem pureCriticalRootLabeling_injective
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {L : ℕ} (hL : 0 < L) :
    Function.Injective (pureCriticalRootLabeling (K := K) hL) := by
  classical
  exact Subtype.val_injective.comp (pureCriticalRootEquiv (K := K) hL).injective

theorem pureCriticalRootLabeling_ne_zero
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {L : ℕ} (hL : 0 < L) (i : Fin L) :
    pureCriticalRootLabeling (K := K) hL i ≠ 0 := by
  classical
  intro hi
  have hmem : pureCriticalRootLabeling (K := K) hL i ∈
      (pureCriticalCyclicPolynomial (K := K) L).roots :=
    Multiset.mem_toFinset.mp (pureCriticalRootEquiv (K := K) hL i).property
  have hp : pureCriticalCyclicPolynomial (K := K) L ≠ 0 :=
    (pureCriticalCyclicPolynomial_separable (K := K) hL).ne_zero
  have heval := (Polynomial.mem_roots hp).mp hmem
  rw [hi] at heval
  simp [pureCriticalCyclicPolynomial, zero_pow hL.ne'] at heval

/-- The product over the canonical root labeling recovers `1 + X^L`. -/
theorem pureCriticalRootLabeling_prod
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {L : ℕ} (hL : 0 < L) :
    (∏ i : Fin L, (X - C (pureCriticalRootLabeling (K := K) hL i))) =
      pureCriticalCyclicPolynomial (K := K) L := by
  classical
  let p := pureCriticalCyclicPolynomial (K := K) L
  let e := pureCriticalRootEquiv (K := K) hL
  have hmonic : p.Monic := by
    simpa [p, pureCriticalCyclicPolynomial, add_comm] using
      (Polynomial.monic_X_pow_add_C (R := K) (1 : K) hL.ne')
  have hseparable : p.Separable := by
    simpa [p] using pureCriticalCyclicPolynomial_separable (K := K) hL
  calc
    (∏ i : Fin L, (X - C (pureCriticalRootLabeling (K := K) hL i))) =
        ∏ z : p.roots.toFinset, (X - C (z : K)) := by
          simpa [pureCriticalRootLabeling, e, p] using
            (e.prod_comp (fun z : p.roots.toFinset ↦ X - C (z : K)))
    _ = ∏ z ∈ p.roots.toFinset, (X - C z) := by
          exact Finset.prod_coe_sort p.roots.toFinset
            (fun z ↦ X - C (z : K))
    _ = (p.roots.map (X - C ·)).prod := by
          rw [Finset.prod_eq_multiset_prod, Multiset.toFinset_val,
            Multiset.dedup_eq_self.mpr (Polynomial.nodup_roots hseparable)]
    _ = p := ((IsAlgClosed.splits p).eq_prod_roots_of_monic hmonic).symm

/-- Each occupation state gives a genuine complementary factorization of `1 + X^(m+n)`. -/
theorem pureCriticalRootFactors_mul
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hL : 0 < m + n) (S : criticalHorizonOccupationStates m n) :
    criticalHorizonLeftFactorFromRoots
        (pureCriticalRootLabeling (K := K) hL) S *
      criticalHorizonRightFactorFromRoots
        (pureCriticalRootLabeling (K := K) hL) S =
      pureCriticalCyclicPolynomial (K := K) (m + n) := by
  rw [criticalHorizonRootFactors_mul, pureCriticalRootLabeling_prod hL]

/-- For a nontrivial split, the selected root factors do not all have the same constant
coefficient. -/
theorem exists_pureCriticalRootFactor_coeff_zero_ne
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ S T : criticalHorizonOccupationStates m n,
      (criticalHorizonLeftFactorFromRoots
        (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S).coeff 0 ≠
      (criticalHorizonLeftFactorFromRoots
        (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T).coeff 0 := by
  apply exists_criticalHorizonLeftFactorFromRoots_coeff_zero_ne hm hn
  · exact pureCriticalRootLabeling_injective (by omega)
  · exact pureCriticalRootLabeling_ne_zero (by omega)

/-- There are two genuine pure critical factor pairs whose left constant coefficients differ. -/
theorem exists_pureCriticalRootFactorPairs_coeff_zero_ne
    {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    ∃ S T : criticalHorizonOccupationStates m n,
      criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S *
        criticalHorizonRightFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S =
          pureCriticalCyclicPolynomial (K := K) (m + n) ∧
      criticalHorizonLeftFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T *
        criticalHorizonRightFactorFromRoots
          (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T =
          pureCriticalCyclicPolynomial (K := K) (m + n) ∧
      (criticalHorizonLeftFactorFromRoots
        (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) S).coeff 0 ≠
      (criticalHorizonLeftFactorFromRoots
        (pureCriticalRootLabeling (K := K) (by omega : 0 < m + n)) T).coeff 0 := by
  obtain ⟨S, T, hST⟩ := exists_pureCriticalRootFactor_coeff_zero_ne (K := K) hm hn
  exact ⟨S, T, pureCriticalRootFactors_mul (by omega) S,
    pureCriticalRootFactors_mul (by omega) T, hST⟩

/-- Add the first postcritical raw coefficient to a pure critical left factor. -/
def pureCriticalPostLeft {K : Type*} [CommRing K]
    (m n : ℕ) (A : K[X]) (u : K) : K[X] :=
  pureCriticalLeftFactor m A + C u * X ^ (m + n)

/-- Add the first postcritical reciprocal coefficient to a pure critical right factor. -/
def pureCriticalPostRight {K : Type*} [CommRing K]
    (m n : ℕ) (B : K[X]) (v : K) : K[X] :=
  pureCriticalRightFactor n B + C v * X ^ (m + n)

/-- Exact first postcritical coefficient of the inverse error over a pure critical factorization. -/
theorem pureCritical_postcritical_error_coeff {K : Type*} [CommRing K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (u v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n)) :
    (pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1).coeff (m + n) =
      1 + u * (pureCriticalRightFactor n B).coeff 0 +
        v * (pureCriticalLeftFactor m A).coeff 0 := by
  have herr :
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1 =
        X ^ (m + n) +
          C u * X ^ (m + n) * pureCriticalRightFactor n B +
          C v * X ^ (m + n) * pureCriticalLeftFactor m A +
          C u * C v * X ^ (2 * (m + n)) := by
    calc
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1 =
          (pureCriticalLeftFactor m A * pureCriticalRightFactor n B - 1) +
            C u * X ^ (m + n) * pureCriticalRightFactor n B +
            C v * X ^ (m + n) * pureCriticalLeftFactor m A +
            C u * C v * X ^ (2 * (m + n)) := by
              simp only [pureCriticalPostLeft, pureCriticalPostRight]
              ring
      _ = X ^ (m + n) +
          C u * X ^ (m + n) * pureCriticalRightFactor n B +
          C v * X ^ (m + n) * pureCriticalLeftFactor m A +
          C u * C v * X ^ (2 * (m + n)) := by
            rw [hfac]
            simp [pureCriticalCyclicPolynomial]
  have hucoeff :
      (C u * X ^ (m + n) * pureCriticalRightFactor n B).coeff (m + n) =
        u * (pureCriticalRightFactor n B).coeff 0 := by
    rw [mul_assoc, coeff_C_mul]
    congr 1
    simpa using coeff_X_pow_mul (pureCriticalRightFactor n B) (m + n) 0
  have hvcoeff :
      (C v * X ^ (m + n) * pureCriticalLeftFactor m A).coeff (m + n) =
        v * (pureCriticalLeftFactor m A).coeff 0 := by
    rw [mul_assoc, coeff_C_mul]
    congr 1
    simpa using coeff_X_pow_mul (pureCriticalLeftFactor m A) (m + n) 0
  have huvcoeff :
      (C u * C v * X ^ (2 * (m + n))).coeff (m + n) = 0 := by
    rw [← C_mul, coeff_C_mul, coeff_X_pow]
    simp [show m + n ≠ 2 * (m + n) by omega]
  rw [herr]
  simp [hucoeff, hvcoeff, huvcoeff]

/-- Compatibility through one more coefficient forces the exact top-coefficient equation. -/
theorem pureCriticalPost_topEquation {K : Type*} [CommRing K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (u v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n))
    (hInv : X ^ (m + n + 1) ∣
      pureCriticalPostLeft m n A u * pureCriticalPostRight m n B v - 1) :
    1 + u * (pureCriticalRightFactor n B).coeff 0 +
        v * (pureCriticalLeftFactor m A).coeff 0 = 0 := by
  rw [← pureCritical_postcritical_error_coeff hL A B u v hfac]
  exact X_pow_dvd_iff.mp hInv (m + n) (by omega)

/-- With zero new raw coefficient, the first postcritical reciprocal coefficient is the negative
inverse constant term of the chosen left factor. -/
theorem pureCriticalPost_rightTop_eq_neg_inv {K : Type*} [Field K]
    {m n : ℕ} (hL : 0 < m + n) (A B : K[X]) (v : K)
    (hfac : pureCriticalLeftFactor m A * pureCriticalRightFactor n B =
      pureCriticalCyclicPolynomial (K := K) (m + n))
    (hx0 : (pureCriticalLeftFactor m A).coeff 0 ≠ 0)
    (hInv : X ^ (m + n + 1) ∣
      pureCriticalPostLeft m n A 0 * pureCriticalPostRight m n B v - 1) :
    v = -((pureCriticalLeftFactor m A).coeff 0)⁻¹ := by
  have heq := pureCriticalPost_topEquation hL A B 0 v hfac hInv
  simp only [zero_mul, add_zero] at heq
  have hmul : v * (pureCriticalLeftFactor m A).coeff 0 = -1 := by
    linear_combination heq
  calc
    v = (-1) / (pureCriticalLeftFactor m A).coeff 0 :=
      (eq_div_iff hx0).2 hmul
    _ = -((pureCriticalLeftFactor m A).coeff 0)⁻¹ := by
      rw [div_eq_mul_inv]
      ring

end

end GaloisForLFunctions.HTGeometry
