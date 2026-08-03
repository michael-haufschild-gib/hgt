import GaloisForLFunctions.HTGeometry.ShiftInvariantDescent

/-!
# A shift-stable relation ideal produces a telescoper

An exponent of degree one is a single variable, so a polynomial of total degree at most one is
`b + ∑ᵢ aᵢ Xᵢ` for a finite index set carrying its linear coefficients.  The operator
`Φ(P) = P^σ(X + R)` acts on such a polynomial by

```text
Φ(b + ∑ᵢ aᵢ Xᵢ) = (σb + ∑ᵢ σ(aᵢ) Rᵢ) + ∑ᵢ σ(aᵢ) Xᵢ,
```

visibly again affine-linear.  Comparing the two presentations coefficient by coefficient turns
`Φ(P) = P` into

```text
σ(aᵢ) = aᵢ    and    ∑ᵢ aᵢ Rᵢ = σg - g   with  g = -b.
```

Combined with the descent, one nonzero element of a `Φ`-stable ideal containing no nonzero constant
therefore yields a nonzero family of `σ`-invariant coefficients whose combination of the `Rᵢ` is a
`σ`-coboundary.
-/

open scoped BigOperators

namespace GaloisForLFunctions

open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] {ι : Type*}

/-! ## Degree-one exponents -/

/-- An exponent of degree one is a single variable. -/
theorem exists_eq_single_of_degree_eq_one {e : ι →₀ ℕ} (h : Finsupp.degree e = 1) :
    ∃ i : ι, e = Finsupp.single i 1 := by
  classical
  have hne : e ≠ 0 := by
    intro hcon
    rw [hcon] at h
    simp only [map_zero] at h
    omega
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hne
  have hi0 : e i ≠ 0 := by simpa using hi
  have hmem : i ∈ e.support := Finsupp.mem_support_iff.mpr hi0
  have hle : e i ≤ Finsupp.degree e := by
    rw [Finsupp.degree_apply]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) hmem
  have hei : e i = 1 := by omega
  refine ⟨i, Finsupp.ext fun j => ?_⟩
  by_cases hij : j = i
  · subst hij
    rw [hei, Finsupp.single_eq_same]
  · rw [Finsupp.single_apply, if_neg (show ¬ i = j from fun hc => hij hc.symm)]
    by_contra hjne
    have hjmem : j ∈ e.support := Finsupp.mem_support_iff.mpr hjne
    have hsub : ({i, j} : Finset ι) ⊆ e.support := by
      intro k hk
      simp only [Finset.mem_insert, Finset.mem_singleton] at hk
      rcases hk with rfl | rfl
      · exact hmem
      · exact hjmem
    have hsum : ∑ k ∈ ({i, j} : Finset ι), e k ≤ ∑ k ∈ e.support, e k :=
      Finset.sum_le_sum_of_subset hsub
    rw [Finset.sum_pair (fun hc => hij hc.symm)] at hsum
    rw [Finsupp.degree_apply] at hle h
    have hjpos : 1 ≤ e j := Nat.one_le_iff_ne_zero.mpr hjne
    omega

/-! ## Affine-linear polynomials -/

/-- The affine-linear polynomial `b + ∑_{i ∈ s} aᵢ Xᵢ`. -/
def affineLinearPoly (s : Finset ι) (a : ι → K) (b : K) : MvPolynomial ι K :=
  C b + ∑ i ∈ s, C (a i) * X i

theorem coeff_zero_affineLinearPoly (s : Finset ι) (a : ι → K) (b : K) :
    coeff 0 (affineLinearPoly s a b) = b := by
  classical
  rw [affineLinearPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_pos rfl,
    MvPolynomial.coeff_sum]
  have hterm : ∀ i ∈ s, coeff (0 : ι →₀ ℕ) (C (a i) * X i) = 0 := by
    intro i _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
    simp
  rw [Finset.sum_eq_zero hterm, add_zero]

theorem coeff_single_affineLinearPoly [DecidableEq ι] (s : Finset ι) (a : ι → K) (b : K) (j : ι) :
    coeff (Finsupp.single j 1) (affineLinearPoly s a b) = if j ∈ s then a j else 0 := by
  classical
  have hzero : ¬ (0 : ι →₀ ℕ) = Finsupp.single j 1 := by
    intro hcon
    have := congrArg (fun t : ι →₀ ℕ => t j) hcon
    simp at this
  rw [affineLinearPoly, MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_neg hzero, zero_add,
    MvPolynomial.coeff_sum]
  by_cases hj : j ∈ s
  · rw [if_pos hj]
    refine (Finset.sum_eq_single_of_mem j hj ?_).trans ?_
    · intro i _ hij
      rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
      intro hcon
      exact hij (Finsupp.single_left_injective one_ne_zero hcon)
    · rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_pos rfl, mul_one]
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun i hi => ?_
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
    intro hcon
    exact hj (by rw [← Finsupp.single_left_injective one_ne_zero hcon]; exact hi)

/-- **The operator preserves affine-linearity**, shifting the linear coefficients and adding the
combination of the translations to the constant term. -/
theorem shiftTranslate_affineLinearPoly (σ : K →+* K) (R : ι → K) (s : Finset ι) (a : ι → K)
    (b : K) :
    shiftTranslate σ R (affineLinearPoly s a b)
      = affineLinearPoly s (fun i => σ (a i)) (σ b + ∑ i ∈ s, σ (a i) * R i) := by
  have hterm : ∀ i ∈ s, shiftTranslate σ R (C (a i) * X i)
      = C (σ (a i)) * X i + C (σ (a i) * R i) := by
    intro i _
    rw [map_mul, shiftTranslate_C, shiftTranslate_X, mul_add, ← MvPolynomial.C_mul]
  have hC : (C (σ b + ∑ i ∈ s, σ (a i) * R i) : MvPolynomial ι K)
      = C (σ b) + ∑ i ∈ s, C (σ (a i) * R i) := by
    rw [map_add, map_sum]
  rw [affineLinearPoly, affineLinearPoly, map_add, shiftTranslate_C, map_sum,
    Finset.sum_congr rfl hterm, Finset.sum_add_distrib, hC]
  abel

/-- **A polynomial of total degree at most one is affine-linear**, with its linear coefficients read
off at the single-variable exponents. -/
theorem exists_affineLinearPoly_repr [DecidableEq ι] (P : MvPolynomial ι K)
    (h : P.totalDegree ≤ 1) :
    ∃ s : Finset ι, (∀ i : ι, coeff (Finsupp.single i 1) P ≠ 0 → i ∈ s) ∧
      P = affineLinearPoly s (fun i => coeff (Finsupp.single i 1) P) (coeff 0 P) := by
  classical
  refine ⟨P.support.biUnion fun e => e.support, ?_, ?_⟩
  · intro i hi
    refine Finset.mem_biUnion.mpr ⟨Finsupp.single i 1, MvPolynomial.mem_support_iff.mpr hi, ?_⟩
    simp
  · refine MvPolynomial.ext _ _ fun e => ?_
    by_cases he0 : e = 0
    · subst he0
      rw [coeff_zero_affineLinearPoly]
    · by_cases he1 : Finsupp.degree e = 1
      · obtain ⟨j, rfl⟩ := exists_eq_single_of_degree_eq_one he1
        rw [coeff_single_affineLinearPoly]
        by_cases hj : j ∈ P.support.biUnion fun e => e.support
        · rw [if_pos hj]
        · rw [if_neg hj]
          by_contra hne
          exact hj (Finset.mem_biUnion.mpr
            ⟨Finsupp.single j 1, MvPolynomial.mem_support_iff.mpr hne, by simp⟩)
      · have hne0 : Finsupp.degree e ≠ 0 := by
          intro hcon
          rw [Finsupp.degree_eq_zero_iff] at hcon
          exact he0 hcon
        have h2 : 1 < Finsupp.degree e := by omega
        rw [coeff_eq_zero_of_totalDegree_lt_degree (lt_of_le_of_lt h h2), affineLinearPoly,
          MvPolynomial.coeff_add, MvPolynomial.coeff_C, if_neg (fun hc => he0 hc.symm), zero_add,
          MvPolynomial.coeff_sum]
        refine (Finset.sum_eq_zero fun i _ => ?_).symm
        rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X, if_neg, mul_zero]
        intro hcon
        rw [← hcon, Finsupp.degree_single] at h2
        omega

/-! ## The telescoper -/

/-- **A shift-stable relation ideal produces a telescoper.**  If an ideal of polynomial relations is
stable under `Φ(P) = P^σ(X + R)`, contains no nonzero constant, and contains a nonzero element, then
some nonzero family of `σ`-invariant coefficients makes the combination `∑ᵢ aᵢ Rᵢ` a `σ`-coboundary.

This is the elementary half of the difference-Galois criterion for indefinite sums: applied to the
relation ideal of a family whose difference defects `Rᵢ` lie in the coefficient field, it says that
a differential relation among the family forces a constant-coefficient linear combination of the
defects to be summable. -/
theorem exists_telescoper_of_mem_ideal [DecidableEq ι] [CharZero K]
    (σ : K →+* K) (R : ι → K) (J : Ideal (MvPolynomial ι K))
    (hJ : ∀ P ∈ J, shiftTranslate σ R P ∈ J) (hJC : ∀ c : K, C c ∈ J → c = 0)
    {P : MvPolynomial ι K} (hP : P ∈ J) (hP0 : P ≠ 0) :
    ∃ (s : Finset ι) (a : ι → K) (g : K), (∃ i ∈ s, a i ≠ 0) ∧
      (∀ i : ι, σ (a i) = a i) ∧ ∑ i ∈ s, a i * R i = σ g - g := by
  classical
  obtain ⟨Q, hQJ, hQ0, hQinv⟩ := exists_ne_zero_shiftTranslate_eq_self σ R J hJ hP hP0
  have hQdeg : 1 ≤ Q.totalDegree := by
    rcases Nat.eq_zero_or_pos Q.totalDegree with h0 | hpos
    · exfalso
      have hQC : Q = C (coeff 0 Q) := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h0
      have hc : coeff 0 Q = 0 := hJC (coeff 0 Q) (hQC ▸ hQJ)
      rw [hQC, hc, map_zero] at hQ0
      exact hQ0 rfl
    · exact hpos
  obtain ⟨P₁, hP₁deg, hP₁inv⟩ :=
    exists_totalDegree_eq_one_shiftTranslate_eq_self σ R Q.totalDegree Q rfl hQdeg hQinv
  obtain ⟨s, hs, hrepr⟩ := exists_affineLinearPoly_repr P₁ (le_of_eq hP₁deg)
  set a : ι → K := fun i => coeff (Finsupp.single i 1) P₁ with hadef
  set b : K := coeff 0 P₁ with hbdef
  have hkey : affineLinearPoly s (fun i => σ (a i)) (σ b + ∑ i ∈ s, σ (a i) * R i)
      = affineLinearPoly s a b := by
    rw [← shiftTranslate_affineLinearPoly, ← hrepr, hP₁inv, hrepr]
  have hinvcoeff : ∀ i ∈ s, σ (a i) = a i := by
    intro i hi
    have hc := congrArg (coeff (Finsupp.single i 1)) hkey
    rw [coeff_single_affineLinearPoly, coeff_single_affineLinearPoly, if_pos hi, if_pos hi] at hc
    exact hc
  have hzero_out : ∀ i : ι, i ∉ s → a i = 0 := by
    intro i hi
    by_contra hne
    exact hi (hs i hne)
  have hinvall : ∀ i : ι, σ (a i) = a i := by
    intro i
    by_cases hi : i ∈ s
    · exact hinvcoeff i hi
    · rw [hzero_out i hi, map_zero]
  have hconst : σ b + ∑ i ∈ s, σ (a i) * R i = b := by
    have hc := congrArg (coeff (0 : ι →₀ ℕ)) hkey
    rwa [coeff_zero_affineLinearPoly, coeff_zero_affineLinearPoly] at hc
  have hsum : ∑ i ∈ s, a i * R i = b - σ b := by
    have h1 : ∑ i ∈ s, a i * R i = ∑ i ∈ s, σ (a i) * R i :=
      Finset.sum_congr rfl fun i _ => by rw [hinvall i]
    rw [h1]
    linear_combination hconst
  have hP₁0 : P₁ ≠ 0 := by
    intro hcon
    rw [hcon, MvPolynomial.totalDegree_zero] at hP₁deg
    exact one_ne_zero hP₁deg.symm
  obtain ⟨e, heS, hedeg⟩ := exists_mem_support_degree_eq_totalDegree hP₁0
  rw [hP₁deg] at hedeg
  obtain ⟨j, rfl⟩ := exists_eq_single_of_degree_eq_one hedeg
  have hja : a j ≠ 0 := MvPolynomial.mem_support_iff.mp heS
  refine ⟨s, a, -b, ⟨j, hs j hja, hja⟩, hinvall, ?_⟩
  rw [map_neg, hsum]
  ring

end

end GaloisForLFunctions
