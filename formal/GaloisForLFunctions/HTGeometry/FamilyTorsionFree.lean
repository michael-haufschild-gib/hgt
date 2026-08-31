import GaloisForLFunctions.HTGeometry.FamilyNoPositiveWeight

/-!
# The family ring is torsion-free over the base line

```text
isFamHomog_monomial_C                     a scalar monomial in the extra variable is homogeneous
familyIdeal_saturated_of_coeff_zero_ne_zero
    ** a scalar polynomial with nonzero constant term does not divide into the family ideal **
```

The proof is the downward sweep once more.  Multiplying by `t ^ k` shifts the homogeneous parts by
`k`, so a scalar polynomial `q` turns the dehomogenizations `a_d` of the parts into the relations
`∑_k q_k · a_{d+k} ∈ I`.  Above weight zero every `a_d` vanishes, and the constant term of `q` is an
invertible scalar, so the relations determine the `a_d` downwards: all of them lie in `I`, which is
membership in the family ideal.

Together with `familyIdeal_saturated` — the case `q = t` — this is torsion-freeness for every nonzero
scalar polynomial, since any such factors as a power of `t` times one with nonzero constant term.
Torsion-freeness over the base line is what makes the graded pieces of the family free, which is the
input a Koszul comparison of the two fibres consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial

universe u
variable {σ : Type*} {K : Type u} [Field K]

theorem isFamHomog_monomial_C (w : σ → ℤ) (k : ℕ) (c : K) :
    IsFamHomog w (-(k : ℤ))
      (Polynomial.monomial k (MvPolynomial.C c) : Polynomial (MvPolynomial σ K)) := by
  classical
  intro j
  rw [Polynomial.coeff_monomial]
  by_cases hj : k = j
  · rw [if_pos hj, ← hj]
    intro γ hγ
    rw [MvPolynomial.coeff_C] at hγ
    by_cases hγ0 : γ = 0
    · rw [hγ0]
      simp
    · rw [if_neg (fun h => hγ0 h.symm)] at hγ
      exact absurd rfl hγ
  · rw [if_neg hj]
    intro γ hγ
    simp at hγ

theorem eval_one_monomial_mul (k : ℕ) (c : K) (G : Polynomial (MvPolynomial σ K)) :
    Polynomial.eval 1 ((Polynomial.monomial k (MvPolynomial.C c)) * G)
      = MvPolynomial.C c * Polynomial.eval 1 G := by
  rw [Polynomial.eval_mul, Polynomial.eval_monomial, one_pow, mul_one]

/-- **The family ring is torsion-free over the base line.**  For a scalar polynomial with nonzero
constant term the same downward sweep works: the homogeneous parts above weight zero vanish, and the
relation propagates downwards with the constant term as an invertible leading coefficient. -/
theorem familyIdeal_saturated_of_coeff_zero_ne_zero {w : σ → ℤ} (hw : ∀ i, w i ≤ 0)
    {I : Ideal (MvPolynomial σ K)} {q : Polynomial K} (hq : q.coeff 0 ≠ 0)
    {F : Polynomial (MvPolynomial σ K)}
    (h : (q.map (MvPolynomial.C : K →+* MvPolynomial σ K)) * F ∈ familyIdeal w I) :
    F ∈ familyIdeal w I := by
  classical
  rw [mem_familyIdeal_iff] at h ⊢
  set a : ℤ → MvPolynomial σ K := fun d => Polynomial.eval 1 (famComp w d F) with ha
  have hzero : ∀ d : ℤ, 0 < d → a d = 0 := by
    intro d hd
    rw [ha]
    simp only []
    rw [famComp_eq_zero_of_pos hw hd, Polynomial.eval_zero]
  have hrel : ∀ d : ℤ, (∑ k ∈ q.support, MvPolynomial.C (q.coeff k) * a (d + k)) ∈ I := by
    intro d
    have hd := h d
    have hexp : famComp w d ((q.map (MvPolynomial.C : K →+* MvPolynomial σ K)) * F)
        = ∑ k ∈ q.support,
          (Polynomial.monomial k (MvPolynomial.C (q.coeff k)) : Polynomial (MvPolynomial σ K))
            * famComp w (d + k) F := by
      have hqmap : (q.map (MvPolynomial.C : K →+* MvPolynomial σ K))
          = ∑ k ∈ q.support,
            (Polynomial.monomial k (MvPolynomial.C (q.coeff k)) : Polynomial (MvPolynomial σ K)) := by
        refine Polynomial.ext fun j => ?_
        rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
        by_cases hj : j ∈ q.support
        · have herase : (∑ k ∈ q.support.erase j,
              (Polynomial.monomial k (MvPolynomial.C (q.coeff k)) :
                Polynomial (MvPolynomial σ K)).coeff j) = 0 := by
            refine Finset.sum_eq_zero fun k hk => ?_
            rw [Polynomial.coeff_monomial, if_neg (Finset.mem_erase.mp hk).1]
          rw [← Finset.add_sum_erase _ _ hj, Polynomial.coeff_monomial, if_pos rfl, herase,
            add_zero]
        · rw [Polynomial.notMem_support_iff] at hj
          rw [hj, map_zero]
          refine (Finset.sum_eq_zero fun k hk => ?_).symm
          rw [Polynomial.coeff_monomial]
          by_cases hkj : k = j
          · exfalso
            subst hkj
            exact (Polynomial.mem_support_iff.mp hk) hj
          · rw [if_neg hkj]
      rw [hqmap, Finset.sum_mul, famComp_finsetSum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [famComp_mul_left_of_isFamHomog (isFamHomog_monomial_C w k (q.coeff k)),
        show d - -(k : ℤ) = d + (k : ℤ) from by ring]
    rw [hexp, Polynomial.eval_finsetSum] at hd
    have hcongr : ∀ k ∈ q.support,
        Polynomial.eval 1 ((Polynomial.monomial k (MvPolynomial.C (q.coeff k)) :
            Polynomial (MvPolynomial σ K)) * famComp w (d + k) F)
          = MvPolynomial.C (q.coeff k) * a (d + k) := by
      intro k _
      rw [eval_one_monomial_mul]
    rw [Finset.sum_congr rfl hcongr] at hd
    exact hd
  have hkey : ∀ n : ℕ, a (-(n : ℤ)) ∈ I := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      have hd := hrel (-(n : ℤ))
      have hsplit : (∑ k ∈ q.support, MvPolynomial.C (q.coeff k) * a (-(n : ℤ) + k))
          = MvPolynomial.C (q.coeff 0) * a (-(n : ℤ))
            + ∑ k ∈ q.support.erase 0, MvPolynomial.C (q.coeff k) * a (-(n : ℤ) + k) := by
        have h0 : (0 : ℕ) ∈ q.support := Polynomial.mem_support_iff.mpr hq
        rw [← Finset.add_sum_erase _ _ h0]
        norm_num
      have hrest : (∑ k ∈ q.support.erase 0,
          MvPolynomial.C (q.coeff k) * a (-(n : ℤ) + k)) ∈ I := by
        refine Ideal.sum_mem _ fun k hk => ?_
        have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
        refine Ideal.mul_mem_left _ _ ?_
        rcases lt_or_ge 0 (-(n : ℤ) + k) with hpos | hle
        · rw [hzero _ hpos]
          exact Ideal.zero_mem _
        · have hex : ∃ m : ℕ, (-(n : ℤ) + k) = -(m : ℤ) ∧ m < n := by
            refine ⟨(-(-(n : ℤ) + k)).toNat, by omega, by omega⟩
          obtain ⟨m, hm, hmn⟩ := hex
          rw [hm]
          exact ih m hmn
      have hC : MvPolynomial.C (q.coeff 0) * a (-(n : ℤ)) ∈ I := by
        have := Ideal.sub_mem I hd hrest
        rw [hsplit] at this
        simpa using this
      have hCinv : (MvPolynomial.C (q.coeff 0)⁻¹ : MvPolynomial σ K)
          * MvPolynomial.C (q.coeff 0) = 1 := by
        rw [← map_mul, inv_mul_cancel₀ hq, map_one]
      have hmul := Ideal.mul_mem_left I (MvPolynomial.C (q.coeff 0)⁻¹) hC
      rwa [← mul_assoc, hCinv, one_mul] at hmul
  intro d
  rcases lt_or_ge 0 d with hd | hd
  · show a d ∈ I
    rw [hzero d hd]
    exact Ideal.zero_mem _
  · show a d ∈ I
    have hk : d = -((-d).toNat : ℤ) := by omega
    have hmem := hkey (-d).toNat
    rw [← hk] at hmem
    exact hmem

end GaloisForLFunctions.HTGeometry
