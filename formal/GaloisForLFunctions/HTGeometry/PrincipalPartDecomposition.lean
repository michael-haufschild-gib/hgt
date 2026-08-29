import GaloisForLFunctions.HTGeometry.PrincipalPartMonomial
import Mathlib.FieldTheory.IsAlgClosed.Basic

/-!
# Partial-fraction decomposition over an algebraically closed field

Every rational function is a polynomial plus a finite combination of the principal-part monomials
`(x − α)^{-d}`, and the coefficients of that combination are exactly its principal-part
coefficients.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {K : Type*} [Field K]

/-- A finite combination of principal-part monomials. -/
def principalPartSum (c : K × ℕ →₀ K) : RatFunc K :=
  c.sum fun p a => algebraMap K (RatFunc K) a * invLinPow p.1 p.2

@[simp] theorem principalPartSum_zero : principalPartSum (0 : K × ℕ →₀ K) = 0 := by
  rw [principalPartSum, Finsupp.sum_zero_index]

theorem principalPartSum_add (c₁ c₂ : K × ℕ →₀ K) :
    principalPartSum (c₁ + c₂) = principalPartSum c₁ + principalPartSum c₂ := by
  refine Finsupp.sum_add_index' (fun p => by rw [map_zero, zero_mul]) fun p a b => ?_
  rw [map_add, add_mul]

theorem principalPartSum_single (p : K × ℕ) (a : K) :
    principalPartSum (Finsupp.single p a) = algebraMap K (RatFunc K) a * invLinPow p.1 p.2 := by
  refine Finsupp.sum_single_index ?_
  rw [map_zero, zero_mul]

theorem polePart_principalPartSum (c : K × ℕ →₀ K) (β : K) (e : ℕ) (he : 0 < e) :
    polePart (principalPartSum c) β e = c (β, e) := by
  classical
  rw [principalPartSum, Finsupp.sum, polePart_sum]
  have hterm : ∀ p ∈ c.support,
      polePart (algebraMap K (RatFunc K) (c p) * invLinPow p.1 p.2) β e
        = if p = (β, e) then c p else 0 := by
    intro p _
    rw [polePart_smul]
    by_cases hp : p.1 = β
    · subst hp
      rw [polePart_invLinPow_self]
      by_cases he2 : e = p.2
      · rw [if_pos he2, mul_one, if_pos (by rw [Prod.ext_iff]; exact ⟨rfl, he2.symm⟩)]
      · refine by
          rw [if_neg he2, mul_zero,
            if_neg (fun h => he2 (by rw [Prod.ext_iff] at h; exact h.2.symm))]
    · rw [polePart_invLinPow_of_ne (fun h => hp h.symm) _ _ he, mul_zero,
        if_neg (by rw [Prod.ext_iff]; exact fun h => hp h.1)]
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' c.support (β, e) (fun p => c p)]
  by_cases hmem : (β, e) ∈ c.support
  · rw [if_pos hmem]
  · rw [if_neg hmem, ← Finsupp.notMem_support_iff.1 hmem]

theorem div_const_decomposition {a : K} (ha : a ≠ 0) (P : Polynomial K) :
    algebraMap (Polynomial K) (RatFunc K) P
        / algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a)
      = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a⁻¹ * P) := by
  have hC : (RatFunc.C a : RatFunc K) ≠ 0 := by
    simpa using ha
  rw [RatFunc.algebraMap_C, div_eq_iff hC, map_mul, RatFunc.algebraMap_C]
  rw [show (RatFunc.C a⁻¹ : RatFunc K) * algebraMap (Polynomial K) (RatFunc K) P * RatFunc.C a
      = (RatFunc.C a⁻¹ * RatFunc.C a) * algebraMap (Polynomial K) (RatFunc K) P from by ring,
    ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul]

/-- **Partial-fraction decomposition.** -/
theorem exists_principalPartSum_decomposition [IsAlgClosed K] :
    ∀ (n : ℕ) (P Q : Polynomial K), Q ≠ 0 → Q.natDegree ≤ n →
      ∃ (R : Polynomial K) (c : K × ℕ →₀ K),
        (∀ p ∈ c.support, 0 < p.2) ∧
        algebraMap (Polynomial K) (RatFunc K) P / algebraMap (Polynomial K) (RatFunc K) Q
          = algebraMap (Polynomial K) (RatFunc K) R + principalPartSum c := by
  classical
  intro n
  induction n with
  | zero =>
      intro P Q hQ hdeg
      obtain ⟨a, ha⟩ : ∃ a : K, Q = Polynomial.C a :=
        ⟨Q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero (by omega)⟩
      have ha0 : a ≠ 0 := fun h => hQ (by rw [ha, h, map_zero])
      exact ⟨Polynomial.C a⁻¹ * P, 0, by simp, by rw [ha, div_const_decomposition ha0,
        principalPartSum_zero, add_zero]⟩
  | succ n ih =>
      intro P Q hQ hdeg
      by_cases hdeg0 : Q.natDegree = 0
      · obtain ⟨a, ha⟩ : ∃ a : K, Q = Polynomial.C a :=
          ⟨Q.coeff 0, Polynomial.eq_C_of_natDegree_eq_zero hdeg0⟩
        have ha0 : a ≠ 0 := fun h => hQ (by rw [ha, h, map_zero])
        exact ⟨Polynomial.C a⁻¹ * P, 0, by simp, by rw [ha, div_const_decomposition ha0,
          principalPartSum_zero, add_zero]⟩
      · obtain ⟨α, hα⟩ : ∃ α : K, Q.IsRoot α := by
          have hdne : Q.degree ≠ 0 := by
            rw [Polynomial.degree_eq_natDegree hQ]
            exact_mod_cast hdeg0
          exact IsAlgClosed.exists_root Q hdne
        set m : ℕ := Q.rootMultiplicity α with hm
        have hm0 : 0 < m := (Polynomial.rootMultiplicity_pos hQ).2 hα
        obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m = m' + 1 := ⟨m - 1, by omega⟩
        set Q₁ : Polynomial K := Q /ₘ (Polynomial.X - Polynomial.C α) ^ m with hQ₁def
        have hfac : (Polynomial.X - Polynomial.C α) ^ m * Q₁ = Q :=
          Polynomial.pow_mul_divByMonic_rootMultiplicity_eq Q α
        have hQ₁eval : Q₁.eval α ≠ 0 :=
          Polynomial.eval_divByMonic_pow_rootMultiplicity_ne_zero α hQ
        have hQ₁ne : Q₁ ≠ 0 := fun h => hQ₁eval (by rw [h, Polynomial.eval_zero])
        set A : K := P.eval α / Q₁.eval α with hA
        have hroot : (P - Polynomial.C A * Q₁).IsRoot α := by
          rw [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, hA,
            div_mul_cancel₀ _ hQ₁eval, sub_self]
        obtain ⟨P₂, hP₂⟩ := Polynomial.dvd_iff_isRoot.2 hroot
        have hPeq : P = Polynomial.C A * Q₁ + (Polynomial.X - Polynomial.C α) * P₂ := by
          rw [← hP₂]
          ring
        set Q' : Polynomial K := (Polynomial.X - Polynomial.C α) ^ m' * Q₁ with hQ'
        have hQ'ne : Q' ≠ 0 :=
          mul_ne_zero (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hQ₁ne
        have hdegQ : Q.natDegree = m + Q₁.natDegree := by
          rw [← hfac, Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hQ₁ne,
            Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
        have hdegQ' : Q'.natDegree ≤ n := by
          rw [hQ', Polynomial.natDegree_mul (pow_ne_zero _ (Polynomial.X_sub_C_ne_zero α)) hQ₁ne,
            Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C, mul_one]
          omega
        obtain ⟨R, c, hc, hdec⟩ := ih P₂ Q' hQ'ne hdegQ'
        refine ⟨R, c + Finsupp.single (α, m) A, ?_, ?_⟩
        · intro p hp
          rcases Finset.mem_union.1 (Finsupp.support_add hp) with h | h
          · exact hc p h
          · have : p = (α, m) := by
              simpa using Finsupp.support_single_subset h
            rw [this]
            exact hm0
        · rw [principalPartSum_add, principalPartSum_single]
          have hXne : algebraMap (Polynomial K) (RatFunc K)
              (Polynomial.X - Polynomial.C α) ≠ 0 :=
            RatFunc.algebraMap_ne_zero (Polynomial.X_sub_C_ne_zero α)
          have hQ₁ne' : algebraMap (Polynomial K) (RatFunc K) Q₁ ≠ 0 :=
            RatFunc.algebraMap_ne_zero hQ₁ne
          have h1 : algebraMap (Polynomial K) (RatFunc K) P
              = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C A)
                  * algebraMap (Polynomial K) (RatFunc K) Q₁
                + algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α)
                  * algebraMap (Polynomial K) (RatFunc K) P₂ := by
            rw [hPeq, map_add, map_mul, map_mul]
          have h2 : algebraMap (Polynomial K) (RatFunc K) Q
              = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) ^ (m' + 1)
                * algebraMap (Polynomial K) (RatFunc K) Q₁ := by
            rw [← hfac, hm', map_mul, map_pow]
          have h3 : algebraMap (Polynomial K) (RatFunc K) Q'
              = algebraMap (Polynomial K) (RatFunc K) (Polynomial.X - Polynomial.C α) ^ m'
                * algebraMap (Polynomial K) (RatFunc K) Q₁ := by
            rw [hQ', map_mul, map_pow]
          have h4 : algebraMap K (RatFunc K) A
              = algebraMap (Polynomial K) (RatFunc K) (Polynomial.C A) :=
            (RatFunc.algebraMap_C A).symm
          have h5 : invLinPow α (m' + 1)
              = (algebraMap (Polynomial K) (RatFunc K)
                  (Polynomial.X - Polynomial.C α) ^ (m' + 1))⁻¹ := by
            rw [invLinPow, map_pow]
          have hkey : algebraMap (Polynomial K) (RatFunc K) P
              / algebraMap (Polynomial K) (RatFunc K) Q
              = algebraMap (Polynomial K) (RatFunc K) P₂
                  / algebraMap (Polynomial K) (RatFunc K) Q'
                + algebraMap K (RatFunc K) A * invLinPow α m := by
            rw [h1, h2, h3, h4, hm', h5]
            field_simp
            ring
          rw [hkey, hdec]
          ring


theorem polePart_algebraMap_polynomial (R : Polynomial K) (β : K) (e : ℕ) (he : 0 < e) :
    polePart (algebraMap (Polynomial K) (RatFunc K) R) β e = 0 := by
  refine polePart_eq_zero_of_poleOrder_zero he ((regularAt_iff_poleOrder_eq_zero _ _).1 ?_)
  exact regularAt_of_repr (P := R) (Q := 1) (by simp) (by rw [map_one, div_one])

/-- **Partial-fraction decomposition of an arbitrary rational function**, with the coefficients
identified as its principal-part coefficients. -/
theorem exists_principalPart_decomposition [IsAlgClosed K] (r : RatFunc K) :
    ∃ (R : Polynomial K) (c : K × ℕ →₀ K),
      (∀ p ∈ c.support, 0 < p.2) ∧
      (∀ β : K, ∀ e : ℕ, 0 < e → c (β, e) = polePart r β e) ∧
      r = algebraMap (Polynomial K) (RatFunc K) R + principalPartSum c := by
  obtain ⟨R, c, hc, hdec⟩ := exists_principalPartSum_decomposition r.denom.natDegree r.num r.denom
    (RatFunc.denom_ne_zero r) le_rfl
  have hr : r = algebraMap (Polynomial K) (RatFunc K) R + principalPartSum c := by
    rw [← hdec, RatFunc.num_div_denom r]
  refine ⟨R, c, hc, fun β e he => ?_, hr⟩
  rw [hr, polePart_add, polePart_algebraMap_polynomial R β e he, zero_add,
    polePart_principalPartSum c β e he]

end

end GaloisForLFunctions.HTGeometry
