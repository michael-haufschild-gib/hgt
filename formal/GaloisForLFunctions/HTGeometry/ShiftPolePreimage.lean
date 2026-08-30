import GaloisForLFunctions.HTGeometry.ShiftPoleObstruction

/-!
# Solving the first-order equation over the rational functions

The equation `v′ - λ v = u` is solvable in `ℂ(s)` exactly when the obstruction `Θ^λ_β(u)` vanishes
at every pole.  The polynomial part is always solvable — by a telescoping finite sum when `λ ≠ 0`
and by an antiderivative when `λ = 0` — and the principal parts are peeled one order at a time.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

/-- The first-order operator on rational functions. -/
def firstOrderOp (lam : ℂ) (v : RatFunc ℂ) : RatFunc ℂ :=
  ratFuncDerivative ℂ v - algebraMap ℂ (RatFunc ℂ) lam * v

theorem firstOrderOp_add (lam : ℂ) (v w : RatFunc ℂ) :
    firstOrderOp lam (v + w) = firstOrderOp lam v + firstOrderOp lam w := by
  rw [firstOrderOp, firstOrderOp, firstOrderOp, map_add, mul_add]
  ring

theorem firstOrderOp_sub (lam : ℂ) (v w : RatFunc ℂ) :
    firstOrderOp lam (v - w) = firstOrderOp lam v - firstOrderOp lam w := by
  rw [firstOrderOp, firstOrderOp, firstOrderOp, map_sub, mul_sub]
  ring

theorem firstOrderOp_sum {ι : Type*} (lam : ℂ) (s : Finset ι) (f : ι → RatFunc ℂ) :
    firstOrderOp lam (∑ i ∈ s, f i) = ∑ i ∈ s, firstOrderOp lam (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [firstOrderOp]
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, firstOrderOp_add, ih]

theorem Theta_firstOrderOp (lam : ℂ) (v : RatFunc ℂ) (β : ℂ) :
    Theta lam (firstOrderOp lam v) β = 0 :=
  Theta_deriv_sub lam v β

/-! ### The polynomial part -/

theorem exists_preimage_polynomial_of_ne_zero {lam : ℂ} (hlam : lam ≠ 0) (P : Polynomial ℂ) :
    ∃ Q : Polynomial ℂ,
      Polynomial.derivative Q - Polynomial.C lam * Q = P := by
  classical
  set n : ℕ := P.natDegree with hn
  refine ⟨-∑ k ∈ Finset.range (n + 1),
    Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k] P), ?_⟩
  have hderiv : Polynomial.derivative (-∑ k ∈ Finset.range (n + 1),
      Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k] P))
      = -∑ k ∈ Finset.range (n + 1),
        Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k + 1] P) := by
    rw [map_neg, map_sum]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Polynomial.derivative_C_mul, Function.iterate_succ_apply']
  rw [hderiv]
  have htop : Polynomial.derivative^[n + 1] P = 0 := by
    have : ∀ m : ℕ, P.natDegree < m → Polynomial.derivative^[m] P = 0 := by
      intro m hm
      exact Polynomial.iterate_derivative_eq_zero hm
    exact this (n + 1) (by omega)
  have hsum : (-∑ k ∈ Finset.range (n + 1),
        Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k + 1] P))
      - Polynomial.C lam * (-∑ k ∈ Finset.range (n + 1),
        Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k] P))
      = ∑ k ∈ Finset.range (n + 1),
          (Polynomial.C (lam⁻¹ ^ k) * (Polynomial.derivative^[k] P)
            - Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k + 1] P)) := by
    have hkey : Polynomial.C lam * ∑ k ∈ Finset.range (n + 1),
        Polynomial.C (lam⁻¹ ^ (k + 1)) * (Polynomial.derivative^[k] P)
        = ∑ k ∈ Finset.range (n + 1),
          Polynomial.C (lam⁻¹ ^ k) * (Polynomial.derivative^[k] P) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul]
      congr 2
      rw [pow_succ']
      rw [← mul_assoc, mul_inv_cancel₀ hlam, one_mul]
    rw [Finset.sum_sub_distrib, mul_neg, sub_neg_eq_add, hkey]
    ring
  rw [hsum, Finset.sum_range_sub' (fun k => Polynomial.C (lam⁻¹ ^ k) *
    (Polynomial.derivative^[k] P))]
  rw [htop, mul_zero, sub_zero, pow_zero, map_one, one_mul, Function.iterate_zero_apply]

/-- **Every complex polynomial has an antiderivative.** -/
theorem exists_derivative_eq (P : Polynomial ℂ) :
    ∃ Q : Polynomial ℂ, Polynomial.derivative Q = P := by
  classical
  refine ⟨∑ k ∈ Finset.range (P.natDegree + 1),
    Polynomial.C (P.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1), ?_⟩
  rw [map_sum]
  have hterm : ∀ k ∈ Finset.range (P.natDegree + 1),
      Polynomial.derivative (Polynomial.C (P.coeff k / ((k : ℂ) + 1)) * Polynomial.X ^ (k + 1))
        = Polynomial.C (P.coeff k) * Polynomial.X ^ k := by
    intro k _
    rw [Polynomial.derivative_C_mul, Polynomial.derivative_X_pow]
    have hne : ((k : ℂ) + 1) ≠ 0 := by
      intro hc
      have hre : ((k : ℂ) + 1).re = 0 := by rw [hc]; simp
      simp at hre
      have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      linarith
    rw [← mul_assoc, ← map_mul]
    congr 2
    push_cast
    field_simp
  rw [Finset.sum_congr rfl hterm]
  have hmono : ∀ k ∈ Finset.range (P.natDegree + 1),
      Polynomial.C (P.coeff k) * Polynomial.X ^ k = (Polynomial.monomial k) (P.coeff k) := by
    intro k _
    rw [Polynomial.C_mul_X_pow_eq_monomial]
  rw [Finset.sum_congr rfl hmono]
  exact (Polynomial.as_sum_range' P (P.natDegree + 1) (by omega)).symm

/-! ### Additivity of the obstruction -/

theorem Theta_sub (lam : ℂ) (u w : RatFunc ℂ) (β : ℂ) :
    Theta lam (u - w) β = Theta lam u β - Theta lam w β := by
  classical
  have hu : (Function.support fun d : ℕ =>
      ((-lam) ^ d / (Nat.factorial d : ℂ)) * polePart u β (d + 1)).Finite := by
    refine Set.Finite.subset (finite_support_polePart_at u β) ?_
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro hc
    exact hd (by rw [hc, mul_zero])
  have hw : (Function.support fun d : ℕ =>
      ((-lam) ^ d / (Nat.factorial d : ℂ)) * polePart w β (d + 1)).Finite := by
    refine Set.Finite.subset (finite_support_polePart_at w β) ?_
    intro d hd
    simp only [Function.mem_support, ne_eq] at hd ⊢
    intro hc
    exact hd (by rw [hc, mul_zero])
  rw [Theta, Theta, Theta, ← finsum_sub_distrib hu hw]
  refine finsum_congr fun d => ?_
  rw [sub_eq_add_neg, polePart_add, polePart_neg]
  ring

/-! ### No poles means polynomial -/

theorem exists_polynomial_of_no_poles {u : RatFunc ℂ}
    (h : ∀ β : ℂ, ∀ d : ℕ, 0 < d → polePart u β d = 0) :
    ∃ P : Polynomial ℂ, u = algebraMap (Polynomial ℂ) (RatFunc ℂ) P := by
  classical
  obtain ⟨R, c, hcpos, hc, hdec⟩ := exists_principalPart_decomposition u
  refine ⟨R, ?_⟩
  have hc0 : c = 0 := by
    ext p
    rcases Nat.eq_zero_or_pos p.2 with h0 | hpos
    · by_cases hmem : p ∈ c.support
      · have := hcpos p hmem
        omega
      · simpa using Finsupp.notMem_support_iff.mp hmem
    · rw [hc p.1 p.2 hpos, h p.1 p.2 hpos]
      simp
  rw [hdec, hc0, principalPartSum_zero, add_zero]

/-! ### Peeling one pole layer -/

/-- The pole coefficients of a finite combination of principal-part monomials of one order. -/
theorem polePart_layer (a : ℂ → ℂ) (S : Finset ℂ) (N : ℕ) (γ : ℂ) (d : ℕ)
    (hd : 0 < d) :
    polePart (∑ β ∈ S, algebraMap ℂ (RatFunc ℂ) (a β) * invLinPow β N) γ d
      = if γ ∈ S ∧ d = N then a γ else 0 := by
  classical
  rw [polePart_sum]
  by_cases hγ : γ ∈ S
  · rw [Finset.sum_eq_single γ]
    · rw [polePart_smul, polePart_invLinPow_self]
      by_cases hdN : d = N
      · rw [if_pos hdN, if_pos ⟨hγ, hdN⟩, mul_one]
      · rw [if_neg hdN, if_neg (by tauto), mul_zero]
    · intro β _ hβγ
      rw [polePart_smul, polePart_invLinPow_of_ne (by exact fun hc => hβγ hc.symm) N d hd,
        mul_zero]
    · intro hcon
      exact absurd hγ hcon
  · rw [if_neg (by tauto), Finset.sum_eq_zero]
    intro β hβ
    have hne : γ ≠ β := by
      intro hc
      exact hγ (hc ▸ hβ)
    rw [polePart_smul, polePart_invLinPow_of_ne hne N d hd, mul_zero]

/-- **The preimage exists as soon as the obstruction vanishes.** -/
theorem exists_preimage_of_Theta_zero (lam : ℂ) : ∀ (N : ℕ) (u : RatFunc ℂ),
    (∀ β : ℂ, ∀ d : ℕ, N < d → polePart u β d = 0) →
    (∀ β : ℂ, Theta lam u β = 0) →
    ∃ v : RatFunc ℂ, firstOrderOp lam v = u := by
  classical
  intro N
  induction N with
  | zero =>
      intro u hpol _
      obtain ⟨P, rfl⟩ := exists_polynomial_of_no_poles (fun β d hd => hpol β d hd)
      rcases eq_or_ne lam 0 with rfl | hlam
      · obtain ⟨Q, hQ⟩ := exists_derivative_eq P
        refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) Q, ?_⟩
        rw [firstOrderOp, map_zero, zero_mul, sub_zero, ratFuncDerivative_algebraMap, hQ]
      · obtain ⟨Q, hQ⟩ := exists_preimage_polynomial_of_ne_zero hlam P
        refine ⟨algebraMap (Polynomial ℂ) (RatFunc ℂ) Q, ?_⟩
        have hC : (algebraMap ℂ (RatFunc ℂ)) lam
            = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C lam) := by
          rw [RatFunc.algebraMap_C, RatFunc.algebraMap_eq_C]
        rw [firstOrderOp, ratFuncDerivative_algebraMap, hC, ← map_mul, ← map_sub, hQ]
  | succ N ih =>
      intro u hpol hTheta
      rcases Nat.eq_zero_or_pos N with hN0 | hNpos
      · subst hN0
        refine ih u (fun β d hd => ?_) hTheta
        rcases Nat.lt_or_ge 1 d with h1 | h1
        · exact hpol β d h1
        · have hd1 : d = 1 := by omega
          subst hd1
          have hvan : ∀ e, 1 ≤ e → polePart u β (e + 1) = 0 := by
            intro e he
            exact hpol β (e + 1) (by omega)
          have := Theta_eq_ThetaN lam u β hvan
          rw [hTheta β] at this
          rw [ThetaN, Finset.sum_range_one] at this
          have h2 : ((-lam) ^ 0 / (Nat.factorial 0 : ℂ)) * polePart u β (0 + 1) = 0 := this.symm
          norm_num at h2
          exact h2
      · have hfin : (Function.support fun β : ℂ => polePart u β (N + 1)).Finite := by
          refine Set.Finite.subset (Set.Finite.image Prod.fst (finite_support_polePart u)) ?_
          intro β hβ
          simp only [Function.mem_support, ne_eq] at hβ
          exact ⟨(β, N), by simpa using hβ, rfl⟩
        set S : Finset ℂ := hfin.toFinset with hS
        have hSmem : ∀ β : ℂ, β ∈ S ↔ polePart u β (N + 1) ≠ 0 := by
          intro β
          rw [hS, Set.Finite.mem_toFinset]
          simp only [Function.mem_support, ne_eq]
        set v₀ : RatFunc ℂ := ∑ β ∈ S,
          algebraMap ℂ (RatFunc ℂ) (-(polePart u β (N + 1)) / (N : ℂ)) * invLinPow β N with hv₀
        have hNne : ((N : ℂ)) ≠ 0 := by
          simp only [ne_eq, Nat.cast_eq_zero]
          omega
        have hlayer : ∀ γ d, 0 < d → polePart v₀ γ d
            = if γ ∈ S ∧ d = N then -(polePart u γ (N + 1)) / (N : ℂ) else 0 :=
          fun γ d hd => polePart_layer _ S N γ d hd
        have hopN : ∀ γ : ℂ, polePart (firstOrderOp lam v₀) γ (N + 1) = polePart u γ (N + 1) := by
          intro γ
          rw [firstOrderOp, polePart_deriv_sub, hlayer γ N hNpos,
            hlayer γ (N + 1) (by omega)]
          by_cases hγ : γ ∈ S
          · rw [if_pos ⟨hγ, rfl⟩, if_neg (by rintro ⟨-, hcon⟩; omega)]
            field_simp
            ring
          · rw [if_neg (by tauto), if_neg (by tauto)]
            have : polePart u γ (N + 1) = 0 := by
              by_contra hc
              exact hγ ((hSmem γ).mpr hc)
            rw [this]
            ring
        have hophigh : ∀ γ : ℂ, ∀ d, N + 1 < d → polePart (firstOrderOp lam v₀) γ d = 0 := by
          intro γ d hd
          obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
          rw [firstOrderOp, polePart_deriv_sub, hlayer γ e (by omega),
            hlayer γ (e + 1) (by omega), if_neg (by rintro ⟨-, hcon⟩; omega),
            if_neg (by rintro ⟨-, hcon⟩; omega)]
          ring
        obtain ⟨v, hv⟩ := ih (u - firstOrderOp lam v₀)
          (fun β d hd => by
            rw [sub_eq_add_neg, polePart_add, polePart_neg]
            rcases Nat.lt_or_ge (N + 1) d with hlt | hle
            · rw [hpol β d hlt, hophigh β d hlt]
              ring
            · have hdN : d = N + 1 := by omega
              subst hdN
              rw [hopN β]
              ring)
          (fun β => by
            rw [Theta_sub, hTheta β, Theta_firstOrderOp]
            ring)
        exact ⟨v + v₀, by rw [firstOrderOp_add, hv]; ring⟩

end

end GaloisForLFunctions.HTGeometry
