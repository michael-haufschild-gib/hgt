import GaloisForLFunctions.HTGeometry.RationalShiftOrbitPole

/-!
# No rational function has a Gamma-type multiplicative shift factor

The recurrence `Γ(s+λ+1) = (s+λ)Γ(s+λ)` says the Gamma translates are multiplicative shift
coordinates with factors `X+λ`.  A rational function cannot imitate a nontrivial monomial in those
factors: if `w(X+1) = w(X)·∏(X+λᵢ)^{mᵢ}` with pairwise incongruent shifts and some `mᵢ ≠ 0`, then
along the translation orbit of `-λᵢ` the order of `w` increases by `mᵢ` exactly once and is constant
elsewhere, so it cannot vanish at both ends of the orbit — which a rational function's order must.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Polynomial

noncomputable section

variable {r : ℕ}

/-- Composition with the unit shift translates root multiplicities. -/
theorem rootMultiplicity_comp_X_add_C_one {A : Polynomial ℂ} (hA : A ≠ 0) (a : ℂ) :
    (A.comp (X + C 1)).rootMultiplicity a = A.rootMultiplicity (a + 1) := by
  have hcomp : A.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hA
  have hfwd : ((X + C 1 : Polynomial ℂ)).comp (X - C 1) = (X : Polynomial ℂ) := by
    rw [add_comp, X_comp, C_comp]
    ring
  have hlin₁ : ((X - C (a + 1) : Polynomial ℂ)).comp (X + C 1) = X - C a := by
    rw [sub_comp, X_comp, C_comp, C_add]
    ring
  have hlin₂ : ((X - C a : Polynomial ℂ)).comp (X - C 1) = X - C (a + 1) := by
    rw [sub_comp, X_comp, C_comp, C_add]
    ring
  have hiff : ∀ k : ℕ, (k ≤ (A.comp (X + C 1)).rootMultiplicity a
      ↔ k ≤ A.rootMultiplicity (a + 1)) := by
    intro k
    rw [le_rootMultiplicity_iff hcomp, le_rootMultiplicity_iff hA]
    constructor
    · rintro ⟨D, hD⟩
      refine ⟨D.comp (X - C 1), ?_⟩
      have h2 := congrArg (fun P : Polynomial ℂ => P.comp (X - C 1)) hD
      simp only [mul_comp, pow_comp, comp_assoc, hfwd, comp_X, hlin₂] at h2
      exact h2
    · rintro ⟨D, hD⟩
      refine ⟨D.comp (X + C 1), ?_⟩
      have h2 := congrArg (fun P : Polynomial ℂ => P.comp (X + C 1)) hD
      simp only [mul_comp, pow_comp, hlin₁] at h2
      exact h2
  exact Nat.le_antisymm ((hiff _).mp le_rfl) ((hiff _).mpr le_rfl)

/-- The root multiplicity of a product of shifted linear factors. -/
theorem rootMultiplicity_prod_shift (lam : Fin r → ℂ) (e : Fin r → ℕ) (a : ℂ) :
    (∏ i : Fin r, (X + C (lam i)) ^ e i).rootMultiplicity a
      = ∑ i : Fin r, (if a + lam i = 0 then e i else 0) := by
  classical
  have hne : ∀ s : Finset (Fin r), (∏ i ∈ s, (X + C (lam i)) ^ e i) ≠ 0 := by
    intro s
    refine Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ ?_
    exact X_add_C_ne_zero (lam i)
  have hstep : ∀ s : Finset (Fin r),
      (∏ i ∈ s, (X + C (lam i)) ^ e i).rootMultiplicity a
        = ∑ i ∈ s, (if a + lam i = 0 then e i else 0) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
        rw [Finset.prod_insert hj, Finset.sum_insert hj,
          rootMultiplicity_mul (mul_ne_zero (pow_ne_zero _ (X_add_C_ne_zero (lam j))) (hne s)), ih]
        congr 1
        have hfac : ((X + C (lam j)) : Polynomial ℂ) = X - C (-lam j) := by
          simp only [map_neg, sub_neg_eq_add]
        by_cases hja : a + lam j = 0
        · rw [if_pos hja, hfac]
          have haj : a = -lam j := by linear_combination hja
          subst haj
          exact rootMultiplicity_X_sub_C_pow _ _
        · rw [if_neg hja]
          have hroot : ¬ ((X + C (lam j)) ^ e j).IsRoot a := by
            intro hr
            rw [IsRoot, eval_pow, eval_add, eval_X, eval_C] at hr
            exact hja (pow_eq_zero_iff'.mp hr).1
          exact rootMultiplicity_eq_zero hroot
  exact hstep Finset.univ


/-- The positive part of an exponent vector, as a product of shifted linear factors. -/
def shiftPosPart (lam : Fin r → ℂ) (m : Fin r → ℤ) : Polynomial ℂ :=
  ∏ i : Fin r, (X + C (lam i)) ^ ((m i).toNat)

/-- The negative part of an exponent vector, as a product of shifted linear factors. -/
def shiftNegPart (lam : Fin r → ℂ) (m : Fin r → ℤ) : Polynomial ℂ :=
  ∏ i : Fin r, (X + C (lam i)) ^ ((-(m i)).toNat)

theorem shiftPosPart_ne_zero (lam : Fin r → ℂ) (m : Fin r → ℤ) :
    shiftPosPart lam m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_add_C_ne_zero (lam i))

theorem shiftNegPart_ne_zero (lam : Fin r → ℂ) (m : Fin r → ℤ) :
    shiftNegPart lam m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun i _ => pow_ne_zero _ (X_add_C_ne_zero (lam i))

/-- The rational monomial in the shift factors, as a quotient of its two parts. -/
theorem shiftMonomial_eq_div (lam : Fin r → ℂ) (m : Fin r → ℤ) :
    (∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (m i))
      = algebraMap (Polynomial ℂ) (RatFunc ℂ) (shiftPosPart lam m) /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (shiftNegPart lam m) := by
  classical
  rw [shiftPosPart, shiftNegPart, map_prod, map_prod, ← Finset.prod_div_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hfac : algebraMap (Polynomial ℂ) (RatFunc ℂ) (X + C (lam i))
      = RatFunc.X + RatFunc.C (lam i) := by
    rw [map_add, RatFunc.algebraMap_X, RatFunc.algebraMap_C]
  have hne : (RatFunc.X + RatFunc.C (lam i)) ≠ 0 := by
    rw [← hfac]
    exact RatFunc.algebraMap_ne_zero (X_add_C_ne_zero (lam i))
  rw [map_pow, map_pow, hfac]
  by_cases hpos : 0 ≤ m i
  · rw [show ((-(m i)).toNat) = 0 by omega, pow_zero, div_one,
      ← zpow_natCast (RatFunc.X + RatFunc.C (lam i)) ((m i).toNat)]
    congr 1
    omega
  · rw [show ((m i).toNat) = 0 by omega, pow_zero, one_div,
      ← zpow_natCast (RatFunc.X + RatFunc.C (lam i)) ((-(m i)).toNat), ← zpow_neg]
    congr 1
    omega

/-- **No rational multiplicative shift factor.**  With pairwise incongruent shifts a rational
function cannot satisfy `w(X+1) = w(X)·∏(X+λ_i)^{m_i}` unless the exponent at each shift
vanishes. -/
theorem ratShift_ne_mul_shiftMonomial (lam : Fin r → ℂ)
    (hincong : ∀ i i', i ≠ i' → ∀ n : ℤ, lam i - lam i' ≠ (n : ℂ))
    (m : Fin r → ℤ) (i₀ : Fin r) (hm : m i₀ ≠ 0) {w : RatFunc ℂ} (hw : w ≠ 0) :
    ratShift w ≠ w * ∏ i : Fin r, (RatFunc.X + RatFunc.C (lam i)) ^ (m i) := by
  classical
  intro heq
  set A : Polynomial ℂ := w.num with hAdef
  set B : Polynomial ℂ := w.denom with hBdef
  have hB : B ≠ 0 := w.denom_ne_zero
  have hA : A ≠ 0 := by
    intro h0
    exact hw (by rw [← RatFunc.num_div_denom w, ← hAdef, h0, map_zero, zero_div])
  set qp : Polynomial ℂ := shiftPosPart lam m with hqp
  set qn : Polynomial ℂ := shiftNegPart lam m with hqn
  have hqpne : qp ≠ 0 := shiftPosPart_ne_zero lam m
  have hqnne : qn ≠ 0 := shiftNegPart_ne_zero lam m
  have hAc : A.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hA
  have hBc : B.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hB
  -- the polynomial form of the shift equation
  have hpoly : A.comp (X + C 1) * B * qn = A * (B.comp (X + C 1)) * qp := by
    apply RatFunc.algebraMap_injective ℂ
    have hw' : algebraMap (Polynomial ℂ) (RatFunc ℂ) A /
        algebraMap (Polynomial ℂ) (RatFunc ℂ) B = w := RatFunc.num_div_denom w
    have hshiftw : ratShift w =
        algebraMap (Polynomial ℂ) (RatFunc ℂ) (A.comp (X + C 1)) /
          algebraMap (Polynomial ℂ) (RatFunc ℂ) (B.comp (X + C 1)) := by
      rw [← hw', map_div₀, ratShift_algebraMap, ratShift_algebraMap]
    have hBK : algebraMap (Polynomial ℂ) (RatFunc ℂ) B ≠ 0 :=
      RatFunc.algebraMap_ne_zero hB
    have hBcK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (B.comp (X + C 1)) ≠ 0 :=
      RatFunc.algebraMap_ne_zero hBc
    have hqnK : algebraMap (Polynomial ℂ) (RatFunc ℂ) qn ≠ 0 :=
      RatFunc.algebraMap_ne_zero hqnne
    rw [shiftMonomial_eq_div lam m, hshiftw, ← hw', ← hqp, ← hqn, div_mul_div_comm,
      div_eq_div_iff hBcK (mul_ne_zero hBK hqnK)] at heq
    rw [map_mul, map_mul, map_mul, map_mul]
    linear_combination heq
  -- the order of the two parts along the orbit
  set pt : ℤ → ℂ := fun k => -lam i₀ + (k : ℂ) with hpt
  have hptinj : Function.Injective pt := by
    intro k l hkl
    have : ((k : ℂ)) = ((l : ℂ)) := by
      have := hkl
      rw [hpt] at this
      linear_combination this
    exact_mod_cast this
  have horbit : ∀ (i : Fin r) (k : ℤ), pt k + lam i = 0 ↔ (i = i₀ ∧ k = 0) := by
    intro i k
    constructor
    · intro h
      by_cases hi : i = i₀
      · subst hi
        refine ⟨rfl, ?_⟩
        have : (k : ℂ) = 0 := by rw [hpt] at h; linear_combination h
        exact_mod_cast this
      · exfalso
        refine hincong i i₀ hi (-k) ?_
        rw [hpt] at h
        push_cast
        linear_combination h
    · rintro ⟨rfl, rfl⟩
      rw [hpt]
      simp
  have hqpmult : ∀ k : ℤ, qp.rootMultiplicity (pt k)
      = if k = 0 then (m i₀).toNat else 0 := by
    intro k
    rw [hqp, shiftPosPart, rootMultiplicity_prod_shift]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, Finset.sum_eq_single i₀]
      · rw [if_pos ((horbit i₀ 0).mpr ⟨rfl, rfl⟩)]
      · intro i _ hi
        rw [if_neg (fun h => hi ((horbit i 0).mp h).1)]
      · intro hnot
        exact absurd (Finset.mem_univ i₀) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (fun h => hk ((horbit i k).mp h).2)]
  have hqnmult : ∀ k : ℤ, qn.rootMultiplicity (pt k)
      = if k = 0 then (-(m i₀)).toNat else 0 := by
    intro k
    rw [hqn, shiftNegPart, rootMultiplicity_prod_shift]
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl, Finset.sum_eq_single i₀]
      · rw [if_pos ((horbit i₀ 0).mpr ⟨rfl, rfl⟩)]
      · intro i _ hi
        rw [if_neg (fun h => hi ((horbit i 0).mp h).1)]
      · intro hnot
        exact absurd (Finset.mem_univ i₀) hnot
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [if_neg (fun h => hk ((horbit i k).mp h).2)]
  have hshiftmult : ∀ (P : Polynomial ℂ), P ≠ 0 → ∀ k : ℤ,
      (P.comp (X + C 1)).rootMultiplicity (pt k) = P.rootMultiplicity (pt (k + 1)) := by
    intro P hP k
    rw [rootMultiplicity_comp_X_add_C_one hP]
    congr 1
    rw [hpt]
    push_cast
    ring
  -- the order defect along the orbit
  set n : ℤ → ℤ := fun k =>
    (A.rootMultiplicity (pt k) : ℤ) - (B.rootMultiplicity (pt k) : ℤ) with hn
  have hrec : ∀ k : ℤ, n (k + 1) - n k = if k = 0 then m i₀ else 0 := by
    intro k
    have hmul := congrArg (fun P : Polynomial ℂ => P.rootMultiplicity (pt k)) hpoly
    rw [rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hAc hB) hqnne),
      rootMultiplicity_mul (mul_ne_zero hAc hB),
      rootMultiplicity_mul (mul_ne_zero (mul_ne_zero hA hBc) hqpne),
      rootMultiplicity_mul (mul_ne_zero hA hBc),
      hshiftmult A hA k, hshiftmult B hB k, hqpmult k, hqnmult k] at hmul
    by_cases hk : k = 0
    · subst hk
      rw [if_pos rfl]
      have hcast : (A.rootMultiplicity (pt (0 + 1)) : ℤ) + (B.rootMultiplicity (pt 0) : ℤ)
          + (((-(m i₀)).toNat : ℕ) : ℤ)
          = (A.rootMultiplicity (pt 0) : ℤ) + (B.rootMultiplicity (pt (0 + 1)) : ℤ)
            + (((m i₀).toNat : ℕ) : ℤ) := by exact_mod_cast hmul
      rw [hn]
      simp only
      omega
    · simp only [if_neg hk] at hmul
      rw [if_neg hk]
      have hcast : (A.rootMultiplicity (pt (k + 1)) : ℤ) + (B.rootMultiplicity (pt k) : ℤ)
          = (A.rootMultiplicity (pt k) : ℤ) + (B.rootMultiplicity (pt (k + 1)) : ℤ) := by
        have hmul' : A.rootMultiplicity (pt (k + 1)) + B.rootMultiplicity (pt k)
            = A.rootMultiplicity (pt k) + B.rootMultiplicity (pt (k + 1)) := by
          simpa using hmul
        exact_mod_cast hmul'
      rw [hn]
      simp only
      omega
  -- the defect is constant on each half of the orbit
  have hleft : ∀ j : ℕ, n (-(j : ℤ)) = n 0 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hk : ((-(j : ℤ) - 1) : ℤ) ≠ 0 := by omega
        have := hrec (-(j : ℤ) - 1)
        rw [if_neg hk] at this
        have hstep : n (-((j : ℤ) + 1)) = n (-(j : ℤ)) := by
          have hval : (-(j : ℤ) - 1) + 1 = -(j : ℤ) := by ring
          rw [hval] at this
          have : n (-(j : ℤ)) - n (-(j : ℤ) - 1) = 0 := this
          have h2 : (-(j : ℤ) - 1) = -((j : ℤ) + 1) := by ring
          rw [h2] at this
          omega
        rw [show ((j : ℤ) + 1) = ((j + 1 : ℕ) : ℤ) by push_cast; ring] at hstep
        rw [hstep, ih]
  have hright : ∀ j : ℕ, n (1 + (j : ℤ)) = n 1 := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have hk : ((1 + (j : ℤ)) : ℤ) ≠ 0 := by omega
        have hstep := hrec (1 + (j : ℤ))
        rw [if_neg hk] at hstep
        have : n (1 + (j : ℤ) + 1) = n (1 + (j : ℤ)) := by omega
        rw [show (1 + ((j + 1 : ℕ) : ℤ)) = 1 + (j : ℤ) + 1 by push_cast; ring, this, ih]
  -- a rational function has only finitely many zeros and poles
  have hfin : {k : ℤ | n k ≠ 0}.Finite := by
    have hsub : {k : ℤ | n k ≠ 0}
        ⊆ pt ⁻¹' ({x : ℂ | A.IsRoot x} ∪ {x : ℂ | B.IsRoot x}) := by
      intro k hk
      by_contra hnot
      simp only [Set.mem_preimage, Set.mem_union, Set.mem_setOf_eq, not_or] at hnot
      have h1 : A.rootMultiplicity (pt k) = 0 := rootMultiplicity_eq_zero hnot.1
      have h2 : B.rootMultiplicity (pt k) = 0 := rootMultiplicity_eq_zero hnot.2
      have : n k = 0 := by rw [hn]; simp only; rw [h1, h2]; ring
      exact hk this
    refine Set.Finite.subset (Set.Finite.preimage hptinj.injOn ?_) hsub
    exact (Polynomial.finite_setOf_isRoot hA).union (Polynomial.finite_setOf_isRoot hB)
  -- both halves are eventually zero, so the jump vanishes
  have hzeroLeft : n 0 = 0 := by
    by_contra hne
    have hall : ∀ j : ℕ, (-(j : ℤ)) ∈ {k : ℤ | n k ≠ 0} := by
      intro j
      have := hleft j
      simp only [Set.mem_setOf_eq]
      rw [this]
      exact hne
    have hinj : Function.Injective (fun j : ℕ => (-(j : ℤ))) := by
      intro a b hab
      simp only at hab
      omega
    exact Set.infinite_of_injective_forall_mem (f := fun j : ℕ => (-(j : ℤ)))
      hinj hall hfin
  have hzeroRight : n 1 = 0 := by
    by_contra hne
    have hall : ∀ j : ℕ, (1 + (j : ℤ)) ∈ {k : ℤ | n k ≠ 0} := by
      intro j
      have := hright j
      simp only [Set.mem_setOf_eq]
      rw [this]
      exact hne
    have hinj : Function.Injective (fun j : ℕ => (1 + (j : ℤ))) := by
      intro a b hab
      simp only at hab
      omega
    exact Set.infinite_of_injective_forall_mem (f := fun j : ℕ => (1 + (j : ℤ)))
      hinj hall hfin
  have hjump := hrec 0
  rw [if_pos rfl, hzeroLeft] at hjump
  simp only [zero_add, sub_zero] at hjump
  rw [hzeroRight] at hjump
  exact hm hjump.symm

end

end GaloisForLFunctions.HTGeometry
