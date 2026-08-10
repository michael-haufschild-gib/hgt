import GaloisForLFunctions.HTGeometry.HolderShiftElimination

/-!
# The shift-elimination engine over an abstract base field

`HolderShiftElimination` runs the Hölder elimination over the rational function field `ℂ(X)` with
the unit shift `X ↦ X+1`.  The q-analogue of Hölder's theorem needs the identical elimination over
the larger field `ℂ(z, qᶻ)` with the automorphism `z ↦ z+1`, `qᶻ ↦ q·qᶻ`, so this module carries
out the same argument over an arbitrary `ℂ`-algebra field `K` with an arbitrary ring endomorphism
`σ`.  The analytic inputs enter as hypotheses of the elimination theorem: `σ` is injective and
fixes the constants, every `σ`-invariant element of `K` is a constant, and no nonzero constant
combination of the jet increments is a `σ`-coboundary.

The jet bookkeeping (`degSum` and its lemmas) and the base translation
`mvPolynomialBaseTranslation` are reused unchanged from the classical development.
-/

noncomputable section

namespace GaloisForLFunctions

open MvPolynomial

section GenericShift

variable {K : Type*} [Field K] {m : ℕ}

theorem totalDegree_eq_sup_degSumGen (P : MvPolynomial (Fin m) K) :
    P.totalDegree = P.support.sup degSum := rfl

namespace GenericShiftHolder

def jetTranslateGen (σ : K →+* K) (rj : ℕ → K) (m : ℕ) :
    MvPolynomial (Fin m) (K) →+* MvPolynomial (Fin m) (K) :=
  ((mvPolynomialBaseTranslation
      (fun j : Fin m => rj (j : ℕ))).toAlgHom.toRingHom).comp
    (MvPolynomial.map σ)

theorem jetTranslate_CGen (σ : K →+* K) (rj : ℕ → K) (k : K) :
    jetTranslateGen σ rj m (C k) = C (σ k) := by
  unfold jetTranslateGen
  rw [RingHom.comp_apply, MvPolynomial.map_C]
  rw [show (C (σ k) : MvPolynomial (Fin m) (K))
      = algebraMap (K) (MvPolynomial (Fin m) (K)) (σ k) from rfl]
  exact (mvPolynomialBaseTranslation _).commutes _

theorem jetTranslate_XGen (σ : K →+* K) (rj : ℕ → K) (j : Fin m) :
    jetTranslateGen σ rj m (X j) = X j + C (rj (j : ℕ)) := by
  unfold jetTranslateGen
  rw [RingHom.comp_apply, MvPolynomial.map_X]
  exact mvPolynomialBaseTranslation_X _ j

/-- The translated monomial `Π_j (Y_j + polePart j)^{α_j}`. -/
def transMonomialGen (rj : ℕ → K) (α : Fin m →₀ ℕ) : MvPolynomial (Fin m) (K) :=
  ∏ j : Fin m, (X j + C (rj (j : ℕ))) ^ (α j)

theorem jetTranslate_monomialGen (σ : K →+* K) (rj : ℕ → K) (α : Fin m →₀ ℕ) (a : K) :
    jetTranslateGen σ rj m (monomial α a) = C (σ a) * transMonomialGen rj α := by
  rw [MvPolynomial.monomial_eq, map_mul]
  congr 1
  · exact jetTranslate_CGen σ rj a
  · rw [Finsupp.prod_fintype _ _ (fun j => pow_zero _), map_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [map_pow, jetTranslate_XGen σ rj]

theorem transMonomial_zeroGen (rj : ℕ → K) : transMonomialGen rj (0 : Fin m →₀ ℕ) = 1 := by
  unfold transMonomialGen
  refine Finset.prod_eq_one fun j _ => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, pow_zero]

theorem transMonomial_add_singleGen (rj : ℕ → K) (α : Fin m →₀ ℕ) (j : Fin m) :
    transMonomialGen rj (α + Finsupp.single j 1)
      = transMonomialGen rj α * (X j + C (rj (j : ℕ))) := by
  unfold transMonomialGen
  rw [Finset.prod_congr rfl (fun k _ => by rw [Finsupp.add_apply, pow_add]),
    Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_eq_single j
    (fun k _ hk => by
      rw [Finsupp.single_apply, if_neg (fun h => hk (Eq.symm h)), pow_zero])
    (fun h => absurd (Finset.mem_univ j) h)]
  rw [Finsupp.single_apply, if_pos rfl, pow_one]

/-- The subtop layer of a translated monomial: `Σ_j α_j·polePart j·Y^{α − e_j}`. -/
def subTopMonomialGen (rj : ℕ → K) (α : Fin m →₀ ℕ) : MvPolynomial (Fin m) (K) :=
  ∑ j : Fin m,
    monomial (α - Finsupp.single j 1) ((α j : K) * rj (j : ℕ))

theorem subTopMonomial_zeroGen (rj : ℕ → K) : subTopMonomialGen rj (0 : Fin m →₀ ℕ) = 0 := by
  unfold subTopMonomialGen
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [Finsupp.coe_zero, Pi.zero_apply, Nat.cast_zero, zero_mul, map_zero]

theorem X_eq_monomial (j : Fin m) :
    (X j : MvPolynomial (Fin m) (K)) = monomial (Finsupp.single j 1) 1 := rfl

theorem subTopMonomial_add_singleGen (rj : ℕ → K) (α : Fin m →₀ ℕ) (j : Fin m) :
    subTopMonomialGen rj (α + Finsupp.single j 1)
      = subTopMonomialGen rj α * X j + C (rj (j : ℕ)) * monomial α 1 := by
  unfold subTopMonomialGen
  rw [Finset.sum_mul]
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j),
    ← Finset.sum_erase_add _
      (fun k => monomial (α - Finsupp.single k 1) ((α k : K) * rj (k : ℕ))
        * X j) (Finset.mem_univ j), add_assoc]
  congr 1
  · -- off-`j` terms match after commuting the added unit past the removed one
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkj : k ≠ j := Finset.ne_of_mem_erase hk
    rw [X_eq_monomial, monomial_mul, mul_one]
    have happ : ((α + Finsupp.single j 1 : Fin m →₀ ℕ)) k = α k := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_neg (fun h => hkj (Eq.symm h)),
        add_zero]
    rw [happ]
    have hidx : (α + Finsupp.single j 1 : Fin m →₀ ℕ) - Finsupp.single k 1
        = α - Finsupp.single k 1 + Finsupp.single j 1 := by
      ext l
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    rw [hidx]
  · -- the `j` term absorbs the extra `C (polePart j) * monomial α 1`
    rw [X_eq_monomial, monomial_mul, mul_one, add_single_sub_single]
    have happ : ((α + Finsupp.single j 1 : Fin m →₀ ℕ)) j = α j + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
    rw [happ]
    have hCmul : C (rj (j : ℕ)) * (monomial α 1 : MvPolynomial (Fin m) (K))
        = monomial α (rj (j : ℕ)) := by
      rw [MvPolynomial.C_mul_monomial, mul_one]
    rw [hCmul]
    by_cases hα : α j = 0
    · rw [hα, Nat.cast_zero, zero_mul, map_zero, zero_add, Nat.cast_one, one_mul]
      rw [zero_add]
    · rw [sub_single_add_single hα]
      rw [show ((α j + 1 : ℕ) : K) = (α j : K) + 1 by push_cast; ring]
      rw [add_mul, one_mul, map_add]

/-- **Layer decomposition of a translated monomial.**  `Π (Y_j + c_j)^{α_j}` is the original
monomial, plus the gradient layer `Σ_j α_j·c_j·Y^{α−e_j}`, plus an error supported in
degrees at most `degSum α − 2`. -/
theorem transMonomial_decomposition (rj : ℕ → K) (α : Fin m →₀ ℕ) :
    ∃ E : MvPolynomial (Fin m) (K),
      transMonomialGen rj α = monomial α 1 + subTopMonomialGen rj α + E ∧
      ∀ β : Fin m →₀ ℕ, degSum α ≤ degSum β + 1 → coeff β E = 0 := by
  generalize hN : degSum α = N
  induction N using Nat.strong_induction_on generalizing α with
  | _ N ih =>
    rcases eq_or_ne α 0 with rfl | hα0
    · refine ⟨0, ?_, fun β _ => coeff_zero β⟩
      rw [transMonomial_zeroGen rj, subTopMonomial_zeroGen rj, add_zero, add_zero]
      rw [show (monomial (0 : Fin m →₀ ℕ) (1 : K)) = C 1 from (C_apply).symm, map_one]
    · have hpos : 0 < degSum α := by
        rcases Nat.eq_zero_or_pos (degSum α) with h0 | h
        · exfalso
          apply hα0
          ext k
          have hk : α k ≤ degSum α := by
            rw [degSum_eq_univ_sum]
            exact Finset.single_le_sum (f := fun k => α k) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ k)
          simp only [Finsupp.coe_zero, Pi.zero_apply]
          omega
        · exact h
      obtain ⟨j, hj⟩ := exists_apply_ne_zero_of_degSum_pos hpos
      set α' := α - Finsupp.single j 1 with hα'_def
      have hres : α' + Finsupp.single j 1 = α := sub_single_add_single hj
      have hdeg' : degSum α' + 1 = degSum α := degSum_sub_single hj
      obtain ⟨E', hE'eq, hE'coeff⟩ := ih (degSum α') (by omega) α' rfl
      refine ⟨C (rj (j : ℕ)) * subTopMonomialGen rj α'
        + E' * (X j + C (rj (j : ℕ))), ?_, ?_⟩
      · rw [← hres, transMonomial_add_singleGen rj, hE'eq, subTopMonomial_add_singleGen rj,
          show (monomial (α' + Finsupp.single j 1) (1 : K))
              = monomial α' 1 * X j by
            rw [X_eq_monomial, monomial_mul, mul_one]]
        ring
      · intro β hβ
        rw [← hN, ← hdeg'] at hβ
        have h1 : coeff β (C (rj (j : ℕ)) * subTopMonomialGen rj α') = 0 := by
          rw [coeff_C_mul]
          have hsub : coeff β (subTopMonomialGen rj α') = 0 := by
            unfold subTopMonomialGen
            rw [coeff_sum]
            refine Finset.sum_eq_zero fun k _ => ?_
            by_cases hk : α' k = 0
            · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
            · rw [coeff_monomial]
              refine if_neg fun hEq => ?_
              have hlt := degSum_sub_single hk
              rw [hEq] at hlt
              omega
          rw [hsub, mul_zero]
        have h2 : coeff β (E' * (X j + C (rj (j : ℕ)))) = 0 := by
          rw [mul_add, coeff_add]
          have h2a : coeff β (E' * X j) = 0 := by
            rw [coeff_mul_X']
            by_cases hmem : j ∈ β.support
            · rw [if_pos hmem]
              refine hE'coeff _ ?_
              have hdegβ := degSum_sub_single (Finsupp.mem_support_iff.mp hmem)
              omega
            · rw [if_neg hmem]
          have h2b : coeff β (E' * C (rj (j : ℕ))) = 0 := by
            rw [mul_comm, coeff_C_mul, hE'coeff β (by omega), mul_zero]
          rw [h2a, h2b, add_zero]
        rw [coeff_add, h1, h2, add_zero]

theorem coeff_transMonomial_of_degSum_eqGen (rj : ℕ → K) {α β : Fin m →₀ ℕ}
    (h : degSum β = degSum α) :
    coeff β (transMonomialGen rj α) = if α = β then 1 else 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition rj α
  rw [hEq, coeff_add, coeff_add, coeff_monomial]
  have h1 : coeff β (subTopMonomialGen rj α) = 0 := by
    unfold subTopMonomialGen
    rw [coeff_sum]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : α k = 0
    · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
    · rw [coeff_monomial]
      refine if_neg fun hEq' => ?_
      have hlt := degSum_sub_single hk
      rw [hEq'] at hlt
      omega
  rw [h1, hE β (by omega), add_zero, add_zero]

theorem coeff_transMonomial_of_degSum_succGen (rj : ℕ → K) {α β : Fin m →₀ ℕ}
    (h : degSum β + 1 = degSum α) :
    coeff β (transMonomialGen rj α)
      = ∑ j : Fin m, if α = β + Finsupp.single j 1
          then (α j : K) * rj (j : ℕ) else 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition rj α
  rw [hEq, coeff_add, coeff_add, coeff_monomial,
    if_neg (fun hEq' => by rw [hEq'] at h; omega), hE β (by omega), zero_add, add_zero]
  unfold subTopMonomialGen
  rw [coeff_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_monomial]
  by_cases hj : α j = 0
  · rw [if_neg, if_neg]
    · intro hEq'
      have : ((β + Finsupp.single j 1 : Fin m →₀ ℕ)) j = α j := by rw [← hEq']
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl] at this
      omega
    · intro hEq'
      have : α - Finsupp.single j 1 = α := by
        ext l
        simp only [Finsupp.tsub_apply, Finsupp.single_apply]
        by_cases hl : j = l
        · subst hl; omega
        · rw [if_neg hl]; omega
      rw [this] at hEq'
      rw [hEq'] at h
      omega
  · have hiff : (α - Finsupp.single j 1 = β) ↔ (α = β + Finsupp.single j 1) := by
      constructor
      · intro hEq'
        rw [← hEq', sub_single_add_single hj]
      · intro hEq'
        rw [hEq', add_single_sub_single]
    by_cases hcase : α = β + Finsupp.single j 1
    · rw [if_pos (hiff.mpr hcase), if_pos hcase]
    · rw [if_neg (fun h' => hcase (hiff.mp h')), if_neg hcase]

theorem coeff_transMonomial_of_degSum_ltGen (rj : ℕ → K) {α β : Fin m →₀ ℕ}
    (h : degSum α < degSum β) :
    coeff β (transMonomialGen rj α) = 0 := by
  obtain ⟨E, hEq, hE⟩ := transMonomial_decomposition rj α
  rw [hEq, coeff_add, coeff_add, coeff_monomial,
    if_neg (fun hEq' => by rw [hEq'] at h; omega), hE β (by omega), zero_add, add_zero]
  unfold subTopMonomialGen
  rw [coeff_sum]
  refine Finset.sum_eq_zero fun k _ => ?_
  by_cases hk : α k = 0
  · rw [hk, Nat.cast_zero, zero_mul, map_zero, coeff_zero]
  · rw [coeff_monomial]
    refine if_neg fun hEq' => ?_
    have hlt := degSum_sub_single hk
    rw [hEq'] at hlt
    omega

theorem totalDegree_transMonomial_leGen (rj : ℕ → K) (α : Fin m →₀ ℕ) :
    (transMonomialGen rj α).totalDegree ≤ degSum α := by
  refine le_trans (MvPolynomial.totalDegree_finsetProd _ _) ?_
  rw [degSum_eq_univ_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  refine le_trans (MvPolynomial.totalDegree_pow _ _) ?_
  have hle : (X j + C (rj (j : ℕ)) :
      MvPolynomial (Fin m) (K)).totalDegree ≤ 1 := by
    refine le_trans (MvPolynomial.totalDegree_add _ _) ?_
    rw [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
    omega
  calc (α j) * (X j + C (rj (j : ℕ)) :
      MvPolynomial (Fin m) (K)).totalDegree ≤ (α j) * 1 :=
        Nat.mul_le_mul_left _ hle
    _ = α j := Nat.mul_one _

/-- The jet substitution expanded over the support. -/
theorem jetTranslate_eq_sumGen (σ : K →+* K) (rj : ℕ → K) (P : MvPolynomial (Fin m) (K)) :
    jetTranslateGen σ rj m P
      = ∑ α ∈ P.support, C (σ (coeff α P)) * transMonomialGen rj α := by
  conv_lhs => rw [P.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun α _ => jetTranslate_monomialGen σ rj α _

theorem totalDegree_jetTranslate_leGen (σ : K →+* K) (rj : ℕ → K) (P : MvPolynomial (Fin m) (K)) :
    (jetTranslateGen σ rj m P).totalDegree ≤ P.totalDegree := by
  rw [jetTranslate_eq_sumGen σ rj]
  refine le_trans (MvPolynomial.totalDegree_finsetSum _ _) ?_
  refine Finset.sup_le fun α hα => ?_
  calc (C (σ (coeff α P)) * transMonomialGen rj α).totalDegree
      ≤ (C (σ (coeff α P)) :
          MvPolynomial (Fin m) (K)).totalDegree + (transMonomialGen rj α).totalDegree :=
        MvPolynomial.totalDegree_mul _ _
    _ ≤ 0 + degSum α := by
        exact Nat.add_le_add (le_of_eq (MvPolynomial.totalDegree_C _))
          (totalDegree_transMonomial_leGen rj α)
    _ ≤ P.totalDegree := by
        rw [Nat.zero_add]
        exact MvPolynomial.le_totalDegree hα

/-- **Top-layer law of the jet substitution.**  On the highest jet-degree layer the
substitution acts coefficientwise by the shift. -/
theorem coeff_jetTranslate_of_le_degSumGen (σ : K →+* K) (rj : ℕ → K) {P : MvPolynomial (Fin m) (K)}
    {β : Fin m →₀ ℕ} (hd : ∀ α ∈ P.support, degSum α ≤ degSum β) :
    coeff β (jetTranslateGen σ rj m P) = σ (coeff β P) := by
  rw [jetTranslate_eq_sumGen σ rj, coeff_sum]
  have hstep : ∀ α ∈ P.support,
      coeff β (C (σ (coeff α P)) * transMonomialGen rj α)
        = if α = β then σ (coeff α P) else 0 := by
    intro α hα
    rw [coeff_C_mul]
    rcases lt_or_eq_of_le (hd α hα) with hlt | heq
    · rw [coeff_transMonomial_of_degSum_ltGen rj hlt, mul_zero,
        if_neg (fun hEq => by rw [hEq] at hlt; omega)]
    · rw [coeff_transMonomial_of_degSum_eqGen rj heq.symm]
      by_cases hcase : α = β
      · rw [if_pos hcase, if_pos hcase, mul_one]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_ite_eq' P.support β
    (fun α => σ (coeff α P))]
  by_cases hβ : β ∈ P.support
  · rw [if_pos hβ]
  · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero]

/-- **Subtop-layer law of the jet substitution.**  One layer below the top, the substitution
acts by the shift plus the gradient term collecting the pole parts. -/
theorem coeff_jetTranslate_of_le_degSum_succGen (σ : K →+* K) (rj : ℕ → K) {P : MvPolynomial (Fin m) (K)}
    {β : Fin m →₀ ℕ} (hd : ∀ α ∈ P.support, degSum α ≤ degSum β + 1) :
    coeff β (jetTranslateGen σ rj m P) = σ (coeff β P)
      + ∑ j : Fin m, ((β j + 1 : ℕ) : K) * rj (j : ℕ)
          * σ (coeff (β + Finsupp.single j 1) P) := by
  rw [jetTranslate_eq_sumGen σ rj, coeff_sum]
  have hstep : ∀ α ∈ P.support,
      coeff β (C (σ (coeff α P)) * transMonomialGen rj α)
        = (if α = β then σ (coeff α P) else 0)
          + ∑ j : Fin m, if α = β + Finsupp.single j 1
              then σ (coeff α P) * ((α j : K) * rj (j : ℕ)) else 0 := by
    intro α hα
    rw [coeff_C_mul]
    have hcases : degSum α < degSum β ∨ degSum α = degSum β
        ∨ degSum α = degSum β + 1 := by
      have := hd α hα
      omega
    rcases hcases with hlt | heq | hsucc
    · rw [coeff_transMonomial_of_degSum_ltGen rj hlt, mul_zero,
        if_neg (fun hEq => by rw [hEq] at hlt; omega)]
      rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hEq => by
        rw [hEq, degSum_add, degSum_single] at hlt
        omega)), add_zero]
    · rw [coeff_transMonomial_of_degSum_eqGen rj heq.symm]
      rw [Finset.sum_eq_zero (fun j _ => if_neg (fun hEq => by
        rw [hEq, degSum_add, degSum_single] at heq
        omega)), add_zero]
      by_cases hcase : α = β
      · rw [if_pos hcase, if_pos hcase, mul_one]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
    · rw [coeff_transMonomial_of_degSum_succGen rj (by omega), Finset.mul_sum]
      rw [if_neg (fun hEq => by rw [hEq] at hsucc; omega), zero_add]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hcase : α = β + Finsupp.single j 1
      · rw [if_pos hcase, if_pos hcase]
      · rw [if_neg hcase, if_neg hcase, mul_zero]
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  congr 1
  · rw [Finset.sum_ite_eq' P.support β (fun α => σ (coeff α P))]
    by_cases hβ : β ∈ P.support
    · rw [if_pos hβ]
    · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero]
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_ite_eq' P.support (β + Finsupp.single j 1)
      (fun α => σ (coeff α P) * ((α j : K) * rj (j : ℕ)))]
    have happ : ((β + Finsupp.single j 1 : Fin m →₀ ℕ)) j = β j + 1 := by
      rw [Finsupp.add_apply, Finsupp.single_apply, if_pos rfl]
    by_cases hβ : β + Finsupp.single j 1 ∈ P.support
    · rw [if_pos hβ, happ]
      ring
    · rw [if_neg hβ, MvPolynomial.notMem_support_iff.mp hβ, map_zero, mul_zero]

/-! ## The elimination theorem -/

open MvPolynomial

/-- **No shift-stable annihilator space.**  A subset of the jet-polynomial algebra over
`ℂ(X)` closed under subtraction, `ℂ(X)`-scalar multiples, and the jet substitution, and
containing no nonzero constant, contains no nonzero element.  A double-minimal member
(minimal jet degree `D`, then minimal top-layer support) satisfies
`jetTranslateGen σ rj P = u·P`; the top layer is shift-periodic and hence has constant coefficient
ratios; the layer below then satisfies difference equations whose right sides lie in the
span of the pole parts, forcing the gradient of the top form to vanish — impossible in
characteristic zero once `D ≥ 1`. -/
theorem no_shift_stable_annihilatorGen [Algebra ℂ K] (σ : K →+* K) (rj : ℕ → K) {m : ℕ}
    (hσinj : Function.Injective σ)
    (hσconst : ∀ t : ℂ, σ (algebraMap ℂ K t) = algebraMap ℂ K t)
    (hσfix : ∀ {w : K}, σ w = w → ∃ t : ℂ, w = algebraMap ℂ K t)
    (I : Set (MvPolynomial (Fin m) (K)))
    (Hsub : ∀ G H, G ∈ I → H ∈ I → G - H ∈ I)
    (Hsmul : ∀ (k : K) (G), G ∈ I → C k * G ∈ I)
    (Hshift : ∀ G, G ∈ I → jetTranslateGen σ rj m G ∈ I)
    (Hconst : ∀ k : K, C k ∈ I → k = 0)
    (Hres : ∀ {w : K} {δ : Fin m → ℂ},
      σ w - w = ∑ j : Fin m, algebraMap ℂ (K) (δ j) * rj (j : ℕ) →
      ∀ j, δ j = 0)
    (Hne : ∃ G ∈ I, G ≠ 0) : False := by
  classical
  obtain ⟨G₀, hG₀I, hG₀0⟩ := Hne
  -- minimal jet degree
  have hex : ∃ N, ∃ G, G ∈ I ∧ G ≠ 0 ∧ G.totalDegree = N :=
    ⟨G₀.totalDegree, G₀, hG₀I, hG₀0, rfl⟩
  set D := Nat.find hex with hD_def
  have hDmin : ∀ G, G ∈ I → G ≠ 0 → D ≤ G.totalDegree := fun G hGI hG0 =>
    Nat.find_min' hex ⟨G, hGI, hG0, rfl⟩
  obtain ⟨P₁, hP₁I, hP₁0, hP₁D⟩ := Nat.find_spec hex
  -- minimal top-layer support among degree-`D` members
  set topCard : MvPolynomial (Fin m) (K) → ℕ :=
    fun G => (G.support.filter fun α => degSum α = D).card with htopCard_def
  have hex2 : ∃ c, ∃ G, G ∈ I ∧ G ≠ 0 ∧ G.totalDegree = D ∧ topCard G = c :=
    ⟨topCard P₁, P₁, hP₁I, hP₁0, hP₁D, rfl⟩
  have hcmin : ∀ G, G ∈ I → G ≠ 0 → G.totalDegree = D →
      Nat.find hex2 ≤ topCard G := fun G hGI hG0 hGD =>
    Nat.find_min' hex2 ⟨G, hGI, hG0, hGD, rfl⟩
  obtain ⟨P, hPI, hP0, hPD, hPc⟩ := Nat.find_spec hex2
  -- degree at least one
  have hD1 : 1 ≤ D := by
    by_contra h
    have hD0 : D = 0 := by omega
    have hPC : P = C (coeff 0 P) :=
      (MvPolynomial.totalDegree_eq_zero_iff_eq_C).mp (hPD.trans hD0)
    have := Hconst (coeff 0 P) (hPC ▸ hPI)
    exact hP0 (by rw [hPC, this, map_zero])
  -- top exponent
  have hsupp : P.support.Nonempty := MvPolynomial.support_nonempty.mpr hP0
  obtain ⟨αs, hαs_mem, hαs_sup⟩ := Finset.exists_mem_eq_sup P.support hsupp degSum
  have hαs : degSum αs = D := by
    rw [← hPD, totalDegree_eq_sup_degSumGen, hαs_sup]
  set a := coeff αs P with ha_def
  have ha : a ≠ 0 := MvPolynomial.mem_support_iff.mp hαs_mem
  have hσa : σ a ≠ 0 := fun h0 =>
    ha (hσinj (by rw [h0, map_zero]))
  -- the eliminant
  set Q := C (σ a) * P - C a * jetTranslateGen σ rj m P with hQ_def
  have hQI : Q ∈ I := Hsub _ _ (Hsmul _ _ hPI) (Hsmul _ _ (Hshift _ hPI))
  have hdegall : ∀ α ∈ P.support, degSum α ≤ D := fun α hα => by
    rw [← hPD]
    exact MvPolynomial.le_totalDegree hα
  have hQtop : ∀ β, degSum β = D →
      coeff β Q = σ a * coeff β P - a * σ (coeff β P) := by
    intro β hβ
    rw [hQ_def, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_jetTranslate_of_le_degSumGen σ rj (fun α hα => by rw [hβ]; exact hdegall α hα)]
  -- the eliminant vanishes
  have hQ0 : Q = 0 := by
    by_contra hQne
    have hQD : Q.totalDegree = D := by
      refine le_antisymm ?_ (hDmin Q hQI hQne)
      rw [hQ_def]
      refine le_trans (MvPolynomial.totalDegree_sub _ _) ?_
      refine max_le ?_ ?_
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, Nat.zero_add, hPD]
      · refine le_trans (MvPolynomial.totalDegree_mul _ _) ?_
        rw [MvPolynomial.totalDegree_C, Nat.zero_add]
        rw [← hPD]
        exact totalDegree_jetTranslate_leGen σ rj P
    have hss : (Q.support.filter fun α => degSum α = D)
        ⊂ (P.support.filter fun α => degSum α = D) := by
      rw [Finset.ssubset_iff_of_subset ?_]
      · refine ⟨αs, Finset.mem_filter.mpr ⟨hαs_mem, hαs⟩, ?_⟩
        intro hmem
        have hcoeffQ : coeff αs Q = 0 := by
          rw [hQtop αs hαs, ← ha_def]
          ring
        exact (MvPolynomial.mem_support_iff.mp (Finset.mem_filter.mp hmem).1) hcoeffQ
      · intro β hβ
        obtain ⟨hβQ, hβD⟩ := Finset.mem_filter.mp hβ
        refine Finset.mem_filter.mpr ⟨?_, hβD⟩
        rw [MvPolynomial.mem_support_iff]
        intro hPβ
        apply MvPolynomial.mem_support_iff.mp hβQ
        rw [hQtop β hβD, hPβ, map_zero, mul_zero, mul_zero, sub_zero]
    have hlt : topCard Q < topCard P := Finset.card_lt_card hss
    have hle := hcmin Q hQI hQne hQD
    omega
  -- top layer: constant coefficient ratios
  have htop : ∀ β, degSum β = D →
      ∃ t : ℂ, coeff β P = algebraMap ℂ (K) t * a := by
    intro β hβ
    have h0 : σ a * coeff β P - a * σ (coeff β P) = 0 := by
      rw [← hQtop β hβ, hQ0, coeff_zero]
    have hfix : σ (coeff β P / a) = coeff β P / a := by
      rw [map_div₀, div_eq_div_iff hσa ha]
      linear_combination -h0
    obtain ⟨t, ht⟩ := hσfix hfix
    refine ⟨t, ?_⟩
    rw [← ht]
    field_simp
  -- subtop layer: the gradient of the top form vanishes
  have hkill : ∀ β, degSum β + 1 = D → ∀ j : Fin m,
      coeff (β + Finsupp.single j 1) P = 0 := by
    intro β hβ j
    choose t ht using fun (k : Fin m) =>
      htop (β + Finsupp.single k 1) (by rw [degSum_add, degSum_single]; omega)
    have hcoeffQ : coeff β Q = 0 := by rw [hQ0, coeff_zero]
    rw [hQ_def, coeff_sub, coeff_C_mul, coeff_C_mul,
      coeff_jetTranslate_of_le_degSum_succGen σ rj
        (fun α hα => by
          have := hdegall α hα
          omega)] at hcoeffQ
    -- rewrite the shifted top coefficients through the constants
    have hsum : ∑ k : Fin m, ((β k + 1 : ℕ) : K) * rj (k : ℕ)
          * σ (coeff (β + Finsupp.single k 1) P)
        = σ a * ∑ k : Fin m, ((β k + 1 : ℕ) : K)
            * algebraMap ℂ (K) (t k) * rj (k : ℕ) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [ht k, map_mul, hσconst]
      ring
    rw [hsum] at hcoeffQ
    set S := ∑ k : Fin m, ((β k + 1 : ℕ) : K)
      * algebraMap ℂ (K) (t k) * rj (k : ℕ) with hS_def
    -- the difference equation for the coefficient ratio
    have hw : σ (coeff β P / a) - coeff β P / a
        = ∑ k : Fin m, algebraMap ℂ (K) (-(((β k : ℂ) + 1) * t k))
            * rj (k : ℕ) := by
      have hnum : σ (coeff β P) * a - σ a * coeff β P
          = (a * σ a) * (-S) := by
        linear_combination -hcoeffQ
      rw [map_div₀, div_sub_div _ _ hσa ha, hnum,
        show σ a * a = a * σ a by ring,
        mul_div_cancel_left₀ _ (mul_ne_zero ha hσa)]
      rw [hS_def, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [map_neg, map_mul]
      rw [show ((β k : ℂ) + 1) = (((β k + 1 : ℕ) : ℂ)) by push_cast; ring,
        map_natCast]
      ring
    have hδ := Hres hw j
    have ht0 : t j = 0 := by
      have hne : ((β j : ℂ) + 1) ≠ 0 := Nat.cast_add_one_ne_zero (β j)
      have := neg_eq_zero.mp hδ
      exact (mul_eq_zero.mp this).resolve_left hne
    rw [ht j, ht0, map_zero, zero_mul]
  -- contradiction at the top exponent
  obtain ⟨j, hj⟩ := exists_apply_ne_zero_of_degSum_pos (by omega : 0 < degSum αs)
  have hres : αs - Finsupp.single j 1 + Finsupp.single j 1 = αs :=
    sub_single_add_single hj
  have hβdeg : degSum (αs - Finsupp.single j 1) + 1 = D := by
    rw [← hαs]
    exact degSum_sub_single hj
  have := hkill (αs - Finsupp.single j 1) hβdeg j
  rw [hres] at this
  exact ha this

end GenericShiftHolder

end GenericShift

end GaloisForLFunctions
