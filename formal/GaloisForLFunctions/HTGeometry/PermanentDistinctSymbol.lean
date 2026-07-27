import GaloisForLFunctions.HTGeometry.WeightPolynomial

/-!
# The distinct-index permanent symbol and its non-degeneracy

At `r` distinct source scales the coefficient of a differential monomial `∏ₜ f^{(μₜ)}` is a
**permanent** of falling factorials, whose polynomial shape is

`permSymbolPoly μ = ∑_{π : Perm (Fin r)} ∏ₜ (descPochhammer ℤ (μₜ)) ∘ X_{π t}`.

Unlike the balanced (single-source) weight polynomial — which can vanish on a nonzero differential
polynomial (`weightPolynomial_class44_dependence`) — the permanent symbols over **distinct order
multisets** are linearly independent: the coefficient of the representative monomial `X^μ` in
`permSymbolPoly ν` is the number of permutations carrying `ν` to `μ`, nonzero only when `ν` and `μ`
are rearrangements.  Hence a nonzero combination of distinct-multiset symbols is a nonzero
polynomial, which — evaluated at distinct integer scales via `exists_injective_eval_ne_zero` — never
degenerates.  This is the leading symbol that survives the distinct-index probe.
-/

open MvPolynomial Finset Polynomial Equiv

namespace GaloisForLFunctions

variable {r : ℕ}

/-- The exponent monomial of the assignment `π`: variable `π t` receives order `μ t`. -/
noncomputable def permMon (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) : Fin r →₀ ℕ :=
  ∑ t, Finsupp.single (π t) (μ t)

/-- The distinct-index permanent symbol as a multivariate polynomial. -/
noncomputable def permSymbolPoly (μ : Fin r → ℕ) : MvPolynomial (Fin r) ℤ :=
  ∑ π : Equiv.Perm (Fin r), ∏ t, (Polynomial.aeval (MvPolynomial.X (π t)) (descPochhammer ℤ (μ t)))

/-- Evaluating the assignment exponent at a variable reads the order on that variable's preimage. -/
theorem permMon_apply (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) (j : Fin r) :
    permMon μ π j = μ (π.symm j) := by
  classical
  rw [permMon, Finsupp.finsetSum_apply, Finset.sum_eq_single (π.symm j)]
  · rw [Finsupp.single_apply, if_pos (by simp)]
  · intro t _ ht
    rw [Finsupp.single_apply, if_neg]
    intro h; exact ht (by rw [← h]; simp)
  · intro h; exact absurd (Finset.mem_univ _) h

/-- The assignment exponent has total mass equal to the total order. -/
theorem permMon_sum (μ : Fin r → ℕ) (π : Equiv.Perm (Fin r)) :
    ∑ j ∈ (permMon μ π).support, (permMon μ π) j = ∑ t, μ t := by
  classical
  have h1 : ∑ j ∈ (permMon μ π).support, (permMon μ π) j = ∑ j : Fin r, (permMon μ π) j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj
  rw [h1]
  simp_rw [permMon_apply]
  exact Equiv.sum_comp π.symm μ

/-- The assignment exponents are injective in the assignment: `permMon μ π` determines `π` when
read against `μ`, and equal `permMon`s over the same `μ` force equal permutations only up to the
`μ`-stabiliser.  What we need downstream is the coarser fact that `permMon μ π = permMon ν σ`
forces `μ ∘ π⁻¹ = ν ∘ σ⁻¹` pointwise. -/
theorem permMon_eq_iff (μ ν : Fin r → ℕ) (π σ : Equiv.Perm (Fin r)) :
    permMon μ π = permMon ν σ ↔ ∀ j, μ (π.symm j) = ν (σ.symm j) := by
  constructor
  · intro h j
    have := congrArg (fun (f : Fin r →₀ ℕ) => f j) h
    simpa [permMon_apply] using this
  · intro h
    ext j
    rw [permMon_apply, permMon_apply, h]

/-- A single-variable factor reads one univariate coefficient: the `m`-coefficient of
`(descPochhammer ℤ k) ∘ X_j` is the univariate coefficient `(descPochhammer ℤ k).coeff (m j)` when
`m` is supported on `j`, and `0` otherwise. -/
theorem coeff_aeval_X (j : Fin r) (q : Polynomial ℤ) (m : Fin r →₀ ℕ) :
    MvPolynomial.coeff m (Polynomial.aeval (MvPolynomial.X j) q)
      = if m = Finsupp.single j (m j) then q.coeff (m j) else 0 := by
  classical
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum_def, MvPolynomial.coeff_sum]
  have hstep : ∀ e ∈ q.support,
      MvPolynomial.coeff m ((algebraMap ℤ (MvPolynomial (Fin r) ℤ)) (q.coeff e) * MvPolynomial.X j ^ e)
        = if Finsupp.single j e = m then q.coeff e else 0 := by
    intro e _
    rw [MvPolynomial.algebraMap_eq, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_X_pow,
      mul_ite, mul_one, mul_zero]
  rw [Finset.sum_congr rfl hstep]
  by_cases hm : m = Finsupp.single j (m j)
  · rw [if_pos hm]
    have hcond : ∀ e : ℕ, (Finsupp.single j e = m) ↔ (e = m j) := by
      intro e
      constructor
      · intro h; have := congrArg (fun f : Fin r →₀ ℕ => f j) h; simpa using this
      · intro h; subst h; exact hm.symm
    simp only [hcond]
    rw [Finset.sum_ite_eq' q.support (m j) q.coeff]
    by_cases hmem : m j ∈ q.support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      rw [Polynomial.mem_support_iff, not_not] at hmem
      exact hmem.symm
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro e _
    rw [if_neg]
    intro h
    exact hm (by rw [← h]; simp)

/-- A single-variable factor as an explicit sum of monomials. -/
theorem aeval_X_eq_sum (j : Fin r) (q : Polynomial ℤ) :
    Polynomial.aeval (MvPolynomial.X j) q
      = ∑ c ∈ q.support, MvPolynomial.monomial (Finsupp.single j c) (q.coeff c) := by
  classical
  ext m
  rw [coeff_aeval_X, MvPolynomial.coeff_sum]
  symm
  simp_rw [MvPolynomial.coeff_monomial]
  by_cases hm : m = Finsupp.single j (m j)
  · rw [if_pos hm]
    have hcond : ∀ c : ℕ, (Finsupp.single j c = m) ↔ (c = m j) := by
      intro c; constructor
      · intro h; have := congrArg (fun f : Fin r →₀ ℕ => f j) h; simpa using this
      · intro h; subst h; exact hm.symm
    simp only [hcond]
    rw [Finset.sum_ite_eq' q.support (m j) q.coeff]
    by_cases hmem : m j ∈ q.support
    · rw [if_pos hmem]
    · rw [if_neg hmem]
      rw [Polynomial.mem_support_iff, not_not] at hmem
      exact hmem.symm
  · rw [if_neg hm]
    apply Finset.sum_eq_zero
    intro c _; rw [if_neg]; intro h; exact hm (by rw [← h]; simp)

/-- **Disjoint-variable coefficient factorisation.**  In a product of single-variable factors
`(q j) ∘ X_j`, one per variable in `s`, the coefficient of a monomial `d` supported on `s`
factorises into the univariate coefficients `∏_{j ∈ s} (q j).coeff (d j)`; if `d` charges a
variable outside `s` the coefficient vanishes. -/
theorem coeff_prod_aeval_X (q : Fin r → Polynomial ℤ) :
    ∀ (s : Finset (Fin r)) (d : Fin r →₀ ℕ),
      MvPolynomial.coeff d (∏ j ∈ s, Polynomial.aeval (MvPolynomial.X j) (q j))
        = if (∀ j, j ∉ s → d j = 0) then ∏ j ∈ s, (q j).coeff (d j) else 0 := by
  classical
  intro s
  induction s using Finset.induction with
  | empty =>
    intro d
    rw [Finset.prod_empty, MvPolynomial.coeff_one, Finset.prod_empty]
    by_cases h0 : d = 0
    · rw [if_pos h0.symm, if_pos (fun j _ => by rw [h0]; rfl)]
    · rw [if_neg (fun h => h0 h.symm), if_neg]
      intro hc; exact h0 (Finsupp.ext fun j => hc j (by simp))
  | insert a s' ha IH =>
    intro d
    rw [Finset.prod_insert ha, aeval_X_eq_sum, Finset.sum_mul, MvPolynomial.coeff_sum]
    simp_rw [MvPolynomial.coeff_monomial_mul', IH]
    by_cases hcond : ∀ j, j ∉ insert a s' → d j = 0
    · rw [if_pos hcond, Finset.prod_insert ha]
      rw [Finset.sum_eq_single (d a)]
      · -- the surviving term at c = d a
        have hle : Finsupp.single a (d a) ≤ d := by
          intro j; by_cases hj : j = a
          · subst hj; simp
          · simp [hj]
        rw [if_pos hle]
        have hinner : ∀ j, j ∉ s' → (d - Finsupp.single a (d a)) j = 0 := by
          intro j hj
          by_cases hja : j = a
          · subst hja; simp
          · have : j ∉ insert a s' := by simp [hja, hj]
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hja h.symm),
              Nat.sub_zero]
            exact hcond j this
        rw [if_pos hinner]
        congr 1
        apply Finset.prod_congr rfl
        intro j hj
        have hja : j ≠ a := fun h => ha (h ▸ hj)
        rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hja h.symm), Nat.sub_zero]
      · -- other c contribute 0
        intro c _ hcne
        by_cases hcle : Finsupp.single a c ≤ d
        · rw [if_pos hcle]
          have hbad : ¬ (∀ j, j ∉ s' → (d - Finsupp.single a c) j = 0) := by
            intro hall
            apply hcne
            have := hall a ha
            rw [Finsupp.tsub_apply, Finsupp.single_apply, if_pos rfl] at this
            have hca : c ≤ d a := by have := hcle a; simpa using this
            omega
          rw [if_neg hbad, mul_zero]
        · rw [if_neg hcle]
      · intro hnotmem
        rw [Polynomial.mem_support_iff, not_not] at hnotmem
        by_cases hle : Finsupp.single a (d a) ≤ d
        · rw [if_pos hle, hnotmem, zero_mul]
        · rw [if_neg hle]
    · rw [if_neg hcond]
      apply Finset.sum_eq_zero
      intro c _
      by_cases hcle : Finsupp.single a c ≤ d
      · rw [if_pos hcle]
        have hbad : ¬ (∀ j, j ∉ s' → (d - Finsupp.single a c) j = 0) := by
          intro hall
          apply hcond
          intro j hj
          rw [Finset.mem_insert, not_or] at hj
          have := hall j hj.2
          rw [Finsupp.tsub_apply, Finsupp.single_apply, if_neg (fun h => hj.1 h.symm),
            Nat.sub_zero] at this
          exact this
        rw [if_neg hbad, mul_zero]
      · rw [if_neg hcle]

/-- At a monomial of the correct total order, a product of falling-factorial coefficients is the
indicator of the exact order match: each `descPochhammer` is monic of its order, so a nonzero
product forces every exponent to hit its factor's degree, and the total-order constraint makes that
the only option. -/
theorem prod_descPochhammer_coeff (ν' : Fin r → ℕ) (d : Fin r →₀ ℕ)
    (hd : ∑ j, d j = ∑ j, ν' j) :
    ∏ j, (descPochhammer ℤ (ν' j)).coeff (d j) = if (∀ j, d j = ν' j) then 1 else 0 := by
  classical
  by_cases hall : ∀ j, d j = ν' j
  · rw [if_pos hall]
    rw [Finset.prod_eq_one]
    intro j _
    rw [hall j]
    calc (descPochhammer ℤ (ν' j)).coeff (ν' j)
        = (descPochhammer ℤ (ν' j)).coeff (descPochhammer ℤ (ν' j)).natDegree := by
          rw [descPochhammer_natDegree]
      _ = 1 := (monic_descPochhammer ℤ (ν' j)).coeff_natDegree
  · rw [if_neg hall]
    -- some coordinate overshoots its factor's degree, killing the product
    have hover : ∃ k, ν' k < d k := by
      by_contra hcon
      have hcon' : ∀ k, d k ≤ ν' k := fun k => not_lt.mp (not_exists.mp hcon k)
      have hne : ∃ j, d j ≠ ν' j := by
        by_contra h2
        exact hall (fun j => not_not.mp (not_exists.mp h2 j))
      obtain ⟨k, hk⟩ := hne
      have hlt : ∑ j, d j < ∑ j, ν' j :=
        Finset.sum_lt_sum (fun j _ => hcon' j)
          ⟨k, Finset.mem_univ k, lt_of_le_of_ne (hcon' k) hk⟩
      omega
    obtain ⟨k, hk⟩ := hover
    apply Finset.prod_eq_zero (Finset.mem_univ k)
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    rw [descPochhammer_natDegree]
    exact hk

/-- **Permanent coefficient = permutation count.**  At a monomial `d` of total order equal to `∑ ν`,
the `d`-coefficient of `permSymbolPoly ν` counts the assignments carrying `ν` onto `d`. -/
theorem coeff_permSymbolPoly_eq_card (ν : Fin r → ℕ) (d : Fin r →₀ ℕ)
    (hd : ∑ j, d j = ∑ t, ν t) :
    MvPolynomial.coeff d (permSymbolPoly ν)
      = ∑ π : Equiv.Perm (Fin r), (if permMon ν π = d then (1 : ℤ) else 0) := by
  classical
  rw [permSymbolPoly, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro π _
  -- reindex the product by `j = π t`
  have hreindex : (∏ t, Polynomial.aeval (MvPolynomial.X (π t)) (descPochhammer ℤ (ν t)))
      = ∏ j : Fin r, Polynomial.aeval (MvPolynomial.X j : MvPolynomial (Fin r) ℤ)
          (descPochhammer ℤ (ν (π.symm j))) := by
    apply Fintype.prod_bijective π π.bijective
    intro t; dsimp only; rw [Equiv.symm_apply_apply]
  rw [hreindex]
  have hH := coeff_prod_aeval_X (fun j => descPochhammer ℤ (ν (π.symm j))) Finset.univ d
  rw [if_pos (fun j hj => absurd (Finset.mem_univ j) hj)] at hH
  rw [hH]
  have hsum' : ∑ j, d j = ∑ j, ν (π.symm j) := by rw [hd]; exact (Equiv.sum_comp π.symm ν).symm
  rw [prod_descPochhammer_coeff (fun j => ν (π.symm j)) d hsum']
  have hiff : (∀ j, d j = ν (π.symm j)) ↔ permMon ν π = d := by
    rw [Finsupp.ext_iff]
    constructor
    · intro h j; rw [permMon_apply]; exact (h j).symm
    · intro h j; rw [← permMon_apply ν π j]; exact (h j).symm
  simp only [hiff]

/-- **Permanent symbol combinations survive in any characteristic-zero ring.**  For coefficients in
a commutative ring of characteristic zero, a combination `∑_{ν∈S} c ν · permSymbolPoly ν`, pushed
forward along `ℤ → R` and indexed by tuples of one fixed total order that are pairwise
non-permutations, is nonzero as soon as one coefficient is.  Reading the coefficient at
`permMon μ₀ 1` isolates `c μ₀` times the positive stabiliser count, which stays nonzero in `R`
because the characteristic is zero. -/
theorem combination_permSymbolPolyMap_ne_zero {R : Type*} [CommRing R] [CharZero R]
    [NoZeroDivisors R]
    {S : Finset (Fin r → ℕ)} {O : ℕ}
    (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → R) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0) :
    (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom R)) ≠ 0 := by
  classical
  intro hzero
  apply hc
  have hsum1 : ∑ j, (permMon μ₀ (1 : Equiv.Perm (Fin r))) j = ∑ t, μ₀ t := by
    rw [← permMon_sum μ₀ 1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj
  have hcoeff : MvPolynomial.coeff (permMon μ₀ (1 : Equiv.Perm (Fin r)))
        (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom R))
      = ∑ ν ∈ S, c ν *
          (((∑ π : Equiv.Perm (Fin r),
            (if permMon ν π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : R) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro ν hν
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      coeff_permSymbolPoly_eq_card ν (permMon μ₀ 1) (by rw [hsum1, hO μ₀ hμ₀, hO ν hν])]
    rfl
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single μ₀] at hcoeff
  · have hpos : (0 : ℤ) < ∑ π : Equiv.Perm (Fin r),
        (if permMon μ₀ π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0) := by
      apply Finset.sum_pos'
      · intro π _; positivity
      · exact ⟨1, Finset.mem_univ 1, by rw [if_pos rfl]; norm_num⟩
    have hcast : (((∑ π : Equiv.Perm (Fin r),
        (if permMon μ₀ π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : R) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt hpos)
    rcases mul_eq_zero.mp hcoeff.symm with h | h
    · exact h
    · exact absurd h hcast
  · intro ν hν hνne
    have hzero_count : (∑ π : Equiv.Perm (Fin r),
        (if permMon ν π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro π _
      rw [if_neg]
      intro hpm
      apply hνne
      symm
      apply hdistinct μ₀ hμ₀ ν hν
      refine ⟨π.symm, fun j => ?_⟩
      have h1 := DFunLike.congr_fun hpm j
      rw [permMon_apply, permMon_apply] at h1
      simpa using h1.symm
    rw [hzero_count]
    simp
  · intro h
    exact absurd hμ₀ h

/-- **Distinct-multiset permanent symbols are independent.**  For a family `S` of order tuples of a
common total order, pairwise distinct as multisets, any nonzero integer combination of the permanent
symbols is a nonzero polynomial: the coefficient of the representative monomial `X^{μ₀}` reads off
`c μ₀` times the (positive) stabiliser count, since no other tuple in `S` rearranges to `μ₀`. -/
theorem combination_permSymbolPoly_ne_zero {S : Finset (Fin r → ℕ)} {O : ℕ}
    (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℤ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0) :
    (∑ ν ∈ S, MvPolynomial.C (c ν) * permSymbolPoly ν) ≠ 0 := by
  have h := combination_permSymbolPolyMap_ne_zero (R := ℤ) hO hdistinct c hμ₀ hc
  simpa [MvPolynomial.map_id] using h

end GaloisForLFunctions
