import GaloisForLFunctions.HTGeometry.PermanentCoefficientIdentity

/-!
# Complex survival of the distinct-index permanent engine

The distinct-index permanent machinery (`PermanentCoefficientIdentity`, `PermanentDistinctSymbol`)
is stated with **integer** differential-polynomial coefficients, because the permanent symbol
`permSymbolPoly` lives over `ℤ`.  A differential-algebraic relation, however, is a polynomial over
`ℂ`.  This file lifts the survival conclusion to complex coefficients: a nonzero complex-coefficient
degree-`r`-homogeneous (or fixed-degree, mixed-order) differential polynomial does not annihilate a
tail-supported superlacunary gap series.

The lift rests on three facts:

* `exists_injective_eval_ne_zero_field` — a nonzero multivariate polynomial over any field is nonzero
  at an injective tuple valued in a prescribed infinite subset (the field version of the integer grid
  nonvanishing);
* `combination_permSymbolPolyC_ne_zero` — a nonzero complex combination of distinct permanent symbols
  is a nonzero complex polynomial (its representative coefficient reads off `c μ₀` times a positive
  stabiliser count, cast to `ℂ`);
* `eval_map_permSymbolPoly_complex` — evaluating the cast permanent symbol at integer scales produces
  the complex falling-factorial permanent, matching `coeff_distinct_index_eq_permanent`.

Assembling these gives `degHom_survives_complex` and `diffPoly_fixedDegree_survives_complex`, the
complex analogues of the integer survival theorems.
-/

open PowerSeries Finset MvPolynomial
open scoped Nat

namespace GaloisForLFunctions

/-- **Ring-hom naturality of evaluation.**  A ring hom `h` commutes with multivariate evaluation and
the coefficient map: `h (eval g p) = eval (h ∘ g) (map h p)`. -/
theorem eval_map_ringHom {R S σ : Type*} [CommRing R] [CommRing S] (h : R →+* S) (g : σ → R)
    (p : MvPolynomial σ R) :
    h (MvPolynomial.eval g p) = MvPolynomial.eval (fun i => h (g i)) (MvPolynomial.map h p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

section FieldEval

variable {𝕜 : Type*} [Field 𝕜]

/-- A nonzero univariate polynomial over a field has a non-root in any infinite set. -/
theorem exists_mem_eval_ne_zero_of_infinite_field (p : Polynomial 𝕜) (hp : p ≠ 0) {S : Set 𝕜}
    (hS : S.Infinite) : ∃ x ∈ S, p.eval x ≠ 0 := by
  classical
  have hfin : {x : 𝕜 | p.eval x = 0}.Finite := by
    apply Set.Finite.subset (p.roots.toFinset.finite_toSet)
    intro x hx
    rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots']
    exact ⟨hp, hx⟩
  obtain ⟨x, hxS, hx⟩ := (hS.diff hfin).nonempty
  exact ⟨x, hxS, hx⟩

/-- **Infinite-grid nonvanishing over a field.**  A nonzero `MvPolynomial (Fin r) 𝕜` is nonzero at
some injective tuple valued in any infinite subset of `𝕜`. -/
theorem exists_injective_eval_ne_zero_field :
    ∀ {r : ℕ} (P : MvPolynomial (Fin r) 𝕜), P ≠ 0 → ∀ {T : Set 𝕜}, T.Infinite →
      ∃ a : Fin r → 𝕜, Function.Injective a ∧ (∀ i, a i ∈ T) ∧ MvPolynomial.eval a P ≠ 0 := by
  intro r
  induction r with
  | zero =>
    intro P hP _ hT
    refine ⟨Fin.elim0, Function.injective_of_subsingleton _, fun i => i.elim0, ?_⟩
    intro hcontra
    apply hP
    obtain ⟨c, rfl⟩ := MvPolynomial.C_surjective (Fin 0) P
    rw [MvPolynomial.eval_C] at hcontra
    rw [hcontra, map_zero]
  | succ r IH =>
    intro P hP T hT
    set Q := (MvPolynomial.finSuccEquiv 𝕜 r) P with hQdef
    have hQ : Q ≠ 0 := (map_ne_zero_iff _ (MvPolynomial.finSuccEquiv 𝕜 r).injective).mpr hP
    obtain ⟨k, hk⟩ : ∃ n, Q.coeff n ≠ 0 := by
      by_contra h
      simp only [not_exists, not_not] at h
      exact hQ (Polynomial.ext (fun n => by rw [h n, Polynomial.coeff_zero]))
    obtain ⟨a', ha'inj, ha'T, ha'ne⟩ := IH (Q.coeff k) hk hT
    set Q' := Q.map (MvPolynomial.eval a') with hQ'def
    have hQ'k : Q'.coeff k ≠ 0 := by rw [hQ'def, Polynomial.coeff_map]; exact ha'ne
    have hQ' : Q' ≠ 0 := fun h => hQ'k (by rw [h]; simp)
    have hTinf : (T \ Set.range a').Infinite := hT.diff (Set.finite_range a')
    obtain ⟨y, hyT, hyne⟩ := exists_mem_eval_ne_zero_of_infinite_field Q' hQ' hTinf
    refine ⟨Fin.cons y a', ?_, ?_, ?_⟩
    · intro i j hij
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩ <;>
        rcases Fin.eq_zero_or_eq_succ j with rfl | ⟨j', rfl⟩
      · rfl
      · rw [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd ⟨j', hij.symm⟩ hyT.2
      · rw [Fin.cons_zero, Fin.cons_succ] at hij
        exact absurd ⟨i', hij⟩ hyT.2
      · rw [Fin.cons_succ, Fin.cons_succ] at hij
        rw [ha'inj hij]
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with rfl | ⟨i', rfl⟩
      · rw [Fin.cons_zero]; exact hyT.1
      · rw [Fin.cons_succ]; exact ha'T i'
    · rw [MvPolynomial.eval_eq_eval_mv_eval', ← hQdef, ← hQ'def]
      exact hyne

end FieldEval

variable {r : ℕ}

/-- **Complex evaluation of the cast permanent symbol.**  Evaluating the `ℤ→ℂ` cast of
`permSymbolPoly μ` at integer scales `s` produces the complex falling-factorial permanent. -/
theorem eval_map_permSymbolPoly_complex (μ s : Fin r → ℕ) :
    MvPolynomial.eval (fun i => (s i : ℂ)) ((permSymbolPoly μ).map (Int.castRingHom ℂ))
      = ∑ π : Equiv.Perm (Fin r), ∏ t, (Nat.descFactorial (s (π t)) (μ t) : ℂ) := by
  have h := eval_map_ringHom (Int.castRingHom ℂ) (fun i => (s i : ℤ)) (permSymbolPoly μ)
  simp only [Int.coe_castRingHom, Int.cast_natCast] at h
  rw [← h, eval_permSymbolPoly]
  push_cast
  rfl

/-- **Distinct-multiset permanent symbols are complex-independent.**  For a family `S` of order tuples
of common total order, pairwise distinct as multisets, any nonzero complex combination of the cast
permanent symbols is a nonzero polynomial. -/
theorem combination_permSymbolPolyC_ne_zero {S : Finset (Fin r → ℕ)} {O : ℕ}
    (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0) :
    (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 := by
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
        (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ))
      = ∑ ν ∈ S, c ν *
          (((∑ π : Equiv.Perm (Fin r),
            (if permMon ν π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) := by
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
        (if permMon μ₀ π = permMon μ₀ (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) ≠ 0 :=
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

/-- **Indexed complex permanent combination.**  A combination `∑_{i∈T} c i · permSymbolPolyℂ (ν i)`
indexed by a finset `T` through an injective, distinct-multiset assignment `ν` is a nonzero polynomial
whenever some `c i₀ ≠ 0`.  The representative coefficient at `X^{ν i₀}` reads off `c i₀` times the
positive stabiliser count. -/
theorem combination_permSymbolPolyC_indexed_ne_zero {ι : Type*} (T : Finset ι)
    (ν : ι → (Fin r → ℕ)) {O : ℕ} (hO : ∀ i ∈ T, ∑ t, ν i t = O)
    (hdist : ∀ i ∈ T, ∀ i' ∈ T,
      (∃ σ : Equiv.Perm (Fin r), ∀ j, ν i j = ν i' (σ j)) → ν i = ν i')
    (hinj : ∀ i ∈ T, ∀ i' ∈ T, ν i = ν i' → i = i')
    (c : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ T) (hc : c i₀ ≠ 0) :
    (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ)) ≠ 0 := by
  classical
  intro hzero
  apply hc
  have hsum1 : ∑ j, (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) j = ∑ t, ν i₀ t := by
    rw [← permMon_sum (ν i₀) 1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj
    exact hj
  have hcoeff : MvPolynomial.coeff (permMon (ν i₀) (1 : Equiv.Perm (Fin r)))
        (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ))
      = ∑ i ∈ T, c i *
          (((∑ π : Equiv.Perm (Fin r),
            (if permMon (ν i) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
      coeff_permSymbolPoly_eq_card (ν i) (permMon (ν i₀) 1) (by rw [hsum1, hO i₀ hi₀, hO i hi])]
    rfl
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i₀] at hcoeff
  · have hpos : (0 : ℤ) < ∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0) := by
      apply Finset.sum_pos'
      · intro π _; positivity
      · exact ⟨1, Finset.mem_univ 1, by rw [if_pos rfl]; norm_num⟩
    have hcast : (((∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt hpos)
    rcases mul_eq_zero.mp hcoeff.symm with h | h
    · exact h
    · exact absurd h hcast
  · intro i hi hine
    have hzero_count : (∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i) π = permMon (ν i₀) (1 : Equiv.Perm (Fin r)) then (1 : ℤ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro π _
      rw [if_neg]
      intro hpm
      apply hine
      apply hinj i hi i₀ hi₀
      apply hdist i hi i₀ hi₀
      refine ⟨π, fun j => ?_⟩
      have h1 := DFunLike.congr_fun hpm (π j)
      rw [permMon_apply, permMon_apply] at h1
      simpa using h1
    rw [hzero_count]
    simp
  · intro h
    exact absurd hi₀ h

/-- Total degree of `aeval (X j)` of a univariate polynomial is bounded by its degree. -/
theorem aeval_X_totalDegree_le {σ : Type*} (j : σ) (p : Polynomial ℤ) :
    (Polynomial.aeval (X j : MvPolynomial σ ℤ) p).totalDegree ≤ p.natDegree := by
  rw [Polynomial.aeval_def, Polynomial.eval₂_eq_sum, Polynomial.sum]
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun k hk => ?_)
  calc (MvPolynomial.C (p.coeff k) * (X j) ^ k).totalDegree
      ≤ (MvPolynomial.C (p.coeff k)).totalDegree + ((X j : MvPolynomial σ ℤ) ^ k).totalDegree :=
        totalDegree_mul _ _
    _ ≤ k := by rw [totalDegree_C, zero_add, totalDegree_X_pow]
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp k hk

/-- **Permanent-symbol total degree.**  `permSymbolPoly ν` has total degree at most `∑ ν` — each
falling-factorial factor contributes its order. -/
theorem permSymbolPoly_totalDegree_le (ν : Fin r → ℕ) :
    (permSymbolPoly ν).totalDegree ≤ ∑ t, ν t := by
  rw [permSymbolPoly]
  refine le_trans (totalDegree_finsetSum _ _) (Finset.sup_le fun π _ => ?_)
  refine le_trans (totalDegree_finsetProd _ _) (Finset.sum_le_sum fun t _ => ?_)
  calc (Polynomial.aeval (X (π t)) (descPochhammer ℤ (ν t))).totalDegree
      ≤ (descPochhammer ℤ (ν t)).natDegree := aeval_X_totalDegree_le _ _
    _ = ν t := by rw [descPochhammer_natDegree]

/-- **Maximal-order complex combination.**  If `i₀` attains the maximal total order in `T` and the
assignment `ν` separates `i₀` from every other index under permutation, the combination
`∑_{i∈T} c i · permSymbolPolyℂ (ν i)` is nonzero (representative coefficient at `X^{ν i₀}`: the strictly
lower-order terms vanish there by total degree, and same-order terms other than `i₀` vanish by
distinctness). -/
theorem combination_permSymbolPolyC_maxorder_ne_zero {ι : Type*} (T : Finset ι)
    (ν : ι → (Fin r → ℕ)) (c : ι → ℂ) {i₀ : ι} (hi₀ : i₀ ∈ T)
    (hOle : ∀ i ∈ T, ∑ t, ν i t ≤ ∑ t, ν i₀ t)
    (hdist : ∀ i ∈ T, (∃ σ : Equiv.Perm (Fin r), ∀ j, ν i j = ν i₀ (σ j)) → i = i₀)
    (hc : c i₀ ≠ 0) :
    (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ)) ≠ 0 := by
  classical
  intro hzero
  apply hc
  have hsum1 : ∑ j, (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) j = ∑ t, ν i₀ t := by
    rw [← permMon_sum (ν i₀) 1]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj; exact hj
  have hsupsum : ∑ k ∈ (permMon (ν i₀) (1 : Equiv.Perm (Fin r))).support,
      (permMon (ν i₀) (1 : Equiv.Perm (Fin r))) k = ∑ t, ν i₀ t := by
    rw [← hsum1]
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ hj
    rw [Finsupp.mem_support_iff, not_not] at hj; exact hj
  have hcoeff : MvPolynomial.coeff (permMon (ν i₀) 1)
        (∑ i ∈ T, MvPolynomial.C (c i) * (permSymbolPoly (ν i)).map (Int.castRingHom ℂ))
      = ∑ i ∈ T, c i * ((MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i)) : ℤ) : ℂ) := by
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map]; rfl
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  rw [Finset.sum_eq_single i₀] at hcoeff
  · have hcard : MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i₀))
        = ∑ π : Equiv.Perm (Fin r),
            (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0) :=
      coeff_permSymbolPoly_eq_card (ν i₀) (permMon (ν i₀) 1) hsum1
    have hpos : (0 : ℤ) < ∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0) := by
      apply Finset.sum_pos'
      · intro π _; positivity
      · exact ⟨1, Finset.mem_univ 1, by rw [if_pos rfl]; norm_num⟩
    rw [hcard] at hcoeff
    have hcast : (((∑ π : Equiv.Perm (Fin r),
        (if permMon (ν i₀) π = permMon (ν i₀) 1 then (1 : ℤ) else 0)) : ℤ) : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (ne_of_gt hpos)
    rcases mul_eq_zero.mp hcoeff.symm with h | h
    · exact h
    · exact absurd h hcast
  · intro i hi hine
    have hczero : MvPolynomial.coeff (permMon (ν i₀) 1) (permSymbolPoly (ν i)) = 0 := by
      by_cases heq : ∑ t, ν i t = ∑ t, ν i₀ t
      · rw [coeff_permSymbolPoly_eq_card (ν i) (permMon (ν i₀) 1) (by rw [hsum1, heq])]
        apply Finset.sum_eq_zero
        intro π _
        rw [if_neg]
        intro hpm
        apply hine
        apply hdist i hi
        refine ⟨π, fun j => ?_⟩
        have h1 := DFunLike.congr_fun hpm (π j)
        rw [permMon_apply, permMon_apply] at h1
        simpa using h1
      · apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
        rw [hsupsum]
        exact lt_of_le_of_lt (permSymbolPoly_totalDegree_le (ν i))
          (lt_of_le_of_ne (hOle i hi) heq)
    rw [hczero]; simp
  · intro h; exact absurd hi₀ h

/-- **Complex coefficient identity.**  At the order-`O` distinct-scale index, the coefficient of a
complex-coefficient order-`O` degree-`r`-homogeneous differential polynomial factors as the product
of the source coefficients times the complex evaluation of the combined cast permanent symbol. -/
theorem coeff_combination_complex_eq {bnat : ℕ → ℕ} (hmono : Monotone bnat)
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (c : (Fin r → ℕ) → ℂ) {f : ℂ⟦X⟧}
    (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    (hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i)) :
    coeff (∑ t, bnat (M t) - O) (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f)
      = (∏ i, coeff (bnat (M i)) f)
        * MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
            (∑ μ ∈ S, MvPolynomial.C (c μ) * (permSymbolPoly μ).map (Int.castRingHom ℂ)) := by
  classical
  rw [map_sum, map_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro μ hμ
  rw [map_smul, smul_eq_mul]
  have hidx : (∑ t, bnat (M t) - O) = ∑ t, (bnat (M t) - μ t) := by
    rw [Finset.sum_tsub_distrib Finset.univ (fun t _ => hbig μ hμ t t), hO μ hμ]
  rw [hidx, coeff_distinct_index_eq_permanent hmono hb0 hstair hbnatinj μ hsupp M hMinj
    (fun i t => hbig μ hμ i t), MvPolynomial.eval_mul, MvPolynomial.eval_C,
    eval_map_permSymbolPoly_complex]
  ring

/-- **Complex degree-homogeneous survival.**  A nonzero complex-coefficient order-`O`
degree-`r`-homogeneous differential polynomial over a distinct-multiset family does not annihilate a
tail-supported superlacunary gap series. -/
theorem degHom_survives_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat)
    (hb0 : 0 < bnat 0) (hstair : ∀ n, r * bnat n < bnat (n + 1)) (hbnatinj : Function.Injective bnat)
    (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} {O : ℕ} (hO : ∀ μ ∈ S, ∑ t, μ t = O)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ μ ∈ S, c μ • ∏ t, (⇑(d⁄dX ℂ))^[μ t] f) ≠ 0 := by
  classical
  intro hPzero
  have hΦne : (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 :=
    combination_permSymbolPolyC_ne_zero hO hdistinct c hμ₀ hc
  set B := S.sup (fun μ => Finset.univ.sup μ) with hBdef
  have hB : ∀ μ ∈ S, ∀ t, μ t ≤ B :=
    fun μ hμ t => le_trans (Finset.le_sup (Finset.mem_univ t)) (Finset.le_sup hμ)
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop B)
  set G := {n : ℕ | coeff (bnat n) f ≠ 0 ∧ NB ≤ n} with hGdef
  have hGinf : G.Infinite := by
    apply (hinf.diff (Set.finite_Iio NB)).mono
    intro n hn
    exact ⟨hn.1, not_lt.mp hn.2⟩
  have hTinf : ((fun n => (bnat n : ℂ)) '' G).Infinite :=
    hGinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ :=
    exists_injective_eval_ne_zero_field
      (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) hΦne hTinf
  choose M hMG hMeq using fun i => haT i
  have haM : a = fun i => ((bnat (M i) : ℂ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := by
    intro i j h
    apply hainj
    rw [← hMeq i, ← hMeq j, h]
  have hbig : ∀ μ ∈ S, ∀ i t, μ t ≤ bnat (M i) :=
    fun μ hμ i t => le_trans (hB μ hμ t) (hNB (M i) (hMG i).2)
  have hprodne : (∏ i, coeff (bnat (M i)) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hMG i).1
  have hkey := coeff_combination_complex_eq hmono hb0 hstair hbnatinj hO c hsupp M hMinj hbig
  rw [hPzero, map_zero] at hkey
  have hevalne : MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
      (∑ ν ∈ S, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 := by
    rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne hevalne) hkey.symm

/-- **Complex order-`O` reduction.**  At the order-`O` distinct index, the coefficient of a
complex-coefficient mixed-order differential polynomial equals that of its order-`O` subfamily. -/
theorem coeff_mixed_eq_orderO_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat) {W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (c : (Fin r → ℕ) → ℂ) {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (M : Fin r → ℕ) (hMinj : Function.Injective M)
    {O : ℕ} (hOle : O ≤ ∑ t, bnat (M t)) (hOW : O ≤ W) :
    coeff (∑ t, bnat (M t) - O) (∑ ν ∈ S, c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f)
      = coeff (∑ t, bnat (M t) - O)
          (∑ ν ∈ S.filter (fun ν => ∑ t, ν t = O), c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) := by
  classical
  rw [map_sum, map_sum, ← Finset.sum_filter_add_sum_filter_not S (fun ν => ∑ t, ν t = O)]
  have hrest : ∑ ν ∈ S.filter (fun ν => ¬ ∑ t, ν t = O),
      coeff (∑ t, bnat (M t) - O) (c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) = 0 := by
    apply Finset.sum_eq_zero
    intro ν hν
    rw [Finset.mem_filter] at hν
    rw [map_smul,
      coeff_distinct_wrong_order_vanish hmono hb0 hWb hW rfl hsupp M hMinj hOle hOW
        (hbound ν hν.1) (fun h => hν.2 h.symm), smul_zero]
  rw [hrest, add_zero]

/-- **Complex fixed-degree survival.**  A nonzero complex-coefficient degree-`r`-homogeneous
differential polynomial with arbitrary bounded orders over a distinct-multiset family does not
annihilate a tail-supported superlacunary gap series. -/
theorem diffPoly_fixedDegree_survives_complex {bnat : ℕ → ℕ} (hmono : Monotone bnat) {W : ℕ}
    (hb0 : 0 < bnat 0) (hWb : W < bnat 0) (hW : ∀ n, r * bnat n + W < bnat (n + 1))
    (hbnatinj : Function.Injective bnat) (hbtop : Filter.Tendsto bnat Filter.atTop Filter.atTop)
    {S : Finset (Fin r → ℕ)} (hbound : ∀ ν ∈ S, ∑ t, ν t ≤ W)
    (hdistinct : ∀ μ ∈ S, ∀ ν ∈ S, (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν)
    (c : (Fin r → ℕ) → ℂ) {μ₀ : Fin r → ℕ} (hμ₀ : μ₀ ∈ S) (hc : c μ₀ ≠ 0)
    {f : ℂ⟦X⟧} (hsupp : ∀ k, coeff k f ≠ 0 → ∃ n, k = bnat n)
    (hinf : {M : ℕ | coeff (bnat M) f ≠ 0}.Infinite) :
    (∑ ν ∈ S, c ν • ∏ t, (⇑(d⁄dX ℂ))^[ν t] f) ≠ 0 := by
  classical
  intro hPzero
  set O := ∑ t, μ₀ t with hOdef
  set SO := S.filter (fun ν => ∑ t, ν t = O) with hSOdef
  have hμ₀O : μ₀ ∈ SO := Finset.mem_filter.mpr ⟨hμ₀, rfl⟩
  have hOall : ∀ ν ∈ SO, ∑ t, ν t = O := fun ν hν => (Finset.mem_filter.mp hν).2
  have hdistinctSO : ∀ μ ∈ SO, ∀ ν ∈ SO,
      (∃ σ : Equiv.Perm (Fin r), ∀ j, μ j = ν (σ j)) → μ = ν :=
    fun μ hμ ν hν => hdistinct μ (Finset.mem_filter.mp hμ).1 ν (Finset.mem_filter.mp hν).1
  have hstair : ∀ n, r * bnat n < bnat (n + 1) := fun n => lt_of_le_of_lt (Nat.le_add_right _ _) (hW n)
  obtain ⟨NB, hNB⟩ := Filter.eventually_atTop.mp (hbtop.eventually_ge_atTop W)
  set G := {n : ℕ | coeff (bnat n) f ≠ 0 ∧ NB ≤ n} with hGdef
  have hGinf : G.Infinite := by
    apply (hinf.diff (Set.finite_Iio NB)).mono
    intro n hn; exact ⟨hn.1, not_lt.mp hn.2⟩
  have hTinf : ((fun n => (bnat n : ℂ)) '' G).Infinite :=
    hGinf.image (fun a _ b _ h => hbnatinj (by exact_mod_cast h))
  obtain ⟨a, hainj, haT, haΦ⟩ :=
    exists_injective_eval_ne_zero_field
      (∑ ν ∈ SO, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ))
      (combination_permSymbolPolyC_ne_zero hOall hdistinctSO c hμ₀O hc) hTinf
  choose M hMG hMeq using fun i => haT i
  have haM : a = fun i => ((bnat (M i) : ℂ)) := funext fun i => (hMeq i).symm
  have hMinj : Function.Injective M := fun i j h => hainj (by rw [← hMeq i, ← hMeq j, h])
  have hbig : ∀ ν ∈ SO, ∀ i t, ν t ≤ bnat (M i) := by
    intro ν hν i t
    calc ν t ≤ ∑ t, ν t := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
      _ = O := hOall ν hν
      _ ≤ W := hOdef.symm ▸ hbound μ₀ hμ₀
      _ ≤ bnat (M i) := hNB (M i) (hMG i).2
  have hprodne : (∏ i, coeff (bnat (M i)) f) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun i _ => (hMG i).1
  have hOW : O ≤ W := hOdef.symm ▸ hbound μ₀ hμ₀
  have hOle : O ≤ ∑ t, bnat (M t) := by
    rcases Nat.eq_zero_or_pos r with hr0 | hr1
    · subst hr0; simp [hOdef]
    · obtain ⟨t0⟩ : Nonempty (Fin r) := Fin.pos_iff_nonempty.mp hr1
      calc O ≤ bnat (M t0) := le_trans hOW (hNB (M t0) (hMG t0).2)
        _ ≤ ∑ t, bnat (M t) :=
            Finset.single_le_sum (f := fun t => bnat (M t)) (fun _ _ => Nat.zero_le _)
              (Finset.mem_univ t0)
  have hkey1 := coeff_mixed_eq_orderO_complex hmono hb0 hWb hW hbound c hsupp M hMinj hOle hOW
  have hkey2 := coeff_combination_complex_eq hmono hb0 hstair hbnatinj hOall c hsupp M hMinj hbig
  rw [hPzero, map_zero, hkey2] at hkey1
  have hevalne : MvPolynomial.eval (fun i => (bnat (M i) : ℂ))
      (∑ ν ∈ SO, MvPolynomial.C (c ν) * (permSymbolPoly ν).map (Int.castRingHom ℂ)) ≠ 0 := by
    rw [← haM]; exact haΦ
  exact (mul_ne_zero hprodne hevalne) hkey1.symm

end GaloisForLFunctions
