import Mathlib
import GaloisForLFunctions.HTGeometry.SymmetricBlockAlgebraicIndependence
import GaloisForLFunctions.HTGeometry.PrimeRadialRelativeJetRank
import GaloisForLFunctions.HTGeometry.StateFieldTrdeg

/-!
# The corank / transcendence-degree realization locus

For a finite family `L` of real numbers write `corank L` for the dimension of its `ℚ`-linear span
and `trdeg L` for the transcendence degree over `ℚ` of the field it generates.  Choosing a
`ℚ`-basis inside `L` shows `trdeg L ≤ corank L`, and that is the only relation: for every pair
`1 ≤ t ≤ c` the family

`θ₁, …, θ_t, θ₁², θ₁³, …, θ₁^(c-t+1)`

built from `t` algebraically independent reals realizes corank `c` and transcendence degree `t`.
Linear independence holds because the members are distinct monomials in an algebraically
independent family, and the transcendence degree is `t` because the field they generate is
`ℚ(θ₁,…,θ_t)`.  A rational translation of the free family, which preserves algebraic independence,
puts every member above `1`, so the family is the multiplier-log set of a finite Beurling system.
-/

namespace GaloisForLFunctions.CorankTrdeg

open scoped Cardinal

/-- Translation by a constant of the base field is an automorphism of the polynomial algebra. -/
noncomputable def shiftAlgEquiv (ι : Type*) (c : ℚ) :
    MvPolynomial ι ℚ ≃ₐ[ℚ] MvPolynomial ι ℚ :=
  AlgEquiv.ofAlgHom
    (MvPolynomial.aeval fun i => MvPolynomial.X i + MvPolynomial.C c)
    (MvPolynomial.aeval fun i => MvPolynomial.X i - MvPolynomial.C c)
    (by refine MvPolynomial.algHom_ext (fun i => ?_); simp)
    (by refine MvPolynomial.algHom_ext (fun i => ?_); simp)

/-- Algebraic independence is preserved by a rational translation. -/
theorem AlgebraicIndependent.add_const {ι : Type*} {x : ι → ℝ}
    (hx : AlgebraicIndependent ℚ x) (c : ℚ) :
    AlgebraicIndependent ℚ (fun i => x i + (c : ℝ)) := by
  rw [algebraicIndependent_iff_injective_aeval] at hx ⊢
  have hcomp : (MvPolynomial.aeval fun i => x i + (c : ℝ) : MvPolynomial ι ℚ →ₐ[ℚ] ℝ)
      = (MvPolynomial.aeval x).comp (shiftAlgEquiv ι c).toAlgHom := by
    refine MvPolynomial.algHom_ext (fun i => ?_)
    simp [shiftAlgEquiv]
  rw [hcomp]
  exact hx.comp (shiftAlgEquiv ι c).bijective.injective


/-- The exponent vector of the `i`-th multiplier log of the realization family: the first `t`
members are the free transcendentals themselves, the remaining `c - t` are powers of the first one. -/
noncomputable def locusExp {t c : ℕ} (ht : 0 < t) (i : Fin c) : Fin t →₀ ℕ :=
  if h : (i : ℕ) < t then Finsupp.single ⟨i, h⟩ 1 else Finsupp.single ⟨0, ht⟩ ((i : ℕ) - t + 2)

theorem locusExp_degree {t c : ℕ} (ht : 0 < t) (i : Fin c) :
    (locusExp (c := c) ht i).sum (fun _ n => n)
      = if (i : ℕ) < t then 1 else (i : ℕ) - t + 2 := by
  rw [locusExp]
  by_cases h : (i : ℕ) < t
  · rw [dif_pos h, if_pos h, Finsupp.sum_single_index rfl]
  · rw [dif_neg h, if_neg h, Finsupp.sum_single_index rfl]

theorem locusExp_injective {t c : ℕ} (ht : 0 < t) :
    Function.Injective (locusExp (c := c) ht) := by
  intro i j hij
  have hdeg := congrArg (fun f : Fin t →₀ ℕ => f.sum (fun _ n => n)) hij
  simp only [locusExp_degree] at hdeg
  by_cases hi : (i : ℕ) < t <;> by_cases hj : (j : ℕ) < t
  · rw [locusExp, dif_pos hi, locusExp, dif_pos hj] at hij
    have h0 := congrArg (fun f => f ⟨i, hi⟩) hij
    simp only [Finsupp.single_apply] at h0
    by_cases h : (⟨j, hj⟩ : Fin t) = ⟨i, hi⟩
    · exact Fin.ext (by simpa using congrArg Fin.val h.symm)
    · rw [if_neg h] at h0
      simp at h0
  · rw [if_pos hi, if_neg hj] at hdeg
    omega
  · rw [if_neg hi, if_pos hj] at hdeg
    omega
  · rw [if_neg hi, if_neg hj] at hdeg
    exact Fin.ext (by omega)

/-- The realization family itself. -/
noncomputable def locusFamily {t c : ℕ} (ht : 0 < t) (θ : Fin t → ℝ) (i : Fin c) : ℝ :=
  if h : (i : ℕ) < t then θ ⟨i, h⟩ else θ ⟨0, ht⟩ ^ ((i : ℕ) - t + 2)

theorem locusFamily_eq_aeval {t c : ℕ} (ht : 0 < t) (θ : Fin t → ℝ) (i : Fin c) :
    locusFamily ht θ i
      = MvPolynomial.aeval θ (MvPolynomial.monomial (locusExp (c := c) ht i) (1 : ℚ)) := by
  rw [locusFamily, locusExp]
  by_cases h : (i : ℕ) < t
  · rw [dif_pos h, dif_pos h, MvPolynomial.aeval_monomial,
      Finsupp.prod_single_index (by simp)]
    simp
  · rw [dif_neg h, dif_neg h, MvPolynomial.aeval_monomial,
      Finsupp.prod_single_index (by simp)]
    simp

theorem one_lt_locusFamily {t c : ℕ} (ht : 0 < t) {θ : Fin t → ℝ} (hθ : ∀ i, 1 < θ i)
    (i : Fin c) : 1 < locusFamily ht θ i := by
  rw [locusFamily]
  by_cases h : (i : ℕ) < t
  · rw [dif_pos h]; exact hθ _
  · rw [dif_neg h]
    exact one_lt_pow₀ (hθ _) (by omega)

theorem linearIndependent_locusFamily {t c : ℕ} (ht : 0 < t) {θ : Fin t → ℝ}
    (hθ : AlgebraicIndependent ℚ θ) : LinearIndependent ℚ (locusFamily (c := c) ht θ) := by
  have hfun : locusFamily (c := c) ht θ
      = fun i => (MvPolynomial.aeval θ)
          (MvPolynomial.monomial (locusExp (c := c) ht i) (1 : ℚ)) := by
    funext i
    exact locusFamily_eq_aeval ht θ i
  have hb0 := (MvPolynomial.basisMonomials (Fin t) ℚ).linearIndependent
  rw [MvPolynomial.coe_basisMonomials] at hb0
  have hbasis := hb0.comp (locusExp (c := c) ht) (locusExp_injective ht)
  have hinj : Function.Injective (MvPolynomial.aeval θ : MvPolynomial (Fin t) ℚ →ₐ[ℚ] ℝ) :=
    algebraicIndependent_iff_injective_aeval.mp hθ
  have hmap := hbasis.map'
    (MvPolynomial.aeval θ : MvPolynomial (Fin t) ℚ →ₐ[ℚ] ℝ).toLinearMap
    (LinearMap.ker_eq_bot.mpr hinj)
  rw [hfun]
  simpa [Function.comp_def] using hmap


theorem adjoin_range_locusFamily {t c : ℕ} (ht : 0 < t) (htc : t ≤ c) (θ : Fin t → ℝ) :
    IntermediateField.adjoin ℚ (Set.range (locusFamily (c := c) ht θ))
      = IntermediateField.adjoin ℚ (Set.range θ) := by
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨i, rfl⟩
    rw [locusFamily]
    by_cases h : (i : ℕ) < t
    · rw [dif_pos h]
      exact IntermediateField.subset_adjoin ℚ (Set.range θ) (Set.mem_range_self _)
    · rw [dif_neg h]
      exact pow_mem (IntermediateField.subset_adjoin ℚ (Set.range θ) (Set.mem_range_self _)) _
  · rw [IntermediateField.adjoin_le_iff]
    rintro x ⟨j, rfl⟩
    have hjc : (j : ℕ) < c := lt_of_lt_of_le j.isLt htc
    have hval : θ j = locusFamily (c := c) ht θ ⟨(j : ℕ), hjc⟩ := by
      rw [locusFamily, dif_pos (by simp)]
    rw [hval]
    exact IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self _)

theorem trdeg_adjoin_range_locusFamily {t c : ℕ} (ht : 0 < t) (htc : t ≤ c) {θ : Fin t → ℝ}
    (hθ : AlgebraicIndependent ℚ θ) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range (locusFamily (c := c) ht θ)))
      = (t : Cardinal) := by
  rw [adjoin_range_locusFamily ht htc]
  have h := HTGeometry.trdeg_intermediateFieldAdjoin_range_eq_cardinalMk_of_algebraicIndependent
    θ hθ
  exact h.trans (by simp)

/-- **The upper constraint.**  The transcendence degree of the field generated by a finite family
of reals is at most the dimension of its `ℚ`-linear span. -/
theorem trdeg_adjoin_le_finrank_span {c : ℕ} (L : Fin c → ℝ) :
    Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range L))
      ≤ (Module.finrank ℚ (Submodule.span ℚ (Set.range L)) : Cardinal) := by
  classical
  obtain ⟨s, hsub, hspan, hli⟩ := exists_linearIndependent ℚ (Set.range L)
  have hfin : s.Finite := (Set.finite_range L).subset hsub
  haveI : Fintype s := hfin.fintype
  have hadj : IntermediateField.adjoin ℚ (Set.range L) = IntermediateField.adjoin ℚ s := by
    apply le_antisymm
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      have hxspan : x ∈ Submodule.span ℚ s := by
        rw [hspan]
        exact Submodule.subset_span hx
      have hsub' : Submodule.span ℚ s
          ≤ Subalgebra.toSubmodule (IntermediateField.adjoin ℚ s).toSubalgebra := by
        rw [Submodule.span_le]
        intro y hy
        exact IntermediateField.subset_adjoin _ _ hy
      exact hsub' hxspan
    · rw [IntermediateField.adjoin_le_iff]
      intro x hx
      exact IntermediateField.subset_adjoin _ _ (hsub hx)
  have hle : Algebra.trdeg ℚ (IntermediateField.adjoin ℚ s) ≤ Cardinal.mk s := by
    have := HTGeometry.trdeg_intermediateFieldAdjoin_range_le (F := ℚ) (E := ℝ)
      ((↑) : s → ℝ)
    rwa [Subtype.range_coe] at this
  have hcard : Cardinal.mk s
      = (Module.finrank ℚ (Submodule.span ℚ (Set.range L)) : Cardinal) := by
    have hrank : Module.finrank ℚ (Submodule.span ℚ s) = s.toFinset.card :=
      finrank_span_set_eq_card hli
    rw [hspan] at hrank
    rw [Cardinal.mk_fintype, ← Set.toFinset_card, hrank]
  rw [hadj, ← hcard]
  exact hle


/-- **Realization of the full sub-diagonal.**  For every pair `1 ≤ t ≤ c` there is a family of `c`
reals larger than `1`, `ℚ`-linearly independent (so of corank exactly `c`), generating a field of
transcendence degree exactly `t`. -/
theorem exists_corank_trdeg_realization {c t : ℕ} (ht : 0 < t) (htc : t ≤ c) :
    ∃ L : Fin c → ℝ, (∀ i, 1 < L i) ∧ Function.Injective L ∧
      Module.finrank ℚ (Submodule.span ℚ (Set.range L)) = c ∧
      Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range L)) = (t : Cardinal) := by
  obtain ⟨θ₀, hθ₀⟩ := HTGeometry.exists_algebraicIndependent_fin_real t
  haveI : Nonempty (Fin t) := ⟨⟨0, ht⟩⟩
  obtain ⟨N, hN⟩ := exists_rat_gt (1 - Finset.univ.inf' Finset.univ_nonempty θ₀)
  have hθ : AlgebraicIndependent ℚ (fun i => θ₀ i + (N : ℝ)) :=
    AlgebraicIndependent.add_const hθ₀ N
  have hone : ∀ i, 1 < θ₀ i + (N : ℝ) := by
    intro i
    have hinf : Finset.univ.inf' Finset.univ_nonempty θ₀ ≤ θ₀ i :=
      Finset.inf'_le (s := (Finset.univ : Finset (Fin t))) θ₀ (Finset.mem_univ i)
    linarith
  refine ⟨locusFamily (c := c) ht (fun i => θ₀ i + (N : ℝ)), ?_, ?_, ?_, ?_⟩
  · exact fun i => one_lt_locusFamily ht hone i
  · exact (linearIndependent_locusFamily ht hθ).injective
  · have := finrank_span_eq_card (linearIndependent_locusFamily (c := c) ht hθ)
    simpa using this
  · exact trdeg_adjoin_range_locusFamily ht htc hθ

/-- **The realization locus.**  A pair `(c, t)` with `1 ≤ t ≤ c` is realized by an explicit family,
and no family can exceed its own corank. -/
theorem corank_trdeg_locus {c t : ℕ} (ht : 0 < t) (htc : t ≤ c) :
    (∃ L : Fin c → ℝ, (∀ i, 1 < L i) ∧ Function.Injective L ∧
        Module.finrank ℚ (Submodule.span ℚ (Set.range L)) = c ∧
        Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range L)) = (t : Cardinal))
      ∧ ∀ L : Fin c → ℝ,
        Algebra.trdeg ℚ (IntermediateField.adjoin ℚ (Set.range L))
          ≤ (Module.finrank ℚ (Submodule.span ℚ (Set.range L)) : Cardinal) :=
  ⟨exists_corank_trdeg_realization ht htc, fun L => trdeg_adjoin_le_finrank_span L⟩

/-- The same transcendence degree read on the relative algebraic closure, the field `ℚ̄(L)` of the
card. -/
theorem trdeg_algebraicClosure_adjoin_range_locusFamily {t c : ℕ} (ht : 0 < t) (htc : t ≤ c)
    {θ : Fin t → ℝ} (hθ : AlgebraicIndependent ℚ θ) :
    Algebra.trdeg ℚ
        ((algebraicClosure
          (IntermediateField.adjoin ℚ (Set.range (locusFamily (c := c) ht θ))) ℝ).restrictScalars ℚ)
      = (t : Cardinal) := by
  have h1 := HTGeometry.trdeg_algebraicClosure_restrictScalars_eq (K := ℚ) (L := ℝ)
    (IntermediateField.adjoin ℚ (Set.range (locusFamily (c := c) ht θ)))
  exact h1.trans (trdeg_adjoin_range_locusFamily ht htc hθ)

end GaloisForLFunctions.CorankTrdeg
