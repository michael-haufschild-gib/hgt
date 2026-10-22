import GaloisForLFunctions.RHTower.Deninger.DeningerHankelHigherRankGroebner
import GaloisForLFunctions.HTGeometry.MonomialSpan

/-!
# Standard monomials of the Hankel secant ideal and its monomial degeneration

The corpus already proves that the canonical `(r+1)`-minors of the generic Hankel matrix are a
degree-lex Gröbner basis of the secant ideal, and that the standard monomials of that basis are the
**chain-reduced** exponents — those whose support contains no `r+1` indices pairwise at distance at
least two.  This file draws the structural consequence.

```text
not_finiteHankelChainReduced_of_diagonal_le
    a leading diagonal below an exponent destroys chain reduction (the converse of
    `exists_finiteHankelMinor_diagonal_le_of_not_chainReduced`)
hankelStandardSpan K N r                 the span of the chain-reduced monomials
isCompl_finiteHankelSecantIdeal_standardSpan
    ** the chain-reduced monomials are a complement of the secant ideal **
finiteHankelChainIdeal K N r             the initial monomial ideal of the degeneration
isCompl_finiteHankelChainIdeal_standardSpan
    ** and a complement of the initial monomial ideal **
hankelDegenerationLinearEquiv
    ** hence the secant quotient and its monomial degeneration are `K`-isomorphic **
```

Existence of the normal form is Gröbner division; uniqueness is the Gröbner-basis property.  One
and the same set of monomials is therefore a `K`-basis of both quotients — the Hilbert-function
equality of the degeneration in its sharpest, basis-level form.  It is the input a Cohen–Macaulay
transfer from the Stanley–Reisner ring of the chain complex to the Hankel secant ring consumes.
-/

namespace GaloisForLFunctions.HTGeometry

open MvPolynomial RHTower

universe u

theorem one_le_hankelDiagonalExponent {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (j0 : Fin n) :
    1 ≤ hankelDiagonalExponent c hbound (finiteHankelIndex c hbound j0 j0) := by
  classical
  rw [hankelDiagonalExponent, hankelPermutationExponent_apply]
  refine le_trans ?_ (Finset.single_le_sum
    (f := fun j : Fin n => if finiteHankelIndex c hbound ((1 : Equiv.Perm (Fin n)) j) j
      = finiteHankelIndex c hbound j0 j0 then 1 else 0)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j0))
  simp

/-- **A leading diagonal below an exponent destroys chain reduction.**  The support of the diagonal
of a canonical Hankel minor is an `(r+1)`-chain, so an exponent above it is not chain-reduced. -/
theorem not_finiteHankelChainReduced_of_diagonal_le {N r : ℕ} {c : Fin (r + 1) → ℕ}
    (hbound : ∀ j, (r + 1) + c j ≤ N) (hc : StrictMono c) {e : Fin N →₀ ℕ}
    (hle : hankelDiagonalExponent c hbound ≤ e) :
    ¬ FiniteHankelChainReduced N r e := by
  classical
  intro hred
  apply hred
  set f : Fin (r + 1) → ℕ := fun j => (j : ℕ) + c j with hf
  have hstep : ∀ i j : Fin (r + 1), i < j → f i + 1 < f j := by
    intro i j hij
    have h1 : (i : ℕ) < (j : ℕ) := hij
    have h2 : c i < c j := hc hij
    simp only [hf]
    omega
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    rcases lt_or_gt_of_ne (fun h : i = j => hne h) with h | h
    · exact absurd hij (by have := hstep i j h; omega)
    · exact absurd hij (by have := hstep j i h; omega)
  refine ⟨Finset.image f Finset.univ, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  · intro a ha b hb hab
    simp only [Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at ha hb
    obtain ⟨i, rfl⟩ := ha
    obtain ⟨j, rfl⟩ := hb
    have hij : i ≠ j := fun h => hab (by rw [h])
    rcases lt_or_gt_of_ne hij with h | h
    · exact Or.inl (hstep i j h)
    · exact Or.inr (hstep j i h)
  · intro a ha
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp ha
    have hval : f j = (finiteHankelIndex c hbound j j : Fin N).val := rfl
    have hone : 1 ≤ e (finiteHankelIndex c hbound j j) :=
      le_trans (one_le_hankelDiagonalExponent c hbound j) (hle _)
    rw [Finsupp.mem_support_iff, hval, Finsupp.mapDomain_apply Fin.val_injective]
    omega

variable {K : Type u} [Field K]

/-- The span of the chain-reduced monomials: the standard monomials of the Hankel degeneration. -/
noncomputable def hankelStandardSpan (K : Type u) [Field K] (N r : ℕ) :
    Submodule K (MvPolynomial (Fin N) K) :=
  monomialSpan K {e : Fin N →₀ ℕ | FiniteHankelChainReduced N r e}

theorem mem_hankelStandardSpan_iff {N r : ℕ} {p : MvPolynomial (Fin N) K} :
    p ∈ hankelStandardSpan K N r ↔ ∀ e ∈ p.support, FiniteHankelChainReduced N r e := by
  rw [hankelStandardSpan, mem_monomialSpan_iff]
  constructor
  · intro h e he
    exact h (by simpa using he)
  · intro h e he
    exact h e (by simpa using he)

theorem hankelMinor_isUnit_leadingCoeff (N r : ℕ) :
    ∀ b ∈ finiteHankelMaximalMinorSetOver K N (r + 1),
      IsUnit (MonomialOrder.degLex.leadingCoeff b) := by
  intro b hb
  rw [(finiteHankelMaximalMinorSetOver_degLex_monic K N (r + 1) b hb).leadingCoeff_eq_one]
  exact isUnit_one

theorem not_degree_le_of_chainReduced {N r : ℕ} {e : Fin N →₀ ℕ}
    (he : FiniteHankelChainReduced N r e) :
    ∀ b ∈ finiteHankelMaximalMinorSetOver K N (r + 1), ¬ MonomialOrder.degLex.degree b ≤ e := by
  rintro b ⟨c, hbound, hc, rfl⟩ hle
  rw [finiteHankelMaximalMinorOver_degLex_degree c hbound hc] at hle
  exact not_finiteHankelChainReduced_of_diagonal_le hbound hc hle he

/-- **The chain-reduced monomials are a complement of the Hankel secant ideal.**  Existence of the
normal form is Gröbner division; uniqueness is the Gröbner-basis property.  So the standard
monomials are a `K`-basis of the secant quotient. -/
theorem isCompl_finiteHankelSecantIdeal_standardSpan (K : Type u) [Field K] (N r : ℕ) :
    IsCompl (Submodule.restrictScalars K (finiteHankelSecantIdeal K N r))
      (hankelStandardSpan K N r) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro p hpI hpS
    rw [Submodule.restrictScalars_mem] at hpI
    rw [mem_hankelStandardSpan_iff] at hpS
    refine MonomialOrder.reduced_mem_span_eq_zero MonomialOrder.degLex
      (finiteHankelMaximalMinorSetOver K N (r + 1))
      (finiteHankelSecant_degLex_isGroebnerBasis K N r) p hpI ?_
    intro c hc b hb
    exact not_degree_le_of_chainReduced (hpS c hc) b hb
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    obtain ⟨g, rem, hpr, -, hnormal⟩ :=
      MonomialOrder.degLex.div_set (hankelMinor_isUnit_leadingCoeff (K := K) N r) p
    set q := Finsupp.linearCombination (MvPolynomial (Fin N) K)
      (fun b : (finiteHankelMaximalMinorSetOver K N (r + 1)) =>
        (b : MvPolynomial (Fin N) K)) g with hq
    have hqmem : q ∈ finiteHankelSecantIdeal K N r :=
      MonomialOrder.linearCombination_mem_span _ g
    have hremReduced : ∀ e ∈ rem.support, FiniteHankelChainReduced N r e := by
      intro e he hnot
      have hnotRed : ¬ FiniteHankelChainReduced N r e := fun hred => hred hnot
      obtain ⟨c, hbound, hc, hdiag⟩ :=
        exists_finiteHankelMinor_diagonal_le_of_not_chainReduced hnotRed
      refine hnormal e he (finiteHankelMaximalMinorOver K c hbound) ⟨c, hbound, hc, rfl⟩ ?_
      rwa [finiteHankelMaximalMinorOver_degLex_degree c hbound hc]
    refine Submodule.mem_sup.mpr ⟨q, ?_, rem, ?_, hpr.symm⟩
    · rwa [Submodule.restrictScalars_mem]
    · rw [mem_hankelStandardSpan_iff]
      exact hremReduced


/-! ## The monomial degeneration -/

/-- The initial (chain) monomial ideal: generated by every non-chain-reduced monomial. -/
noncomputable def finiteHankelChainIdeal (K : Type u) [Field K] (N r : ℕ) :
    Ideal (MvPolynomial (Fin N) K) :=
  Ideal.span ((fun e => MvPolynomial.monomial e (1 : K)) ''
    {e : Fin N →₀ ℕ | ¬ FiniteHankelChainReduced N r e})

theorem not_chainReduced_of_le {N r : ℕ} {d e : Fin N →₀ ℕ} (hde : d ≤ e)
    (hd : ¬ FiniteHankelChainReduced N r d) : ¬ FiniteHankelChainReduced N r e := by
  classical
  obtain ⟨J, hcard, hpair, hsub⟩ := not_not.mp hd
  intro he
  refine he ⟨J, hcard, hpair, hsub.trans ?_⟩
  rw [Finsupp.mapDomain_support_of_injective Fin.val_injective,
    Finsupp.mapDomain_support_of_injective Fin.val_injective]
  intro a ha
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
  refine Finset.mem_image.mpr ⟨i, ?_, rfl⟩
  rw [Finsupp.mem_support_iff] at hi ⊢
  have := hde i
  omega

theorem mem_finiteHankelChainIdeal_iff {N r : ℕ} {p : MvPolynomial (Fin N) K} :
    p ∈ finiteHankelChainIdeal K N r ↔ ∀ e ∈ p.support, ¬ FiniteHankelChainReduced N r e := by
  rw [finiteHankelChainIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  constructor
  · intro h e he
    obtain ⟨d, hd, hle⟩ := h e he
    exact not_chainReduced_of_le hle hd
  · intro h e he
    exact ⟨e, h e he, le_rfl⟩

/-- **The chain-reduced monomials are also a complement of the initial monomial ideal.** -/
theorem isCompl_finiteHankelChainIdeal_standardSpan (K : Type u) [Field K] (N r : ℕ) :
    IsCompl (Submodule.restrictScalars K (finiteHankelChainIdeal K N r))
      (hankelStandardSpan K N r) := by
  classical
  constructor
  · rw [Submodule.disjoint_def]
    intro p hpI hpS
    rw [Submodule.restrictScalars_mem, mem_finiteHankelChainIdeal_iff] at hpI
    rw [mem_hankelStandardSpan_iff] at hpS
    by_contra hp0
    obtain ⟨e, he⟩ := MvPolynomial.support_nonempty.mpr hp0
    exact hpI e he (hpS e he)
  · rw [codisjoint_iff, eq_top_iff]
    intro p _
    have hsplit : ∑ e ∈ p.support.filter (fun e => ¬ FiniteHankelChainReduced N r e),
          MvPolynomial.monomial e (MvPolynomial.coeff e p)
        + ∑ e ∈ p.support.filter (fun e => FiniteHankelChainReduced N r e),
          MvPolynomial.monomial e (MvPolynomial.coeff e p) = p := by
      rw [add_comm, Finset.sum_filter_add_sum_filter_not]
      exact MvPolynomial.support_sum_monomial_coeff p
    refine Submodule.mem_sup.mpr ⟨_, ?_, _, ?_, hsplit⟩
    · rw [Submodule.restrictScalars_mem]
      refine Ideal.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      have hgen : MvPolynomial.monomial e (1 : K) ∈ finiteHankelChainIdeal K N r :=
        Ideal.subset_span ⟨e, he.2, rfl⟩
      have : MvPolynomial.monomial e (MvPolynomial.coeff e p)
          = MvPolynomial.C (MvPolynomial.coeff e p) * MvPolynomial.monomial e (1 : K) := by
        rw [MvPolynomial.C_mul_monomial, mul_one]
      rw [this]
      exact Ideal.mul_mem_left _ _ hgen
    · rw [hankelStandardSpan]
      refine Submodule.sum_mem _ fun e he => ?_
      rw [Finset.mem_filter] at he
      have hgen : MvPolynomial.monomial e (1 : K)
          ∈ monomialSpan K {e : Fin N →₀ ℕ | FiniteHankelChainReduced N r e} :=
        Submodule.subset_span ⟨e, he.2, rfl⟩
      have : MvPolynomial.monomial e (MvPolynomial.coeff e p)
          = (MvPolynomial.coeff e p) • MvPolynomial.monomial e (1 : K) := by
        rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
      rw [this]
      exact Submodule.smul_mem _ _ hgen

/-- **The Hankel secant quotient and its monomial degeneration are `K`-isomorphic**, by the
common standard-monomial complement.  This is the Hilbert-function equality of the degeneration in
its sharpest form: one and the same set of monomials is a `K`-basis of both. -/
noncomputable def hankelDegenerationLinearEquiv (K : Type u) [Field K] (N r : ℕ) :
    (MvPolynomial (Fin N) K ⧸ Submodule.restrictScalars K (finiteHankelSecantIdeal K N r))
      ≃ₗ[K]
    (MvPolynomial (Fin N) K ⧸ Submodule.restrictScalars K (finiteHankelChainIdeal K N r)) :=
  (Submodule.quotientEquivOfIsCompl _ _ (isCompl_finiteHankelSecantIdeal_standardSpan K N r)).trans
    (Submodule.quotientEquivOfIsCompl _ _
      (isCompl_finiteHankelChainIdeal_standardSpan K N r)).symm


end GaloisForLFunctions.HTGeometry
