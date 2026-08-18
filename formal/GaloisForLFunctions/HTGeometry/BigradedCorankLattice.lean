import Mathlib
import GaloisForLFunctions.Core

/-!
# The bigraded corank and its relation lattice

`bigraded-corank-dss-cross.md` §A defines, for a "regular" family `u` and an "exponential" family
`w` inside a field extension, the bigraded corank

```text
corank^{(T,U)} = dim_F span_F { ∏ u_i^{a_i} · ∏ w_j^{b_j} : Σ a ≤ T, Σ b ≤ U }.
```

This file builds that object and proves the provable content of §A and §B.

* `algebraicIndependent_iff_linearIndependent_monomialValue` — a family is algebraically
  independent exactly when its monomials are linearly independent.  This is the general fact
  underlying Proposition A1; note that "full rank" there must be read as *linear independence of
  the monomials*, not merely infinite dimension of their span (an infinite-dimensional span is
  strictly weaker and does not characterise algebraic independence).
* `algebraicIndependent_iff_linearIndependent_mixed` and
  `algebraicIndependent_iff_forall_bidegreeBox` — Proposition A1 in the bigraded parametrisation:
  the joint family is algebraically independent iff every bidegree box carries linearly independent
  mixed monomials.  Combined with §G's `algebraicIndependent_sumElim_intermediateField_iff` this is
  the DSS-cross factorisation.
* `bigradedSpan_exponential_zero` — §B's `U = 0` column: only pure regular monomials occur.
* `bigradedSpan_of_isEmpty` — §B's function-field collapse: with no exponential generators the
  `U`-direction is trivial.
* `bigradedCorank_eq_rank_quotient` — the corank is the quotient rank of the lattice of linear
  relations among the box monomials, as §A states.
* `aleph0_le_bigradedCorank_primeLog` — the proven floor `corank^{(1,0)} = ∞` for the prime
  logarithms, from `GaloisForLFunctions.linearIndependent_log_primes`.

The apex (`corank^{(T,U)} = ∞` for all positive bidegrees) is DSS-cross and is *not* claimed.
-/

noncomputable section

open MvPolynomial

namespace GaloisForLFunctions.HTGeometry.BigradedCorank

universe uF uE uI uK

variable {F : Type uF} {E : Type uE} {ι : Type uI} {κ : Type uK}
variable [Field F] [CommRing E] [Algebra F E]

/-- The value of the monomial with exponent vector `d` in the family `v`. -/
def monomialValue (v : ι → E) (d : ι →₀ ℕ) : E := ∏ i ∈ d.support, v i ^ d i

theorem aeval_eq_sum_monomialValue (v : ι → E) (p : MvPolynomial ι F) :
    MvPolynomial.aeval v p = ∑ d ∈ p.support, p.coeff d • monomialValue v d := by
  classical
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  rw [monomialValue, Algebra.smul_def]

/-- **Algebraic independence is linear independence of the monomials.**  This is the precise form
of the card's "every bidegree has full rank": full rank means the monomials are linearly
independent. -/
theorem algebraicIndependent_iff_linearIndependent_monomialValue (v : ι → E) :
    AlgebraicIndependent F v ↔ LinearIndependent F (monomialValue v) := by
  classical
  rw [algebraicIndependent_iff, linearIndependent_iff']
  constructor
  · intro h s g hsum d hd
    set p : MvPolynomial ι F := ∑ e ∈ s, MvPolynomial.monomial e (g e) with hp
    have hzero : MvPolynomial.aeval v p = 0 := by
      rw [hp, map_sum]
      refine Eq.trans (Finset.sum_congr rfl (fun e _ => ?_)) hsum
      rw [MvPolynomial.aeval_monomial, monomialValue, Algebra.smul_def]
      rfl
    have hp0 : p = 0 := h p hzero
    have hcoeff : p.coeff d = g d := by
      rw [hp, MvPolynomial.coeff_sum]
      rw [Finset.sum_eq_single d]
      · rw [MvPolynomial.coeff_monomial, if_pos rfl]
      · intro e _ hed
        rw [MvPolynomial.coeff_monomial, if_neg hed]
      · intro hcon
        exact absurd hd hcon
    rw [← hcoeff, hp0, MvPolynomial.coeff_zero]
  · intro h p hp
    have hsum : ∑ d ∈ p.support, p.coeff d • monomialValue v d = 0 := by
      rw [← aeval_eq_sum_monomialValue, hp]
    have hall : ∀ d ∈ p.support, p.coeff d = 0 := h p.support (fun d => p.coeff d) hsum
    refine MvPolynomial.ext p 0 (fun d => ?_)
    rw [MvPolynomial.coeff_zero]
    by_cases hd : d ∈ p.support
    · exact hall d hd
    · exact MvPolynomial.notMem_support_iff.mp hd

/-! ## Mixed monomials and the bigrading -/

/-- The exponent vector of the joined family attached to a bidegree. -/
def joinExp (b : κ →₀ ℕ) (a : ι →₀ ℕ) : (κ ⊕ ι) →₀ ℕ :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm (b, a)

theorem joinExp_eq (b : κ →₀ ℕ) (a : ι →₀ ℕ) :
    joinExp b a = b.mapDomain Sum.inl + a.mapDomain Sum.inr := by
  classical
  refine Finsupp.ext (fun x => ?_)
  cases x with
  | inl j =>
      rw [joinExp, Finsupp.sumFinsuppEquivProdFinsupp_symm_inl, Finsupp.add_apply,
        Finsupp.mapDomain_apply Sum.inl_injective]
      have : (Finsupp.mapDomain Sum.inr a) (Sum.inl j) = 0 := by
        refine Finsupp.notMem_support_iff.mp (fun hcon => ?_)
        obtain ⟨i, _, hi⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hcon)
        exact Sum.inr_ne_inl hi
      rw [this, add_zero]
  | inr i =>
      rw [joinExp, Finsupp.sumFinsuppEquivProdFinsupp_symm_inr, Finsupp.add_apply,
        Finsupp.mapDomain_apply Sum.inr_injective]
      have : (Finsupp.mapDomain Sum.inl b) (Sum.inr i) = 0 := by
        refine Finsupp.notMem_support_iff.mp (fun hcon => ?_)
        obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (Finsupp.mapDomain_support hcon)
        exact Sum.inl_ne_inr hj
      rw [this, zero_add]

/-- The mixed monomial of a bidegree. -/
def mixedMonomialValue (u : ι → E) (w : κ → E) (p : (κ →₀ ℕ) × (ι →₀ ℕ)) : E :=
  monomialValue w p.1 * monomialValue u p.2

theorem monomialValue_joinExp (u : ι → E) (w : κ → E) (b : κ →₀ ℕ) (a : ι →₀ ℕ) :
    monomialValue (Sum.elim w u) (joinExp b a) = monomialValue w b * monomialValue u a := by
  classical
  have hprod : ∀ (v : (κ ⊕ ι) → E) (d : (κ ⊕ ι) →₀ ℕ),
      monomialValue v d = d.prod (fun x n => v x ^ n) := fun v d => rfl
  rw [hprod, joinExp_eq]
  rw [Finsupp.prod_add_index' (fun x => pow_zero _) (fun x m n => pow_add _ m n)]
  congr 1
  · rw [Finsupp.prod_mapDomain_index_inj Sum.inl_injective]
    rfl
  · rw [Finsupp.prod_mapDomain_index_inj Sum.inr_injective]
    rfl

/-- The bidegree reindexing is a bijection onto the exponent vectors of the joined family. -/
def bidegreeEquiv : (κ →₀ ℕ) × (ι →₀ ℕ) ≃ ((κ ⊕ ι) →₀ ℕ) :=
  Finsupp.sumFinsuppEquivProdFinsupp.symm

theorem mixedMonomialValue_eq (u : ι → E) (w : κ → E) :
    mixedMonomialValue u w
      = (monomialValue (Sum.elim w u)) ∘ (bidegreeEquiv (κ := κ) (ι := ι)) := by
  funext p
  rw [Function.comp_apply, mixedMonomialValue, bidegreeEquiv]
  exact (monomialValue_joinExp u w p.1 p.2).symm

/-- **Proposition A1.**  The joint family is algebraically independent exactly when the mixed
monomials of all bidegrees are linearly independent — the precise reading of "every bidegree has
full rank". -/
theorem algebraicIndependent_iff_linearIndependent_mixed (u : ι → E) (w : κ → E) :
    AlgebraicIndependent F (Sum.elim w u) ↔ LinearIndependent F (mixedMonomialValue u w) := by
  rw [algebraicIndependent_iff_linearIndependent_monomialValue, mixedMonomialValue_eq]
  exact (linearIndependent_equiv _).symm

/-! ## The bigraded span, corank and relation lattice -/

/-- The total degree of an exponent vector. -/
def expDegree (d : ι →₀ ℕ) : ℕ := d.sum fun _ n => n

theorem expDegree_eq_zero_iff {d : ι →₀ ℕ} : expDegree d = 0 ↔ d = 0 := by
  constructor
  · intro h
    refine Finsupp.ext (fun i => ?_)
    by_contra hcon
    have hmem : i ∈ d.support := Finsupp.mem_support_iff.mpr hcon
    have hle : d i ≤ expDegree d :=
      Finset.single_le_sum (f := fun i => d i) (fun _ _ => Nat.zero_le _) hmem
    rw [h] at hle
    exact hcon (Nat.le_zero.mp hle)
  · intro h
    rw [h, expDegree]
    simp

/-- The bidegree box: mixed monomials of regular degree at most `T` and exponential degree at most
`U`. -/
def bidegreeBox (ι κ : Type*) (T U : ℕ) : Set ((κ →₀ ℕ) × (ι →₀ ℕ)) :=
  {p | expDegree p.1 ≤ U ∧ expDegree p.2 ≤ T}

/-- The bigraded span of all mixed monomials in a bidegree box. -/
def bigradedSpan (F : Type*) [Field F] {E ι κ : Type*} [CommRing E] [Algebra F E]
    (u : ι → E) (w : κ → E) (T U : ℕ) : Submodule F E :=
  Submodule.span F (mixedMonomialValue u w '' bidegreeBox ι κ T U)

/-- The bigraded corank. -/
def bigradedCorank (F : Type*) [Field F] {E ι κ : Type*} [CommRing E] [Algebra F E]
    (u : ι → E) (w : κ → E) (T U : ℕ) : Cardinal :=
  Module.rank F (bigradedSpan F u w T U)

/-- The bidegree boxes exhaust every bidegree. -/
theorem iUnion_bidegreeBox : (⋃ p : ℕ × ℕ, bidegreeBox ι κ p.1 p.2) = Set.univ := by
  refine Set.eq_univ_of_forall (fun q => ?_)
  exact Set.mem_iUnion.mpr ⟨(expDegree q.2, expDegree q.1), le_rfl, le_rfl⟩

theorem directed_bidegreeBox :
    Directed (· ⊆ ·) (fun p : ℕ × ℕ => bidegreeBox ι κ p.1 p.2) := by
  intro p q
  refine ⟨(max p.1 q.1, max p.2 q.2), ?_, ?_⟩
  · exact fun x hx => ⟨le_trans hx.1 (le_max_left _ _), le_trans hx.2 (le_max_left _ _)⟩
  · exact fun x hx => ⟨le_trans hx.1 (le_max_right _ _), le_trans hx.2 (le_max_right _ _)⟩

/-- **The bigraded form of Proposition A1.**  The joint family is algebraically independent exactly
when every bidegree box carries linearly independent mixed monomials. -/
theorem algebraicIndependent_iff_forall_bidegreeBox (u : ι → E) (w : κ → E) :
    AlgebraicIndependent F (Sum.elim w u) ↔
      ∀ T U : ℕ, LinearIndepOn F (mixedMonomialValue u w) (bidegreeBox ι κ T U) := by
  rw [algebraicIndependent_iff_linearIndependent_mixed]
  constructor
  · intro h T U
    exact h.linearIndepOn _
  · intro h
    rw [← linearIndepOn_univ_iff, ← iUnion_bidegreeBox]
    exact linearIndepOn_iUnion_of_directed directed_bidegreeBox (fun p => h p.1 p.2)

/-! ## The three regions -/

theorem monomialValue_zero (v : ι → E) : monomialValue v 0 = 1 := by
  rw [monomialValue]
  simp

/-- **The `U = 0` column is the regular layer.**  Only pure regular monomials occur. -/
theorem bigradedSpan_exponential_zero (u : ι → E) (w : κ → E) (T : ℕ) :
    bigradedSpan F u w T 0
      = Submodule.span F (monomialValue u '' {a : ι →₀ ℕ | expDegree a ≤ T}) := by
  rw [bigradedSpan]
  congr 1
  ext x
  constructor
  · rintro ⟨p, hp, rfl⟩
    have hb : p.1 = 0 := expDegree_eq_zero_iff.mp (Nat.le_zero.mp hp.1)
    refine ⟨p.2, hp.2, ?_⟩
    rw [mixedMonomialValue, hb, monomialValue_zero, one_mul]
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(0, a), ⟨by rw [expDegree_eq_zero_iff.mpr rfl], ha⟩, ?_⟩
    rw [mixedMonomialValue, monomialValue_zero, one_mul]

/-- **The function-field collapse.**  With no exponential generators the `U`-direction is trivial:
every bidegree box reduces to its regular column. -/
theorem bigradedSpan_of_isEmpty [IsEmpty κ] (u : ι → E) (w : κ → E) (T U : ℕ) :
    bigradedSpan F u w T U = bigradedSpan F u w T 0 := by
  have hbox : bidegreeBox ι κ T U = bidegreeBox ι κ T 0 := by
    ext p
    have hp : p.1 = 0 := Finsupp.ext (fun j => isEmptyElim j)
    simp only [bidegreeBox, Set.mem_setOf_eq, hp, expDegree_eq_zero_iff.mpr rfl]
    simp
  rw [bigradedSpan, bigradedSpan, hbox]

/-! ## The relation lattice -/

/-- The lattice of `F`-linear relations among the mixed monomials of a bidegree box. -/
def bigradedRelations (F : Type*) [Field F] {E ι κ : Type*} [CommRing E] [Algebra F E]
    (u : ι → E) (w : κ → E) (T U : ℕ) :
    Submodule F ((bidegreeBox ι κ T U) →₀ F) :=
  LinearMap.ker (Finsupp.linearCombination F
    (fun p : (bidegreeBox ι κ T U) => mixedMonomialValue u w (p : (κ →₀ ℕ) × (ι →₀ ℕ))))

/-- **The corank is the quotient rank of the relation lattice.** -/
theorem bigradedCorank_eq_rank_quotient (u : ι → E) (w : κ → E) (T U : ℕ) :
    Cardinal.lift.{max uF uI uK} (bigradedCorank F u w T U)
      = Cardinal.lift.{uE}
          (Module.rank F (((bidegreeBox ι κ T U) →₀ F) ⧸ bigradedRelations F u w T U)) := by
  classical
  set f := Finsupp.linearCombination F
    (fun p : (bidegreeBox ι κ T U) => mixedMonomialValue u w (p : (κ →₀ ℕ) × (ι →₀ ℕ))) with hf
  have hrange : LinearMap.range f = bigradedSpan F u w T U := by
    rw [hf, Finsupp.range_linearCombination, bigradedSpan]
    congr 1
    exact (Set.image_eq_range (mixedMonomialValue u w) (bidegreeBox ι κ T U)).symm
  rw [bigradedCorank, ← hrange, bigradedRelations, ← hf]
  exact (f.quotKerEquivRange.lift_rank_eq).symm

/-! ## The proven regular floor -/

theorem monomialValue_single (v : ι → E) (i : ι) : monomialValue v (Finsupp.single i 1) = v i := by
  classical
  have hsupp : (Finsupp.single i (1 : ℕ)).support = {i} := by
    simp
  rw [monomialValue, hsupp, Finset.prod_singleton, Finsupp.single_eq_same, pow_one]

theorem expDegree_single (i : ι) : expDegree (Finsupp.single i 1) = 1 := by
  rw [expDegree, Finsupp.sum_single_index rfl]

/-- **The regular floor `corank^{(1,0)} = ∞`.**  The prime logarithms are `ℚ`-linearly independent,
so the regular column already has infinite corank at degree one. -/
theorem aleph0_le_bigradedCorank_primeLog {κ : Type} (w : κ → ℝ) :
    Cardinal.aleph0
      ≤ bigradedCorank ℚ (fun p : Nat.Primes => Real.log (p : ℕ)) w 1 0 := by
  classical
  set u : Nat.Primes → ℝ := fun p => Real.log (p : ℕ) with hu
  set S : Submodule ℚ ℝ := bigradedSpan ℚ u w 1 0 with hSdef
  have hmem : ∀ p : Nat.Primes, u p ∈ S := by
    intro p
    refine Submodule.subset_span ⟨(0, Finsupp.single p 1), ⟨?_, ?_⟩, ?_⟩
    · rw [expDegree_eq_zero_iff.mpr rfl]
    · rw [expDegree_single]
    · rw [mixedMonomialValue, monomialValue_zero, one_mul, monomialValue_single]
  set v : Nat.Primes → S := fun p => ⟨u p, hmem p⟩ with hv
  have hli : LinearIndependent ℚ v := by
    refine LinearIndependent.of_comp (S.subtype) ?_
    exact GaloisForLFunctions.linearIndependent_log_primes
  have hcard : Cardinal.mk Nat.Primes ≤ Module.rank ℚ S := hli.cardinal_le_rank
  exact le_trans (Cardinal.aleph0_le_mk Nat.Primes) hcard

end GaloisForLFunctions.HTGeometry.BigradedCorank
