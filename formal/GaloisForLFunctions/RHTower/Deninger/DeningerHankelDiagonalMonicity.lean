import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Data.Finsupp.MonomialOrder.DegLex

namespace RHTower
noncomputable section

open MvPolynomial
open scoped MonomialOrder BigOperators

def finiteHankelIndex {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (i j : Fin n) : Fin N :=
  ⟨i.val + c j, by have := i.isLt; have := hbound j; omega⟩

def hankelPermutationExponent {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (σ : Equiv.Perm (Fin n)) : Fin N →₀ ℕ :=
  ∑ j : Fin n, Finsupp.single (finiteHankelIndex c hbound (σ j) j) 1

def hankelDiagonalExponent {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) : Fin N →₀ ℕ :=
  hankelPermutationExponent c hbound 1

@[simp] theorem hankelPermutationExponent_apply {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (σ : Equiv.Perm (Fin n)) (v : Fin N) :
    hankelPermutationExponent c hbound σ v =
      ∑ j : Fin n, if finiteHankelIndex c hbound (σ j) j = v then 1 else 0 := by
  rw [hankelPermutationExponent]
  simp [Finsupp.single_apply]

@[simp] theorem hankelPermutationExponent_totalDegree {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (σ : Equiv.Perm (Fin n)) :
    Finsupp.degree (hankelPermutationExponent c hbound σ) = n := by
  rw [hankelPermutationExponent, map_sum]
  simp

theorem hankelDiagonalIndex_strictMono {n : ℕ} {c : Fin n → ℕ}
    (hc : StrictMono c) : StrictMono fun j : Fin n => j.val + c j := by
  intro i j hij
  have hijv : i.val < j.val := hij
  have hcij : c i < c j := hc hij
  exact Nat.add_lt_add hijv hcij

theorem hankelPermutationExponent_lt_diagonal {N n : ℕ} {c : Fin n → ℕ}
    (hbound : ∀ j, n + c j ≤ N) (hc : StrictMono c)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    hankelPermutationExponent c hbound σ ≺[MonomialOrder.lex]
      hankelDiagonalExponent c hbound := by
  let moved : Finset (Fin n) := Finset.univ.filter fun j => σ j ≠ j
  have hex : ∃ j : Fin n, σ j ≠ j := by
    by_contra h
    push Not at h
    exact hσ (Equiv.Perm.ext h)
  have hmoved : moved.Nonempty := by
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, by simp [moved, hj]⟩
  let k : Fin n := moved.min' hmoved
  have hkmem : k ∈ moved := Finset.min'_mem moved hmoved
  have hk : σ k ≠ k := by simpa [moved] using hkmem
  have hbefore : ∀ j : Fin n, j < k → σ j = j := by
    intro j hj
    by_contra hjm
    have hjmem : j ∈ moved := by simp [moved, hjm]
    have hle := Finset.min'_le moved j hjmem
    change k ≤ j at hle
    exact (not_le_of_gt hj) hle
  have hrow : ∀ j : Fin n, k ≤ j → k ≤ σ j := by
    intro j hkj
    by_contra hnot
    have hvlt : σ j < k := lt_of_not_ge hnot
    have hvfix : σ (σ j) = σ j := hbefore (σ j) hvlt
    have hin : σ j = j := σ.injective hvfix
    rw [hin] at hvlt
    exact (not_lt_of_ge hkj) hvlt
  let d : Fin N := finiteHankelIndex c hbound k k
  have hdiagStrict := hankelDiagonalIndex_strictMono hc
  have hpermAfter : ∀ j : Fin n, k ≤ j →
      d < finiteHankelIndex c hbound (σ j) j := by
    intro j hkj
    have hr : k.val ≤ (σ j).val := by exact hrow j hkj
    have hcol : c k ≤ c j := hc.monotone hkj
    apply Fin.mk_lt_mk.mpr
    have hle : k.val + c k ≤ (σ j).val + c j := by omega
    apply lt_of_le_of_ne hle
    intro heq
    have hrEq : (σ j).val = k.val := by omega
    have hcEq : c j = c k := by omega
    have hjk : j = k := hc.injective hcEq
    subst j
    apply hk
    apply Fin.ext
    exact hrEq
  have hpermBefore : ∀ j : Fin n, j < k →
      finiteHankelIndex c hbound (σ j) j = finiteHankelIndex c hbound j j := by
    intro j hj
    rw [hbefore j hj]
  rw [MonomialOrder.lex_lt_iff, Finsupp.Lex.lt_iff]
  refine ⟨d, ?_, ?_⟩
  · intro v hv
    simp only [ofLex_toLex]
    rw [hankelPermutationExponent_apply]
    rw [hankelDiagonalExponent, hankelPermutationExponent_apply]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hjk : j < k
    · rw [hpermBefore j hjk]
      simp
    · have hkj : k ≤ j := le_of_not_gt hjk
      have hpgt := hpermAfter j hkj
      have hdge : d ≤ finiteHankelIndex c hbound j j := by
        by_cases hEq : j = k
        · subst j; exact le_rfl
        · apply Fin.mk_le_mk.mpr
          exact le_of_lt (hdiagStrict (lt_of_le_of_ne hkj (Ne.symm hEq)))
      have hpne : finiteHankelIndex c hbound (σ j) j ≠ v := by
        intro heq
        rw [heq] at hpgt
        exact lt_asymm hv hpgt
      have hdne : finiteHankelIndex c hbound j j ≠ v := by
        intro heq
        rw [heq] at hdge
        exact (not_le_of_gt hv) hdge
      simp [hpne, hdne]
  · simp only [ofLex_toLex]
    have hpzero : (∑ j : Fin n,
        if finiteHankelIndex c hbound (σ j) j = d then 1 else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro j hj
      by_cases hjk : j < k
      · have heq := hpermBefore j hjk
        have hlt : finiteHankelIndex c hbound j j < d := by
          apply Fin.mk_lt_mk.mpr
          exact hdiagStrict hjk
        simp [heq, ne_of_lt hlt]
      · have hgt := hpermAfter j (le_of_not_gt hjk)
        simp [ne_of_gt hgt]
    have hdiagone : (∑ j : Fin n,
        if finiteHankelIndex c hbound
          ((1 : Equiv.Perm (Fin n)) j) j = d then 1 else 0) = 1 := by
      rw [Finset.sum_eq_single k]
      · simp [d]
      · intro j hj hjk
        have hne : finiteHankelIndex c hbound j j ≠ d := by
          intro heq
          apply hjk
          apply hdiagStrict.injective
          change j.val + c j = k.val + c k
          simpa [finiteHankelIndex, d] using congrArg Fin.val heq
        simp only [Equiv.Perm.one_apply]
        simp [hne]
      · simp
    have hpermApply : hankelPermutationExponent c hbound σ d = 0 := by
      rw [hankelPermutationExponent_apply]
      exact hpzero
    have hdiagApply : hankelDiagonalExponent c hbound d = 1 := by
      rw [hankelDiagonalExponent, hankelPermutationExponent_apply]
      exact hdiagone
    change hankelPermutationExponent c hbound σ d <
      hankelDiagonalExponent c hbound d
    rw [hpermApply, hdiagApply]
    exact Nat.zero_lt_one

/-- Nam's published order is degree-lexicographic.  All determinant terms have the same total
degree, so the strict diagonal comparison upgrades from lex to degree-lex without changing the
leading term. -/
theorem hankelPermutationExponent_degLex_lt_diagonal {N n : ℕ} {c : Fin n → ℕ}
    (hbound : ∀ j, n + c j ≤ N) (hc : StrictMono c)
    {σ : Equiv.Perm (Fin n)} (hσ : σ ≠ 1) :
    hankelPermutationExponent c hbound σ ≺[MonomialOrder.degLex]
      hankelDiagonalExponent c hbound := by
  rw [MonomialOrder.degLex_lt_iff, Finsupp.DegLex.lt_iff]
  right
  constructor
  · simp [hankelDiagonalExponent]
  · exact hankelPermutationExponent_lt_diagonal hbound hc hσ

/-! ## Generic finite maximal Hankel minors -/

/-- Maximal minor of the finite generic Hankel matrix with rows `0,...,n-1` and
strictly increasing selected columns `c`. -/
def finiteHankelMaximalMinor {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) : MvPolynomial (Fin N) ℤ :=
  Matrix.det fun i j : Fin n =>
    MvPolynomial.X (finiteHankelIndex c hbound i j)

/-- Same finite generic Hankel minor over an arbitrary coefficient ring. -/
def finiteHankelMaximalMinorOver (R : Type*) [CommRing R]
    {N n : ℕ} (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N) :
    MvPolynomial (Fin N) R :=
  Matrix.det fun i j : Fin n =>
    MvPolynomial.X (finiteHankelIndex c hbound i j)

/-- Generic Hankel minors commute with every coefficient base change.  Injectivity, domain,
characteristic, and reducedness are irrelevant because every matrix entry has coefficient one. -/
theorem map_finiteHankelMaximalMinor {R : Type*} [CommRing R]
    (f : ℤ →+* R) {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) :
    MvPolynomial.map f (finiteHankelMaximalMinor c hbound) =
      finiteHankelMaximalMinorOver R c hbound := by
  rw [finiteHankelMaximalMinor, finiteHankelMaximalMinorOver,
    (MvPolynomial.map f).map_det]
  congr 1
  ext i j
  simp

/-- Every Leibniz term is the monomial recording its Hankel anti-diagonal
multiplicities.  Repeated indices are retained as higher exponents. -/
theorem finiteHankel_detTerm_eq_monomial {N n : ℕ} (c : Fin n → ℕ)
    (hbound : ∀ j, n + c j ≤ N) (σ : Equiv.Perm (Fin n)) :
    ((Equiv.Perm.sign σ : ℤ) : MvPolynomial (Fin N) ℤ) *
        ∏ j : Fin n,
          MvPolynomial.X (finiteHankelIndex c hbound (σ j) j) =
      MvPolynomial.monomial (hankelPermutationExponent c hbound σ)
        (Equiv.Perm.sign σ : ℤ) := by
  rw [hankelPermutationExponent]
  let e : Fin n → Fin N →₀ ℕ := fun j =>
    Finsupp.single (finiteHankelIndex c hbound (σ j) j) 1
  have hprod (s : Finset (Fin n)) :
      ∏ j ∈ s, MvPolynomial.monomial (e j) (1 : ℤ) =
        MvPolynomial.monomial (∑ j ∈ s, e j) 1 := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hjs ih =>
        rw [Finset.prod_insert hjs, Finset.sum_insert hjs, ih,
          MvPolynomial.monomial_mul]
        simp
  rw [show (∏ j : Fin n,
      MvPolynomial.X (finiteHankelIndex c hbound (σ j) j)) =
      ∏ j : Fin n, MvPolynomial.monomial (e j) (1 : ℤ) by
        apply Finset.prod_congr rfl
        intro j hj
        simp [e, MvPolynomial.X]]
  rw [hprod Finset.univ]
  change MvPolynomial.C (Equiv.Perm.sign σ : ℤ) *
      MvPolynomial.monomial (∑ j : Fin n, e j) 1 = _
  rw [MvPolynomial.C_mul_monomial]
  simp [e]

theorem finiteHankelMaximalMinor_eq_sum_monomial {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N) :
    finiteHankelMaximalMinor c hbound =
      ∑ σ : Equiv.Perm (Fin n),
        MvPolynomial.monomial (hankelPermutationExponent c hbound σ)
          (Equiv.Perm.sign σ : ℤ) := by
  rw [finiteHankelMaximalMinor, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ hσ
  exact finiteHankel_detTerm_eq_monomial c hbound σ

/-- The lexicographic diagonal monomial occurs with coefficient exactly one. -/
theorem finiteHankelMaximalMinor_coeff_diagonal {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MvPolynomial.coeff (hankelDiagonalExponent c hbound)
      (finiteHankelMaximalMinor c hbound) = 1 := by
  rw [finiteHankelMaximalMinor_eq_sum_monomial,
    MvPolynomial.coeff_sum]
  rw [Finset.sum_eq_single (1 : Equiv.Perm (Fin n))]
  · simp [hankelDiagonalExponent]
  · intro σ hσ hσone
    rw [MvPolynomial.coeff_monomial]
    have hlt := hankelPermutationExponent_lt_diagonal hbound hc hσone
    have hne : hankelPermutationExponent c hbound σ ≠
        hankelDiagonalExponent c hbound := by
      intro heq
      rw [heq] at hlt
      exact (lt_irrefl _) hlt
    simp [hne]
  · simp

theorem finiteHankelMaximalMinorOver_coeff_diagonal
    {R : Type*} [CommRing R] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MvPolynomial.coeff (hankelDiagonalExponent c hbound)
      (finiteHankelMaximalMinorOver R c hbound) = 1 := by
  rw [← map_finiteHankelMaximalMinor (Int.castRingHom R),
    MvPolynomial.coeff_map,
    finiteHankelMaximalMinor_coeff_diagonal c hbound hc, map_one]

/-- No monomial in a maximal Hankel minor exceeds its diagonal monomial in lex order. -/
theorem finiteHankelMaximalMinor_support_le_diagonal {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) {e : Fin N →₀ ℕ}
    (he : e ∈ (finiteHankelMaximalMinor c hbound).support) :
    MonomialOrder.lex.toSyn e ≤
      MonomialOrder.lex.toSyn (hankelDiagonalExponent c hbound) := by
  rw [finiteHankelMaximalMinor_eq_sum_monomial] at he
  have hmem := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun σ : Equiv.Perm (Fin n) =>
      MvPolynomial.monomial (hankelPermutationExponent c hbound σ)
        (Equiv.Perm.sign σ : ℤ)) he
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨σ, hσuniv, heσ⟩ := hmem
  have heq : e = hankelPermutationExponent c hbound σ := by
    exact Finset.mem_singleton.mp
      (MvPolynomial.support_monomial_subset heσ)
  subst e
  by_cases hσ : σ = 1
  · subst σ
    exact le_rfl
  · exact le_of_lt (hankelPermutationExponent_lt_diagonal hbound hc hσ)

/-- The lexicographic degree of a generic maximal Hankel minor is its diagonal exponent. -/
theorem finiteHankelMaximalMinor_degree {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.lex.degree (finiteHankelMaximalMinor c hbound) =
      hankelDiagonalExponent c hbound := by
  apply MonomialOrder.lex.toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro e he
    exact finiteHankelMaximalMinor_support_le_diagonal c hbound hc he
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff,
      finiteHankelMaximalMinor_coeff_diagonal c hbound hc]
    exact one_ne_zero

/-- **Integral diagonal monicity.** Every maximal minor of the finite generic Hankel matrix,
with strictly increasing selected columns, is monic for lex order over `ℤ`.  No field or
reducedness premise enters the statement. -/
theorem finiteHankelMaximalMinor_monic {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.lex.Monic (finiteHankelMaximalMinor c hbound) := by
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
    finiteHankelMaximalMinor_degree c hbound hc,
    finiteHankelMaximalMinor_coeff_diagonal c hbound hc]

theorem finiteHankelMaximalMinor_support_degLex_le_diagonal {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) {e : Fin N →₀ ℕ}
    (he : e ∈ (finiteHankelMaximalMinor c hbound).support) :
    MonomialOrder.degLex.toSyn e ≤
      MonomialOrder.degLex.toSyn (hankelDiagonalExponent c hbound) := by
  rw [finiteHankelMaximalMinor_eq_sum_monomial] at he
  have hmem := MvPolynomial.support_sum (s := Finset.univ)
    (f := fun σ : Equiv.Perm (Fin n) =>
      MvPolynomial.monomial (hankelPermutationExponent c hbound σ)
        (Equiv.Perm.sign σ : ℤ)) he
  rw [Finset.mem_biUnion] at hmem
  obtain ⟨σ, hσuniv, heσ⟩ := hmem
  have heq : e = hankelPermutationExponent c hbound σ := by
    exact Finset.mem_singleton.mp
      (MvPolynomial.support_monomial_subset heσ)
  subst e
  by_cases hσ : σ = 1
  · subst σ
    exact le_rfl
  · exact le_of_lt (hankelPermutationExponent_degLex_lt_diagonal hbound hc hσ)

theorem finiteHankelMaximalMinor_degLex_degree {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.degLex.degree (finiteHankelMaximalMinor c hbound) =
      hankelDiagonalExponent c hbound := by
  apply MonomialOrder.degLex.toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro e he
    exact finiteHankelMaximalMinor_support_degLex_le_diagonal c hbound hc he
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff,
      finiteHankelMaximalMinor_coeff_diagonal c hbound hc]
    exact one_ne_zero

/-- Integral monicity for the exact degree-lex order used in the Hankel Gröbner literature. -/
theorem finiteHankelMaximalMinor_degLex_monic {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.degLex.Monic (finiteHankelMaximalMinor c hbound) := by
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
    finiteHankelMaximalMinor_degLex_degree c hbound hc,
    finiteHankelMaximalMinor_coeff_diagonal c hbound hc]

theorem finiteHankelMaximalMinorOver_support_degLex_le_diagonal
    {R : Type*} [CommRing R] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) {e : Fin N →₀ ℕ}
    (he : e ∈ (finiteHankelMaximalMinorOver R c hbound).support) :
    MonomialOrder.degLex.toSyn e ≤
      MonomialOrder.degLex.toSyn (hankelDiagonalExponent c hbound) := by
  rw [← map_finiteHankelMaximalMinor (Int.castRingHom R)] at he
  have heZ := MvPolynomial.support_map_subset
    (Int.castRingHom R) (finiteHankelMaximalMinor c hbound) he
  exact finiteHankelMaximalMinor_support_degLex_le_diagonal c hbound hc heZ

theorem finiteHankelMaximalMinorOver_degLex_degree
    {R : Type*} [CommRing R] [Nontrivial R] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.degLex.degree (finiteHankelMaximalMinorOver R c hbound) =
      hankelDiagonalExponent c hbound := by
  apply MonomialOrder.degLex.toSyn.injective
  apply le_antisymm
  · rw [MonomialOrder.degree_le_iff]
    intro e he
    exact finiteHankelMaximalMinorOver_support_degLex_le_diagonal c hbound hc he
  · apply MonomialOrder.le_degree
    rw [MvPolynomial.mem_support_iff,
      finiteHankelMaximalMinorOver_coeff_diagonal c hbound hc]
    exact one_ne_zero

/-- Degree-lex monicity survives arbitrary coefficient base change, including passage to rings
with nilpotents and zero divisors. -/
theorem finiteHankelMaximalMinorOver_degLex_monic
    {R : Type*} [CommRing R] {N n : ℕ}
    (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N)
    (hc : StrictMono c) :
    MonomialOrder.degLex.Monic (finiteHankelMaximalMinorOver R c hbound) := by
  nontriviality R
  rw [MonomialOrder.Monic, MonomialOrder.leadingCoeff,
    finiteHankelMaximalMinorOver_degLex_degree c hbound hc,
    finiteHankelMaximalMinorOver_coeff_diagonal c hbound hc]

/-- Finite family of nonzero maximal Hankel minors, indexed without duplicate or unordered
columns.  This is the monic generating family occurring in Conca--Nam's Gröbner theorem. -/
def finiteHankelMaximalMinorSet (N n : ℕ) :
    Set (MvPolynomial (Fin N) ℤ) :=
  {p | ∃ (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N),
    StrictMono c ∧ p = finiteHankelMaximalMinor c hbound}

def finiteHankelMaximalMinorSetOver (R : Type*) [CommRing R]
    (N n : ℕ) : Set (MvPolynomial (Fin N) R) :=
  {p | ∃ (c : Fin n → ℕ) (hbound : ∀ j, n + c j ≤ N),
    StrictMono c ∧ p = finiteHankelMaximalMinorOver R c hbound}

theorem image_finiteHankelMaximalMinorSet
    (R : Type*) [CommRing R] (N n : ℕ) :
    MvPolynomial.map (Int.castRingHom R) ''
        finiteHankelMaximalMinorSet N n =
      finiteHankelMaximalMinorSetOver R N n := by
  ext p
  constructor
  · rintro ⟨q, ⟨c, hbound, hc, rfl⟩, rfl⟩
    exact ⟨c, hbound, hc,
      map_finiteHankelMaximalMinor (Int.castRingHom R) c hbound⟩
  · rintro ⟨c, hbound, hc, rfl⟩
    refine ⟨finiteHankelMaximalMinor c hbound, ⟨c, hbound, hc, rfl⟩, ?_⟩
    exact map_finiteHankelMaximalMinor (Int.castRingHom R) c hbound

/-- Every member of the canonical finite Hankel family is integrally monic. -/
theorem finiteHankelMaximalMinorSet_monic (N n : ℕ) :
    ∀ p ∈ finiteHankelMaximalMinorSet N n, MonomialOrder.lex.Monic p := by
  rintro p ⟨c, hbound, hc, rfl⟩
  exact finiteHankelMaximalMinor_monic c hbound hc

/-- Canonical finite Hankel family is monic for Nam's degree-lex order. -/
theorem finiteHankelMaximalMinorSet_degLex_monic (N n : ℕ) :
    ∀ p ∈ finiteHankelMaximalMinorSet N n,
      MonomialOrder.degLex.Monic p := by
  rintro p ⟨c, hbound, hc, rfl⟩
  exact finiteHankelMaximalMinor_degLex_monic c hbound hc

theorem finiteHankelMaximalMinorSetOver_degLex_monic
    (R : Type*) [CommRing R] (N n : ℕ) :
    ∀ p ∈ finiteHankelMaximalMinorSetOver R N n,
      MonomialOrder.degLex.Monic p := by
  rintro p ⟨c, hbound, hc, rfl⟩
  exact finiteHankelMaximalMinorOver_degLex_monic c hbound hc


end
end RHTower
