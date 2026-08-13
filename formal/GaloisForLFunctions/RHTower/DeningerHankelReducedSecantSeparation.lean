import GaloisForLFunctions.RHTower.DeningerHankelChainSecant
import GaloisForLFunctions.RHTower.DeningerHankelSecantParameterization
import Mathlib.RingTheory.MvPolynomial.MonomialOrder
import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Reduced higher-rank Hankel secant separation

This module proves the algebraic half of the Conca--Nam Hankel secant theorem without field,
domain, characteristic, or reducedness assumptions. A chain-reduced exponent decomposes into
adjacent color parts. Each part is lexicographically minimal at fixed mass and first moment, so
the canonical colored allocation is the unique fiber over its ordered-atom exponent. Its
coefficient is exactly one by a coordinate retraction. Consequently every nonzero polynomial
supported on reduced exponents has nonzero ordered-atom image over every commutative semiring.
-/

namespace RHTower

noncomputable section
open scoped MonomialOrder BigOperators

def hankelNatWeight (e : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ e.support, i * e i

def hankelNatTailMass (q : ℕ) (e : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ e.support with q < i, e i

def hankelNatTailWeight (q : ℕ) (e : ℕ →₀ ℕ) : ℕ :=
  ∑ i ∈ e.support with q < i, i * e i

theorem finsupp_degree_eq_value_add_tailMass {e : ℕ →₀ ℕ} {q : ℕ}
    (hbelow : ∀ i < q, e i = 0) :
    Finsupp.degree e = e q + hankelNatTailMass q e := by
  change (∑ i ∈ e.support, e i) = _
  rw [← Finset.sum_filter_add_sum_filter_not e.support (fun i => q < i)]
  rw [add_comm]
  congr 1
  apply Finset.sum_eq_single q
  · intro i hi hine
    simp only [Finset.mem_filter] at hi
    exact hbelow i (lt_of_le_of_ne (Nat.le_of_not_gt hi.2) hine)
  · intro hq
    exact Finsupp.notMem_support_iff.mp (fun hmem => hq (Finset.mem_filter.mpr ⟨hmem, by simp⟩))

theorem hankelNatWeight_eq_value_add_tailWeight {e : ℕ →₀ ℕ} {q : ℕ}
    (hbelow : ∀ i < q, e i = 0) :
    hankelNatWeight e = q * e q + hankelNatTailWeight q e := by
  rw [hankelNatWeight, hankelNatTailWeight,
    ← Finset.sum_filter_add_sum_filter_not e.support (fun i => q < i)]
  rw [add_comm]
  congr 1
  apply Finset.sum_eq_single q
  · intro i hi hine
    simp only [Finset.mem_filter] at hi
    rw [hbelow i (lt_of_le_of_ne (Nat.le_of_not_gt hi.2) hine), mul_zero]
  · intro hq
    rw [Finsupp.notMem_support_iff.mp
      (fun hmem => hq (Finset.mem_filter.mpr ⟨hmem, by simp⟩)), mul_zero]

theorem tailMass_mul_succ_le_tailWeight (q : ℕ) (e : ℕ →₀ ℕ) :
    (q + 1) * hankelNatTailMass q e ≤ hankelNatTailWeight q e := by
  rw [hankelNatTailMass, hankelNatTailWeight, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  exact Nat.mul_le_mul_right (e i) (by
    have := (Finset.mem_filter.mp hi).2
    omega)

theorem tailMass_eq_value_add_farMass (q : ℕ) (e : ℕ →₀ ℕ) :
    hankelNatTailMass q e = e (q + 1) + hankelNatTailMass (q + 1) e := by
  rw [hankelNatTailMass, hankelNatTailMass]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (e.support.filter (fun i => q < i)) (fun i => q + 1 < i) (fun i => e i)
  rw [Finset.filter_filter] at hsplit
  have hfilter :
      e.support.filter (fun i => q < i ∧ q + 1 < i) =
        e.support.filter (fun i => q + 1 < i) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hqi, hqi'⟩
      exact ⟨hi, hqi'⟩
    · rintro ⟨hi, hqi⟩
      exact ⟨hi, by omega, hqi⟩
  rw [hfilter] at hsplit
  have hnear :
      (∑ i ∈ e.support.filter (fun i => q < i) with ¬q + 1 < i, e i) = e (q + 1) := by
    apply Finset.sum_eq_single (q + 1)
    · intro i hi hine
      simp only [Finset.mem_filter] at hi
      omega
    · intro hq
      exact Finsupp.notMem_support_iff.mp (fun hmem => hq
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, by omega⟩, by omega⟩))
  omega

theorem tailWeight_eq_value_add_farWeight (q : ℕ) (e : ℕ →₀ ℕ) :
    hankelNatTailWeight q e =
      (q + 1) * e (q + 1) + hankelNatTailWeight (q + 1) e := by
  rw [hankelNatTailWeight, hankelNatTailWeight]
  have hsplit := Finset.sum_filter_add_sum_filter_not
    (e.support.filter (fun i => q < i)) (fun i => q + 1 < i) (fun i => i * e i)
  rw [Finset.filter_filter] at hsplit
  have hfilter :
      e.support.filter (fun i => q < i ∧ q + 1 < i) =
        e.support.filter (fun i => q + 1 < i) := by
    ext i
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hi, hqi, hqi'⟩
      exact ⟨hi, hqi'⟩
    · rintro ⟨hi, hqi⟩
      exact ⟨hi, by omega, hqi⟩
  rw [hfilter] at hsplit
  have hnear :
      (∑ i ∈ e.support.filter (fun i => q < i) with ¬q + 1 < i, i * e i) =
        (q + 1) * e (q + 1) := by
    apply Finset.sum_eq_single (q + 1)
    · intro i hi hine
      simp only [Finset.mem_filter] at hi
      omega
    · intro hq
      rw [Finsupp.notMem_support_iff.mp (fun hmem => hq
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hmem, by omega⟩, by omega⟩)), mul_zero]
  omega

theorem tailWeight_strict_of_value_lt_mass
    (q : ℕ) (e : ℕ →₀ ℕ)
    (hvalue : e (q + 1) < hankelNatTailMass q e) :
    (q + 1) * hankelNatTailMass q e < hankelNatTailWeight q e := by
  have hmass := tailMass_eq_value_add_farMass q e
  have hweight := tailWeight_eq_value_add_farWeight q e
  have hfar := tailMass_mul_succ_le_tailWeight (q + 1) e
  have hfarpos : 0 < hankelNatTailMass (q + 1) e := by omega
  calc
    (q + 1) * hankelNatTailMass q e =
        (q + 1) * e (q + 1) + (q + 1) * hankelNatTailMass (q + 1) e := by
      rw [hmass, Nat.mul_add]
    _ < (q + 1) * e (q + 1) + (q + 2) * hankelNatTailMass (q + 1) e := by
      exact Nat.add_lt_add_left
        (Nat.mul_lt_mul_of_pos_right (by omega) hfarpos) _
    _ ≤ (q + 1) * e (q + 1) + hankelNatTailWeight (q + 1) e := by
      exact Nat.add_le_add_left hfar _
    _ = hankelNatTailWeight q e := hweight.symm

theorem tailMass_eq_of_adjacentSupport {e : ℕ →₀ ℕ} {q : ℕ}
    (he : ∀ i, e i ≠ 0 → i = q ∨ i = q + 1) :
    hankelNatTailMass q e = e (q + 1) := by
  rw [hankelNatTailMass]
  apply Finset.sum_eq_single (q + 1)
  · intro i hi hine
    simp only [Finset.mem_filter] at hi
    rcases he i (Finsupp.mem_support_iff.mp hi.1) with h | h
    · omega
    · exact (hine h).elim
  · intro hq
    exact Finsupp.notMem_support_iff.mp (fun hmem => hq
      (Finset.mem_filter.mpr ⟨hmem, by omega⟩))

theorem tailWeight_eq_of_adjacentSupport {e : ℕ →₀ ℕ} {q : ℕ}
    (he : ∀ i, e i ≠ 0 → i = q ∨ i = q + 1) :
    hankelNatTailWeight q e = (q + 1) * e (q + 1) := by
  rw [hankelNatTailWeight]
  apply Finset.sum_eq_single (q + 1)
  · intro i hi hine
    simp only [Finset.mem_filter] at hi
    rcases he i (Finsupp.mem_support_iff.mp hi.1) with h | h
    · omega
    · exact (hine h).elim
  · intro hq
    rw [Finsupp.notMem_support_iff.mp (fun hmem => hq
      (Finset.mem_filter.mpr ⟨hmem, by omega⟩)), mul_zero]

/-- An exponent supported on two adjacent indices is lexicographically minimal among all
exponents with the same total degree and first moment. -/
theorem hankelAdjacentExponent_lex_le
    {e f : ℕ →₀ ℕ} {q : ℕ}
    (he : ∀ i, e i ≠ 0 → i = q ∨ i = q + 1)
    (hdegree : Finsupp.degree e = Finsupp.degree f)
    (hweight : hankelNatWeight e = hankelNatWeight f) :
    toLex e ≤ toLex f := by
  by_contra hnot
  have hlt : toLex f < toLex e := lt_of_not_ge hnot
  obtain ⟨d, hbefore, hd⟩ := Finsupp.Lex.lt_iff.mp hlt
  have hbefore' : ∀ j < d, f j = e j := by
    intro j hj
    simpa using hbefore j hj
  have hd' : f d < e d := by simpa using hd
  have hed : e d ≠ 0 := by omega
  rcases he d hed with hdq | hdq
  · subst d
    have hfbelow : ∀ i < q, f i = 0 := by
      intro i hi
      rw [hbefore' i hi]
      by_contra hei
      rcases he i hei with h | h <;> omega
    have hebelow : ∀ i < q, e i = 0 := by
      intro i hi
      by_contra hei
      rcases he i hei with h | h <;> omega
    have hedeg := finsupp_degree_eq_value_add_tailMass hebelow
    have hfdeg := finsupp_degree_eq_value_add_tailMass hfbelow
    have heweight := hankelNatWeight_eq_value_add_tailWeight hebelow
    have hfweight := hankelNatWeight_eq_value_add_tailWeight hfbelow
    have hetailMass := tailMass_eq_of_adjacentSupport he
    have hetailWeight := tailWeight_eq_of_adjacentSupport he
    have hmassgt : e (q + 1) < hankelNatTailMass q f := by omega
    have htail := tailMass_mul_succ_le_tailWeight q f
    have hmul := congrArg (fun n : ℕ => q * n) hdegree
    rw [hedeg, hfdeg, Nat.mul_add, Nat.mul_add] at hmul
    rw [hetailMass] at hmul
    rw [heweight, hfweight, hetailWeight] at hweight
    rw [Nat.add_mul, one_mul] at hweight htail
    omega
  · have hdq' : d = q + 1 := hdq
    have hfbelow : ∀ i < q, f i = 0 := by
      intro i hi
      rw [hbefore' i (by omega)]
      by_contra hei
      rcases he i hei with h | h <;> omega
    have hebelow : ∀ i < q, e i = 0 := by
      intro i hi
      by_contra hei
      rcases he i hei with h | h <;> omega
    have hfq : f q = e q := hbefore' q (by omega)
    have hedeg := finsupp_degree_eq_value_add_tailMass hebelow
    have hfdeg := finsupp_degree_eq_value_add_tailMass hfbelow
    have heweight := hankelNatWeight_eq_value_add_tailWeight hebelow
    have hfweight := hankelNatWeight_eq_value_add_tailWeight hfbelow
    have hetailMass := tailMass_eq_of_adjacentSupport he
    have hetailWeight := tailWeight_eq_of_adjacentSupport he
    have hmassEq : hankelNatTailMass q f = e (q + 1) := by omega
    have hdqvalue : f (q + 1) < e (q + 1) := by simpa [hdq'] using hd'
    have hstrict := tailWeight_strict_of_value_lt_mass q f (by omega)
    rw [heweight, hfweight, hetailWeight] at hweight
    rw [hfq] at hweight
    rw [hmassEq] at hstrict
    omega

theorem finsupp_toLex_add_le_add_left {a b : ℕ →₀ ℕ}
    (h : toLex a ≤ toLex b) (c : ℕ →₀ ℕ) :
    toLex (c + a) ≤ toLex (c + b) := by
  rcases h.eq_or_lt with hab | hab
  · have hab' : a = b := by
      simpa using congrArg ofLex hab
    exact le_of_eq (congrArg toLex (congrArg (c + ·) hab'))
  · apply le_of_lt
    rw [Finsupp.Lex.lt_iff] at hab ⊢
    obtain ⟨d, hbefore, hd⟩ := hab
    refine ⟨d, ?_, ?_⟩
    · intro j hj
      simpa using congrArg (fun n : ℕ => c j + n) (hbefore j hj)
    · simpa using Nat.add_lt_add_left hd (c d)

theorem finsupp_toLex_sum_le_sum {ι : Type*} [Fintype ι]
    (a b : ι → ℕ →₀ ℕ) (h : ∀ i, toLex (a i) ≤ toLex (b i)) :
    toLex (∑ i, a i) ≤ toLex (∑ i, b i) := by
  classical
  have aux : ∀ s : Finset ι,
      toLex (∑ i ∈ s, a i) ≤ toLex (∑ i ∈ s, b i) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert i s his ih =>
        rw [Finset.sum_insert his, Finset.sum_insert his]
        calc
          toLex (a i + ∑ j ∈ s, a j) =
              toLex ((∑ j ∈ s, a j) + a i) := by rw [add_comm]
          _ ≤ toLex ((∑ j ∈ s, a j) + b i) :=
            finsupp_toLex_add_le_add_left (h i) _
          _ = toLex (b i + ∑ j ∈ s, a j) := by rw [add_comm]
          _ ≤ toLex (b i + ∑ j ∈ s, b j) :=
            finsupp_toLex_add_le_add_left ih _
  simpa using aux Finset.univ

/-- Decomposition of an exponent into adjacent-support color parts. -/
structure HankelAdjacentDecomposition (r : ℕ) (e : ℕ →₀ ℕ) where
  part : Fin r → ℕ →₀ ℕ
  sum_part : ∑ j, part j = e
  supported_adjacent : ∀ j, ∃ q, ∀ i, part j i ≠ 0 → i = q ∨ i = q + 1

/-- Multiplicity part assigned to one color of a proper coloring of exponent support. -/
noncomputable def hankelColorPart {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (j : Fin r) : ℕ →₀ ℕ :=
  e.filter fun i => ∃ hi : i ∈ e.support, C ⟨i, hi⟩ = j

theorem hankelColorPart_apply_of_mem {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (j : Fin r) {i : ℕ} (hi : i ∈ e.support) :
    hankelColorPart e C j i = if C ⟨i, hi⟩ = j then e i else 0 := by
  rw [hankelColorPart, Finsupp.filter_apply]
  congr 1
  apply propext
  constructor
  · rintro ⟨hi', hcolor⟩
    simpa using hcolor
  · intro hcolor
    exact ⟨hi, hcolor⟩

theorem hankelColorPart_nonzero {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (j : Fin r) {i : ℕ} (hi : hankelColorPart e C j i ≠ 0) :
    ∃ his : i ∈ e.support, C ⟨i, his⟩ = j := by
  rw [hankelColorPart, Finsupp.filter_apply] at hi
  split at hi
  · assumption
  · simp at hi

theorem sum_hankelColorPart {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r)) :
    ∑ j, hankelColorPart e C j = e := by
  classical
  ext i
  by_cases hi : e i = 0
  · simp [hankelColorPart, hi]
  · have his : i ∈ e.support := Finsupp.mem_support_iff.mpr hi
    rw [Finsupp.finsetSum_apply]
    simp_rw [hankelColorPart_apply_of_mem e C _ his]
    simp

theorem hankelColorPart_supported_adjacent {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (j : Fin r) :
    ∃ q, ∀ i, hankelColorPart e C j i ≠ 0 → i = q ∨ i = q + 1 := by
  classical
  by_cases hne : (hankelColorPart e C j).support.Nonempty
  · let q := (hankelColorPart e C j).support.min' hne
    refine ⟨q, ?_⟩
    intro i hi
    have his : i ∈ (hankelColorPart e C j).support :=
      Finsupp.mem_support_iff.mpr hi
    have hqs : q ∈ (hankelColorPart e C j).support :=
      Finset.min'_mem _ hne
    have hqi : q ≤ i := Finset.min'_le _ _ his
    have hipred : ∃ hip : i ∈ e.support, C ⟨i, hip⟩ = j :=
      hankelColorPart_nonzero e C j hi
    have hqpred : ∃ hqp : q ∈ e.support, C ⟨q, hqp⟩ = j := by
      have hqne : hankelColorPart e C j q ≠ 0 :=
        Finsupp.mem_support_iff.mp hqs
      exact hankelColorPart_nonzero e C j hqne
    obtain ⟨hip, hipcolor⟩ := hipred
    obtain ⟨hqp, hqpcolor⟩ := hqpred
    have hnotadj : ¬hankelChainGraph.Adj q i := by
      intro hadj
      have hinduced :
          (hankelChainGraph.induce (e.support : Set ℕ)).Adj ⟨q, hqp⟩ ⟨i, hip⟩ := hadj
      exact C.valid hinduced (hqpcolor.trans hipcolor.symm)
    change ¬(q + 1 < i ∨ i + 1 < q) at hnotadj
    omega
  · refine ⟨0, ?_⟩
    intro i hi
    exact (hne ⟨i, Finsupp.mem_support_iff.mpr hi⟩).elim

/-- Adjacent-support decomposition furnished by a proper coloring. -/
noncomputable def hankelAdjacentDecompositionOfColoring {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r)) :
    HankelAdjacentDecomposition r e :=
  { part := hankelColorPart e C
    sum_part := sum_hankelColorPart e C
    supported_adjacent := hankelColorPart_supported_adjacent e C }

/-- Every reduced Hankel-chain exponent has an adjacent-support decomposition into `r` parts. -/
noncomputable def hankelAdjacentDecompositionOfReduced {r : ℕ} {e : ℕ →₀ ℕ}
    (hred : HankelChainReduced r e) : HankelAdjacentDecomposition r e :=
  hankelAdjacentDecompositionOfColoring e
    ((hankelChainReduced_iff_colorable r e).mp hred).some

/-- Collision extremality: preserving degree and first moment color by color can only move an
adjacent decomposition lexicographically upward. -/
theorem HankelAdjacentDecomposition.lex_le_of_color_invariants
    {r : ℕ} {e f : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e)
    (b : Fin r → ℕ →₀ ℕ)
    (hdegree : ∀ j, Finsupp.degree (D.part j) = Finsupp.degree (b j))
    (hweight : ∀ j, hankelNatWeight (D.part j) = hankelNatWeight (b j))
    (hsum : ∑ j, b j = f) :
    toLex e ≤ toLex f := by
  rw [← D.sum_part, ← hsum]
  apply finsupp_toLex_sum_le_sum
  intro j
  obtain ⟨q, hq⟩ := D.supported_adjacent j
  exact hankelAdjacentExponent_lex_le hq (hdegree j) (hweight j)

/-! ## Color expansion and exact row grading -/

open MvPolynomial

/-- Variables separating every source row and atomic color before moment collapse. -/
abbrev HankelColorExpansionIndex (r : ℕ) := Fin r × ℕ

/-- Universal color expansion of one source variable. -/
def hankelColorExpansionMoment
    (R : Type*) [CommSemiring R] (r i : ℕ) :
    MvPolynomial (HankelColorExpansionIndex r) R :=
  ∑ j : Fin r, X (j, i)

/-- Expands `X_i` as the sum of its `r` independently colored copies. -/
def hankelColorExpansion
    (R : Type*) [CommSemiring R] (r : ℕ) :
    MvPolynomial ℕ R →+* MvPolynomial (HankelColorExpansionIndex r) R :=
  MvPolynomial.eval₂Hom MvPolynomial.C (hankelColorExpansionMoment R r)

@[simp] theorem hankelColorExpansion_X
    (R : Type*) [CommSemiring R] (r i : ℕ) :
    hankelColorExpansion R r (X i) = hankelColorExpansionMoment R r i := by
  simp [hankelColorExpansion]

/-- Multigrading retaining, for each source row, total multiplicity across all colors. -/
def hankelColorRowWeight {r : ℕ} :
    HankelColorExpansionIndex r → ℕ →₀ ℕ :=
  fun p => Finsupp.single p.2 1

theorem hankelColorExpansionMoment_isWeightedHomogeneous
    (R : Type*) [CommSemiring R] (r i : ℕ) :
    (hankelColorExpansionMoment R r i).IsWeightedHomogeneous
      hankelColorRowWeight (Finsupp.single i 1) := by
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ _ _
  intro j hj
  simpa [hankelColorRowWeight] using
    (MvPolynomial.isWeightedHomogeneous_X R hankelColorRowWeight (j, i))

theorem hankelColorExpansion_monomial_isWeightedHomogeneous
    (R : Type*) [CommSemiring R] (r : ℕ) (e : ℕ →₀ ℕ) (a : R) :
    (hankelColorExpansion R r (MvPolynomial.monomial e a)).IsWeightedHomogeneous
      hankelColorRowWeight e := by
  rw [hankelColorExpansion, MvPolynomial.eval₂Hom_monomial]
  have hprod :
      (e.prod fun i n => (hankelColorExpansionMoment R r i) ^ n).IsWeightedHomogeneous
        hankelColorRowWeight
        (∑ i ∈ e.support, e i • Finsupp.single i 1) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod e.support _ _
    intro i hi
    exact (hankelColorExpansionMoment_isWeightedHomogeneous R r i).pow (e i)
  have hdegree : (∑ i ∈ e.support, e i • Finsupp.single i 1) = e := by
    simpa [Finsupp.sum, nsmul_eq_mul, mul_comm] using e.sum_single
  rw [hdegree] at hprod
  exact hprod.C_mul a

/-- Every monomial occurring in a color expansion has exactly the source row multiplicities. -/
theorem hankelColorExpansion_monomial_support_rowWeight
    (R : Type*) [CommSemiring R] (r : ℕ) {e : ℕ →₀ ℕ} {a : R}
    {g : HankelColorExpansionIndex r →₀ ℕ}
    (hg : g ∈ (hankelColorExpansion R r (MvPolynomial.monomial e a)).support) :
    Finsupp.weight hankelColorRowWeight g = e := by
  by_contra hne
  have hz := (hankelColorExpansion_monomial_isWeightedHomogeneous R r e a).coeff_eq_zero g hne
  exact Finsupp.mem_support_iff.mp hg hz

/-- Color part of an allocation exponent. -/
def hankelAllocationColorPart {r : ℕ}
    (g : HankelColorExpansionIndex r →₀ ℕ) (j : Fin r) : ℕ →₀ ℕ :=
  g.curry j

@[simp] theorem hankelAllocationColorPart_apply {r : ℕ}
    (g : HankelColorExpansionIndex r →₀ ℕ) (j : Fin r) (i : ℕ) :
    hankelAllocationColorPart g j i = g (j, i) := rfl

theorem weight_hankelColorRowWeight_apply {r : ℕ}
    (g : HankelColorExpansionIndex r →₀ ℕ) (i : ℕ) :
    Finsupp.weight hankelColorRowWeight g i =
      ∑ j : Fin r, hankelAllocationColorPart g j i := by
  classical
  rw [Finsupp.weight_apply]
  calc
    (g.sum fun p c => c • hankelColorRowWeight p) i =
        g.sum (fun p c => if i = p.2 then c else 0) := by
      rw [Finsupp.sum_apply]
      apply Finsupp.sum_congr
      intro p hp
      simp [hankelColorRowWeight, Finsupp.single_apply, eq_comm]
    _ = g.curry.sum (fun j part =>
        part.sum (fun k c => if i = k then c else 0)) := by
      exact (Finsupp.sum_curry_index g
        (fun _ k c => if i = k then c else 0)).symm
    _ = g.curry.sum (fun _ part => part i) := by
      apply Finsupp.sum_congr
      intro j hj
      exact Finsupp.sum_ite_self_eq (g.curry j) i
    _ = ∑ j : Fin r, hankelAllocationColorPart g j i := by
      rw [Finsupp.sum_fintype]
      · rfl
      · intro j
        rfl

theorem sum_hankelAllocationColorPart_eq_of_rowWeight {r : ℕ}
    {g : HankelColorExpansionIndex r →₀ ℕ} {e : ℕ →₀ ℕ}
    (hg : Finsupp.weight hankelColorRowWeight g = e) :
    ∑ j, hankelAllocationColorPart g j = e := by
  ext i
  rw [Finsupp.finsetSum_apply, ← weight_hankelColorRowWeight_apply, hg]

/-- Exponent collapse from row-separated colors to amplitude/node exponents. -/
def hankelColorCollapseExponentHom (r : ℕ) :
    (HankelColorExpansionIndex r →₀ ℕ) →+ (Fin r × Fin 2 →₀ ℕ) :=
  (Finsupp.linearCombination ℕ fun p : HankelColorExpansionIndex r =>
    Finsupp.single (p.1, (0 : Fin 2)) 1 +
      Finsupp.single (p.1, (1 : Fin 2)) p.2).toAddMonoidHom

/-- Monoid-algebra collapse of separated color variables to amplitude/node variables. -/
def hankelColorCollapse
    (R : Type*) [CommSemiring R] (r : ℕ) :
    MvPolynomial (HankelColorExpansionIndex r) R →+*
      MvPolynomial (Fin r × Fin 2) R :=
  AddMonoidAlgebra.mapDomainRingHom R (hankelColorCollapseExponentHom r)

@[simp] theorem hankelColorCollapse_C
    (R : Type*) [CommSemiring R] (r : ℕ) (a : R) :
    hankelColorCollapse R r (MvPolynomial.C a) = MvPolynomial.C a := by
  rw [hankelColorCollapse, AddMonoidAlgebra.mapDomainRingHom_apply]
  change AddMonoidAlgebra.mapDomain (hankelColorCollapseExponentHom r)
    (AddMonoidAlgebra.single 0 a) = AddMonoidAlgebra.single 0 a
  rw [AddMonoidAlgebra.mapDomain_single, map_zero]

theorem hankelColorCollapseExponentHom_amplitude
    {r : ℕ} (g : HankelColorExpansionIndex r →₀ ℕ) (j : Fin r) :
    hankelColorCollapseExponentHom r g (j, (0 : Fin 2)) =
      Finsupp.degree (hankelAllocationColorPart g j) := by
  classical
  change ((Finsupp.linearCombination ℕ (fun p : HankelColorExpansionIndex r =>
    Finsupp.single (p.1, (0 : Fin 2)) 1 +
      Finsupp.single (p.1, (1 : Fin 2)) p.2) g : Fin r × Fin 2 →₀ ℕ)
        (j, (0 : Fin 2))) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  have hleft :
      g.sum (fun p c => (c •
        (Finsupp.single (p.1, (0 : Fin 2)) 1 +
          Finsupp.single (p.1, (1 : Fin 2)) p.2 : Fin r × Fin 2 →₀ ℕ))
            (j, (0 : Fin 2))) =
        g.sum (fun p c => if p.1 = j then c else 0) := by
    apply Finsupp.sum_congr
    intro p hp
    simp [Finsupp.single_apply, eq_comm]
  rw [hleft]
  rw [← Finsupp.sum_curry_index g
    (fun k _ c => if k = j then c else 0)]
  have houter :
      g.curry.sum (fun k part =>
        part.sum (fun _ c => if k = j then c else 0)) =
      g.curry.sum (fun k part =>
        if k = j then Finsupp.degree part else 0) := by
    apply Finsupp.sum_congr
    intro k hk
    by_cases hkj : k = j
    · subst k
      simp [Finsupp.degree, Finsupp.sum]
    · simp [hkj]
  rw [houter]
  rw [Finsupp.sum_ite_eq']
  change (if j ∈ g.curry.support then Finsupp.degree (g.curry j) else 0) =
    Finsupp.degree (g.curry j)
  by_cases hj : j ∈ g.curry.support
  · rw [if_pos hj]
  · rw [if_neg hj, Finsupp.notMem_support_iff.mp hj]
    rfl

theorem hankelColorCollapseExponentHom_node
    {r : ℕ} (g : HankelColorExpansionIndex r →₀ ℕ) (j : Fin r) :
    hankelColorCollapseExponentHom r g (j, (1 : Fin 2)) =
      hankelNatWeight (hankelAllocationColorPart g j) := by
  classical
  change ((Finsupp.linearCombination ℕ (fun p : HankelColorExpansionIndex r =>
    Finsupp.single (p.1, (0 : Fin 2)) 1 +
      Finsupp.single (p.1, (1 : Fin 2)) p.2) g : Fin r × Fin 2 →₀ ℕ)
        (j, (1 : Fin 2))) = _
  rw [Finsupp.linearCombination_apply, Finsupp.sum_apply]
  have hleft :
      g.sum (fun p c => (c •
        (Finsupp.single (p.1, (0 : Fin 2)) 1 +
          Finsupp.single (p.1, (1 : Fin 2)) p.2 : Fin r × Fin 2 →₀ ℕ))
            (j, (1 : Fin 2))) =
        g.sum (fun p c => if p.1 = j then p.2 * c else 0) := by
    apply Finsupp.sum_congr
    intro p hp
    by_cases hpj : p.1 = j
    · simp [hpj, mul_comm]
    · simp [hpj, Ne.symm hpj]
  rw [hleft]
  rw [← Finsupp.sum_curry_index g
    (fun k i c => if k = j then i * c else 0)]
  have houter :
      g.curry.sum (fun k part =>
        part.sum (fun i c => if k = j then i * c else 0)) =
      g.curry.sum (fun k part =>
        if k = j then hankelNatWeight part else 0) := by
    apply Finsupp.sum_congr
    intro k hk
    by_cases hkj : k = j
    · subst k
      simp [hankelNatWeight, Finsupp.sum]
    · simp [hkj]
  rw [houter]
  rw [Finsupp.sum_ite_eq']
  change (if j ∈ g.curry.support then hankelNatWeight (g.curry j) else 0) =
    hankelNatWeight (g.curry j)
  by_cases hj : j ∈ g.curry.support
  · rw [if_pos hj]
  · rw [if_neg hj, Finsupp.notMem_support_iff.mp hj]
    rfl

/-- Canonical allocation attached to an adjacent decomposition. -/
noncomputable def HankelAdjacentDecomposition.allocation
    {r : ℕ} {e : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e) :
    HankelColorExpansionIndex r →₀ ℕ :=
  (Finsupp.equivFunOnFinite.symm D.part).uncurry

@[simp] theorem HankelAdjacentDecomposition.allocation_apply
    {r : ℕ} {e : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e)
    (j : Fin r) (i : ℕ) :
    D.allocation (j, i) = D.part j i := rfl

@[simp] theorem HankelAdjacentDecomposition.allocation_colorPart
    {r : ℕ} {e : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e)
    (j : Fin r) :
    hankelAllocationColorPart D.allocation j = D.part j := by
  ext i
  rfl

theorem HankelAdjacentDecomposition.allocation_rowWeight
    {r : ℕ} {e : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e) :
    Finsupp.weight hankelColorRowWeight D.allocation = e := by
  ext i
  rw [weight_hankelColorRowWeight_apply]
  simpa only [D.allocation_colorPart, Finsupp.finsetSum_apply] using
    congrArg (fun f : ℕ →₀ ℕ => f i) D.sum_part

theorem hankelAllocation_eq_of_sum_eq_of_lex_le
    {r : ℕ} (a b : Fin r → ℕ →₀ ℕ)
    (hle : ∀ j, toLex (a j) ≤ toLex (b j))
    (hsum : ∑ j, a j = ∑ j, b j) :
    a = b := by
  funext j
  by_contra hne
  have hjlt : toLex (a j) < toLex (b j) := by
    exact lt_of_le_of_ne (hle j) (fun h => hne (by
      simpa using congrArg ofLex h))
  have hlt : (∑ k : Fin r, toLex (a k)) < ∑ k : Fin r, toLex (b k) := by
    apply Finset.sum_lt_sum
    · intro k hk
      exact hle k
    · exact ⟨j, Finset.mem_univ j, hjlt⟩
  have heq : (∑ k : Fin r, toLex (a k)) = ∑ k : Fin r, toLex (b k) := by
    let L : (ℕ →₀ ℕ) →+ Lex (ℕ →₀ ℕ) :=
      { toFun := toLex
        map_zero' := rfl
        map_add' := toLex_add }
    have h := congrArg L hsum
    rw [map_sum, map_sum] at h
    change (∑ k : Fin r, L (a k)) = ∑ k : Fin r, L (b k)
    exact h
  exact (ne_of_lt hlt) heq

/-- Exact collision rigidity for the collapse exponent: a canonical adjacent allocation is the
only allocation with the same row multidegree and the same collapsed amplitude/node exponent. -/
theorem HankelAdjacentDecomposition.allocation_eq_of_rowWeight_of_collapse
    {r : ℕ} {e : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e)
    {g : HankelColorExpansionIndex r →₀ ℕ}
    (hrow : Finsupp.weight hankelColorRowWeight g = e)
    (hcollapse : hankelColorCollapseExponentHom r g =
      hankelColorCollapseExponentHom r D.allocation) :
    g = D.allocation := by
  have hdegree : ∀ j,
      Finsupp.degree (D.part j) =
        Finsupp.degree (hankelAllocationColorPart g j) := by
    intro j
    have h := congrArg (fun d : Fin r × Fin 2 →₀ ℕ => d (j, (0 : Fin 2))) hcollapse
    simpa [hankelColorCollapseExponentHom_amplitude] using h.symm
  have hweight : ∀ j,
      hankelNatWeight (D.part j) =
        hankelNatWeight (hankelAllocationColorPart g j) := by
    intro j
    have h := congrArg (fun d : Fin r × Fin 2 →₀ ℕ => d (j, (1 : Fin 2))) hcollapse
    simpa [hankelColorCollapseExponentHom_node] using h.symm
  have hle : ∀ j, toLex (D.part j) ≤
      toLex (hankelAllocationColorPart g j) := by
    intro j
    obtain ⟨q, hq⟩ := D.supported_adjacent j
    exact hankelAdjacentExponent_lex_le hq (hdegree j) (hweight j)
  have hsumg : ∑ j, hankelAllocationColorPart g j = e :=
    sum_hankelAllocationColorPart_eq_of_rowWeight hrow
  have hparts : (fun j => hankelAllocationColorPart g j) = D.part := by
    symm
    apply hankelAllocation_eq_of_sum_eq_of_lex_le D.part
      (fun j => hankelAllocationColorPart g j) hle
    rw [D.sum_part, hsumg]
  apply Finsupp.curryEquiv.injective
  change g.curry = D.allocation.curry
  ext j i
  have hj := congrFun hparts j
  change hankelAllocationColorPart g j i = D.part j i
  exact congrArg (fun f : ℕ →₀ ℕ => f i) hj

/-- A collapse collision above an adjacent decomposition forces the source row exponent to be
lexicographically no smaller than the decomposed exponent. -/
theorem HankelAdjacentDecomposition.lex_le_of_rowWeight_of_collapse
    {r : ℕ} {e f : ℕ →₀ ℕ} (D : HankelAdjacentDecomposition r e)
    {g : HankelColorExpansionIndex r →₀ ℕ}
    (hrow : Finsupp.weight hankelColorRowWeight g = f)
    (hcollapse : hankelColorCollapseExponentHom r g =
      hankelColorCollapseExponentHom r D.allocation) :
    toLex e ≤ toLex f := by
  apply D.lex_le_of_color_invariants (fun j => hankelAllocationColorPart g j)
  · intro j
    have h := congrArg (fun d : Fin r × Fin 2 →₀ ℕ => d (j, (0 : Fin 2))) hcollapse
    simpa [hankelColorCollapseExponentHom_amplitude] using h.symm
  · intro j
    have h := congrArg (fun d : Fin r × Fin 2 →₀ ℕ => d (j, (1 : Fin 2))) hcollapse
    simpa [hankelColorCollapseExponentHom_node] using h.symm
  · exact sum_hankelAllocationColorPart_eq_of_rowWeight hrow

/-! ## Unit coefficient of a concentrated allocation -/

/-- Embedding selecting one color variable in each source row. -/
def hankelSelectedColorEmbedding {r : ℕ} (s : ℕ → Fin r) :
    ℕ ↪ HankelColorExpansionIndex r where
  toFun i := (s i, i)
  inj' := by
    intro i k h
    exact congrArg Prod.snd h

@[simp] theorem hankelSelectedColorEmbedding_apply {r : ℕ}
    (s : ℕ → Fin r) (i : ℕ) :
    hankelSelectedColorEmbedding s i = (s i, i) := rfl

theorem killCompl_hankelColorExpansion
    (R : Type*) [CommSemiring R] {r : ℕ} (s : ℕ → Fin r)
    (P : MvPolynomial ℕ R) :
    MvPolynomial.killCompl (hankelSelectedColorEmbedding s).injective
      (hankelColorExpansion R r P) = P := by
  classical
  let lhs : MvPolynomial ℕ R →+* MvPolynomial ℕ R :=
    (MvPolynomial.killCompl
      (hankelSelectedColorEmbedding s).injective).toRingHom.comp
        (hankelColorExpansion R r)
  have hlhs : lhs = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [lhs, hankelColorExpansion]
    · intro i
      simp only [lhs, RingHom.comp_apply, hankelColorExpansion_X,
        hankelColorExpansionMoment, map_sum]
      rw [Finset.sum_eq_single (s i)]
      · change (MvPolynomial.aeval (R := R) (fun p : HankelColorExpansionIndex r =>
            if h : p ∈ Set.range (hankelSelectedColorEmbedding s) then
              X ((Equiv.ofInjective (hankelSelectedColorEmbedding s)
                (hankelSelectedColorEmbedding s).injective).symm ⟨p, h⟩)
            else 0) (X (s i, i))) = X i
        rw [MvPolynomial.aeval_X, dif_pos ⟨i,
          hankelSelectedColorEmbedding_apply s i⟩]
        congr 1
        simpa only [hankelSelectedColorEmbedding_apply] using
          (Equiv.ofInjective_symm_apply
            (hankelSelectedColorEmbedding s).injective i)
      · intro j hj hji
        have hnotrange : (j, i) ∉ Set.range (hankelSelectedColorEmbedding s) := by
          rintro ⟨k, hk⟩
          have hki : k = i := congrArg Prod.snd hk
          subst k
          exact hji (congrArg Prod.fst hk).symm
        change (MvPolynomial.aeval (R := R) (fun p : HankelColorExpansionIndex r =>
            if h : p ∈ Set.range (hankelSelectedColorEmbedding s) then
              X ((Equiv.ofInjective (hankelSelectedColorEmbedding s)
                (hankelSelectedColorEmbedding s).injective).symm ⟨p, h⟩)
            else 0) (X (j, i))) = 0
        rw [MvPolynomial.aeval_X, dif_neg hnotrange]
      · simp
  exact RingHom.congr_fun hlhs P

/-- The selected allocation of an exponent: all multiplicity in row `i` is assigned to `s i`. -/
def hankelSelectedAllocation {r : ℕ} (s : ℕ → Fin r) (e : ℕ →₀ ℕ) :
    HankelColorExpansionIndex r →₀ ℕ :=
  e.mapDomain (hankelSelectedColorEmbedding s)

theorem hankelSelectedAllocation_apply {r : ℕ} (s : ℕ → Fin r)
    (e : ℕ →₀ ℕ) (j : Fin r) (i : ℕ) :
    hankelSelectedAllocation s e (j, i) =
      if j = s i then e i else 0 := by
  classical
  by_cases hji : j = s i
  · subst j
    rw [if_pos rfl]
    change (Finsupp.mapDomain (hankelSelectedColorEmbedding s) e)
      (hankelSelectedColorEmbedding s i) = e i
    exact Finsupp.mapDomain_apply (hankelSelectedColorEmbedding s).injective e i
  · rw [if_neg hji]
    apply Finsupp.mapDomain_notin_range
    rintro ⟨k, hk⟩
    have hki : k = i := congrArg Prod.snd hk
    subst k
    exact hji (congrArg Prod.fst hk).symm

/-- Total color choice extending a support coloring by an arbitrary default color. -/
noncomputable def hankelColoringSelection {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (default : Fin r) (i : ℕ) : Fin r :=
  if hi : i ∈ e.support then C ⟨i, hi⟩ else default

theorem hankelAdjacentDecompositionOfColoring_allocation_eq_selected
    {r : ℕ} (e : ℕ →₀ ℕ)
    (C : (hankelChainGraph.induce (e.support : Set ℕ)).Coloring (Fin r))
    (default : Fin r) :
    (hankelAdjacentDecompositionOfColoring e C).allocation =
      hankelSelectedAllocation (hankelColoringSelection e C default) e := by
  classical
  ext p
  obtain ⟨j, i⟩ := p
  rw [HankelAdjacentDecomposition.allocation_apply,
    hankelSelectedAllocation_apply]
  by_cases hi : i ∈ e.support
  · rw [hankelAdjacentDecompositionOfColoring, hankelColorPart_apply_of_mem e C j hi]
    simp only [hankelColoringSelection, dif_pos hi]
    split_ifs with h <;> simp_all
  · have hei : e i = 0 := Finsupp.notMem_support_iff.mp hi
    simp [hankelAdjacentDecompositionOfColoring, hankelColorPart,
      hankelColoringSelection, hi, hei]

theorem coeff_hankelColorExpansion_monomial_selectedAllocation
    (R : Type*) [CommSemiring R] {r : ℕ} (s : ℕ → Fin r)
    (e : ℕ →₀ ℕ) (a : R) :
    MvPolynomial.coeff (hankelSelectedAllocation s e)
        (hankelColorExpansion R r (MvPolynomial.monomial e a)) = a := by
  rw [hankelSelectedAllocation, ← MvPolynomial.coeff_killCompl
    (p := hankelColorExpansion R r (MvPolynomial.monomial e a))
    (hankelSelectedColorEmbedding s).injective]
  rw [killCompl_hankelColorExpansion]
  simp

/-- Selected coefficient survives color expansion unchanged for every polynomial. -/
theorem coeff_hankelColorExpansion_selectedAllocation
    (R : Type*) [CommSemiring R] {r : ℕ} (s : ℕ → Fin r)
    (e : ℕ →₀ ℕ) (P : MvPolynomial ℕ R) :
    MvPolynomial.coeff (hankelSelectedAllocation s e)
        (hankelColorExpansion R r P) = MvPolynomial.coeff e P := by
  rw [hankelSelectedAllocation, ← MvPolynomial.coeff_killCompl
    (p := hankelColorExpansion R r P)
    (hankelSelectedColorEmbedding s).injective]
  rw [killCompl_hankelColorExpansion]

/-- Every monomial in the support of an expanded polynomial comes from an expanded source
monomial in the original support. -/
theorem exists_source_of_mem_hankelColorExpansion_support
    (R : Type*) [CommSemiring R] {r : ℕ} {P : MvPolynomial ℕ R}
    {g : HankelColorExpansionIndex r →₀ ℕ}
    (hg : g ∈ (hankelColorExpansion R r P).support) :
    ∃ e ∈ P.support,
      g ∈ (hankelColorExpansion R r
        (MvPolynomial.monomial e (MvPolynomial.coeff e P))).support := by
  rw [P.as_sum, map_sum] at hg
  have hmem := MvPolynomial.support_sum
    (s := P.support)
    (f := fun e => hankelColorExpansion R r
      (MvPolynomial.monomial e (MvPolynomial.coeff e P))) hg
  rw [Finset.mem_biUnion] at hmem
  exact hmem

theorem Finsupp.mapDomain_apply_of_unique_preimage
    {α β M : Type*} [AddCommMonoid M] (f : α → β) (x : α →₀ M)
    {a : α} (ha : a ∈ x.support)
    (hunique : ∀ b ∈ x.support, f b = f a → b = a) :
    Finsupp.mapDomain f x (f a) = x a := by
  classical
  rw [Finsupp.mapDomain, Finsupp.sum_apply, Finsupp.sum,
    Finset.sum_eq_single a]
  · simp
  · intro b hb hba
    rw [Finsupp.single_apply]
    simp only [ite_eq_right_iff]
    intro hfb
    exact (hba (hunique b hb hfb)).elim
  · exact fun h => (h ha).elim

/-- Color expansion followed by exponent collapse is the ordered-atom secant parameterization. -/
theorem hankelColorCollapse_comp_expansion
    (R : Type*) [CommSemiring R] (r : ℕ) :
    (hankelColorCollapse R r).comp (hankelColorExpansion R r) =
      MvPolynomial.eval₂Hom MvPolynomial.C
        (fun n => ∑ j : Fin r,
          X (j, (0 : Fin 2)) * X (j, (1 : Fin 2)) ^ n) := by
  apply MvPolynomial.ringHom_ext
  · intro a
    simp only [RingHom.comp_apply, hankelColorExpansion,
      MvPolynomial.eval₂Hom_C]
    exact hankelColorCollapse_C R r a
  · intro i
    simp only [RingHom.comp_apply, hankelColorExpansion_X,
      hankelColorExpansionMoment, map_sum, MvPolynomial.eval₂Hom_X']
    apply Finset.sum_congr rfl
    intro j hj
    rw [hankelColorCollapse, AddMonoidAlgebra.mapDomainRingHom_apply]
    change AddMonoidAlgebra.mapDomain (hankelColorCollapseExponentHom r)
        (MvPolynomial.X (j, i)) = _
    rw [MvPolynomial.X, ← MvPolynomial.single_eq_monomial,
      AddMonoidAlgebra.mapDomain_single]
    change AddMonoidAlgebra.single
      ((Finsupp.linearCombination ℕ fun p : HankelColorExpansionIndex r =>
        Finsupp.single (p.1, (0 : Fin 2)) 1 +
          Finsupp.single (p.1, (1 : Fin 2)) p.2)
        (Finsupp.single (j, i) 1)) 1 = _
    rw [Finsupp.linearCombination_single, one_nsmul]
    simp only [MvPolynomial.X, MvPolynomial.monomial_pow,
      MvPolynomial.monomial_mul, one_pow, one_mul]
    congr 2
    ext p
    simp [Finsupp.single_apply]

/-- **Reduced-support coefficient separation.** Over any commutative semiring, a nonzero
polynomial all of whose exponents avoid `(r+1)` Hankel chains remains nonzero under ordered-atom
parameterization. This is the missing algebraic half of the Conca--Nam secant comparison. -/
theorem ne_zero_of_orderedAtomParameterization_of_reduced
    (R : Type*) [CommSemiring R] (r : ℕ) {P : MvPolynomial ℕ R}
    (hred : ∀ e ∈ P.support, HankelChainReduced r e)
    (hP : P ≠ 0) :
    MvPolynomial.eval₂Hom MvPolynomial.C
      (fun n => ∑ j : Fin r,
        X (j, (0 : Fin 2)) * X (j, (1 : Fin 2)) ^ n) P ≠ 0 := by
  classical
  have hsupp : P.support.Nonempty := by
    simpa [Finset.nonempty_iff_ne_empty, Finsupp.support_eq_empty] using hP
  by_cases hrzero : r = 0
  · subst r
    have hsupportZero : P.support ⊆ {0} := by
      intro e he
      have hcolor := (hankelChainReduced_iff_colorable 0 e).mp (hred e he)
      have hempty : IsEmpty {n // n ∈ (e.support : Set ℕ)} := hcolor.isEmpty
      have hesupp : e.support = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hne
        obtain ⟨i, hi⟩ := hne
        exact isEmptyElim (⟨i, hi⟩ : {n // n ∈ (e.support : Set ℕ)})
      exact Finset.mem_singleton.mpr (Finsupp.support_eq_empty.mp hesupp)
    have hPeq : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := by
      ext e
      by_cases he : e = 0
      · subst e
        simp
      · have henot : e ∉ P.support := fun hemem => he
          (Finset.mem_singleton.mp (hsupportZero hemem))
        have hz := Finsupp.notMem_support_iff.mp henot
        rw [MvPolynomial.coeff_C]
        calc
          MvPolynomial.coeff e P = 0 := hz
          _ = (if (0 : ℕ →₀ ℕ) = e then MvPolynomial.coeff 0 P else 0) :=
            (if_neg (Ne.symm he)).symm
    rw [hPeq]
    simp only [MvPolynomial.eval₂Hom_C]
    exact MvPolynomial.C_ne_zero.mpr (by
      intro hcoeff
      apply hP
      rw [hPeq, hcoeff, map_zero])
  obtain ⟨e, heP, hemax⟩ := Finset.exists_max_image P.support toLex hsupp
  let C := ((hankelChainReduced_iff_colorable r e).mp (hred e heP)).some
  let D := hankelAdjacentDecompositionOfColoring e C
  have hrpos : 0 < r := Nat.pos_of_ne_zero hrzero
  let default : Fin r := ⟨0, hrpos⟩
  let s := hankelColoringSelection e C default
  let a := D.allocation
  let d := hankelColorCollapseExponentHom r a
  have haSelected : a = hankelSelectedAllocation s e := by
    exact hankelAdjacentDecompositionOfColoring_allocation_eq_selected e C default
  have hcoeffExpansion :
      MvPolynomial.coeff a (hankelColorExpansion R r P) =
        MvPolynomial.coeff e P := by
    rw [haSelected]
    exact coeff_hankelColorExpansion_selectedAllocation R s e P
  have hcoeffExpansion_ne :
      MvPolynomial.coeff a (hankelColorExpansion R r P) ≠ 0 := by
    rw [hcoeffExpansion]
    exact Finsupp.mem_support_iff.mp heP
  have haSupport : a ∈ (hankelColorExpansion R r P).support :=
    Finsupp.mem_support_iff.mpr hcoeffExpansion_ne
  have hunique : ∀ g ∈ (hankelColorExpansion R r P).support,
      hankelColorCollapseExponentHom r g =
        hankelColorCollapseExponentHom r a → g = a := by
    intro g hg hcollapse
    obtain ⟨f, hfP, hgf⟩ :=
      exists_source_of_mem_hankelColorExpansion_support R hg
    have hgrow := hankelColorExpansion_monomial_support_rowWeight R r hgf
    have hge : toLex e ≤ toLex f := by
      exact D.lex_le_of_rowWeight_of_collapse hgrow
        (by simpa [a] using hcollapse)
    have hfe := hemax f hfP
    have hfeq : f = e := by
      apply toLex.injective
      exact le_antisymm hfe hge
    have hgrowe : Finsupp.weight hankelColorRowWeight g = e := hgrow.trans hfeq
    exact D.allocation_eq_of_rowWeight_of_collapse hgrowe (by
      simpa [a] using hcollapse)
  have hcoeffCollapse := Finsupp.mapDomain_apply_of_unique_preimage
    (hankelColorCollapseExponentHom r)
    (AddMonoidAlgebra.coeff (hankelColorExpansion R r P))
    haSupport (by
      intro g hg hcollapse
      exact hunique g hg (by simpa [a] using hcollapse))
  intro hzero
  have hcoeffZero := congrArg (MvPolynomial.coeff d) hzero
  have hcomp := congrArg (fun F : MvPolynomial ℕ R →+*
      MvPolynomial (Fin r × Fin 2) R => MvPolynomial.coeff d (F P))
    (hankelColorCollapse_comp_expansion R r)
  rw [← hcomp] at hcoeffZero
  simp only [RingHom.comp_apply] at hcoeffZero
  change (AddMonoidAlgebra.mapDomain (hankelColorCollapseExponentHom r)
      (hankelColorExpansion R r P)).coeff d = 0 at hcoeffZero
  rw [AddMonoidAlgebra.coeff_mapDomain] at hcoeffZero
  rw [hcoeffCollapse] at hcoeffZero
  exact hcoeffExpansion_ne hcoeffZero

/-- Named parameterization form of reduced-support separation. -/
theorem deningerHankelSecantParameterization_ne_zero_of_reduced
    (R : Type*) [CommRing R] (r : ℕ) {P : MvPolynomial ℕ R}
    (hred : ∀ e ∈ P.support, HankelChainReduced r e)
    (hP : P ≠ 0) :
    deningerHankelSecantParameterization R r P ≠ 0 := by
  unfold deningerHankelSecantParameterization deningerHankelSecantMoment
  exact ne_zero_of_orderedAtomParameterization_of_reduced R r hred hP

end
end RHTower
