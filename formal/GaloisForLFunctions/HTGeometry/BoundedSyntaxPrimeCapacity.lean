import GaloisForLFunctions.HTGeometry.KolchinCapacityMinimalOrder
import Mathlib.NumberTheory.PrimeCounting

/-!
# Bounded differential syntax has a universal finite jet capacity

An algebraic differential relation of order at most `n` bounds the Kolchin jet capacity of every
solution by `n`, uniformly in the coefficients and independently of the degree: below the minimal
differential order the jets are algebraically independent, so a nonzero relation among the first
`n+1` jets forces the minimal order down to `n`.

The consequence is a prime-growth law.  A carrier whose rational frequency rank retains `π(N)`
independent prime directions and which satisfies a nonzero autonomous relation of order `n_N` obeys
`π(N) ≤ 2 n_N`; since the prime-counting function is unbounded, `n_N` cannot stay bounded.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Differential F] [Differential E]
  [DifferentialAlgebra F E] [CharZero E]

omit [Differential F] [DifferentialAlgebra F E] [CharZero E] in
/-- **A relation of order `n` bounds the minimal differential order by `n`.**  Below the minimal
order the jets are algebraically independent, so no nonzero polynomial can annihilate the first
`n+1` of them. -/
theorem differentialOrder_le_of_jetRelation {x : E} {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P ≠ 0)
    (hann : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P = 0) :
    differentialOrder F x ≤ n := by
  by_contra hcon
  have hle : n + 1 ≤ differentialOrder F x := by omega
  have hindep := algebraicIndepOn_jets_lt_differentialOrder (F := F) x (n + 1) hle
  set emb : Fin (n + 1) → Set.Iio (n + 1) :=
    fun j => ⟨(j : ℕ), by simpa using j.is_lt⟩ with hemb
  have hinj : Function.Injective emb := by
    intro a b hab
    exact Fin.ext (congrArg Subtype.val hab)
  have hcomp := hindep.comp emb hinj
  have hfin : AlgebraicIndependent F (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) := hcomp
  exact hP (algebraicIndependent_iff.mp hfin P hann)

omit [Differential F] [DifferentialAlgebra F E] [CharZero E] in
/-- A nonzero relation among finitely many jets makes the element differentially algebraic. -/
theorem differentialAlgebraicOver_of_jetRelation {x : E} {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P ≠ 0)
    (hann : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P = 0) :
    DifferentialAlgebraicOver F x := by
  intro hind
  set emb : Fin (n + 1) → Unit × ℕ := fun j => ((), (j : ℕ)) with hemb
  have hinj : Function.Injective emb := by
    intro a b hab
    exact Fin.ext (congrArg Prod.snd hab)
  have hAI : AlgebraicIndependent F (fun p : Unit × ℕ => differentialJet p.2 x) := hind
  have hcomp := hAI.comp emb hinj
  have hfin : AlgebraicIndependent F (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) := hcomp
  exact hP (algebraicIndependent_iff.mp hfin P hann)

/-- **The universal jet-capacity bound.**  Every solution of a nonzero algebraic differential
relation of order at most `n` has Kolchin jet capacity at most `n`, whatever its coefficients and
whatever the degree of the relation. -/
theorem kolchinJetCapacity_le_of_jetRelation {x : E} {n : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P ≠ 0)
    (hann : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P = 0) :
    kolchinJetCapacity F x ≤ n :=
  (kolchinJetCapacity_le_differentialOrder
    (differentialAlgebraicOver_of_jetRelation P hP hann)).trans
    (differentialOrder_le_of_jetRelation P hP hann)

/-- The universal capacity of the bounded-syntax class of order `n` and degree `d`.  It does not
depend on the degree, and it is uniform over all coefficient fields. -/
def boundedSyntaxCapacity (n : ℕ) (_d : ℕ) : ℕ := n

/-- **Bounded syntax has a universal finite jet capacity.** -/
theorem kolchinJetCapacity_le_boundedSyntaxCapacity {x : E} {n d : ℕ}
    (P : MvPolynomial (Fin (n + 1)) F) (hP : P ≠ 0)
    (hann : MvPolynomial.aeval (fun j : Fin (n + 1) => differentialJet (j : ℕ) x) P = 0) :
    kolchinJetCapacity F x ≤ boundedSyntaxCapacity n d :=
  kolchinJetCapacity_le_of_jetRelation P hP hann

end

section PrimeGrowth

open Filter

/-- The prime-counting function is unbounded. -/
theorem exists_primeCounting_gt (D : ℕ) : ∃ N : ℕ, D < Nat.primeCounting N := by
  obtain ⟨t, hts, htcard⟩ :=
    Nat.infinite_setOf_prime.exists_subset_card_eq (D + 1)
  refine ⟨t.sup id, ?_⟩
  have hsub : t ⊆ (Finset.range (t.sup id + 1)).filter Nat.Prime := by
    intro p hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ?_, hts hp⟩
    have hle : p ≤ t.sup id := by simpa using Finset.le_sup (f := id) hp
    omega
  have hcard := Finset.card_le_card hsub
  have hpc : Nat.primeCounting (t.sup id)
      = ((Finset.range (t.sup id + 1)).filter Nat.Prime).card := by
    simp [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
  omega

/-- **The prime budget.**  A carrier retaining `π N` independent prime directions inside a
frequency group of rank at most `2 n` forces `π N ≤ 2 n`. -/
theorem primeCounting_le_two_mul {M : Type*} [AddCommGroup M] [Module ℤ M] (N n : ℕ)
    (hlow : (Nat.primeCounting N : Cardinal) ≤ Module.rank ℤ M)
    (hhigh : Module.rank ℤ M ≤ ((n * 2 : ℕ) : Cardinal)) :
    Nat.primeCounting N ≤ 2 * n := by
  have h : (Nat.primeCounting N : Cardinal) ≤ ((n * 2 : ℕ) : Cardinal) := hlow.trans hhigh
  have := (Nat.cast_le (α := Cardinal)).mp h
  omega

/-- **Cofinal prime growth.**  No bounded-syntax family absorbs a cofinal prime module: if every
cutoff `N` obeys the budget `π N ≤ 2 · order N`, then the orders are unbounded. -/
theorem exists_lt_order_of_primeBudget (order : ℕ → ℕ)
    (hbudget : ∀ N, Nat.primeCounting N ≤ 2 * order N) (D : ℕ) :
    ∃ N, D < order N := by
  obtain ⟨N, hN⟩ := exists_primeCounting_gt (2 * D + 1)
  exact ⟨N, by have := hbudget N; omega⟩

/-- Equivalently: no uniform syntax bound exists along a cofinal prime exhaustion. -/
theorem not_bddAbove_order_of_primeBudget (order : ℕ → ℕ)
    (hbudget : ∀ N, Nat.primeCounting N ≤ 2 * order N) :
    ¬ ∃ D : ℕ, ∀ N, order N ≤ D := by
  rintro ⟨D, hD⟩
  obtain ⟨N, hN⟩ := exists_lt_order_of_primeBudget order hbudget D
  exact absurd (hD N) (by omega)

end PrimeGrowth

end GaloisForLFunctions.HTGeometry
