import GaloisForLFunctions.HTGeometry.CountableAlgebraicLocusDichotomy
import GaloisForLFunctions.RepresentationLifting.Probability.PolynomialZeroSetsInProductMeasure
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex

/-!
# Complex polynomial zero sets have measure zero

A nonzero complex polynomial in finitely many variables has a Lebesgue-null zero set.  The proof
is by induction on the number of variables: outside the null zero set of the leading coefficient,
every one-variable section is a nonzero polynomial and hence has finitely many roots; Fubini then
closes the induction.

This supplies the measure-theoretic strengthening of the existing nowhere-density theorem and
the corresponding countable finite-algebraic-locus alternative.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero set of a nonzero complex multivariate polynomial in `n` variables is Lebesgue-null. -/
theorem mvPolynomial_zero_set_volume_fin :
    ∀ n : ℕ, ∀ P : MvPolynomial (Fin n) ℂ, P ≠ 0 →
      volume {x : Fin n → ℂ | MvPolynomial.eval x P = 0} = 0 :=
  fun n P hP => RepresentationLifting.mvPolynomial_product_null n (fun _ => (volume : Measure ℂ)) P hP

/-- Dehomogenization in the projective chart whose `i`th coordinate is one. -/
def dehomogenizeAt {m : ℕ} (i : Fin (m + 1))
    (P : MvPolynomial (Fin (m + 1)) ℂ) : MvPolynomial (Fin m) ℂ :=
  MvPolynomial.aeval (i.insertNth 1 fun j ↦ MvPolynomial.X j) P

theorem eval_dehomogenizeAt {m : ℕ} (i : Fin (m + 1))
    (P : MvPolynomial (Fin (m + 1)) ℂ) (c : Fin m → ℂ) :
    MvPolynomial.eval c (dehomogenizeAt i P) =
      MvPolynomial.eval (i.insertNth 1 c) P := by
  change MvPolynomial.aeval c
      (MvPolynomial.aeval (i.insertNth 1 fun j ↦ MvPolynomial.X j) P) =
    MvPolynomial.aeval (i.insertNth 1 c) P
  rw [MvPolynomial.comp_aeval_apply]
  congr 1
  apply MvPolynomial.algHom_ext
  rw [i.forall_iff_succAbove]
  constructor
  · simp
  · intro j
    simp

/-- A proper finite complex algebraic locus in `Fin m` coordinates is Lebesgue-null. -/
theorem finitePolynomialZeroLocus_volume_zero_fin {m : ℕ}
    (P : Finset (MvPolynomial (Fin m) ℂ))
    (hproper : finitePolynomialZeroLocus P ≠ Set.univ) :
    volume (finitePolynomialZeroLocus P) = 0 := by
  obtain ⟨x, hx⟩ :=
    (Set.ne_univ_iff_exists_notMem (finitePolynomialZeroLocus P)).mp hproper
  simp only [finitePolynomialZeroLocus, Set.mem_setOf_eq, not_forall] at hx
  push Not at hx
  obtain ⟨p, hpP, hpx⟩ := hx
  have hpne : p ≠ 0 := by
    intro hpzero
    subst p
    simp at hpx
  exact measure_mono_null (s := finitePolynomialZeroLocus P)
    (t := {y : Fin m → ℂ | MvPolynomial.eval y p = 0})
    (fun y hy ↦ hy p hpP) (mvPolynomial_zero_set_volume_fin m p hpne)

/-- Countably many finite algebraic loci either contain one universal level or have null union. -/
theorem finitePolynomialZeroLoci_collapse_or_fullMeasure_fin {m : ℕ}
    (P : ℕ → Finset (MvPolynomial (Fin m) ℂ)) :
    (∃ N, finitePolynomialZeroLocus (P N) = Set.univ) ∨
      volume {x | ∃ n, x ∈ finitePolynomialZeroLocus (P n)} = 0 := by
  by_cases hcollapse : ∃ N, finitePolynomialZeroLocus (P N) = Set.univ
  · exact Or.inl hcollapse
  · right
    have hproper : ∀ n, finitePolynomialZeroLocus (P n) ≠ Set.univ := by
      intro n hn
      exact hcollapse ⟨n, hn⟩
    have hnull : ∀ n, volume (finitePolynomialZeroLocus (P n)) = 0 :=
      fun n ↦ finitePolynomialZeroLocus_volume_zero_fin (P n) (hproper n)
    have hset : {x : Fin m → ℂ | ∃ n, x ∈ finitePolynomialZeroLocus (P n)} =
        ⋃ n, finitePolynomialZeroLocus (P n) := by
      ext x
      simp
    rw [hset]
    exact measure_iUnion_null hnull

end

end GaloisForLFunctions.HTGeometry
