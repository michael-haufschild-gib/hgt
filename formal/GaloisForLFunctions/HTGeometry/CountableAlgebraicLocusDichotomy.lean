import GaloisForLFunctions.HTGeometry.PolynomialJetEscape
import GaloisForLFunctions.HTGeometry.BaireGenericAvoidance
import Mathlib.Topology.Baire.CompleteMetrizable

/-!
# Countable algebraic-locus collapse or generic avoidance

A countable family of finite complex algebraic loci has an exact Baire alternative: either one
finite locus is universal, or the points avoiding every locus form a dense residual set.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open MvPolynomial Topology

variable {ι : Type*} [Fintype ι]

/-- The common zero locus of a finite family of complex law-coordinate polynomials. -/
def finitePolynomialZeroLocus (P : Finset (MvPolynomial ι ℂ)) : Set (ι → ℂ) :=
  {x | ∀ p ∈ P, MvPolynomial.eval x p = 0}

omit [Fintype ι] in
theorem finitePolynomialZeroLocus_isClosed (P : Finset (MvPolynomial ι ℂ)) :
    IsClosed (finitePolynomialZeroLocus P) := by
  rw [show finitePolynomialZeroLocus P =
      ⋂ p ∈ P, {x | MvPolynomial.eval x p = 0} by
    ext x
    simp [finitePolynomialZeroLocus]]
  exact isClosed_biInter fun p hp => mvPolynomial_zero_set_isClosed p

/-- A proper finite algebraic locus is nowhere dense. -/
theorem finitePolynomialZeroLocus_isNowhereDense
    (P : Finset (MvPolynomial ι ℂ))
    (hproper : finitePolynomialZeroLocus P ≠ Set.univ) :
    IsNowhereDense (finitePolynomialZeroLocus P) := by
  obtain ⟨x, hx⟩ :=
    (Set.ne_univ_iff_exists_notMem (finitePolynomialZeroLocus P)).mp hproper
  simp only [finitePolynomialZeroLocus, Set.mem_setOf_eq, not_forall] at hx
  push Not at hx
  obtain ⟨p, hpP, hpx⟩ := hx
  have hpne : p ≠ 0 := by
    intro hpzero
    subst p
    simp at hpx
  apply IsNowhereDense.mono
    (s := {y : ι → ℂ | MvPolynomial.eval y p = 0})
  · intro y hy
    exact hy p hpP
  · exact mvPolynomial_zero_set_isNowhereDense p hpne

/-- Countably many finite algebraic law loci have the exact Baire alternative: either one finite
level is universal, or simultaneous avoidance is dense residual. -/
theorem finitePolynomialZeroLoci_collapse_or_denseResidual
    (P : ℕ → Finset (MvPolynomial ι ℂ)) :
    (∃ N, finitePolynomialZeroLocus (P N) = Set.univ) ∨
      (Dense {x | ∀ n, x ∉ finitePolynomialZeroLocus (P n)} ∧
        {x | ∀ n, x ∉ finitePolynomialZeroLocus (P n)} ∈ residual (ι → ℂ)) := by
  by_cases hcollapse : ∃ N, finitePolynomialZeroLocus (P N) = Set.univ
  · exact Or.inl hcollapse
  · right
    have hproper : ∀ n, finitePolynomialZeroLocus (P n) ≠ Set.univ := by
      intro n hn
      exact hcollapse ⟨n, hn⟩
    have hclosed : ∀ n, IsClosed (finitePolynomialZeroLocus (P n)) :=
      fun n => finitePolynomialZeroLocus_isClosed (P n)
    have hnowhere : ∀ n, IsNowhereDense (finitePolynomialZeroLocus (P n)) :=
      fun n => finitePolynomialZeroLocus_isNowhereDense (P n) (hproper n)
    have hopen : ∀ n, IsOpen (finitePolynomialZeroLocus (P n))ᶜ :=
      fun n => (hclosed n).isOpen_compl
    have hdense : ∀ n, Dense (finitePolynomialZeroLocus (P n))ᶜ := fun n =>
      interior_eq_empty_iff_dense_compl.mp
        ((hclosed n).isNowhereDense_iff.mp (hnowhere n))
    have hset : {x | ∀ n, x ∉ finitePolynomialZeroLocus (P n)} =
        ⋂ n, (finitePolynomialZeroLocus (P n))ᶜ := by
      ext x
      simp
    rw [hset]
    exact ⟨dense_iInter_of_isOpen_nat hopen hdense,
      countable_iInter_mem.mpr
        (fun n => residual_of_dense_open (hopen n) (hdense n))⟩

end

end GaloisForLFunctions.HTGeometry
