import GaloisForLFunctions.HTGeometry.CountableAlgebraicLocusDichotomy
import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import Mathlib.MeasureTheory.Measure.Prod

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
      volume {x : Fin n → ℂ | MvPolynomial.eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have hconst : ∀ x : Fin 0 → ℂ, MvPolynomial.eval x P ≠ 0 := by
        intro x
        have hPC : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := P.eq_C_of_isEmpty
        rw [hPC] at hP ⊢
        simpa using hP
      have hempty : {x : Fin 0 → ℂ | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp [hconst x]
      simp [hempty]
  | succ n ih =>
      intro P hP
      let Q : Polynomial (MvPolynomial (Fin n) ℂ) :=
        MvPolynomial.finSuccEquiv ℂ n P
      have hQ : Q ≠ 0 := (MvPolynomial.finSuccEquiv ℂ n).injective.ne hP
      let A : MvPolynomial (Fin n) ℂ := Q.leadingCoeff
      have hA : A ≠ 0 := by
        simpa [A] using Polynomial.leadingCoeff_ne_zero.mpr hQ
      have hAzero : volume {x : Fin n → ℂ | MvPolynomial.eval x A = 0} = 0 :=
        ih A hA
      let S : Set ((Fin n → ℂ) × ℂ) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℂ) P = 0}
      have hcons : Continuous (fun z : (Fin n → ℂ) × ℂ ↦
          (Fin.cons z.2 z.1 : Fin (n + 1) → ℂ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_snd
        · exact (continuous_apply j).comp continuous_fst
      have hS : MeasurableSet S := by
        exact isClosed_singleton.preimage (P.continuous_eval.comp hcons) |>.measurableSet
      have hsections : (
          fun x : Fin n → ℂ ↦ volume (Prod.mk x ⁻¹' S)) =ᵐ[volume] 0 := by
        have hae : ∀ᵐ x ∂volume, MvPolynomial.eval x A ≠ 0 := by
          rw [ae_iff]
          simpa using hAzero
        filter_upwards [hae] with x hx
        let U : Polynomial ℂ := Q.map (MvPolynomial.eval x)
        have hU : U ≠ 0 := by
          intro hzero
          have hcoeff : U.coeff Q.natDegree ≠ 0 := by
            rw [show U = Q.map (MvPolynomial.eval x) by rfl,
              Polynomial.coeff_map]
            simpa [A] using hx
          exact hcoeff (by rw [hzero]; simp)
        have hroot : Prod.mk x ⁻¹' S = {y : ℂ | Polynomial.IsRoot U y} := by
          ext y
          change MvPolynomial.eval (Fin.cons y x : Fin (n + 1) → ℂ) P = 0 ↔
            Polynomial.IsRoot U y
          rw [MvPolynomial.eval_eq_eval_mv_eval']
          rfl
        rw [hroot]
        exact (Polynomial.finite_setOf_isRoot hU).measure_zero volume
      have hprod : (volume.prod volume) S = 0 :=
        Measure.measure_prod_null_of_ae_null hS hsections
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0
      let f : (Fin (n + 1) → ℂ) → ((Fin n → ℂ) × ℂ) := fun z ↦ (e z).swap
      have hf : MeasurePreserving f volume (volume.prod volume) := by
        simpa [f, e, Function.comp_def] using
          (Measure.measurePreserving_swap.comp
            (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℂ) 0))
      have hpre : f ⁻¹' S = {x : Fin (n + 1) → ℂ | MvPolynomial.eval x P = 0} := by
        ext z
        simp [f, e, S, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
      rw [← hpre]
      rw [hf.measure_preimage hS.nullMeasurableSet, hprod]

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
