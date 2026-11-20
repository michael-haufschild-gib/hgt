import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Algebraic null sets for independent coordinate measures

A nonzero polynomial over a topological integral domain vanishes with
probability zero under independent atomless coordinate measures. Outside
the exceptional zero set of the leading coefficient, every one-variable
section has finitely many roots.
-/

open MeasureTheory
namespace GaloisForLFunctions.RepresentationLifting
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R] [TopologicalSpace R] [IsTopologicalRing R]
  [T2Space R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]

/-- Nonidentical independent atomless coordinates avoid every proper
polynomial equation, even for infinite sigma-finite measures. -/
theorem mvPolynomial_product_null :
    ∀ n : ℕ, ∀ (μ : Fin n → Measure R) [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)],
      ∀ P : MvPolynomial (Fin n) R, P ≠ 0 →
        Measure.pi μ {x : Fin n → R | MvPolynomial.eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro μ _ _ P hP
      have hconst : ∀ x : Fin 0 → R, MvPolynomial.eval x P ≠ 0 := by
        intro x
        have hPC : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := P.eq_C_of_isEmpty
        rw [hPC] at hP ⊢
        simpa using hP
      have hempty : {x : Fin 0 → R | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp [hconst x]
      simp [hempty]
  | succ n ih =>
      intro μ _ _ P hP
      let Q : Polynomial (MvPolynomial (Fin n) R) :=
        MvPolynomial.finSuccEquiv R n P
      have hQ : Q ≠ 0 := (MvPolynomial.finSuccEquiv R n).injective.ne hP
      let A : MvPolynomial (Fin n) R := Q.leadingCoeff
      have hA : A ≠ 0 := by
        simpa [A] using Polynomial.leadingCoeff_ne_zero.mpr hQ
      let ν := Measure.pi (fun i : Fin n => μ i.succ)
      have hAzero : ν {x : Fin n → R | MvPolynomial.eval x A = 0} = 0 :=
        ih (fun i : Fin n => μ i.succ) A hA
      let S : Set ((Fin n → R) × R) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → R) P = 0}
      have hcons : Continuous (fun z : (Fin n → R) × R ↦
          (Fin.cons z.2 z.1 : Fin (n + 1) → R)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_snd
        · exact (continuous_apply j).comp continuous_fst
      have hS : MeasurableSet S := by
        exact isClosed_singleton.preimage (P.continuous_eval.comp hcons) |>.measurableSet
      have hsections : (
          fun x : Fin n → R ↦ μ 0 (Prod.mk x ⁻¹' S)) =ᵐ[ν] 0 := by
        have hae : ∀ᵐ x ∂ν, MvPolynomial.eval x A ≠ 0 := by
          rw [ae_iff]
          simpa using hAzero
        filter_upwards [hae] with x hx
        let U : Polynomial R := Q.map (MvPolynomial.eval x)
        have hU : U ≠ 0 := by
          intro hzero
          have hcoeff : U.coeff Q.natDegree ≠ 0 := by
            rw [show U = Q.map (MvPolynomial.eval x) by rfl,
              Polynomial.coeff_map]
            simpa [A] using hx
          exact hcoeff (by rw [hzero]; simp)
        have hroot : Prod.mk x ⁻¹' S = {y : R | Polynomial.IsRoot U y} := by
          ext y
          change MvPolynomial.eval (Fin.cons y x : Fin (n + 1) → R) P = 0 ↔
            Polynomial.IsRoot U y
          rw [MvPolynomial.eval_eq_eval_mv_eval']
          rfl
        rw [hroot]
        exact (Polynomial.finite_setOf_isRoot hU).measure_zero (μ 0)
      have hprod : (ν.prod (μ 0)) S = 0 :=
        Measure.measure_prod_null_of_ae_null hS hsections
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ R) 0
      let f : (Fin (n + 1) → R) → ((Fin n → R) × R) := fun z ↦ (e z).swap
      have hf : MeasurePreserving f (Measure.pi μ) (ν.prod (μ 0)) := by
        simpa [f, e, ν, Function.comp_def] using
          (Measure.measurePreserving_swap.comp
            (measurePreserving_piFinSuccAbove μ 0))
      have hpre : f ⁻¹' S = {x : Fin (n + 1) → R | MvPolynomial.eval x P = 0} := by
        ext z
        simp [f, e, S, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
      rw [← hpre]
      rw [hf.measure_preimage hS.nullMeasurableSet, hprod]

/-- A countable family of nonzero equations is avoided simultaneously
under the same product measure. -/
theorem ae_avoids_polynomial_family {n : ℕ} (μ : Fin n → Measure R)
    [∀ i, SigmaFinite (μ i)] [∀ i, NullSingletonClass (μ i)]
    {ι : Type*} [Countable ι] (P : ι → MvPolynomial (Fin n) R) (hne : ∀ j, P j≠0) :
    ∀ᵐ x ∂Measure.pi μ, ∀ j, MvPolynomial.eval x (P j)≠0 := by
  apply ae_all_iff.mpr
  intro j
  rw [ae_iff]
  simpa using mvPolynomial_product_null n μ (P j) (hne j)

#print axioms ae_avoids_polynomial_family

#print axioms mvPolynomial_product_null
end
end GaloisForLFunctions.RepresentationLifting
