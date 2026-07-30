import Mathlib.Algebra.MvPolynomial.Polynomial
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Topology.Algebra.MvPolynomial

/-!
# Real polynomial zero sets have measure zero

A nonzero real polynomial in finitely many real variables has a
Lebesgue-null zero set.  The proof is by induction on the number of
variables and Fubini.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The zero set of a nonzero real multivariate polynomial in `n`
variables is Lebesgue-null. -/
theorem realMvPolynomial_zero_set_volume_fin :
    ∀ n : ℕ, ∀ P : MvPolynomial (Fin n) ℝ, P ≠ 0 →
      volume {x : Fin n → ℝ |
        MvPolynomial.eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have hconst :
          ∀ x : Fin 0 → ℝ,
            MvPolynomial.eval x P ≠ 0 := by
        intro x
        have hPC :
            P = MvPolynomial.C
              (MvPolynomial.coeff 0 P) :=
          P.eq_C_of_isEmpty
        rw [hPC] at hP ⊢
        simpa using hP
      have hempty :
          {x : Fin 0 → ℝ |
            MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp [hconst x]
      simp [hempty]
  | succ n ih =>
      intro P hP
      let Q : Polynomial (MvPolynomial (Fin n) ℝ) :=
        MvPolynomial.finSuccEquiv ℝ n P
      have hQ : Q ≠ 0 :=
        (MvPolynomial.finSuccEquiv ℝ n).injective.ne hP
      let A : MvPolynomial (Fin n) ℝ :=
        Q.leadingCoeff
      have hA : A ≠ 0 := by
        simpa [A] using
          Polynomial.leadingCoeff_ne_zero.mpr hQ
      have hAzero :
          volume {x : Fin n → ℝ |
            MvPolynomial.eval x A = 0} = 0 :=
        ih A hA
      let S : Set ((Fin n → ℝ) × ℝ) :=
        {z |
          MvPolynomial.eval
            (Fin.cons z.2 z.1 :
              Fin (n + 1) → ℝ) P = 0}
      have hcons :
          Continuous
            (fun z : (Fin n → ℝ) × ℝ =>
              (Fin.cons z.2 z.1 :
                Fin (n + 1) → ℝ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact continuous_snd
        · exact (continuous_apply j).comp continuous_fst
      have hS : MeasurableSet S := by
        exact
          isClosed_singleton.preimage
              (P.continuous_eval.comp hcons)
            |>.measurableSet
      have hsections :
          (fun x : Fin n → ℝ =>
            volume (Prod.mk x ⁻¹' S)) =ᵐ[volume] 0 := by
        have hae :
            ∀ᵐ x ∂volume,
              MvPolynomial.eval x A ≠ 0 := by
          rw [ae_iff]
          simpa using hAzero
        filter_upwards [hae] with x hx
        let U : Polynomial ℝ :=
          Q.map (MvPolynomial.eval x)
        have hU : U ≠ 0 := by
          intro hzero
          have hcoeff :
              U.coeff Q.natDegree ≠ 0 := by
            rw [show U =
                Q.map (MvPolynomial.eval x) by rfl,
              Polynomial.coeff_map]
            simpa [A] using hx
          exact hcoeff (by rw [hzero]; simp)
        have hroot :
            Prod.mk x ⁻¹' S =
              {y : ℝ | Polynomial.IsRoot U y} := by
          ext y
          change
            MvPolynomial.eval
                (Fin.cons y x :
                  Fin (n + 1) → ℝ) P = 0 ↔
              Polynomial.IsRoot U y
          rw [MvPolynomial.eval_eq_eval_mv_eval']
          rfl
        rw [hroot]
        exact
          (Polynomial.finite_setOf_isRoot hU).measure_zero
            volume
      have hprod :
          (volume.prod volume) S = 0 :=
        Measure.measure_prod_null_of_ae_null
          hS hsections
      let e :=
        MeasurableEquiv.piFinSuccAbove
          (fun _ : Fin (n + 1) => ℝ) 0
      let f :
          (Fin (n + 1) → ℝ) →
            ((Fin n → ℝ) × ℝ) :=
        fun z => (e z).swap
      have hf :
          MeasurePreserving f volume
            (volume.prod volume) := by
        simpa [f, e, Function.comp_def] using
          (Measure.measurePreserving_swap.comp
            (volume_preserving_piFinSuccAbove
              (fun _ : Fin (n + 1) => ℝ) 0))
      have hpre :
          f ⁻¹' S =
            {x : Fin (n + 1) → ℝ |
              MvPolynomial.eval x P = 0} := by
        ext z
        simp [f, e, S,
          MeasurableEquiv.piFinSuccAbove_apply,
          Fin.insertNthEquiv]
      rw [← hpre]
      rw [hf.measure_preimage hS.nullMeasurableSet,
        hprod]

end

end GaloisForLFunctions.HTGeometry
