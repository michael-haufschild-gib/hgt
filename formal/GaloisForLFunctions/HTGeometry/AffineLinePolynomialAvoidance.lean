import GaloisForLFunctions.HTGeometry.ComplexPolynomialZeroMeasure
import Mathlib.MeasureTheory.Group.Prod

/-!
# Generic affine lines avoid countably many polynomial obstructions

A nonzero real multivariate polynomial has a Lebesgue-null zero set. For almost every affine
line `a + g • v`, its restriction is therefore a nonzero one-variable polynomial. A countable
family of such restrictions has only a countable union of exceptional real parameters.

This is the reusable algebraic-measure layer behind one-control activation theorems. It makes no
claim that a particular physical obstruction family is nonzero; that witness remains a separate
theorem.
-/

open MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The common real zero set of countably many nonzero one-variable polynomials is countable. -/
theorem countable_setOf_exists_polynomial_isRoot
    (P : ℕ → Polynomial ℝ) (hP : ∀ n, P n ≠ 0) :
    {g : ℝ | ∃ n, (P n).IsRoot g}.Countable := by
  have hfinite : ∀ n, {g : ℝ | (P n).IsRoot g}.Finite :=
    fun n => Polynomial.finite_setOf_isRoot (hP n)
  have hset :
      {g : ℝ | ∃ n, (P n).IsRoot g} =
        ⋃ n, {g : ℝ | (P n).IsRoot g} := by
    ext g
    simp
  rw [hset]
  exact Set.countable_iUnion fun n => (hfinite n).countable

/-- Restriction of a real multivariate polynomial to the affine line `a + g • v`. -/
noncomputable def mvPolynomialAffineLineRestriction {σ : Type*}
    (a v : σ → ℝ) (P : MvPolynomial σ ℝ) : Polynomial ℝ :=
  MvPolynomial.eval₂ Polynomial.C
    (fun i => Polynomial.C (a i) + Polynomial.X * Polynomial.C (v i)) P

/-- Evaluation of the restricted polynomial is evaluation on the corresponding affine line. -/
theorem eval_mvPolynomialAffineLineRestriction {σ : Type*}
    (a v : σ → ℝ) (P : MvPolynomial σ ℝ) (g : ℝ) :
    Polynomial.eval g (mvPolynomialAffineLineRestriction a v P) =
      MvPolynomial.eval (fun i => a i + g * v i) P := by
  rw [mvPolynomialAffineLineRestriction, MvPolynomial.polynomial_eval_eval₂]
  have hcomp :
      (Polynomial.evalRingHom g).comp Polynomial.C = RingHom.id ℝ := by
    ext x
    simp
  rw [hcomp]
  change
    MvPolynomial.eval₂ (RingHom.id ℝ)
        (fun s => Polynomial.eval g
          (Polynomial.C (a s) + Polynomial.X * Polynomial.C (v s))) P =
      MvPolynomial.eval₂ (RingHom.id ℝ) (fun i => a i + g * v i) P
  apply MvPolynomial.eval₂_congr
  intro i c hi hc
  simp
  ring

/-- The zero set of a nonzero real multivariate polynomial in `n` variables is Lebesgue-null. -/
theorem mvPolynomial_zero_set_volume_real_fin :
    ∀ n : ℕ, ∀ P : MvPolynomial (Fin n) ℝ, P ≠ 0 →
      volume {x : Fin n → ℝ | MvPolynomial.eval x P = 0} = 0 := by
  intro n
  induction n with
  | zero =>
      intro P hP
      have hconst : ∀ x : Fin 0 → ℝ, MvPolynomial.eval x P ≠ 0 := by
        intro x
        have hPC : P = MvPolynomial.C (MvPolynomial.coeff 0 P) := P.eq_C_of_isEmpty
        rw [hPC] at hP ⊢
        simpa using hP
      have hempty : {x : Fin 0 → ℝ | MvPolynomial.eval x P = 0} = ∅ := by
        ext x
        simp [hconst x]
      simp [hempty]
  | succ n ih =>
      intro P hP
      let Q : Polynomial (MvPolynomial (Fin n) ℝ) :=
        MvPolynomial.finSuccEquiv ℝ n P
      have hQ : Q ≠ 0 := (MvPolynomial.finSuccEquiv ℝ n).injective.ne hP
      let A : MvPolynomial (Fin n) ℝ := Q.leadingCoeff
      have hA : A ≠ 0 := by
        simpa [A] using Polynomial.leadingCoeff_ne_zero.mpr hQ
      have hAzero : volume {x : Fin n → ℝ | MvPolynomial.eval x A = 0} = 0 :=
        ih A hA
      let S : Set ((Fin n → ℝ) × ℝ) :=
        {z | MvPolynomial.eval (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ) P = 0}
      have hcons : Continuous (fun z : (Fin n → ℝ) × ℝ ↦
          (Fin.cons z.2 z.1 : Fin (n + 1) → ℝ)) := by
        apply continuous_pi
        intro i
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · exact continuous_snd
        · exact (continuous_apply j).comp continuous_fst
      have hS : MeasurableSet S := by
        exact isClosed_singleton.preimage (P.continuous_eval.comp hcons) |>.measurableSet
      have hsections : (
          fun x : Fin n → ℝ ↦ volume (Prod.mk x ⁻¹' S)) =ᵐ[volume] 0 := by
        have hae : ∀ᵐ x ∂volume, MvPolynomial.eval x A ≠ 0 := by
          rw [ae_iff]
          simpa using hAzero
        filter_upwards [hae] with x hx
        let U : Polynomial ℝ := Q.map (MvPolynomial.eval x)
        have hU : U ≠ 0 := by
          intro hzero
          have hcoeff : U.coeff Q.natDegree ≠ 0 := by
            rw [show U = Q.map (MvPolynomial.eval x) by rfl,
              Polynomial.coeff_map]
            simpa [A] using hx
          exact hcoeff (by rw [hzero]; simp)
        have hroot : Prod.mk x ⁻¹' S = {y : ℝ | Polynomial.IsRoot U y} := by
          ext y
          change MvPolynomial.eval (Fin.cons y x : Fin (n + 1) → ℝ) P = 0 ↔
            Polynomial.IsRoot U y
          rw [MvPolynomial.eval_eq_eval_mv_eval']
          rfl
        rw [hroot]
        exact (Polynomial.finite_setOf_isRoot hU).measure_zero volume
      have hprod : (volume.prod volume) S = 0 :=
        Measure.measure_prod_null_of_ae_null hS hsections
      let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
      let f : (Fin (n + 1) → ℝ) → ((Fin n → ℝ) × ℝ) := fun z ↦ (e z).swap
      have hf : MeasurePreserving f volume (volume.prod volume) := by
        simpa [f, e, Function.comp_def] using
          (Measure.measurePreserving_swap.comp
            (volume_preserving_piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0))
      have hpre : f ⁻¹' S =
          {x : Fin (n + 1) → ℝ | MvPolynomial.eval x P = 0} := by
        ext z
        simp [f, e, S, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv]
      rw [← hpre]
      rw [hf.measure_preimage hS.nullMeasurableSet, hprod]

/-- Almost every affine line has a nonzero restriction of a fixed nonzero polynomial. -/
theorem mvPolynomialAffineLineRestriction_ne_zero_ae_pair {n : ℕ}
    (P : MvPolynomial (Fin n) ℝ) (hP : P ≠ 0) :
    ∀ᵐ av : (Fin n → ℝ) × (Fin n → ℝ) ∂(volume.prod volume),
      mvPolynomialAffineLineRestriction av.1 av.2 P ≠ 0 := by
  let Z : Set (Fin n → ℝ) := {x | MvPolynomial.eval x P = 0}
  have hZ : volume Z = 0 := by
    simpa [Z] using mvPolynomial_zero_set_volume_real_fin n P hP
  have hZm : MeasurableSet Z :=
    isClosed_singleton.preimage P.continuous_eval |>.measurableSet
  let shear :
      ((Fin n → ℝ) × (Fin n → ℝ)) →
        ((Fin n → ℝ) × (Fin n → ℝ)) :=
    fun av => (av.1 + av.2, av.2)
  have hshear :
      MeasurePreserving shear (volume.prod volume) (volume.prod volume) := by
    simpa [shear] using
      (MeasureTheory.measurePreserving_add_prod
        (volume : Measure (Fin n → ℝ)) volume)
  have htarget :
      (volume.prod volume) (Z ×ˢ (Set.univ : Set (Fin n → ℝ))) = 0 := by
    rw [Measure.prod_prod Z Set.univ, hZ]
    simp
  have hpre :
      (volume.prod volume)
        (shear ⁻¹' (Z ×ˢ (Set.univ : Set (Fin n → ℝ)))) = 0 := by
    rw [hshear.measure_preimage (hZm.prod MeasurableSet.univ).nullMeasurableSet,
      htarget]
  rw [ae_iff]
  refine measure_mono_null (t :=
    shear ⁻¹' (Z ×ˢ (Set.univ : Set (Fin n → ℝ)))) ?_ hpre
  intro av hav
  simp only [Set.mem_setOf_eq, ne_eq, not_not] at hav
  have heval :
      Polynomial.eval 1 (mvPolynomialAffineLineRestriction av.1 av.2 P) = 0 := by
    rw [hav]
    simp
  have hsum : MvPolynomial.eval (av.1 + av.2) P = 0 := by
    rw [eval_mvPolynomialAffineLineRestriction] at heval
    simpa [Pi.add_apply] using heval
  exact ⟨hsum, Set.mem_univ _⟩

/-- For almost every affine line, countably many nonzero polynomial obstructions fail only at a
countable set of real line parameters. -/
theorem countable_mvPolynomialAffineLineAvoidance_ae_pair {n : ℕ}
    (P : ℕ → MvPolynomial (Fin n) ℝ) (hP : ∀ r, P r ≠ 0) :
    ∀ᵐ av : (Fin n → ℝ) × (Fin n → ℝ) ∂(volume.prod volume),
      ∃ C : Set ℝ, C.Countable ∧
        ∀ g ∉ C, ∀ r, MvPolynomial.eval
          (fun i => av.1 i + g * av.2 i) (P r) ≠ 0 := by
  have hall :
      ∀ᵐ av : (Fin n → ℝ) × (Fin n → ℝ) ∂(volume.prod volume),
        ∀ r, mvPolynomialAffineLineRestriction av.1 av.2 (P r) ≠ 0 :=
    ae_all_iff.2 fun r => mvPolynomialAffineLineRestriction_ne_zero_ae_pair (P r) (hP r)
  filter_upwards [hall] with av hav
  let Q : ℕ → Polynomial ℝ :=
    fun r => mvPolynomialAffineLineRestriction av.1 av.2 (P r)
  let C : Set ℝ := {g | ∃ r, (Q r).IsRoot g}
  have hC : C.Countable := by
    exact countable_setOf_exists_polynomial_isRoot Q
      (fun r => by simpa [Q] using hav r)
  refine ⟨C, hC, ?_⟩
  intro g hg r heval
  apply hg
  refine ⟨r, ?_⟩
  change Polynomial.eval g (Q r) = 0
  rw [show Q r = mvPolynomialAffineLineRestriction av.1 av.2 (P r) by rfl,
    eval_mvPolynomialAffineLineRestriction]
  exact heval

end

end GaloisForLFunctions.HTGeometry
