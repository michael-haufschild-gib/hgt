import GaloisForLFunctions.HTGeometry.ParametricRootCovering

/-!
# Universal monic coefficient-space root covering

The simple-root locus of the universal monic polynomial is locally a covering over coefficient
space.  This is the finite-dimensional analytic model used by local monogenic presentations.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Topology Set

noncomputable section

/-- Monic degree-`d` polynomial encoded by its `d` lower coefficients. -/
def monicCoeffPolynomial (d : ℕ) (c : Fin d → ℂ) : ℂ[X] :=
  X ^ d + ∑ i : Fin d, C (c i) * X ^ (i : ℕ)

/-- Evaluation of the universal monic degree-`d` polynomial. -/
def monicCoeffRelation (d : ℕ) (q : (Fin d → ℂ) × ℂ) : ℂ :=
  q.2 ^ d + ∑ i : Fin d, q.1 i * q.2 ^ (i : ℕ)

theorem monicCoeffRelation_eq_eval (d : ℕ) (q : (Fin d → ℂ) × ℂ) :
    monicCoeffRelation d q = (monicCoeffPolynomial d q.1).eval q.2 := by
  simp only [monicCoeffRelation, monicCoeffPolynomial, eval_add, eval_pow, eval_X]
  congr 1
  change (∑ i : Fin d, q.1 i * q.2 ^ (i : ℕ)) =
    (evalRingHom q.2) (∑ i : Fin d, C (q.1 i) * X ^ (i : ℕ))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp

theorem analyticAt_monicCoeffRelation (d : ℕ) (q : (Fin d → ℂ) × ℂ) :
    AnalyticAt ℂ (monicCoeffRelation d) q := by
  unfold monicCoeffRelation
  refine analyticAt_snd.pow d |>.add (Finset.analyticAt_fun_sum _ ?_)
  intro i _
  let ev : (Fin d → ℂ) →L[ℂ] ℂ := ContinuousLinearMap.proj (R := ℂ) i
  exact (ev.analyticAt q.1).comp analyticAt_fst |>.mul (analyticAt_snd.pow (i : ℕ))

theorem monicCoeffRelation_partial_snd (d : ℕ) (q : (Fin d → ℂ) × ℂ) :
    (fderiv ℂ (monicCoeffRelation d) q) (0, 1) =
      (derivative (monicCoeffPolynomial d q.1)).eval q.2 := by
  have hfdiff : HasFDerivAt (monicCoeffRelation d)
      (fderiv ℂ (monicCoeffRelation d) q) q :=
    (analyticAt_monicCoeffRelation d q).differentiableAt.hasFDerivAt
  have hι : HasFDerivAt (fun z : ℂ => (q.1, z))
      ((0 : ℂ →L[ℂ] (Fin d → ℂ)).prod (ContinuousLinearMap.id ℂ ℂ)) q.2 :=
    (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
  have hcomp : HasFDerivAt (fun z => monicCoeffRelation d (q.1, z))
      ((fderiv ℂ (monicCoeffRelation d) q).comp
        ((0 : ℂ →L[ℂ] (Fin d → ℂ)).prod
          (ContinuousLinearMap.id ℂ ℂ))) q.2 := by
    simpa [Function.comp_def] using hfdiff.comp q.2 hι
  have hpoly : HasDerivAt (fun z => monicCoeffRelation d (q.1, z))
      ((derivative (monicCoeffPolynomial d q.1)).eval q.2) q.2 := by
    have heq : (fun z => monicCoeffRelation d (q.1, z)) =
        fun z => (monicCoeffPolynomial d q.1).eval z := by
      funext z
      exact monicCoeffRelation_eq_eval d (q.1, z)
    rw [heq]
    exact Polynomial.hasDerivAt _ q.2
  have huniq := hcomp.unique hpoly.hasFDerivAt
  have hev := ContinuousLinearMap.ext_iff.mp huniq 1
  simpa using hev

/-- Root locus of the universal monic degree-`d` polynomial. -/
abbrev MonicCoeffRootLocus (d : ℕ) : Set ((Fin d → ℂ) × ℂ) :=
  ParametricRootLocus (monicCoeffRelation d)

/-- Coefficient projection of the universal monic root locus. -/
abbrev monicCoeffRootProj {d : ℕ} : MonicCoeffRootLocus d → (Fin d → ℂ) :=
  parametricRootProj

/-- A coefficient-space root has a projection chart whenever its specialized polynomial is
separable; no global separability assumption on coefficient space is needed. -/
theorem exists_chart_monicCoeffRootProj {d : ℕ} (q : MonicCoeffRootLocus d)
    (hsep : (monicCoeffPolynomial d q.1.1).Separable) :
    ∃ φ : OpenPartialHomeomorph (MonicCoeffRootLocus d) (Fin d → ℂ),
      q ∈ φ.source ∧ monicCoeffRootProj = φ := by
  apply exists_chart_parametricRootProj q (analyticAt_monicCoeffRelation d q.1)
  rw [monicCoeffRelation_partial_snd]
  apply hsep.eval₂_derivative_ne_zero (RingHom.id ℂ)
  have hroot : (monicCoeffPolynomial d q.1.1).eval q.1.2 = 0 := by
    rw [← monicCoeffRelation_eq_eval]
    exact q.2
  simpa using hroot

/-- The coefficient projection is locally a homeomorphism on the separable locus. -/
theorem isLocalHomeomorph_monicCoeffRootProj (d : ℕ)
    (hsep : ∀ c : Fin d → ℂ, (monicCoeffPolynomial d c).Separable) :
    IsLocalHomeomorph (monicCoeffRootProj (d := d)) :=
  fun q => exists_chart_monicCoeffRootProj q (hsep q.1.1)

end

end GaloisForLFunctions.HTGeometry
