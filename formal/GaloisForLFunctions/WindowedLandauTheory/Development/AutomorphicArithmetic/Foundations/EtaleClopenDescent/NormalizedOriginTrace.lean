import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FiniteNormalizationProjective
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ReducedFibreTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveTraceEvaluation
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveResidueAtOrigin
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.RationalExteriorTrace

/-! The constant Laurent coefficient of the trace of an origin-chart
section is the sum of its values on the reduced origin fibre. -/

noncomputable section

open GlobalTheory.SchemeCohomology

namespace GlobalTheory.PD

variable {k F E : Type} [Field k] [IsAlgClosed k] [Field F] [Field E] [Algebra k F]
  [Algebra k E] [Algebra F E] [IsScalarTower k F E] {d : ℕ} {x : Fin (d + 1) → F}

omit [IsAlgClosed k] in
private theorem map_ker_originEval (h : IsPd k x) :
    let A := rA k x {0}
    let B := integralClosure A E
    letI : Algebra A B := B.algebra
    (RingHom.ker (originEval h).toRingHom).map (algebraMap A B) =
      originIdeal k E x := by
  intro A B
  rw [ker_originEval h, Ideal.map_span, ← Set.range_comp]
  unfold originIdeal
  apply congrArg Ideal.span
  apply congrArg Set.range
  funext j
  exact Subtype.ext rfl

/-- The trace through the projective normalization specializes at the
origin to the sum of all rational evaluations on the fibre. -/
theorem IsFinCover.residue_trace_origin (h : IsFinCover k E x)
    [IsReduced ((rB k E x {0}) ⧸ originIdeal k E x)]
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ) (b : rB k E x {0}) :
    ρ (Algebra.trace F E b) = ∑ᶠ e : OriginFibrePoint k E x, e.1 b := by
  let A := rA k x {0}
  let B := integralClosure A E
  letI : Algebra A B := B.algebra
  letI : IsFractionRing A F := h.pd.isFractionRing_rA 0
  letI := h.fin
  letI : IsFractionRing B E := integralClosure.isFractionRing_of_finite_extension F E
  letI := (h.finiteProjective_chart 0).1
  letI := (h.finiteProjective_chart 0).2
  letI : Algebra.IsPushout A F B E := fractionFields_isPushout fun a a' haa' => by
    apply Subtype.ext
    exact (algebraMap F E).injective (congrArg (fun b : B => (b : E)) haa')
  have htr := (projectiveAlgebraTrace_eq_trace (R := F) (A := E) (algebraMap B E b)).symm.trans
    (projectiveAlgebraTrace_baseChange (R := A) (A := B) (S := F) (B := E) b)
  calc
    _ = ρ (projectiveAlgebraTrace A B b : A) := congrArg ρ htr
    _ = originEval h.pd (projectiveAlgebraTrace A B b) := res_eq_originEval h.pd ρ hρ _
    _ = _ := ?_
  let J : Ideal B := (RingHom.ker (originEval h.pd).toRingHom).map (algebraMap A B)
  have hJ : J = originIdeal k E x := map_ker_originEval (E := E) h.pd
  have hspecial := projectiveAlgebraTrace_rationalFibre (A := A) (B := B) (originEval h.pd) b
  have htrace := congrArg (fun I : Ideal B => Algebra.trace k (B ⧸ I) (Ideal.Quotient.mk I b)) hJ
  exact hspecial.trans (htrace.trans ((trace_originFibre h).2.2 b))

end GlobalTheory.PD
