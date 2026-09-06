import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryCompletion
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.RecoverySurgeryFaithful
import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicHilbertMellin

/-!
# The same thermal zero divisor from the new geometric completion

Polynomial scaling is the literal pullback along the new radial domains.
Its quotient flow has a unique bounded extension to the completed geometric
norm. The extension, selected by this property, is identified with the diagonal
Hilbert flow. Its analytic operator trace and continuum-subtracted Mellin
response therefore retain the Gamma-zeta formula and all strip zero orders.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Polynomial Set MeasureTheory Complex
attribute [local instance] cubicGradedLineNormedGroup cubicGradedLineInnerProductSpace
  cubicGradedLine_complete

def recoverySurgeryRadialMap (n : ℕ) (q : Icc (0 : ℝ) 1) :
    recoverySurgeryDomain n → recoverySurgeryDomain n :=
  fun p => ⟨(q.val*p.val.1,q.val*p.val.2),recoverySurgeryDomain_radial n p.val p.property q.val q.property⟩

theorem recoveryPolynomialFlow_plane (q : ℝ) (P : Polynomial (Polynomial ℝ)) (p : ℝ × ℝ) :
    recoveryPlaneEval (cubicPolynomialFlow q P) p = recoveryPlaneEval P (q*p.1,q*p.2) := by
  induction P using Polynomial.induction_on' with
  | add P Q hP hQ =>
    simpa only [map_add,recoveryPlaneEval,eval₂_add] using congrArg₂ (·+·) hP hQ
  | monomial k P =>
    rw [cubicPolynomialFlow_monomial]
    simp only [recoveryPlaneEval,eval₂_monomial,coe_evalRingHom,eval_mul,eval_C,
      cubicInnerPolynomialFlow_evaluation,mul_pow]
    ring

theorem recoverySurgeryEvaluation_flow (n : ℕ) (q : Icc (0 : ℝ) 1)
    (P : Polynomial (Polynomial ℝ)) :
    recoverySurgeryEvaluation n (cubicPolynomialFlow q.val P) =
      (recoverySurgeryEvaluation n P) ∘ recoverySurgeryRadialMap n q := by
  funext p
  exact recoveryPolynomialFlow_plane q.val P p.val

theorem recoverySurgeryHilbert_intertwines (n : ℕ) (q : Icc (0 : ℝ) 1)
    (x : Polynomial (Polynomial ℝ) ⧸ cubicCuspAlgebra.toSubmodule) :
    cubicHilbertFlow q (recoverySurgeryHilbertEmbedding n x) =
      recoverySurgeryHilbertEmbedding n (cubicCuspDefectFlow q.val x) := by
  have he : (cubicHilbertFlow q).toLinearMap.comp (recoverySurgeryHilbertEmbedding n) =
      (recoverySurgeryHilbertEmbedding n).comp (cubicCuspDefectFlow q.val) := by
    apply cubicCuspDefectBasis.ext
    intro k
    simp only [LinearMap.comp_apply, recoverySurgeryHilbertEmbedding_basis,
      cubicCuspDefectFlow_spectrum, map_smul]
    change recoverySurgeryGap n k • cubicHilbertFlow q (cubicHilbertBasis k) =
      q.val^(k+1) • (recoverySurgeryGap n k • cubicHilbertBasis k)
    rw [cubicHilbertFlow_basis,smul_smul,smul_smul,mul_comm]
  exact congrArg (fun f => f x) he

theorem recoverySurgeryFlow_existsUnique (n : ℕ) (q : Icc (0 : ℝ) 1) :
    ∃! F : cubicDefectHilbert →L[ℝ] cubicDefectHilbert,
      ∀ x, F (recoverySurgeryHilbertEmbedding n x) =
        recoverySurgeryHilbertEmbedding n (cubicCuspDefectFlow q.val x) := by
  refine ⟨cubicHilbertFlow q,recoverySurgeryHilbert_intertwines n q,?_⟩
  intro F hF
  have he := (recoverySurgeryHilbertEmbedding_denseRange n).equalizer F.continuous
    (cubicHilbertFlow q).continuous (by
      funext x
      change F (recoverySurgeryHilbertEmbedding n x)=cubicHilbertFlow q (recoverySurgeryHilbertEmbedding n x)
      rw [hF x,recoverySurgeryHilbert_intertwines])
  exact DFunLike.coe_injective he

def recoverySurgeryHilbertFlow (n : ℕ) (q : Icc (0 : ℝ) 1) :
    cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  Classical.choose (recoverySurgeryFlow_existsUnique n q)

theorem recoverySurgeryHilbertFlow_extension (n : ℕ) (q : Icc (0 : ℝ) 1) :
    ∀ x, recoverySurgeryHilbertFlow n q (recoverySurgeryHilbertEmbedding n x) =
      recoverySurgeryHilbertEmbedding n (cubicCuspDefectFlow q.val x) :=
  (Classical.choose_spec (recoverySurgeryFlow_existsUnique n q)).1

theorem recoverySurgeryHilbertFlow_eq (n : ℕ) (q : Icc (0 : ℝ) 1) :
    recoverySurgeryHilbertFlow n q=cubicHilbertFlow q :=
  ((Classical.choose_spec (recoverySurgeryFlow_existsUnique n q)).2
    (cubicHilbertFlow q) (recoverySurgeryHilbert_intertwines n q)).symm

theorem recoverySurgeryHilbertFlow_polynomial (n : ℕ) (q : Icc (0 : ℝ) 1)
    (P : Polynomial (Polynomial ℝ)) :
    recoverySurgeryHilbertFlow n q (recoverySurgeryHilbertEmbedding n (Submodule.Quotient.mk P)) =
      recoverySurgeryHilbertEmbedding n (Submodule.Quotient.mk (cubicPolynomialFlow q.val P)) := by
  rw [recoverySurgeryHilbertFlow_extension,cubicCuspDefectFlow_mk]

theorem recoverySurgeryHilbertFlow_basis (n : ℕ) (q : Icc (0 : ℝ) 1) (k : ℕ) :
    recoverySurgeryHilbertFlow n q (cubicHilbertBasis k)=q.val^(k+1) • cubicHilbertBasis k := by
  rw [recoverySurgeryHilbertFlow_eq]
  exact cubicHilbertFlow_basis q k

theorem recoverySurgeryHilbertFlow_trace (n : ℕ) (q : Ico (0 : ℝ) 1) :
    ContinuousLinearMap.opTrace (recoverySurgeryHilbertFlow n ⟨q.val,⟨q.property.1,q.property.2.le⟩⟩) =
      q.val/(1-q.val) := by
  rw [recoverySurgeryHilbertFlow_eq]
  exact cubicHilbertStrictFlow_trace q

def recoverySurgeryHeatOperator (n : ℕ) (u : ℝ) :
    cubicDefectHilbert →L[ℝ] cubicDefectHilbert :=
  recoverySurgeryHilbertFlow n ⟨Real.exp (-Real.exp u),
    ⟨(cubicCuspHeat_parameter u).1.le,(cubicCuspHeat_parameter u).2.le⟩⟩

theorem recoverySurgeryHeatOperator_eq (n : ℕ) (u : ℝ) :
    recoverySurgeryHeatOperator n u=cubicHilbertHeatOperator u := by
  rw [recoverySurgeryHeatOperator,recoverySurgeryHilbertFlow_eq]
  rfl

def recoverySurgeryResponseKernel (n : ℕ) (t : ℝ) : ℂ :=
  if 0<t then ((cubicCuspContinuousHeat t-
    ContinuousLinearMap.opTrace (recoverySurgeryHeatOperator n (Real.log t)) : ℝ) : ℂ) else 0

theorem recoverySurgeryResponseKernel_eq (n : ℕ) :
    recoverySurgeryResponseKernel n=cubicHilbertResponseKernel := by
  funext t
  simp only [recoverySurgeryResponseKernel,cubicHilbertResponseKernel,recoverySurgeryHeatOperator_eq]

theorem recoverySurgeryResponseKernel_converges (n : ℕ) :
    ∀ s ∈ fusionMellinStrip, MellinConvergent (recoverySurgeryResponseKernel n) s := by
  rw [recoverySurgeryResponseKernel_eq]
  exact cubicHilbertResponseKernel_converges

theorem recoverySurgeryResponseKernel_mellin (n : ℕ) :
    EqOn (mellin (recoverySurgeryResponseKernel n)) (fun s => -Complex.Gamma s*riemannZeta s)
      fusionMellinStrip := by
  rw [recoverySurgeryResponseKernel_eq]
  exact cubicHilbertResponseKernel_mellin

theorem recoverySurgeryResponseKernel_analytic (n : ℕ) :
    AnalyticOnNhd ℂ (mellin (recoverySurgeryResponseKernel n)) fusionMellinStrip := by
  rw [recoverySurgeryResponseKernel_eq]
  exact cubicHilbertResponseKernel_analytic

theorem recoverySurgeryResponseKernel_zeroLocus (n : ℕ) :
    {s ∈ fusionMellinStrip | mellin (recoverySurgeryResponseKernel n) s=0} =
      {s ∈ fusionMellinStrip | riemannZeta s=0} := by
  rw [recoverySurgeryResponseKernel_eq]
  exact cubicHilbertResponseKernel_zeroLocus

theorem recoverySurgeryResponseKernel_zeroMultiplicity (n : ℕ) :
    EqOn (analyticOrderAt (mellin (recoverySurgeryResponseKernel n)))
      (analyticOrderAt riemannZeta) fusionMellinStrip := by
  rw [recoverySurgeryResponseKernel_eq]
  exact cubicHilbertResponseKernel_zeroMultiplicity

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
