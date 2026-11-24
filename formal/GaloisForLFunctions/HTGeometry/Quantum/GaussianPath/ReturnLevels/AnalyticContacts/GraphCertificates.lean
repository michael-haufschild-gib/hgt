import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.VariableAccuracy.Affordable
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Frontier
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EigenlineSignals.AnalyticSignal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.CircuitCellAverage
import Mathlib.Data.Finsupp.Encodable

/-! # Analytic equations covering the graph of physical circuit distance -/

open Set Filter Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
open PhaseBoundary
noncomputable section

abbrev ErrorVars (N : ℕ) := Unit ⊕ (Bits N × Bits N × Bool)

private def values {N : ℕ} (H : selfAdjoint (Square (Bits N))) (p : ℝ × ℝ) : ErrorVars N → ℝ
  | .inl _ => p.2
  | .inr (i,j,b) => if b then ((unitaryEvolution H.val p.1) i j).im else
      ((unitaryEvolution H.val p.1) i j).re

/-- Rational certificate evaluated on time, error and physical matrix entries. -/
def certEval {N : ℕ} (H : selfAdjoint (Square (Bits N))) (z : ℝ × ℝ) :
    MvPolynomial (ErrorVars N) ℚ →+* ℝ :=
  MvPolynomial.eval₂Hom (Rat.castHom ℝ) (values H z)

private theorem analytic_value {N : ℕ} (H : selfAdjoint (Square (Bits N))) (i : ErrorVars N)
    (p : ℝ × ℝ) : AnalyticAt ℝ (fun z => values H z i) p := by
  rcases i with _|⟨i,j,b⟩
  · exact analyticAt_snd
  · let e : Square (Bits N) →ₗ[ℝ] ℂ :=
      { toFun := fun M => M i j, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
    let L := e.mkContinuous 1 fun M => (norm_entry_le_l2_opNorm M i j).trans_eq (one_mul ‖M‖).symm
    have h := (L.analyticAt _).comp ((EigenlineSignals.analytic_evolution H.val p.1).comp analyticAt_fst)
    cases b
    · exact (Complex.reCLM.analyticAt _).comp h
    · exact (Complex.imCLM.analyticAt _).comp h

theorem cert_analytic {N : ℕ} (H : selfAdjoint (Square (Bits N))) (P : MvPolynomial (ErrorVars N) ℚ)
    (z : ℝ × ℝ) : AnalyticAt ℝ (fun w => certEval H w P) z := by
  induction P using MvPolynomial.induction_on with
  | C r =>
    simp only [certEval,MvPolynomial.eval₂Hom_C]
    exact analyticAt_const
  | add p q hp hq => simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
    simpa only [map_mul,certEval,MvPolynomial.eval₂Hom_X'] using hp.mul (analytic_value H i z)

/-- A positive best error lies on a nontrivial analytic zero set in the
time-error plane. The family of certificates is the same countable ring
at every gate budget. -/
theorem distance_certificate {N : ℕ} (H : selfAdjoint (Square (Bits N))) (s : ℕ) (t : ℝ)
    (he : 0 < orbitCircuitDistance H s t) :
    ∃ P : MvPolynomial (ErrorVars N) ℚ, certEval H (t,orbitCircuitDistance H s t) P=0 ∧
      ∃ w : ℝ × ℝ, certEval H w P≠0 := by
  let U (x : ℝ × ℝ) := unitaryEvolution H.val x.1
  let ρ := certEval H
  let A := {x : ℝ × ℝ | HasProjectiveCircuitApproximation N |x.2| s (U x)}
  let e := orbitCircuitDistance H s t
  have repU : MatrixRep ρ U := fun i j =>
    ⟨⟨MvPolynomial.X (.inr (i,j,false)),fun _ => MvPolynomial.eval₂Hom_X' ..⟩,
     ⟨MvPolynomial.X (.inr (i,j,true)),fun _ => MvPolynomial.eval₂Hom_X' ..⟩⟩
  have repε : Represents ρ (fun x : ℝ × ℝ => x.2) :=
    ⟨MvPolynomial.X (.inl ()),fun _ => MvPolynomial.eval₂Hom_X' ..⟩
  have repSq : Represents ρ (fun x : ℝ × ℝ => |x.2|^2) := by
    simpa only [sq_abs,sq] using repε.mul repε
  have hc : LocallyCertified ρ A := VariableAccuracy.affordable_certified
    (fun P => continuous_iff_continuousAt.mpr fun z => (cert_analytic H P z).continuousAt)
    repU s (fun x => |x.2|) repSq (fun _ => abs_nonneg _)
  have hA : IsClosed A := by
    simp only [A,hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le ((orbitCircuitDistance_lipschitz H s).continuous.comp continuous_fst) continuous_snd.abs
  apply hc.frontier_witness hA
  constructor
  · apply subset_closure
    exact (hasProjectiveCircuitApproximation_iff_infDist ..).mpr (le_abs_self e)
  · intro hin
    obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp isOpen_interior _ hin
    let u := min (r/2) (e/2)
    have hu : 0 < u := lt_min (half_pos hr) (half_pos he)
    have hur : u < r := (min_le_left ..).trans_lt (half_lt_self hr)
    have hue : u < e := (min_le_right ..).trans_lt (half_lt_self he)
    have hnear : (t,e-u) ∈ Metric.ball (t,e) r := by
      rw [Metric.mem_ball,Prod.dist_eq,dist_self,Real.dist_eq,show e-u-e= -u by ring,abs_neg,
        abs_of_pos hu,max_eq_right hu.le]
      exact hur
    have ha := interior_subset (hball hnear)
    change HasProjectiveCircuitApproximation N |e-u| s (unitaryEvolution H.val t) at ha
    have h := (hasProjectiveCircuitApproximation_iff_infDist ..).mp ha
    change e ≤ |e-u| at h
    rw [abs_of_pos (sub_pos.mpr hue)] at h
    linarith only [h,hu]

#print axioms distance_certificate
end
end GaloisForLFunctions.HTGeometry.ReturnLevels.AnalyticContacts
