import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Affordable
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.Frontier
import GaloisForLFunctions.HTGeometry.Quantum.PhysicalCircuitReturnDeadline
import Mathlib.Data.Finsupp.Encodable

/-! # The affordable frontier on a dense analytic matrix trajectory is invariant-null -/
open MeasureTheory Filter Set Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary
noncomputable section

private abbrev TargetVar (N : ℕ) := Unit ⊕ (Bits N × Bits N × Bool)

private def targetValue {N : ℕ} (U : Square (Bits N)) (ε : ℝ) : TargetVar N → ℝ
  | .inl _ => ε
  | .inr (i,j,b) => if b then (U i j).im else (U i j).re

/-- At any fixed error, including a possible atom of the distance
distribution, the boundary of the affordable set has zero invariant measure. -/
theorem affordable_null_frontier {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {N : ℕ} (μ : Measure X) [SFinite μ] (τ : ℝ → X → X)
    (hm : Measurable fun p : X × ℝ => τ p.2 p.1)
    (hinv : ∀ t, MeasurePreserving (τ t) μ μ) (hd : ∀ x, DenseRange fun t => τ t x)
    (U : X → Square (Bits N)) (hU : Continuous U)
    (ha : ∀ x i j, AnalyticOnNhd ℝ (fun t => (U (τ t x) i j).re) univ ∧
      AnalyticOnNhd ℝ (fun t => (U (τ t x) i j).im) univ) (s : ℕ) (ε : ℝ) :
    μ (frontier {x | HasProjectiveCircuitApproximation N ε s (U x)}) = 0 := by
  let A := MvPolynomial (TargetVar N) ℚ
  let ρ (x : X) : A →+* ℝ := MvPolynomial.eval₂Hom (Rat.castHom ℝ) (targetValue (U x) ε)
  letI : Countable A := AddMonoidAlgebra.coeff_injective.countable
  have evalC (x : X) (r : ℚ) : ρ x (MvPolynomial.C r) = (r:ℝ) := MvPolynomial.eval₂Hom_C ..
  have evalX (x : X) (i : TargetVar N) : ρ x (MvPolynomial.X i) = targetValue (U x) ε i :=
    MvPolynomial.eval₂Hom_X' ..
  have hc0 (i : TargetVar N) : Continuous (fun x => targetValue (U x) ε i) := by
    rcases i with a|⟨i,j,b⟩
    · exact continuous_const
    · cases b
      · exact Complex.continuous_re.comp ((continuous_apply j).comp ((continuous_apply i).comp hU))
      · exact Complex.continuous_im.comp ((continuous_apply j).comp ((continuous_apply i).comp hU))
  have hc (p : A) : Continuous (fun x => ρ x p) := by
    induction p using MvPolynomial.induction_on with
    | C r => simpa only [evalC] using (continuous_const (y := (r:ℝ)))
    | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
    | mul_X p i hp => simpa only [map_mul,evalX,Pi.mul_def] using hp.mul (hc0 i)
  have han (x : X) (p : A) : AnalyticOnNhd ℝ (fun t => ρ (τ t x) p) univ := by
    have hvar (i : TargetVar N) : AnalyticOnNhd ℝ (fun t => targetValue (U (τ t x)) ε i) univ := by
      rcases i with a|⟨i,j,b⟩
      · exact analyticOnNhd_const
      · cases b
        · exact (ha x i j).1
        · exact (ha x i j).2
    induction p using MvPolynomial.induction_on with
    | C r => simp only [evalC]; exact analyticOnNhd_const
    | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
    | mul_X p i hp => simpa only [map_mul,evalX,Pi.mul_def] using hp.mul (hvar i)
  have hrepr : MatrixRep ρ U := by
    intro i j
    exact ⟨⟨MvPolynomial.X (.inr (i,j,false)),fun _ => MvPolynomial.eval₂Hom_X' ..⟩,
      ⟨MvPolynomial.X (.inr (i,j,true)),fun _ => MvPolynomial.eval₂Hom_X' ..⟩⟩
  have herr : Represents ρ (fun _ => ε) := ⟨MvPolynomial.X (.inl ()),fun _ => MvPolynomial.eval₂Hom_X' ..⟩
  have hcls : IsClosed {x | HasProjectiveCircuitApproximation N ε s (U x)} := by
    simp only [hasProjectiveCircuitApproximation_iff_infDist]
    exact isClosed_le ((Metric.continuous_infDist_pt _).comp hU) continuous_const
  exact (affordable_certified hc hrepr s ε herr).frontier_null hcls μ
    (fun p hn => null_flow_zeros μ τ hm hinv hd _ (hc p) hn (fun x => han x p))

#print axioms affordable_null_frontier
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary
