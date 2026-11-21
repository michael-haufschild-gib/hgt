import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.NearDiagonal
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.FirstWaitLaw
import GaloisForLFunctions.HTGeometry.PathCarrierSeparatingDirection
import GaloisForLFunctions.HTGeometry.GaussianIntervalPositivity

/-! # A positive-mass open set with a nearly linear Hilbert-dimension gate cap -/
open Set MeasureTheory ProbabilityTheory Filter Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds
open DiagonalSynthesis PrescribedTimes
noncomputable section

private theorem standardGaussian_openPos : Measure.IsOpenPosMeasure (gaussianReal 0 1) := by
  constructor
  rintro U hU ⟨x,hx⟩
  obtain ⟨r,hr,hball⟩ := Metric.isOpen_iff.mp hU x hx
  have hsub : Icc (x-r/2) (x+r/2) ⊆ U := by
    intro y hy
    apply hball
    rw [Metric.mem_ball,Real.dist_eq,abs_lt]
    constructor <;> linarith only [hy.1,hy.2,hr]
  exact ((gaussianReal_Icc_pos (show x-r/2<x+r/2 by linarith only [hr])).trans_le (measure_mono hsub)).ne'

/-- For each finite Gaussian prefix and every positive physical error, an
open set of positive disorder probability admits the diagonal circuit budget
for all real times, including after generic spectral phases have filled the torus. -/
theorem gaussian_open_all_time_gate_cap (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ O : Set (PrefixIndex n → ℝ), IsOpen O ∧
      0 < (Measure.pi (fun _ : PrefixIndex n => gaussianReal 0 1)) O ∧
      ∀ x ∈ O, ∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) ε (2^(n+2)*(2*(n+2)+1))
        (unitaryEvolution (numberedGenerator n x) t) := by
  let u := sepCarrier n 1 0
  let x₀ := fun i => u (pathCoeffEquiv n i)
  let d := fun i => ((pathDiagEnergy u i : ℝ) : ℂ)
  have hi : Function.Injective d := by
    intro i j he
    by_contra h
    have hgap := abs_sub_pathDiagEnergy_sepCarrier_ge (n := n) (A := 1) (b := 0) zero_le_one le_rfl h
    have he' : pathDiagEnergy u i = pathDiagEnergy u j := Complex.ofReal_injective he
    change 2*1-2*0*((n:ℝ)+1) ≤ |pathDiagEnergy u i-pathDiagEnergy u j| at hgap
    rw [he',sub_self,abs_zero] at hgap
    norm_num at hgap
  have hbase : numberedGenerator n x₀ = diagonal d :=
    (numberedGenerator_shell u).trans (pathHamiltonian_eq_diagonal u (sepCarrier_offDiag 1 0))
  have hcont : Continuous (numberedGenerator n) := by unfold numberedGenerator; fun_prop
  have hlim : Tendsto (numberedGenerator n) (𝓝 x₀) (𝓝 (diagonal d)) := hbase ▸ hcont.continuousAt
  have h := hlim.eventually (eventually_cheap_near_diagonal (by omega : 2 ≤ n+2) d hi hε)
  obtain ⟨O,hO,hopen,hx⟩ := mem_nhds_iff.mp h
  letI := standardGaussian_openPos
  refine ⟨O,hopen,hopen.measure_pos _ ⟨x₀,hx⟩,?_⟩
  intro x hx' t
  exact hO hx' (prefixGenerator n x).property t

#print axioms gaussian_open_all_time_gate_cap
end
end GaloisForLFunctions.HTGeometry.WeakBonds
