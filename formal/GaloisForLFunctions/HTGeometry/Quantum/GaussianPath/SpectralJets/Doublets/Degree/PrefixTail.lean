import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Doublets.Degree.PhysicalTail
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrefixCoordinates

/-! # A simultaneous lower bound on the trace minors of a single Gaussian sample -/
open MvPolynomial MeasureTheory ProbabilityTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
noncomputable section

/-- The column choice depends only on the number of spins. -/
def traceColumns (n : ℕ) : Fin (2^(n+1)) → Fin (2^(n+2)) :=
  (physicalTrace_lower_tail n).choose

def prefixTrace (n : ℕ) (ω : PathPauliDisorder) : ℂ :=
  eval₂Hom GaussianInt.toComplex (fun i => (pathPauliDisorderShell ω n (pathCoeffEquiv n i):ℂ))
    (physicalTrace n (traceColumns n))

/-- Outside a single event of probability at most δ, every prefix of at least two
spins clears its explicit threshold. Prefixes may overlap arbitrarily. -/
theorem gaussian_all_prefixes_trace_lower_tail {δ : ℝ} (hδ : 0<δ) (hδ' : δ≤1) :
    pathPauliDisorderLaw {ω | ∃ n : ℕ,
      ‖prefixTrace n ω‖ < (δ/2*(1/2:ℝ)^n/(1+2*(traceDegreeBound n:ℝ)))^(traceDegreeBound n)} ≤
      ENNReal.ofReal δ := by
  let r (n : ℕ) := δ/2*(1/2:ℝ)^n/(1+2*(traceDegreeBound n:ℝ))
  let bad (n : ℕ) : Set (Coordinates (n+2) → ℝ) := {x |
    ‖eval₂Hom GaussianInt.toComplex (fun i => (x i:ℂ)) (physicalTrace n (traceColumns n))‖ <
      (r n)^(traceDegreeBound n)}
  let π (n : ℕ) (ω : PathPauliDisorder) := fun i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hm (n : ℕ) : pathPauliDisorderLaw (π n ⁻¹' bad n) ≤
      ENNReal.ofReal (δ/2) * (2⁻¹:ℝ≥0∞)^n := by
    let B : ℝ := traceDegreeBound n
    have hB : 0 ≤ B := Nat.cast_nonneg _
    have hd : 0 < 1+2*B := by positivity
    have hpow : (1/2:ℝ)^n ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hp : 0 ≤ δ/2*(1/2:ℝ)^n := by positivity
    have hr : 0<r n := by dsimp [r]; positivity
    have hr' : r n ≤ 1 := by
      apply (div_le_iff₀ hd).mpr
      have hp' := mul_le_one₀ (show δ/2≤1 by linarith only [hδ']) (by positivity) hpow
      linarith only [hB,hp']
    have hmp := gaussian_pauli_prefix_coordinates_law n
    refine (Measure.le_map_apply hmp.measurable.aemeasurable (bad n)).trans ?_
    rw [hmp.map_eq]
    refine ((physicalTrace_lower_tail n).choose_spec hr hr').trans ?_
    have hprice : 2*B*r n ≤ δ/2*(1/2:ℝ)^n := by
      change 2*B*(_/_) ≤ _
      rw [← mul_div_assoc]
      apply (div_le_iff₀ hd).mpr
      linarith only [hp]
    refine (ENNReal.ofReal_le_ofReal hprice).trans_eq ?_
    rw [ENNReal.ofReal_mul (by positivity : 0≤δ/2),ENNReal.ofReal_pow (by norm_num : (0:ℝ)≤1/2),
      one_div,ENNReal.ofReal_inv_of_pos (by norm_num : (0:ℝ)<2)]
    norm_num
  suffices h : pathPauliDisorderLaw (⋃ n, π n ⁻¹' bad n) ≤ ENNReal.ofReal δ by
    exact (measure_mono fun _ hω => Set.mem_iUnion.mpr hω).trans h
  refine (measure_iUnion_le _).trans ((ENNReal.tsum_le_tsum hm).trans_eq ?_)
  rw [ENNReal.tsum_mul_left,ENNReal.tsum_geometric_two]
  calc
    _ = ENNReal.ofReal (δ/2*2) := by rw [ENNReal.ofReal_mul (by positivity : 0≤δ/2)]; norm_num
    _ = _ := by rw [div_mul_cancel₀ _ (by norm_num : (2:ℝ)≠0)]

#print axioms gaussian_all_prefixes_trace_lower_tail
end
end GaloisForLFunctions.HTGeometry.SpectralJets.Doublets
