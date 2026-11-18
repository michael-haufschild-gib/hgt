import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeCauchyDephasing
import GaloisForLFunctions.RHTower.ModularArcDyadicHarmonicLaplacianSubharmonicModulus
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
# The weak-step limit of Cauchy dephasing of Weil probes

Dividing the log rates by √N and iterating N times gives the Gaussian
squared-gap multiplier of Donadi–Lobo–Fadel, arXiv:2611.17260, equations
(5)–(7). The finite-step logarithm approaches the Gaussian exponent from
above, with an explicit fourth-power error valid at all separations.
-/

noncomputable section
open Filter Matrix
open scoped Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
open HilbertMetric.CauchyDephasing

private theorem log_cosh_remainder (x : ℝ) :
    let u := x^2/2
    0 ≤ u-Real.log (Real.cosh x) ∧ u-Real.log (Real.cosh x) ≤ u^2 := by
  let u := x^2/2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hp : 0 < 1+u := by positivity
  have hlow : 1+u ≤ Real.cosh x := by
    dsimp [u]
    linarith only [_root_.RHTower.cosh_sub_one_sub_sq_div_two_nonneg x]
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hp)
  rw [Real.log_inv] at hlog
  have ht : (1+u)⁻¹ ≤ 1-u+u^2 := by
    rw [← one_div,div_le_iff₀ hp]
    nlinarith only [pow_nonneg hu 3]
  exact ⟨sub_nonneg.mpr ((Real.log_le_iff_le_exp (Real.cosh_pos x)).mpr
      (Real.cosh_le_exp_half_sq x)),by
    linarith only [ht,hlog,Real.log_le_log hp hlow]⟩

/-- Gaussian dephasing rate in the normalization of the Cauchy kernel. -/
def gapCost (s t : ℝ) : ℝ := (s-t)^2/8

/-- N = n+1 steps at log rates divided by √N. -/
def weakCoherence (n : ℕ) (s t : ℝ) : ℝ :=
  coherence (s / Real.sqrt (n+1:ℝ)) (t / Real.sqrt (n+1:ℝ)) ^ (n+1)

/-- Two-sided, nonasymptotic error in the negative logarithmic rate. -/
theorem weakCoherence_log_error (n : ℕ) (s t : ℝ) :
    0 ≤ Real.log (weakCoherence n s t) + gapCost s t ∧
      Real.log (weakCoherence n s t) + gapCost s t ≤ (gapCost s t)^2 / (n+1:ℝ) := by
  let N : ℝ := n+1
  let x := (s/Real.sqrt N-t/Real.sqrt N)/2
  have hN : 0 < N := by dsimp [N]; positivity
  have hroot : Real.sqrt N ≠ 0 := (Real.sqrt_pos.mpr hN).ne'
  have hx : x^2/2 = gapCost s t / N := by
    dsimp only [x,gapCost]
    rw [← sub_div,div_pow,div_pow,Real.sq_sqrt hN.le]
    ring
  have he : Real.log (weakCoherence n s t) = -N*Real.log (Real.cosh x) := by
    simp only [weakCoherence,coherence_eq_cosh_inv,Real.log_pow,Real.log_inv,N,x,
      Nat.cast_add,Nat.cast_one,neg_mul,mul_neg]
  obtain ⟨hl,hu⟩ := log_cosh_remainder x
  rw [hx] at hl hu
  rw [he]
  change 0 ≤ -N*_+_ ∧ -N*_+_ ≤ _/N
  have hfactor : -N*Real.log (Real.cosh x)+gapCost s t =
      N*(gapCost s t / N - Real.log (Real.cosh x)) := by
    field_simp [hN.ne']
    ring
  rw [hfactor]
  refine ⟨mul_nonneg hN.le hl, (mul_le_mul_of_nonneg_left hu hN.le).trans_eq ?_⟩
  field_simp [hN.ne']
  ring

/-- The exact continuous multiplier arising from infinitely many weak steps. -/
theorem weakCoherence_tendsto (s t : ℝ) :
    Tendsto (fun n => weakCoherence n s t) atTop (𝓝 (Real.exp (-gapCost s t))) := by
  have ht : Tendsto (fun n : ℕ => gapCost s t ^ 2 / (n+1:ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv,one_div,mul_zero] using
      tendsto_one_div_add_atTop_nhds_zero_nat.const_mul (gapCost s t ^ 2)
  have hzero := squeeze_zero (fun n => (weakCoherence_log_error n s t).1)
    (fun n => (weakCoherence_log_error n s t).2) ht
  have hlog := hzero.sub_const (gapCost s t)
  have h := Real.continuous_exp.continuousAt.tendsto.comp hlog
  have hpos (n : ℕ) : 0 < weakCoherence n s t := pow_pos (coherence_pos _ _) _
  simpa only [Function.comp_def,add_sub_cancel_right,zero_sub,Real.exp_log (hpos _)] using h

/-- The entire arithmetic matrix has a Gaussian dephasing limit for
arbitrary real labels, including labels shared by several probes. -/
theorem weak_probe_dephasing_limit {m : ℕ} (r : Fin m → ℝ) (p : Fin m → {x : ℝ // 1 ≤ x}) :
    Tendsto (fun n : ℕ => dephasedProbeGram (n+1) (fun i => r i/Real.sqrt (n+1:ℝ)) p)
      atTop (𝓝 (Matrix.of fun i j => (Real.exp (-gapCost (r i) (r j)) : ℂ) *
        probeGram (fun k => (p k).val) i j)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have h := (Complex.continuous_ofReal.continuousAt.tendsto.comp
    (weakCoherence_tendsto (r i) (r j))).mul_const (probeGram (fun k => (p k).val) i j)
  simpa only [dephasedProbeGram,channelPower,weakCoherence,Function.comp_def,Complex.ofReal_pow,
    Matrix.of_apply] using h

/-- Quadratic and quartic jumps are indistinguishable on an opposite-momentum
pair, whereas the linear jump leaves a nonzero decay rate away from zero. -/
theorem reflected_momentum_costs (p : ℝ) :
    gapCost p (-p) = p^2/2 ∧ gapCost (p^2) ((-p)^2) = 0 ∧ gapCost (p^4) ((-p)^4) = 0 := by
  unfold gapCost
  exact ⟨by ring,by ring,by ring⟩

/-- The two even jump rates determine the squared radii sum wherever the
quadratic rate distinguishes the momenta. The division-free identity
continues through the reflected-pair collision. -/
theorem quartic_gap_factor (p q : ℝ) :
    gapCost (p^4) (q^4) = gapCost (p^2) (q^2)*(p^2+q^2)^2 := by
  unfold gapCost
  ring

#print axioms weakCoherence_log_error
#print axioms weakCoherence_tendsto
#print axioms weak_probe_dephasing_limit
#print axioms reflected_momentum_costs
#print axioms quartic_gap_factor
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeWalk
