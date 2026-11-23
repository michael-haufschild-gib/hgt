import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OccupationGaps
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.OmittedEigenvector
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.Stability.ShellBoundary

/-! # Recovering the whole occupation spectrum from two scalar readings

Each adjacent pair of squared amplitudes excludes an interval of the graph
of the fourth power. The shell omissions reach its endpoints in the closure.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap

/-- The squared-operator measurement resolves every gap between adjacent occupations. -/
theorem squared_error_gap (G : Propagator) (k : ℕ) :
    let q := ‖criticalOperator^2-G.val^2‖
    let a := occupationWeight k
    let b := occupationWeight (k+1)
    2*(a+b)*q ≤ traceLoss G.val+q^2+2*a*b := by
  dsimp only
  by_cases hzero : criticalOperator^2-G.val^2 = 0
  · rw [hzero,norm_zero,mul_zero,zero_pow two_ne_zero,add_zero]
    have hnn := (sq_nonneg ‖criticalOperator^2-G.val^2‖).trans (square_trace_stability G).2
    exact add_nonneg hnn (mul_nonneg (mul_nonneg (by norm_num) (occupationWeight_pos k).le)
      (occupationWeight_pos (k+1)).le)
  obtain ⟨f,hf,hm,ht⟩ := omitted_top_moments G hzero
  have h := occupation_moment_gap k f
  rw [hf,one_pow,mul_one,hm] at h
  linarith only [h,ht]

/-- A closed inequality in the measured propagator error and the fourth-trace deficit. -/
theorem observed_gap (k : ℕ) (z : {z : ℝ × ℝ // z ∈ closure errorReadings}) :
    (occupationWeight k+occupationWeight (k+1))*z.val.1^2 ≤
      z.val.2+occupationWeight k*occupationWeight (k+1) := by
  let a := occupationWeight k
  let b := occupationWeight (k+1)
  have hc : IsClosed {w : ℝ × ℝ | (a+b)*w.1^2 ≤ w.2+a*b} :=
    isClosed_le (continuous_const.mul (continuous_fst.pow 2)) (continuous_snd.add continuous_const)
  have hs : errorReadings ⊆ {w : ℝ × ℝ | (a+b)*w.1^2 ≤ w.2+a*b} := by
    rintro _ ⟨G,rfl⟩
    obtain ⟨hp,hq⟩ := square_trace_stability G
    have hx := (positive_square_comparison critical_isPositive G.property.1 hp).2.2
    have hn := mul_le_mul_of_nonneg_left hx (add_nonneg (occupationWeight_pos k).le (occupationWeight_pos (k+1)).le)
    have hg := squared_error_gap G k
    change (a+b)*‖criticalOperator-G.val‖^2 ≤ traceLoss G.val+a*b
    dsimp only at hg
    dsimp only [a,b]
    linarith only [hn,hq,hg]
  exact (hc.closure_subset_iff.mpr hs) z.property

private theorem no_gap (t : ℝ) (ht : 0 < t) (hu : t ≤ 1)
    (h : ∀ k, (occupationWeight k+occupationWeight (k+1))*t ≤ t^2+occupationWeight k*occupationWeight (k+1)) :
    ∃ k, t = occupationWeight k := by
  classical
  have hex : ∃ j, occupationWeight j < t := (occupationWeight_tendsto.eventually_lt_const ht).exists
  let m := Nat.find hex
  have hm : occupationWeight m < t := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro e
    rw [e,occupationWeight_zero] at hm
    exact (not_lt_of_ge hu) hm
  obtain ⟨k,hk⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hprev : t ≤ occupationWeight k := le_of_not_gt (Nat.find_min hex (show k < m by omega))
  rw [hk] at hm
  refine ⟨k,le_antisymm hprev (le_of_not_gt fun e => ?_)⟩
  have hp := mul_neg_of_neg_of_pos (sub_neg.mpr e) (sub_pos.mpr hm)
  linarith only [h k,hp]

/-- The nonzero contacts with the fourth-power bound recover exactly all positive integer shells. -/
theorem boundary_spectrum_iff (x : ℝ) :
    (x,x^4) ∈ closure errorReadings ↔ x = 0 ∨ ∃ n : ℕ+, x = attenuation n := by
  constructor
  · intro hx
    have hs : errorReadings ⊆ Prod.fst ⁻¹' Set.Icc (0:ℝ) 1 := by
      rintro _ ⟨G,rfl⟩
      exact ⟨norm_nonneg _,(trace_stability G).2.1⟩
    have hI : x ∈ Set.Icc (0:ℝ) 1 :=
      ((isClosed_Icc.preimage (continuous_fst : Continuous (Prod.fst : ℝ × ℝ → ℝ))).closure_subset_iff.mpr hs) hx
    rcases hI.1.eq_or_lt with h0 | hpos
    · exact Or.inl h0.symm
    right
    have hu : x^2 ≤ 1 := (pow_le_pow_left₀ hpos.le hI.2 2).trans_eq (one_pow 2)
    have hg (k : ℕ) := observed_gap k ⟨(x,x^4),hx⟩
    obtain ⟨k,hk⟩ := no_gap (x^2) (sq_pos_of_pos hpos) hu (fun k => by
      simpa only [← pow_mul] using hg k)
    exact ⟨number k,(pow_left_inj₀ hpos.le (attenuation_pos _).le two_ne_zero).mp hk⟩
  · rintro (rfl | ⟨n,rfl⟩)
    · have hh := (positive_fourth_iff criticalOperator).mpr rfl
      apply subset_closure
      refine ⟨⟨criticalOperator,hh.1,hh.2.1⟩,?_⟩
      simp only [traceLoss,hh.2.2,sub_self,norm_zero,zero_pow (by decide : 4 ≠ 0)]
    · exact shell_boundary n

#print axioms squared_error_gap
#print axioms observed_gap
#print axioms boundary_spectrum_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
