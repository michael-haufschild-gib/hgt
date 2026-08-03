import GaloisForLFunctions.HTGeometry.DiscreteJetObservationLocallySurjective

/-!
# The jet packet depends continuously on the mass parameter

Each coordinate of the jet packet of a discrete Cauchy transform is a factorial multiple of a series
over the atoms, with the masses as coefficients.  On any ball of parameters the masses are bounded by
their value at the centre times a fixed exponential, and the kernel powers are bounded off the real
axis, so the series converges uniformly there.

Continuity is a local statement, so this gives continuity of the whole packet in the parameter.
-/

open Filter Topology MeasureTheory
open _root_.HTGeometry

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem continuous_massParameter_apply (n : ℕ) :
    Continuous fun u : MassParameter => (u : ℕ → ℝ) n := by
  refine LipschitzWith.continuous (K := 1) (LipschitzWith.of_dist_le_mul fun u v => ?_)
  have hle : ‖((u - v : MassParameter) : ℕ → ℝ) n‖ ≤ ‖u - v‖ :=
    lp.norm_apply_le_norm (by simp) (u - v) n
  rw [lp.coeFn_sub] at hle
  simpa [Real.dist_eq, dist_eq_norm, abs_sub_comm] using hle

/-- **The jet packet is continuous in the mass parameter.** -/
theorem continuous_discreteJetPacket_expParameter {ι : Type*} [Fintype ι]
    (nodes : ι → ℂ) (hupper : ∀ i, 0 < (nodes i).im) (ord : ι → ℕ) (x : ℕ → ℝ)
    {ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) :
    Continuous fun u : MassParameter =>
      discreteJetPacket nodes ord x fun n => ε n * Real.exp (u n) := by
  classical
  refine continuous_pi fun t => ?_
  set k : ℕ := (t.2 : ℕ) with hk
  set z : ℂ := nodes t.1 with hz
  have hzim : z.im ≠ 0 := (hupper t.1).ne'
  set K : ℕ → ℂ := fun n => (((x n : ℝ) : ℂ) - z)⁻¹ ^ (k + 1) with hK
  set C : ℝ := (|z.im|⁻¹) ^ (k + 1) with hC
  have hKle : ∀ n, ‖K n‖ ≤ C := fun n => norm_kernelPow_le hzim k (x n)
  have hform : ∀ u : MassParameter,
      discreteJetPacket nodes ord x (fun n => ε n * Real.exp (u n)) t
        = ((Nat.factorial k : ℕ) : ℂ)
          * ∑' n, ((ε n * Real.exp (u n) : ℝ) : ℂ) * K n := by
    intro u
    haveI := isFiniteMeasure_countableWeightedDirac (x := x)
      (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le)
      (summable_expParameter (fun n => (hεpos n).le) hε u)
    exact iteratedDeriv_cauchyTransform_countableWeightedDirac
      (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le) k hzim
  simp only [hform]
  refine continuous_const.mul ?_
  rw [continuous_iff_continuousAt]
  intro u₀
  set M : ℝ := ‖u₀‖ + 1 with hM
  have hCnn : 0 ≤ C := by positivity
  have hcon : ContinuousOn (fun u : MassParameter =>
      ∑' n, ((ε n * Real.exp (u n) : ℝ) : ℂ) * K n) (Metric.ball u₀ 1) := by
    refine continuousOn_tsum (fun n => ?_) (hε.mul_right (Real.exp M * C)) fun n u hu => ?_
    · refine Continuous.continuousOn ?_
      exact (Complex.continuous_ofReal.comp
        (continuous_const.mul (Real.continuous_exp.comp (continuous_massParameter_apply n)))).mul
        continuous_const
    · have hunorm : ‖u‖ ≤ M := by
        have hd : dist u u₀ < 1 := Metric.mem_ball.mp hu
        have := norm_sub_norm_le u u₀
        rw [dist_eq_norm] at hd
        linarith
      have huval : (u : ℕ → ℝ) n ≤ M := by
        have hle : ‖(u : ℕ → ℝ) n‖ ≤ ‖u‖ := lp.norm_apply_le_norm (by simp) u n
        rw [Real.norm_eq_abs] at hle
        exact le_trans (le_trans (le_abs_self _) hle) hunorm
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (hεpos n).le (Real.exp_nonneg _))]
      have hexp : Real.exp ((u : ℕ → ℝ) n) ≤ Real.exp M := Real.exp_le_exp.mpr huval
      calc ε n * Real.exp ((u : ℕ → ℝ) n) * ‖K n‖
          ≤ ε n * Real.exp M * C := by
            refine mul_le_mul ?_ (hKle n) (norm_nonneg _)
              (mul_nonneg (hεpos n).le (Real.exp_nonneg _))
            exact mul_le_mul_of_nonneg_left hexp (hεpos n).le
        _ = ε n * (Real.exp M * C) := by ring
  exact hcon.continuousAt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self one_pos))

end

end GaloisForLFunctions.HTGeometry
