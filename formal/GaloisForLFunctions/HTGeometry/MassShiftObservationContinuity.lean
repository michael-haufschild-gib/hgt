import GaloisForLFunctions.HTGeometry.OuterShiftAvoidance

/-!
# The observation is jointly continuous in the mass parameter and the shift

The jets of a discrete Cauchy transform at the combined nodes are a weighted kernel series.  A real
translation does not move the imaginary part of a node, so the kernel bound is uniform in the shift,
and the series converges locally uniformly in the mass parameter and the shift together.

This is the joint continuity the tube lemma needs to make patchwise avoidance an *open* condition on
the mass parameter.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- **Joint continuity of the shifted jet packet.** -/
theorem continuous_shiftedJetPacket_expParameter {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (ord : row × Fin r → ℕ) (x : ℕ → ℝ) {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) :
    Continuous fun p : MassParameter × (Fin r → ℝ) =>
      discreteJetPacket (combinedNodes z p.2) ord x fun n => ε n * Real.exp (p.1 n) := by
  classical
  refine continuous_pi fun v => ?_
  set k : ℕ := (v.2 : ℕ) with hk
  set C : ℝ := (|(z v.1.1).im|⁻¹) ^ (k + 1) with hC
  have hCnn : 0 ≤ C := by positivity
  have hzim : ∀ t : Fin r → ℝ, (combinedNodes z t v.1).im ≠ 0 := fun t =>
    (im_combinedNodes_pos hupper t v.1).ne'
  have hKle : ∀ (n : ℕ) (t : Fin r → ℝ),
      ‖(((x n : ℝ) : ℂ) - combinedNodes z t v.1)⁻¹ ^ (k + 1)‖ ≤ C := by
    intro n t
    have hbound := norm_kernelPow_le (hzim t) k (x n)
    rwa [im_combinedNodes] at hbound
  have hform : ∀ p : MassParameter × (Fin r → ℝ),
      discreteJetPacket (combinedNodes z p.2) ord x (fun n => ε n * Real.exp (p.1 n)) v
        = ((Nat.factorial k : ℕ) : ℂ) * ∑' n, ((ε n * Real.exp (p.1 n) : ℝ) : ℂ)
          * (((x n : ℝ) : ℂ) - combinedNodes z p.2 v.1)⁻¹ ^ (k + 1) := by
    intro p
    haveI := isFiniteMeasure_countableWeightedDirac (x := x)
      (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le)
      (summable_expParameter (fun n => (hεpos n).le) hε p.1)
    exact iteratedDeriv_cauchyTransform_countableWeightedDirac
      (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le) k (hzim p.2)
  simp only [hform]
  refine continuous_const.mul ?_
  rw [continuous_iff_continuousAt]
  intro p₀
  set M : ℝ := ‖p₀.1‖ + 1 with hM
  have hopen : IsOpen (Metric.ball p₀.1 1 ×ˢ (Set.univ : Set (Fin r → ℝ))) :=
    Metric.isOpen_ball.prod isOpen_univ
  have hmem : p₀ ∈ Metric.ball p₀.1 1 ×ˢ (Set.univ : Set (Fin r → ℝ)) :=
    ⟨Metric.mem_ball_self one_pos, Set.mem_univ _⟩
  have hcon : ContinuousOn (fun p : MassParameter × (Fin r → ℝ) =>
      ∑' n, ((ε n * Real.exp (p.1 n) : ℝ) : ℂ)
        * (((x n : ℝ) : ℂ) - combinedNodes z p.2 v.1)⁻¹ ^ (k + 1))
      (Metric.ball p₀.1 1 ×ˢ (Set.univ : Set (Fin r → ℝ))) := by
    refine continuousOn_tsum (fun n => ?_) (hε.mul_right (Real.exp M * C)) fun n p hp => ?_
    · refine Continuous.continuousOn (Continuous.mul ?_ ?_)
      · exact Complex.continuous_ofReal.comp (continuous_const.mul
          ((Real.continuous_exp.comp (continuous_massParameter_apply n)).comp continuous_fst))
      · refine Continuous.pow (Continuous.inv₀ ?_ ?_) _
        · exact continuous_const.sub
            ((contDiff_combinedNodes z v.1).continuous.comp continuous_snd)
        · intro p hzero
          have him : (combinedNodes z p.2 v.1).im = 0 := by
            have hc := congrArg Complex.im hzero
            simpa using hc.symm
          exact hzim p.2 him
    · have hunorm : ‖p.1‖ ≤ M := by
        have hd : dist p.1 p₀.1 < 1 := Metric.mem_ball.mp hp.1
        have hsub := norm_sub_norm_le p.1 p₀.1
        rw [dist_eq_norm] at hd
        linarith
      have hexp : Real.exp (p.1 n) ≤ Real.exp M := by
        refine Real.exp_le_exp.mpr ?_
        have hle : ‖((p.1 : MassParameter) : ℕ → ℝ) n‖ ≤ ‖p.1‖ :=
          lp.norm_apply_le_norm (by simp) p.1 n
        rw [Real.norm_eq_abs] at hle
        exact le_trans (le_trans (le_abs_self _) hle) hunorm
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (hεpos n).le (Real.exp_nonneg _))]
      have hstep : ε n * Real.exp (p.1 n) ≤ ε n * Real.exp M :=
        mul_le_mul_of_nonneg_left hexp (hεpos n).le
      calc ε n * Real.exp (p.1 n)
            * ‖(((x n : ℝ) : ℂ) - combinedNodes z p.2 v.1)⁻¹ ^ (k + 1)‖
          ≤ ε n * Real.exp M * C := by
            refine mul_le_mul hstep (hKle n p.2) (norm_nonneg _) ?_
            exact mul_nonneg (hεpos n).le (Real.exp_nonneg _)
        _ = ε n * (Real.exp M * C) := by ring
  exact hcon.continuousAt (hopen.mem_nhds hmem)

/-- The observation as a function of the bounded exponential mass parameter and the shift. -/
def massShiftObservation {row : Type*} (z : row → ℂ) {r : ℕ} (d : ℕ) (x ε : ℕ → ℝ)
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (p : MassParameter × (Fin r → ℝ)) : (Σ _ : row × Fin r, Fin (d + 1)) → ℂ :=
  outerJetSigma (fun _ : row × Fin r => d)
    (discreteJetPacket (combinedNodes z p.2) (fun _ : row × Fin r => d + 1) x
      fun n => ε n * Real.exp (p.1 n)) + carrier p.2

/-- **The observation is jointly continuous.** -/
theorem continuous_massShiftObservation {row : Type*} [Fintype row] {z : row → ℂ}
    (hupper : ∀ b, 0 < (z b).im) {r : ℕ} (d : ℕ) (x : ℕ → ℝ) {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Summable ε)
    {carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ)}
    (hcarrier : Continuous carrier) :
    Continuous (massShiftObservation z d x ε carrier) := by
  have hJ : Continuous fun p : MassParameter × (Fin r → ℝ) =>
      discreteJetPacket (combinedNodes z p.2) (fun _ : row × Fin r => d + 1) x
        fun n => ε n * Real.exp (p.1 n) :=
    continuous_shiftedJetPacket_expParameter hupper _ x hεpos hε
  have hmaps : ∀ p : MassParameter × (Fin r → ℝ),
      (discreteJetPacket (combinedNodes z p.2) (fun _ : row × Fin r => d + 1) x
        fun n => ε n * Real.exp (p.1 n)) ∈ outerJetSigmaDomain (fun _ : row × Fin r => d) := by
    intro p i
    exact discreteJetPacket_zero_add_I_ne_zero (combinedNodes z p.2)
      (fun w => im_combinedNodes_pos hupper p.2 w) (fun _ : row × Fin r => d) x
      (fun n => (mul_pos (hεpos n) (Real.exp_pos _)).le)
      (summable_expParameter (fun n => (hεpos n).le) hε p.1) i
  have hchart : Continuous fun p : MassParameter × (Fin r → ℝ) =>
      outerJetSigma (fun _ : row × Fin r => d)
        (discreteJetPacket (combinedNodes z p.2) (fun _ : row × Fin r => d + 1) x
          fun n => ε n * Real.exp (p.1 n)) :=
    (continuousOn_outerJetSigma (fun _ : row × Fin r => d)).comp_continuous hJ hmaps
  exact hchart.add (hcarrier.comp continuous_snd)

/-- **The finite mass slice is the observation at a shifted parameter.** -/
theorem massShiftObservation_pertParameter {row : Type*} (z : row → ℂ) {r : ℕ} (d : ℕ)
    (x : ℕ → ℝ) {ε : ℕ → ℝ}
    (carrier : (Fin r → ℝ) → ((Σ _ : row × Fin r, Fin (d + 1)) → ℂ))
    (u : MassParameter) {K : ℕ} {a : Fin K → ℕ} (ha : Function.Injective a) {s : Fin K → ℝ}
    {c : ℝ} (hc : 0 ≤ c) (hs : ∀ k, |s k| ≤ c) (t : Fin r → ℝ) :
    massShiftObservation z d x ε carrier (u + pertParameter a s ha hc hs, t)
      = outerShiftObservation z d x (fun n => ε n * Real.exp (u n)) a carrier (s, t) := by
  have hweq : (fun n => ε n * Real.exp (((u + pertParameter a s ha hc hs : MassParameter) :
        ℕ → ℝ) n))
      = perturbedWeight a s fun n => ε n * Real.exp ((u : ℕ → ℝ) n) := by
    funext n
    have hcoe : ((u + pertParameter a s ha hc hs : MassParameter) : ℕ → ℝ) n
        = (u : ℕ → ℝ) n + pertSeq a s n := by
      rw [lp.coeFn_add]
      rfl
    rw [hcoe, perturbedWeight_eq_expParameter]
  show outerJetSigma (fun _ : row × Fin r => d)
      (discreteJetPacket (combinedNodes z t) (fun _ : row × Fin r => d + 1) x
        fun n => ε n * Real.exp (((u + pertParameter a s ha hc hs : MassParameter) : ℕ → ℝ) n))
      + carrier t = _
  rw [hweq]
  rfl

end

end GaloisForLFunctions.HTGeometry
