import GaloisForLFunctions.HTGeometry.KleinGordonFieldSolutionMap
import GaloisForLFunctions.HTGeometry.IntegralGronwall

/-!
# The solution depends continuously on the perturbation

Every stability statement so far varies the Cauchy data and keeps the equation fixed. For an inverse
problem the interesting variation is the other one: how much does the observed field move when the
potential moves?

Subtracting the two Duhamel formulas and splitting `W₁u₁ - W₂u₂ = (W₁-W₂)u₁ + W₂(u₁-u₂)` gives an
integral inequality for `‖u₁(t) - u₂(t)‖` whose inhomogeneous term is proportional to `‖W₁ - W₂‖` and
whose kernel is the constant `‖W₂‖`. The corpus's integral Grönwall inequality closes it, and the
answer is Lipschitz in the perturbation:

`‖u₁(t) - u₂(t)‖ ≤ ‖W₁ - W₂‖ (‖f‖+‖h‖) |t| e^{2b|t|}`.

The bound vanishes at `t = 0` and grows only linearly for short times, so on a fixed time interval
the map from the equation to the field it produces is Lipschitz, uniformly over data of bounded
norm. Passing to a limit, a norm-convergent sequence of potentials produces a convergent sequence of
fields.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set Filter Topology

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

section Stability

variable {W₁ W₂ : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b δ : ℝ}

/-- The difference of two solutions with different perturbations, in Duhamel form. The source term
of the difference is the difference of the potentials applied to the first solution; the memory term
is the second potential applied to the difference. -/
theorem kgFieldMild_sub_potential (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (f h : Lp ℂ 2 (volume : Measure E)) (x : ℝ) :
    kgFieldMild W₁ f h x - kgFieldMild W₂ f h x
      = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₁ f h s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₂ (kgFieldMild W₁ f h s - kgFieldMild W₂ f h s)) := by
  have hc1 := continuous_kgFieldMild hb0 hW₁ f h
  have hc2 := continuous_kgFieldMild hb0 hW₂ f h
  have hk1 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) (W₁.continuous.comp hc1)
  have hk2 : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id) (W₂.continuous.comp hc2)
  have hA : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₁ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      ((W₁ - W₂).continuous.comp hc1)
  have hB : Continuous fun s : ℝ =>
      kgSinFreqOp (x - s) (W₂ (kgFieldMild W₁ f h s - kgFieldMild W₂ f h s)) :=
    continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
      (W₂.continuous.comp (hc1.sub hc2))
  have hsum : (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (kgFieldMild W₁ f h s)))
        + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s)
            (W₂ (kgFieldMild W₁ f h s - kgFieldMild W₂ f h s))
      = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f h s)))
        - ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f h s)) := by
    rw [← intervalIntegral.integral_add (hA.intervalIntegrable (μ := volume) 0 x)
      (hB.intervalIntegrable (μ := volume) 0 x),
      ← intervalIntegral.integral_sub (hk1.intervalIntegrable (μ := volume) 0 x)
      (hk2.intervalIntegrable (μ := volume) 0 x)]
    refine intervalIntegral.integral_congr fun s _ => ?_
    have hvec : (W₁ - W₂) (kgFieldMild W₁ f h s)
        + W₂ (kgFieldMild W₁ f h s - kgFieldMild W₂ f h s)
        = W₁ (kgFieldMild W₁ f h s) - W₂ (kgFieldMild W₂ f h s) := by
      simp only [sub_apply, map_sub]
      abel
    rw [← map_add, ← map_sub, hvec]
  have he1 := kgFieldMild_eq hb0 hW₁ f h x
  have he2 := kgFieldMild_eq hb0 hW₂ f h x
  have hker1 : (∫ s in (0 : ℝ)..x, kgFieldKernel W₁ x s (kgFieldMild W₁ f h s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₁ (kgFieldMild W₁ f h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply W₁ x s _
  have hker2 : (∫ s in (0 : ℝ)..x, kgFieldKernel W₂ x s (kgFieldMild W₂ f h s))
      = ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (kgFieldMild W₂ f h s)) :=
    intervalIntegral.integral_congr fun s _ => kgFieldKernel_apply W₂ x s _
  rw [hsum, he1, he2, hker1, hker2]
  abel

/-- **The solution is Lipschitz in the perturbation**, forwards in time. -/
theorem norm_kgFieldMild_sub_potential_le_of_nonneg (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (hδ0 : 0 ≤ δ) (hδ : ‖W₁ - W₂‖ ≤ δ) (f h : Lp ℂ 2 (volume : Measure E))
    {t : ℝ} (ht : 0 ≤ t) :
    ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖
      ≤ δ * ((‖f‖ + ‖h‖) * t) * Real.exp (2 * (b * t)) := by
  set u₁ := kgFieldMild W₁ f h with hu₁
  set u₂ := kgFieldMild W₂ f h with hu₂
  set D : ℝ := ‖f‖ + ‖h‖ with hDdef
  have hD0 : 0 ≤ D := by rw [hDdef]; positivity
  set M : ℝ := D * Real.exp (b * t) with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; positivity
  have hc1 : Continuous u₁ := continuous_kgFieldMild hb0 hW₁ f h
  have hc2 : Continuous u₂ := continuous_kgFieldMild hb0 hW₂ f h
  have hScont : ContinuousOn (fun x => ‖u₁ x - u₂ x‖) (Icc 0 t) := ((hc1.sub hc2).norm).continuousOn
  have hu₁bound : ∀ s ∈ Icc (0 : ℝ) t, ‖u₁ s‖ ≤ M := by
    intro s hs
    have h1 : ‖u₁ s‖ ≤ D * Real.exp (b * |s|) := norm_kgFieldMild_le hb0 hW₁ f h s
    have habs : |s| ≤ t := by rw [abs_of_nonneg hs.1]; exact hs.2
    have h2 : Real.exp (b * |s|) ≤ Real.exp (b * t) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left habs hb0)
    exact h1.trans (mul_le_mul_of_nonneg_left h2 hD0)
  have hbound : ∀ x ∈ Icc (0 : ℝ) t,
      ‖u₁ x - u₂ x‖ ≤ δ * (M * t) + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
    intro x hx
    have hx0 : (0 : ℝ) ≤ x := hx.1
    have hA : Continuous fun s : ℝ => kgSinFreqOp (x - s) ((W₁ - W₂) (u₁ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
        ((W₁ - W₂).continuous.comp hc1)
    have hB : Continuous fun s : ℝ => kgSinFreqOp (x - s) (W₂ (u₁ s - u₂ s)) :=
      continuous_kgSinFreqOp_comp (continuous_const.sub continuous_id)
        (W₂.continuous.comp (hc1.sub hc2))
    have hAbd : ∀ s ∈ Set.uIoc (0 : ℝ) x,
        ‖kgSinFreqOp (x - s) ((W₁ - W₂) (u₁ s))‖ ≤ δ * M := by
      intro s hs
      have hsmem : s ∈ Icc (0 : ℝ) t := by
        rcases Set.mem_uIoc.mp hs with hs' | hs'
        · exact ⟨le_of_lt hs'.1, le_trans hs'.2 hx.2⟩
        · exact absurd (hs'.1.trans_le (hs'.2.trans hx0)) (lt_irrefl x)
      have h1 := norm_kgSinFreqOp_apply_le (x - s) ((W₁ - W₂) (u₁ s))
      have h2 : ‖(W₁ - W₂) (u₁ s)‖ ≤ δ * ‖u₁ s‖ := (W₁ - W₂).le_of_opNorm_le hδ _
      have h3 : ‖u₁ s‖ ≤ M := hu₁bound s hsmem
      calc ‖kgSinFreqOp (x - s) ((W₁ - W₂) (u₁ s))‖ ≤ ‖(W₁ - W₂) (u₁ s)‖ := h1
        _ ≤ δ * ‖u₁ s‖ := h2
        _ ≤ δ * M := mul_le_mul_of_nonneg_left h3 hδ0
    have hAint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₁ s))‖ ≤ δ * M * x := by
      have hle := intervalIntegral.norm_integral_le_of_norm_le_const hAbd
      simpa [abs_of_nonneg hx0] using hle
    have hBint : ‖∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (u₁ s - u₂ s))‖
        ≤ ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      refine le_trans (intervalIntegral.norm_integral_le_integral_norm hx0) ?_
      refine intervalIntegral.integral_mono_on hx0
        ((hB.norm).intervalIntegrable (μ := volume) 0 x)
        ((continuous_const.mul ((hc1.sub hc2).norm)).intervalIntegrable (μ := volume) 0 x)
        fun s _ => ?_
      have h1 := norm_kgSinFreqOp_apply_le (x - s) (W₂ (u₁ s - u₂ s))
      have h2 : ‖W₂ (u₁ s - u₂ s)‖ ≤ b * ‖u₁ s - u₂ s‖ := W₂.le_of_opNorm_le hW₂ _
      exact h1.trans h2
    have hsplit : u₁ x - u₂ x
        = (∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) ((W₁ - W₂) (u₁ s)))
          + ∫ s in (0 : ℝ)..x, kgSinFreqOp (x - s) (W₂ (u₁ s - u₂ s)) :=
      kgFieldMild_sub_potential hb0 hW₁ hW₂ f h x
    have hstep : ‖u₁ x - u₂ x‖ ≤ δ * M * x + ∫ s in (0 : ℝ)..x, b * ‖u₁ s - u₂ s‖ := by
      rw [hsplit]
      exact le_trans (norm_add_le _ _) (add_le_add hAint hBint)
    refine hstep.trans ?_
    have hxt : δ * M * x ≤ δ * (M * t) := by
      have hle : δ * M * x ≤ δ * M * t := mul_le_mul_of_nonneg_left hx.2 (by positivity)
      linarith
    linarith
  have hgron := le_mul_exp_integral_of_le_add_integral (S := fun x => ‖u₁ x - u₂ x‖)
    (k := fun _ => b) (C := δ * (M * t)) ht hScont continuousOn_const (fun _ _ => hb0) hbound
    t (right_mem_Icc.mpr ht)
  refine hgron.trans ?_
  simp only [intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  have hexp2 : Real.exp (2 * (b * t)) = Real.exp (b * t) * Real.exp (b * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have htb : t * b = b * t := mul_comm t b
  refine le_of_eq ?_
  rw [hMdef, hexp2, htb]
  ring

/-- **The solution is Lipschitz in the perturbation.** If two potentials differ by at most `δ` in
operator norm, the fields they produce from the same Cauchy data differ by at most
`δ (‖f‖+‖h‖) |t| e^{2b|t|}`. The negative-time half follows from the reversibility of the evolution,
which changes the sign of the velocity datum but not its norm. -/
theorem norm_kgFieldMild_sub_potential_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (hδ0 : 0 ≤ δ) (hδ : ‖W₁ - W₂‖ ≤ δ) (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖
      ≤ δ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|)) := by
  rcases le_total (0 : ℝ) t with ht | ht
  · rw [abs_of_nonneg ht]
    exact norm_kgFieldMild_sub_potential_le_of_nonneg hb0 hW₁ hW₂ hδ0 hδ f h ht
  · have hneg : (0 : ℝ) ≤ -t := by linarith
    have hkey := norm_kgFieldMild_sub_potential_le_of_nonneg hb0 hW₁ hW₂ hδ0 hδ f (-h) hneg
    rw [← kgFieldMild_neg hb0 hW₁ f h (-t), ← kgFieldMild_neg hb0 hW₂ f h (-t), neg_neg,
      norm_neg] at hkey
    rw [abs_of_nonpos ht]
    exact hkey

/-- **The solution operator is Lipschitz in the perturbation**, uniformly on bounded sets of data
and bounded time intervals. -/
theorem norm_kgFieldMild_sub_potential_le_of_le (hb0 : 0 ≤ b) (hW₁ : ‖W₁‖ ≤ b) (hW₂ : ‖W₂‖ ≤ b)
    (hδ0 : 0 ≤ δ) (hδ : ‖W₁ - W₂‖ ≤ δ) (f h : Lp ℂ 2 (volume : Measure E))
    {R T : ℝ} (hf : ‖f‖ + ‖h‖ ≤ R) {t : ℝ} (hT : |t| ≤ T) :
    ‖kgFieldMild W₁ f h t - kgFieldMild W₂ f h t‖ ≤ δ * (R * T) * Real.exp (2 * (b * T)) := by
  refine (norm_kgFieldMild_sub_potential_le hb0 hW₁ hW₂ hδ0 hδ f h t).trans ?_
  have hT0 : (0 : ℝ) ≤ T := le_trans (abs_nonneg t) hT
  have hR0 : (0 : ℝ) ≤ R := le_trans (by positivity) hf
  have h1 : (‖f‖ + ‖h‖) * |t| ≤ R * T := mul_le_mul hf hT (abs_nonneg t) hR0
  have h2 : Real.exp (2 * (b * |t|)) ≤ Real.exp (2 * (b * T)) := by
    refine Real.exp_le_exp.mpr ?_
    have : b * |t| ≤ b * T := mul_le_mul_of_nonneg_left hT hb0
    linarith
  have h3 : δ * ((‖f‖ + ‖h‖) * |t|) ≤ δ * (R * T) := mul_le_mul_of_nonneg_left h1 hδ0
  have h4 : (0 : ℝ) ≤ δ * ((‖f‖ + ‖h‖) * |t|) := by positivity
  calc δ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|))
      ≤ δ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * T)) :=
        mul_le_mul_of_nonneg_left h2 h4
    _ ≤ δ * (R * T) * Real.exp (2 * (b * T)) :=
        mul_le_mul_of_nonneg_right h3 (Real.exp_nonneg _)

/-- **The field depends continuously on the potential.** A net of uniformly bounded perturbations
converging in operator norm produces a net of fields converging in `L²`, at every time. -/
theorem tendsto_kgFieldMild_of_tendsto_potential {ι : Type*} {l : Filter ι}
    {V : ι → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))}
    (hb0 : 0 ≤ b) (hW : ‖W₂‖ ≤ b) (hV : ∀ i, ‖V i‖ ≤ b)
    (hten : Tendsto (fun i => ‖V i - W₂‖) l (𝓝 0))
    (f h : Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    Tendsto (fun i => kgFieldMild (V i) f h t) l (𝓝 (kgFieldMild W₂ f h t)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  set C : ℝ := ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|)) with hC
  have hle : ∀ i, ‖kgFieldMild (V i) f h t - kgFieldMild W₂ f h t‖ ≤ ‖V i - W₂‖ * C := by
    intro i
    have hb := norm_kgFieldMild_sub_potential_le hb0 (hV i) hW (norm_nonneg _) le_rfl f h t
    have heq : ‖V i - W₂‖ * C
        = ‖V i - W₂‖ * ((‖f‖ + ‖h‖) * |t|) * Real.exp (2 * (b * |t|)) := by
      rw [hC]; ring
    rw [heq]
    exact hb
  have hz : Tendsto (fun i => ‖V i - W₂‖ * C) l (𝓝 0) := by
    simpa using hten.mul_const C
  exact squeeze_zero (fun _ => norm_nonneg _) hle hz

end Stability

end GaloisForLFunctions.HTGeometry
