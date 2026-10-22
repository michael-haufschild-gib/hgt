import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonTimeBandEnergyUniform

/-!
# Strong solutions in a moving background

The strong theory of statements 74–78 fixes one bounded perturbation. Its energy method never
differentiates the perturbation — the energy identity

`d/dt (‖⟨D⟩⁻¹∂ₜu‖² + ‖u‖²) = 2 Re⟨⟨D⟩⁻²∂ₜu, Wu⟩`

evaluates `W` at the same time as everything else — so it holds verbatim for a curve of operators, and
the Grönwall bound only uses the uniform norm bound. This file carries the whole strong layer to a
moving background: the energy identity, its exponential bound, time reversal, and uniqueness for

`∂ₜ²u = −⟨D⟩²u + W(t)u`.

Uniqueness needs no more than linearity of each `W(t)`: the difference of two solutions solves the same
equation, because `W(t)u₁ − W(t)u₂ = W(t)(u₁−u₂)` at every time separately.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A **strong solution** of `∂ₜ²u = -⟨D⟩²u + W(t)u`: a field, its velocity and its acceleration,
with the equation read through two applications of the inverse frequency. -/
def SolvesKGSourceT (W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)))
    (u v a : ℝ → Lp ℂ 2 (volume : Measure E)) : Prop :=
  (∀ t : ℝ, HasDerivAt u (v t) t) ∧ (∀ t : ℝ, HasDerivAt v (a t) t) ∧
    (∀ t : ℝ, kgFreqInvOp (kgFreqInvOp (a t))
      = -(u t) + kgFreqInvOp (kgFreqInvOp (W t (u t))))

/-- The autonomous strong theory is the constant case. -/
theorem solvesKGSourceT_const (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (u v a : ℝ → Lp ℂ 2 (volume : Measure E)) :
    SolvesKGSourceT (fun _ : ℝ => W) u v a ↔ SolvesKGSource W u v a := Iff.rfl

section StrongT

variable {W : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))} {b : ℝ}

/-- **The derivative of the energy of a strong solution in a moving background.** -/
theorem hasDerivAt_kgStrongEnergy_sourceT {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSourceT W u v a) (t : ℝ) :
    HasDerivAt (kgStrongEnergy u v)
      (2 * RCLike.re (inner ℂ (kgFreqInvOp (kgFreqInvOp (v t))) (W t (u t)))) t := by
  obtain ⟨hu, hv, heq⟩ := h
  have hA : HasDerivAt (fun s => kgFreqInvOp (v s)) (kgFreqInvOp (a t)) t :=
    hasDerivAt_clm _ (hv t)
  have h1 := hasDerivAt_norm_sq hA
  have h2 := hasDerivAt_norm_sq (hu t)
  have hsum := h1.add h2
  have hmove : inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))
      = -inner ℂ (v t) (u t)
        + inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W t (u t)) := by
    rw [inner_kgFreqInvOp, heq t, inner_add_right, inner_neg_right,
      ← inner_kgFreqInvOp, ← inner_kgFreqInvOp]
  have hswap1 : inner ℂ (kgFreqInvOp (E := E) (a t)) (kgFreqInvOp (v t))
      = (starRingEnd ℂ) (inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))) :=
    (inner_conj_symm _ _).symm
  have hswap2 : inner ℂ (v t) (u t) = (starRingEnd ℂ) (inner ℂ (u t) (v t)) :=
    (inner_conj_symm _ _).symm
  have hval : RCLike.re (inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))
        + inner ℂ (kgFreqInvOp (E := E) (a t)) (kgFreqInvOp (v t)))
      + RCLike.re (inner ℂ (u t) (v t) + inner ℂ (v t) (u t))
      = 2 * RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W t (u t))) := by
    rw [hswap1, hmove, hswap2]
    simp only [map_add, map_neg, RCLike.conj_conj, RCLike.re_to_complex, Complex.conj_re]
    ring
  rw [hval] at hsum
  exact hsum

/-- **The energy of a strong solution in a moving background grows at most exponentially**, at a rate
set by the uniform bound alone. -/
theorem kgStrongEnergy_le_expT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKGSourceT W u v a) {t : ℝ}
    (ht : 0 ≤ t) : kgStrongEnergy u v t ≤ kgStrongEnergy u v 0 * Real.exp (b * t) := by
  set F : ℝ → ℝ := kgStrongEnergy u v with hF
  set F' : ℝ → ℝ := fun s =>
    2 * RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v s))) (W s (u s))) with hF'
  have hderiv : ∀ s : ℝ, HasDerivAt F (F' s) s := fun s =>
    hasDerivAt_kgStrongEnergy_sourceT h s
  have hcont : ContinuousOn F (Icc 0 t) :=
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖F' s‖ ≤ b * ‖F s‖ + 0 := by
    intro s _
    have hnn : 0 ≤ F s := kgStrongEnergy_nonneg u v s
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, add_zero]
    exact abs_deriv_kgStrongEnergy_le hb0 (hWb s) u v s
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => (hderiv s).hasDerivWithinAt) (le_refl ‖F 0‖) hbound t (right_mem_Icc.mpr ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (kgStrongEnergy_nonneg u v t)] at hmain
  rw [gronwallBound_ε0] at hmain
  rw [Real.norm_eq_abs, abs_of_nonneg (kgStrongEnergy_nonneg u v 0)] at hmain
  simpa using hmain

/-- Reversing time carries a strong solution to a strong solution in the reversed background. -/
theorem SolvesKGSourceT.comp_neg {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSourceT W u v a) :
    SolvesKGSourceT (fun t : ℝ => W (-t)) (fun t => u (-t)) (fun t => -(v (-t)))
      (fun t => a (-t)) := by
  obtain ⟨hu, hv, heq⟩ := h
  refine ⟨fun t => ?_, fun t => ?_, fun t => heq (-t)⟩
  · have hcomp := (hu (-t)).scomp t (hasDerivAt_neg t)
    have hval : (-1 : ℝ) • v (-t) = -(v (-t)) := neg_one_smul ℝ (v (-t))
    rw [hval] at hcomp
    exact hcomp
  · have hcomp := ((hv (-t)).scomp t (hasDerivAt_neg t)).neg
    have hval : -((-1 : ℝ) • a (-t)) = a (-t) := by
      rw [neg_one_smul, neg_neg]
    rw [hval] at hcomp
    exact hcomp

/-- **A strong solution in a moving background with vanishing Cauchy data vanishes.** -/
theorem eq_zero_of_solvesKGSourceT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKGSourceT W u v a)
    (hu0 : u 0 = 0) (hv0 : v 0 = 0) (t : ℝ) : u t = 0 := by
  have hzero : kgStrongEnergy u v 0 = 0 := by
    rw [kgStrongEnergy, hu0, hv0, map_zero, norm_zero]
    norm_num
  have key : ∀ (V : ℝ → (Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))),
      (∀ r : ℝ, ‖V r‖ ≤ b) →
      ∀ (u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E)), SolvesKGSourceT V u' v' a' →
      kgStrongEnergy u' v' 0 = 0 → ∀ s : ℝ, 0 ≤ s → u' s = 0 := by
    intro V hV u' v' a' h' hz s hs
    have hle := kgStrongEnergy_le_expT hb0 hV h' hs
    rw [hz, zero_mul] at hle
    have h1 : (0 : ℝ) ≤ ‖kgFreqInvOp (E := E) (v' s)‖ ^ (2 : ℕ) := sq_nonneg _
    have h2 : ‖u' s‖ ^ (2 : ℕ) ≤ 0 := by
      rw [kgStrongEnergy] at hle
      linarith
    have h3 : ‖u' s‖ = 0 := by
      have hnn : (0 : ℝ) ≤ ‖u' s‖ := norm_nonneg _
      nlinarith
    exact norm_eq_zero.mp h3
  rcases le_total 0 t with hpos | hneg
  · exact key W hWb u v a h hzero t hpos
  · have hrefl := h.comp_neg
    have hVb : ∀ r : ℝ, ‖W (-r)‖ ≤ b := fun r => hWb (-r)
    have hz : kgStrongEnergy (fun s => u (-s)) (fun s => -(v (-s))) 0 = 0 := by
      rw [kgStrongEnergy]
      simp only [neg_zero, hu0, hv0]
      simp
    have := key _ hVb _ _ _ hrefl hz (-t) (by linarith)
    simpa using this

/-- **Uniqueness for the strong Cauchy problem in a moving background.** -/
theorem eq_of_solvesKGSourceT (hb0 : 0 ≤ b) (hWb : ∀ r : ℝ, ‖W r‖ ≤ b)
    {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSourceT W u₁ v₁ a₁) (h₂ : SolvesKGSourceT W u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t := by
  obtain ⟨hu₁, hv₁, he₁⟩ := h₁
  obtain ⟨hu₂, hv₂, he₂⟩ := h₂
  have hsub : SolvesKGSourceT W (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s)
      (fun s => a₁ s - a₂ s) := by
    refine ⟨fun s => (hu₁ s).sub (hu₂ s), fun s => (hv₁ s).sub (hv₂ s), fun s => ?_⟩
    simp only [map_sub]
    rw [he₁ s, he₂ s]
    abel
  have h0 := eq_zero_of_solvesKGSourceT hb0 hWb hsub (by simp [hu0]) (by simp [hv0]) t
  exact sub_eq_zero.mp h0

end StrongT

end GaloisForLFunctions.HTGeometry
