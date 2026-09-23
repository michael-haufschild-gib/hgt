import GaloisForLFunctions.HTGeometry.KleinGordonStrongUniqueness
import Mathlib.Analysis.ODE.Gronwall

/-!
# The strong Cauchy problem with a bounded perturbation

The free energy `F(t) = ‖⟨D⟩⁻¹∂ₜu(t)‖² + ‖u(t)‖²` is no longer conserved once a bounded perturbation
`W` is added to the equation, but its derivative is *controlled by itself*:

`F'(t) = 2 Re⟪∂ₜu, ⟨D⟩⁻²(Wu)⟫ = 2 Re⟪⟨D⟩⁻²∂ₜu, Wu⟫`,

and moving both factors of `⟨D⟩⁻¹` to the left — legitimate because `⟨D⟩⁻¹` is self-adjoint — makes
the first argument a *contraction* of `⟨D⟩⁻¹∂ₜu`, which is exactly one of the two terms of `F`. So
`|F'| ≤ ‖W‖ F`, and Grönwall gives `F(t) ≤ F(0)e^{‖W‖|t|}` on both sides of the initial slice.

Multiplication by a bounded measurable potential is such a `W`, so this covers the clock equation
`∂ₜ²u = -⟨D⟩²u + Vu` with no hypothesis on `V` beyond measurability and boundedness.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory Set

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## The perturbed strong solutions -/

/-- A **strong solution of the perturbed Klein–Gordon equation** `∂ₜ²u = -⟨D⟩²u + Wu`, with `W` any
bounded operator on `L²`. The equation is stated in the regularised form the unbounded `⟨D⟩²`
forbids writing directly. -/
def SolvesKGSource (W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E))
    (u v a : ℝ → Lp ℂ 2 (volume : Measure E)) : Prop :=
  (∀ t : ℝ, HasDerivAt u (v t) t) ∧ (∀ t : ℝ, HasDerivAt v (a t) t) ∧
    (∀ t : ℝ, kgFreqInvOp (kgFreqInvOp (a t))
      = -(u t) + kgFreqInvOp (kgFreqInvOp (W (u t))))

/-- The free equation is the case `W = 0`. -/
theorem solvesKGSource_zero {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKG u v a) :
    SolvesKGSource 0 u v a := by
  obtain ⟨hu, hv, heq⟩ := h
  exact ⟨hu, hv, fun t => by rw [heq t]; simp⟩

/-! ## The energy identity -/

/-- **The derivative of the energy of a perturbed strong solution.** -/
theorem hasDerivAt_kgStrongEnergy_source
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKGSource W u v a) (t : ℝ) :
    HasDerivAt (kgStrongEnergy u v)
      (2 * RCLike.re (inner ℂ (kgFreqInvOp (kgFreqInvOp (v t))) (W (u t)))) t := by
  obtain ⟨hu, hv, heq⟩ := h
  have hA : HasDerivAt (fun s => kgFreqInvOp (v s)) (kgFreqInvOp (a t)) t :=
    hasDerivAt_clm _ (hv t)
  have h1 := hasDerivAt_norm_sq hA
  have h2 := hasDerivAt_norm_sq (hu t)
  have hsum := h1.add h2
  have hmove : inner ℂ (kgFreqInvOp (E := E) (v t)) (kgFreqInvOp (a t))
      = -inner ℂ (v t) (u t)
        + inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W (u t)) := by
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
      = 2 * RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W (u t))) := by
    rw [hswap1, hmove, hswap2]
    simp only [map_add, map_neg, RCLike.conj_conj, RCLike.re_to_complex, Complex.conj_re]
    ring
  rw [hval] at hsum
  exact hsum

/-- **The energy derivative is controlled by the energy.** -/
theorem abs_deriv_kgStrongEnergy_le
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) (u v : ℝ → Lp ℂ 2 (volume : Measure E)) (t : ℝ) :
    |2 * RCLike.re (inner ℂ (kgFreqInvOp (kgFreqInvOp (v t))) (W (u t)))|
      ≤ b * kgStrongEnergy u v t := by
  have hinv : ‖kgFreqInvOp (E := E) (kgFreqInvOp (v t))‖ ≤ ‖kgFreqInvOp (E := E) (v t)‖ := by
    have h := (kgFreqInvOp (E := E)).le_of_opNorm_le norm_kgFreqInvOp_le (kgFreqInvOp (v t))
    rwa [one_mul] at h
  have hWb : ‖W (u t)‖ ≤ b * ‖u t‖ := W.le_of_opNorm_le hW (u t)
  have hcs : |RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W (u t)))|
      ≤ ‖kgFreqInvOp (E := E) (kgFreqInvOp (v t))‖ * ‖W (u t)‖ := by
    refine le_trans (RCLike.abs_re_le_norm _) ?_
    exact norm_inner_le_norm (𝕜 := ℂ) _ _
  have hstep : |2 * RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v t))) (W (u t)))|
      ≤ 2 * (‖kgFreqInvOp (E := E) (v t)‖ * (b * ‖u t‖)) := by
    rw [abs_mul, abs_two]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    refine hcs.trans ?_
    exact mul_le_mul hinv hWb (norm_nonneg _) (norm_nonneg _)
  refine hstep.trans ?_
  have hsq : 2 * (‖kgFreqInvOp (E := E) (v t)‖ * ‖u t‖)
      ≤ ‖kgFreqInvOp (E := E) (v t)‖ ^ (2 : ℕ) + ‖u t‖ ^ (2 : ℕ) := by
    nlinarith [sq_nonneg (‖kgFreqInvOp (E := E) (v t)‖ - ‖u t‖)]
  rw [kgStrongEnergy]
  nlinarith [hsq, norm_nonneg (kgFreqInvOp (E := E) (v t)), norm_nonneg (u t)]

/-! ## The Grönwall estimate -/

/-- **The energy of a perturbed strong solution grows at most exponentially**, at a rate set by the
norm of the perturbation alone. -/
theorem kgStrongEnergy_le_exp
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSource W u v a) {t : ℝ} (ht : 0 ≤ t) :
    kgStrongEnergy u v t ≤ kgStrongEnergy u v 0 * Real.exp (b * t) := by
  set F : ℝ → ℝ := kgStrongEnergy u v with hF
  set F' : ℝ → ℝ := fun s =>
    2 * RCLike.re (inner ℂ (kgFreqInvOp (E := E) (kgFreqInvOp (v s))) (W (u s))) with hF'
  have hderiv : ∀ s : ℝ, HasDerivAt F (F' s) s := fun s =>
    hasDerivAt_kgStrongEnergy_source h s
  have hcont : ContinuousOn F (Icc 0 t) :=
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
  have hbound : ∀ s ∈ Ico (0 : ℝ) t, ‖F' s‖ ≤ b * ‖F s‖ + 0 := by
    intro s _
    have hnn : 0 ≤ F s := kgStrongEnergy_nonneg u v s
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hnn, add_zero]
    exact abs_deriv_kgStrongEnergy_le hb0 hW u v s
  have hmain := norm_le_gronwallBound_of_norm_deriv_right_le hcont
    (fun s hs => (hderiv s).hasDerivWithinAt) (le_refl ‖F 0‖) hbound t (right_mem_Icc.mpr ht)
  rw [Real.norm_eq_abs, abs_of_nonneg (kgStrongEnergy_nonneg u v t)] at hmain
  rw [gronwallBound_ε0] at hmain
  rw [Real.norm_eq_abs, abs_of_nonneg (kgStrongEnergy_nonneg u v 0)] at hmain
  simpa using hmain

/-! ## Uniqueness -/

/-- Reversing time carries a perturbed strong solution to a perturbed strong solution. -/
theorem SolvesKGSource.comp_neg
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {u v a : ℝ → Lp ℂ 2 (volume : Measure E)} (h : SolvesKGSource W u v a) :
    SolvesKGSource W (fun t => u (-t)) (fun t => -(v (-t))) (fun t => a (-t)) := by
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

/-- **A perturbed strong solution with vanishing Cauchy data vanishes.** -/
theorem eq_zero_of_solvesKGSource
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSource W u v a) (hu0 : u 0 = 0) (hv0 : v 0 = 0) (t : ℝ) : u t = 0 := by
  have hzero : kgStrongEnergy u v 0 = 0 := by
    rw [kgStrongEnergy, hu0, hv0, map_zero, norm_zero]
    norm_num
  have key : ∀ (u' v' a' : ℝ → Lp ℂ 2 (volume : Measure E)), SolvesKGSource W u' v' a' →
      kgStrongEnergy u' v' 0 = 0 → ∀ s : ℝ, 0 ≤ s → u' s = 0 := by
    intro u' v' a' h' hz s hs
    have hle := kgStrongEnergy_le_exp hb0 hW h' hs
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
  · exact key u v a h hzero t hpos
  · have hrefl := h.comp_neg
    have hz : kgStrongEnergy (fun s => u (-s)) (fun s => -(v (-s))) 0 = 0 := by
      rw [kgStrongEnergy]
      simp only [neg_zero, hu0, hv0]
      simp
    have := key _ _ _ hrefl hz (-t) (by linarith)
    simpa using this

/-- **Uniqueness for the perturbed strong Cauchy problem.** Two strong solutions of
`∂ₜ²u = -⟨D⟩²u + Wu` with the same field and velocity at time zero agree at every time. -/
theorem eq_of_solvesKGSource
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSource W u₁ v₁ a₁) (h₂ : SolvesKGSource W u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t := by
  obtain ⟨hu₁, hv₁, he₁⟩ := h₁
  obtain ⟨hu₂, hv₂, he₂⟩ := h₂
  have hsub : SolvesKGSource W (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s)
      (fun s => a₁ s - a₂ s) := by
    refine ⟨fun s => (hu₁ s).sub (hu₂ s), fun s => (hv₁ s).sub (hv₂ s), fun s => ?_⟩
    simp only [map_sub]
    rw [he₁ s, he₂ s]
    abel
  have h0 := eq_zero_of_solvesKGSource hb0 hW hsub (by simp [hu0]) (by simp [hv0]) t
  exact sub_eq_zero.mp h0

/-! ## The bounded measurable potential -/

/-- **Uniqueness for the clock equation with a bounded measurable potential.** No continuity, decay
or smoothness of the potential is used. -/
theorem eq_of_solvesKGSource_potential {V : E → ℂ} (hV : Measurable V) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ ξ, ‖V ξ‖ ≤ b) {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSource (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb)
      u₁ v₁ a₁)
    (h₂ : SolvesKGSource (lpBoundedMulCLM (p := 2) (μ := (volume : Measure E)) hV hb0 hb)
      u₂ v₂ a₂)
    (hu0 : u₁ 0 = u₂ 0) (hv0 : v₁ 0 = v₂ 0) (t : ℝ) : u₁ t = u₂ t :=
  eq_of_solvesKGSource hb0
    (norm_lpBoundedMulCLM_le (p := 2) (μ := (volume : Measure E)) hV hb0 hb) h₁ h₂ hu0 hv0 t

end GaloisForLFunctions.HTGeometry
