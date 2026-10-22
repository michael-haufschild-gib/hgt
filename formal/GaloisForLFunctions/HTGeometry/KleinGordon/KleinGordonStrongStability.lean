import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonPotentialStrong
import GaloisForLFunctions.HTGeometry.KleinGordon.KleinGordonMildSolution

/-!
# Two-sided estimate, stability, and the free case of the mild solution

Three closing statements for the perturbed strong theory.

Reflecting time carries a strong solution to a strong solution and leaves the energy unchanged, so
the Grönwall estimate holds on both sides of the initial slice. Applying it to the difference of two
solutions — the class being linear — turns uniqueness into *continuous dependence*: the energy of the
difference at time `t` is controlled by the energy of the difference of the Cauchy data.

Finally, the mild solution of the first-order system is checked against the free evolution: if the
potential vanishes almost everywhere, the perturbation series collapses to its first term and the
mild solution is the propagator. That is the consistency of the two constructions.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open MeasureTheory

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-! ## Reflection and the two-sided estimate -/

theorem kgStrongEnergy_comp_neg (u v : ℝ → Lp ℂ 2 (volume : Measure E)) (s : ℝ) :
    kgStrongEnergy (fun r => u (-r)) (fun r => -(v (-r))) s = kgStrongEnergy u v (-s) := by
  rw [kgStrongEnergy, kgStrongEnergy, map_neg, norm_neg]

/-- **The Grönwall estimate on both sides of the initial slice.** -/
theorem kgStrongEnergy_le_exp_abs
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {u v a : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h : SolvesKGSource W u v a) (t : ℝ) :
    kgStrongEnergy u v t ≤ kgStrongEnergy u v 0 * Real.exp (b * |t|) := by
  rcases le_total 0 t with ht | ht
  · rw [abs_of_nonneg ht]
    exact kgStrongEnergy_le_exp hb0 hW h ht
  · have hrefl := h.comp_neg
    have hnt : (0 : ℝ) ≤ -t := by linarith
    have hle := kgStrongEnergy_le_exp hb0 hW hrefl hnt
    rw [kgStrongEnergy_comp_neg, kgStrongEnergy_comp_neg, neg_neg, neg_zero] at hle
    rw [abs_of_nonpos ht]
    exact hle

/-! ## Linearity and continuous dependence -/

/-- The perturbed strong solutions form a vector space: differences are solutions. -/
theorem SolvesKGSource.sub
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)}
    {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSource W u₁ v₁ a₁) (h₂ : SolvesKGSource W u₂ v₂ a₂) :
    SolvesKGSource W (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s) (fun s => a₁ s - a₂ s) := by
  obtain ⟨hu₁, hv₁, he₁⟩ := h₁
  obtain ⟨hu₂, hv₂, he₂⟩ := h₂
  refine ⟨fun s => (hu₁ s).sub (hu₂ s), fun s => (hv₁ s).sub (hv₂ s), fun s => ?_⟩
  simp only [map_sub]
  rw [he₁ s, he₂ s]
  abel

/-- **Continuous dependence on the Cauchy data.** The energy of the difference of two perturbed
strong solutions at any time is controlled by the energy of the difference of their data. -/
theorem kgStrongEnergy_sub_le_exp_abs
    {W : Lp ℂ 2 (volume : Measure E) →L[ℂ] Lp ℂ 2 (volume : Measure E)} {b : ℝ}
    (hb0 : 0 ≤ b) (hW : ‖W‖ ≤ b) {u₁ v₁ a₁ u₂ v₂ a₂ : ℝ → Lp ℂ 2 (volume : Measure E)}
    (h₁ : SolvesKGSource W u₁ v₁ a₁) (h₂ : SolvesKGSource W u₂ v₂ a₂) (t : ℝ) :
    kgStrongEnergy (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s) t
      ≤ kgStrongEnergy (fun s => u₁ s - u₂ s) (fun s => v₁ s - v₂ s) 0
        * Real.exp (b * |t|) :=
  kgStrongEnergy_le_exp_abs hb0 hW (h₁.sub h₂) t

/-! ## The Volterra equation with a vanishing kernel -/

section Volterra

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

theorem volterraIterate_zero_kernel (f : ℝ → X) (n : ℕ) (t : ℝ) :
    volterraIterate f (fun _ _ => 0) n t = f t := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [volterraIterate_succ]
    simp

/-- **A vanishing kernel leaves the inhomogeneous term untouched.** -/
theorem volterraSolution_zero_kernel (f : ℝ → X) (t : ℝ) :
    volterraSolution f (fun _ _ => 0) t = f t := by
  rw [volterraSolution]
  have hterm : ∀ n : ℕ, volterraIterate f (fun _ _ => (0 : X →L[ℝ] X)) (n + 1) t
      - volterraIterate f (fun _ _ => (0 : X →L[ℝ] X)) n t = 0 := by
    intro n
    rw [volterraIterate_zero_kernel, volterraIterate_zero_kernel, sub_self]
  rw [tsum_congr hterm, tsum_zero, add_zero]

end Volterra

/-! ## The free case of the mild solution -/

/-- **A potential vanishing almost everywhere gives the free evolution.** The perturbation series
collapses to its first term, so the mild solution of the first-order system is the propagator: the
two constructions of the corpus agree where they overlap. -/
theorem kgMildSolution_of_ae_zero {V : E → ℂ} (hV : Measurable V) {b : ℝ} (hb0 : 0 ≤ b)
    (hb : ∀ ξ, ‖V ξ‖ ≤ b) (hae : ∀ᵐ ξ ∂(volume : Measure E), V ξ = 0)
    (w₀ : KGEnergy E) (t : ℝ) :
    kgMildSolution hV hb0 hb w₀ t = kgPropagator t w₀ := by
  have hpot : kgPotentialOp hV hb0 hb = 0 := by
    refine ContinuousLinearMap.ext fun v => ?_
    rw [kgPotentialOp_apply,
      lpBoundedMulCLM_eq_zero (p := 2) (μ := (volume : Measure E)) hV hb0 hb hae]
    simp only [zero_apply]
    exact map_zero _
  have hker : kgMildDuhamelKernel hV hb0 hb = fun _ _ : ℝ => (0 : KGEnergy E →L[ℝ] KGEnergy E) := by
    funext r s
    rw [kgMildDuhamelKernel, hpot]
    simp
  rw [kgMildSolution, hker, volterraSolution_zero_kernel]
  rfl

end GaloisForLFunctions.HTGeometry
