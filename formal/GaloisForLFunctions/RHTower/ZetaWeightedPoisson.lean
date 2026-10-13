import GaloisForLFunctions.RHTower.ZetaTwistedPoisson

/-!
# Weighted Poisson summation for the Gabor grid

Let `W(s) = ∫ ψ(ξ) e^{iξs} dξ` with `ψ` integrable and supported in `[−L, L]`.  Integrating the modulated Poisson
identity against `ψ` gives (`hasSum_weighted_phiHat`)

`Σ_{k∈ℤ} W(τ_k) φ̂(τ − τ_k) φ̂(τ' − τ_k) = ∫ ψ(ξ) e^{iξτ'} (G_ξ(−1) + G_ξ(0) + G_ξ(1)) dξ`,

the interchange of `Σ_k` and `∫ dξ` being justified by `|φ̂(r)| ≪ (1 + r²)⁻¹`.  With `|φ| ≤ M` the aliased part is at
most `2LM² ∫ |ξ| |ψ(ξ)| dξ` (`norm_weighted_sub_main_le`): the weighted kernel of the grid equals its main term
`∫ ψ(ξ) e^{iξτ'} G_ξ(0) dξ` up to an error controlled by the first absolute moment of `ψ`, i.e. by the inverse width of
the weight.
-/

open Complex MeasureTheory Real Set Filter Topology Asymptotics Zeta23
open scoped FourierTransform

noncomputable section

namespace RHTower

namespace TwistedPoisson

variable {φ : ℝ → ℝ} {L : ℝ}

/-- The grid products `φ̂(τ − τ_k) φ̂(τ' − τ_k)` are absolutely summable over `k ∈ ℤ`. -/
theorem summable_norm_phiHat_mul (hL : 0 < L)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C) (T τ τ' : ℝ) :
    Summable (fun k : ℤ => ‖paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
        * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ)‖) := by
  obtain ⟨C, hC⟩ := hdecay
  have hC0 : 0 ≤ C := le_trans (by positivity) (hC 0)
  have hbdd : ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ ≤ C := by
    intro s
    have h2 : ‖paperFT (fun u => (φ u : ℂ)) s‖ * 1
        ≤ ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) := by gcongr; nlinarith
    linarith [hC s]
  set g : ℝ → ℂ := fun w => paperFT (fun u => (φ u : ℂ)) ((τ - (T + w * (2 * π / L)) : ℝ) : ℂ)
      * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + w * (2 * π / L)) : ℝ) : ℂ) with hg
  have hO : g =O[cocompact ℝ] fun w : ℝ => |w| ^ (-2 : ℝ) := by
    apply Poisson.isBigO_of_decay (c := τ - T) (h := 2 * π / L) (C := C * C) (by positivity)
    intro w
    rw [hg, norm_mul]
    have e1 : τ - T - w * (2 * π / L) = τ - (T + w * (2 * π / L)) := by ring
    rw [e1]
    calc ‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖
          * (1 + (τ - (T + w * (2 * π / L))) ^ 2)
        = (‖paperFT (fun u => (φ u : ℂ)) ↑(τ - (T + w * (2 * π / L)))‖
            * (1 + (τ - (T + w * (2 * π / L))) ^ 2))
          * ‖paperFT (fun u => (φ u : ℂ)) ↑(τ' - (T + w * (2 * π / L)))‖ := by ring
      _ ≤ C * C := mul_le_mul (hC _) (hbdd _) (norm_nonneg _) hC0
  have hO' : (fun w : ℝ => ‖g w‖) =O[cocompact ℝ] fun w : ℝ => |w| ^ (-2 : ℝ) := hO.norm_left
  exact summable_of_isBigO (Real.summable_abs_int_rpow one_lt_two)
    (hO'.comp_tendsto Int.tendsto_coe_cofinite)

/-- **Weighted Poisson summation.**  For `ψ` integrable and supported in `[−L, L]`,
`Σ_k (∫ ψ(ξ) e^{iξτ_k} dξ) φ̂(τ − τ_k) φ̂(τ' − τ_k) = ∫ ψ(ξ) e^{iξτ'} (G_ξ(−1) + G_ξ(0) + G_ξ(1)) dξ`. -/
theorem hasSum_weighted_phiHat (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (hdecay : ∃ C, ∀ s : ℝ, ‖paperFT (fun u => (φ u : ℂ)) s‖ * (1 + s ^ 2) ≤ C)
    {ψ : ℝ → ℂ} (hψ : Integrable ψ) (hψsupp : ∀ ξ, L < |ξ| → ψ ξ = 0) (T τ τ' : ℝ) :
    HasSum (fun k : ℤ => ∫ ξ, ψ ξ * cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ))
        * (paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
          * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ)))
      (∫ ξ, ψ ξ * (cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1))) := by
  set c : ℤ → ℂ := fun k => paperFT (fun u => (φ u : ℂ)) ((τ - (T + k * (2 * π / L)) : ℝ) : ℂ)
      * paperFT (fun u => (φ u : ℂ)) ((τ' - (T + k * (2 * π / L)) : ℝ) : ℂ) with hc
  set F : ℤ → ℝ → ℂ := fun k ξ => ψ ξ * cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ)) * c k
    with hF
  have hnormF : ∀ k ξ, ‖F k ξ‖ = ‖ψ ξ‖ * ‖c k‖ := by
    intro k ξ
    rw [hF]
    simp only
    rw [norm_mul, norm_mul,
      show I * (ξ : ℂ) * ((T + k * (2 * π / L) : ℝ) : ℂ) = ((ξ * (T + k * (2 * π / L)) : ℝ) : ℂ) * I
        by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  have hFint : ∀ k, Integrable (F k) := by
    intro k
    refine Integrable.mono' (hψ.norm.mul_const ‖c k‖) ?_ (Eventually.of_forall fun ξ => le_of_eq (hnormF k ξ))
    exact (hψ.aestronglyMeasurable.mul (by fun_prop : Continuous fun ξ : ℝ =>
      cexp (I * ξ * ((T + k * (2 * π / L) : ℝ) : ℂ))).aestronglyMeasurable).mul_const _
  have hsumm : Summable fun k => ∫ ξ, ‖F k ξ‖ := by
    have h1 : (fun k => ∫ ξ, ‖F k ξ‖) = fun k => (∫ ξ, ‖ψ ξ‖) * ‖c k‖ := by
      funext k
      simp_rw [hnormF k]
      exact integral_mul_const _ _
    rw [h1]
    exact (summable_norm_phiHat_mul hL hdecay T τ τ').mul_left _
  have h := hasSum_integral_of_summable_integral_norm hFint hsumm
  have hpt : ∀ ξ, ∑' k, F k ξ = ψ ξ * (cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1)) := by
    intro ξ
    by_cases hξ : |ξ| ≤ L
    · have ht := (hasSum_twisted_phiHat hL hφc hsupp hdecay hξ T τ τ').mul_left (ψ ξ)
      rw [← ht.tsum_eq]
      congr 1 with k
      rw [hF, hc]
      simp only
      ring
    · have h0 : ψ ξ = 0 := hψsupp ξ (not_le.mp hξ)
      rw [h0, zero_mul]
      simp [hF, h0]
  simp_rw [hpt] at h
  exact h

/-- `ξ ↦ G_ξ(η)` is continuous. -/
theorem continuous_Gaux2_shift (hφc : Continuous φ) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0)
    (T τ τ' η : ℝ) : Continuous fun ξ => Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' η := by
  have e : (fun ξ => Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' η)
      = fun ξ => ∫ u in Icc (-(L / 2)) (L / 2), gInt2 φ (fun v => φ (v + ξ)) L T τ τ' η u := by
    funext ξ
    unfold Gaux2
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
    intro u hu
    apply gInt2_eq_zero_left hsupp
    by_contra h
    apply hu
    rw [mem_Icc]
    push Not at h
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  rw [e]
  refine continuous_parametric_integral_of_continuous ?_ isCompact_Icc
  unfold gInt2 Function.uncurry
  fun_prop

/-- `‖G_ξ(η)‖ ≤ L² M²` when `|φ| ≤ M`. -/
theorem norm_Gaux2_shift_le (hL : 0 < L) (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {M : ℝ}
    (hM : ∀ u, |φ u| ≤ M) (ξ T τ τ' η : ℝ) :
    ‖Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' η‖ ≤ L * (M * M) * L := by
  have hsupp' : ∀ u ∉ Icc (-(L / 2)) (L / 2), gInt2 φ (fun v => φ (v + ξ)) L T τ τ' η u = 0 := by
    intro u hu
    apply gInt2_eq_zero_left hsupp
    by_contra h
    apply hu
    rw [mem_Icc]
    push Not at h
    exact ⟨by linarith [neg_abs_le u], by linarith [le_abs_self u]⟩
  unfold Gaux2
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hsupp']
  refine (norm_setIntegral_le_of_norm_le_const (by simp)
    (fun u _ => norm_gInt2_le hL hM (fun v => hM (v + ξ)) η u)).trans (le_of_eq ?_)
  rw [Measure.real, Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]
  ring

/-- `ξ ↦ ψ(ξ) e^{iξτ'} g(ξ)` is integrable for integrable `ψ` and bounded continuous `g`. -/
theorem integrable_psi_cexp_mul_bdd {ψ : ℝ → ℂ} (hψ : Integrable ψ) (τ' : ℝ) (g : ℝ → ℂ)
    (hg : Continuous g) {C : ℝ}
    (hgC : ∀ ξ, ‖g ξ‖ ≤ C) : Integrable fun ξ => ψ ξ * (cexp (I * ξ * τ') * g ξ) := by
  refine Integrable.mono' (hψ.norm.mul_const C) ?_ (Eventually.of_forall fun ξ => ?_)
  · exact hψ.aestronglyMeasurable.mul (by fun_prop : Continuous fun ξ : ℝ =>
      cexp (I * ξ * τ') * g ξ).aestronglyMeasurable
  · rw [norm_mul, norm_mul, show I * (ξ : ℂ) * (τ' : ℂ) = ((ξ * τ' : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul]
    exact mul_le_mul_of_nonneg_left (hgC ξ) (norm_nonneg _)

/-- **The aliased part of the weighted kernel.**  With `|φ| ≤ M`, the weighted grid sum differs from its main term
`∫ ψ(ξ) e^{iξτ'} G_ξ(0) dξ` by at most `2LM² ∫ |ξ| ‖ψ(ξ)‖ dξ`. -/
theorem norm_weighted_sub_main_le (hL : 0 < L) (hφc : Continuous φ)
    (hsupp : ∀ u, L / 2 ≤ |u| → φ u = 0) {M : ℝ} (hM : ∀ u, |φ u| ≤ M) {ψ : ℝ → ℂ}
    (hψ : Integrable ψ) (hψ1 : Integrable (fun ξ => |ξ| * ‖ψ ξ‖)) (T τ τ' : ℝ) :
    ‖(∫ ξ, ψ ξ * (cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1)))
      - ∫ ξ, ψ ξ * (cexp (I * ξ * τ') * Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0)‖
      ≤ 2 * L * M ^ 2 * ∫ ξ, |ξ| * ‖ψ ξ‖ := by
  have hc := fun η => continuous_Gaux2_shift (L := L) hφc hsupp T τ τ' η
  have hb := fun η ξ => norm_Gaux2_shift_le hL hsupp hM ξ T τ τ' η
  have hint := integrable_psi_cexp_mul_bdd hψ τ' (fun ξ => Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
      + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1)
    (((hc (-1)).add (hc 0)).add (hc 1)) (C := L * (M * M) * L + L * (M * M) * L + L * (M * M) * L)
    (fun ξ => (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
      (add_le_add (hb (-1) ξ) (hb 0 ξ))) (hb 1 ξ)))
  have hint0 := integrable_psi_cexp_mul_bdd hψ τ' (fun ξ => Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0)
    (hc 0) (hb 0)
  rw [← integral_sub hint hint0, ← integral_const_mul]
  refine norm_integral_le_of_norm_le (hψ1.const_mul _) (Eventually.of_forall fun ξ => ?_)
  have e : ψ ξ * (cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0 + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1))
      - ψ ξ * (cexp (I * ξ * τ') * Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 0)
      = ψ ξ * cexp (I * ξ * τ') * (Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1)
        + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1) := by ring
  rw [e, norm_mul, norm_mul,
    show I * (ξ : ℂ) * (τ' : ℂ) = ((ξ * τ' : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I, mul_one]
  have h := norm_twisted_alias_le (ξ := ξ) hL hsupp hM T τ τ'
  have hψ0 := norm_nonneg (ψ ξ)
  calc ‖ψ ξ‖ * ‖Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' (-1) + Gaux2 φ (fun v => φ (v + ξ)) L T τ τ' 1‖
      ≤ ‖ψ ξ‖ * (2 * L * M ^ 2 * |ξ|) := mul_le_mul_of_nonneg_left h hψ0
    _ = 2 * L * M ^ 2 * (|ξ| * ‖ψ ξ‖) := by ring

end TwistedPoisson

end RHTower
