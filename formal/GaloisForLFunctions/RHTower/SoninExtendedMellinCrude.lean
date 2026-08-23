import GaloisForLFunctions.RHTower.SoninExtendedMellinPole
import GaloisForLFunctions.RHTower.SoninDecayTailIdentity

/-!
# The crude polynomial bound for the continued Mellin transform

Burnol's Theorem 4.8 runs Phragmén--Lindelöf on a vertical strip, and its growth hypothesis needs a
bound valid *throughout* the strip — in particular on the critical line, where neither Hardy
representative is bounded.  The corpus's uniform Cauchy estimate supplies it: on `Re s > 0`

`‖soninMellinExtension g a s‖ ≤ a^{-σ}·((2 + ‖s‖/σ)/2π)·N(a)·‖g‖`,

which is `O(‖s‖)` on every closed substrip of the open right half-plane.  Adding the sinc tail and
the explicit head gives the same for the continued transform of a vector of `L_a`.

## Main results

* `extendedMellinRight`, `extendedMellinRight_eq`
* `differentiableOn_extendedMellinRight`
* `exists_norm_extendedMellinRight_le` — the crude `O(1+|t|)` bound on a closed substrip
-/

noncomputable section

open MeasureTheory Set Filter Topology

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-- The continued Mellin transform of a vector of `L_a`, right of the imaginary axis. -/
def extendedMellinRight (a : ℝ) (c d : ℂ) (f : SoninL2) (s : ℂ) : ℂ :=
  extendedTailMellin a c f s + d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)

theorem extendedMellinRight_eq {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d)
    {s : ℂ} (hs : 1 / 2 < s.re) (hs1 : s.re < 1) :
    extendedMellinRight a c d f s
      = ∫ t in Ioi (0 : ℝ), ((t : ℝ) : ℂ) ^ (-s) * (f : ℝ → ℂ) t := by
  rw [extendedMellinRight, extendedTailMellin_eq ha hc hs,
    integral_split_extendedMellin ha hd hs hs1]
  ring

theorem differentiableOn_extendedMellinRight {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c) :
    DifferentiableOn ℂ (extendedMellinRight a c d f) {s : ℂ | 0 < s.re ∧ s ≠ 1} := by
  have hane : ((a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  intro s hs
  refine DifferentiableAt.differentiableWithinAt ?_
  have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
  have h1 : DifferentiableAt ℂ (extendedTailMellin a c f) s :=
    (differentiableOn_extendedTailMellin ha hc).differentiableAt (hopen.mem_nhds hs.1)
  have hne : (1 : ℂ) - s ≠ 0 := by
    intro h
    exact hs.2 (by linear_combination -h)
  have h2 : DifferentiableAt ℂ (fun z : ℂ => d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - z) / (1 - z)) s := by
    refine DifferentiableAt.div ?_ ?_ hne
    · refine (differentiableAt_const d).mul ?_
      exact DifferentiableAt.const_cpow
        ((differentiableAt_const (1 : ℂ)).sub differentiableAt_id) (Or.inl hane)
    · exact (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
  exact h1.add h2

theorem rpow_le_max_of_mem_Icc {a σ σ₀ b : ℝ} (ha : 0 < a) (h0 : σ₀ ≤ σ) (h1 : σ ≤ b) :
    a ^ σ ≤ max (a ^ σ₀) (a ^ b) := by
  rcases le_or_gt a 1 with h | h
  · exact le_trans (Real.rpow_le_rpow_of_exponent_ge ha h h0) (le_max_left _ _)
  · exact le_trans (Real.rpow_le_rpow_of_exponent_le h.le h1) (le_max_right _ _)

/-- **The crude polynomial bound.**  On every closed substrip of the open right half-plane the
continued Mellin transform of a vector of `L_a` is `O(1 + ‖s‖)`. -/
theorem exists_norm_extendedMellinRight_le {a : ℝ} (ha : 0 < a) {f : SoninL2} {c d : ℂ}
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (σ₀ b : ℝ) (hσ₀ : 0 < σ₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, σ₀ ≤ s.re → s.re ≤ b → 1 ≤ |s.im| →
      ‖extendedMellinRight a c d f s‖ ≤ C * (1 + ‖s‖) := by
  set g : SoninL2 := f - c • fourierBandIndicator a with hg
  have hgmem : g ∈ (centralFourierForbidden a)ᗮ := sub_smul_fourierBandIndicator_mem hc
  set Apow : ℝ := max (a ^ (-b)) (a ^ (-σ₀)) with hApow
  have hApow0 : 0 ≤ Apow := le_trans (Real.rpow_nonneg ha.le _) (le_max_left _ _)
  set Bpow : ℝ := max (a ^ ((1 : ℝ) - b)) (a ^ ((1 : ℝ) - σ₀)) with hBpow
  have hBpow0 : 0 ≤ Bpow := le_trans (Real.rpow_nonneg ha.le _) (le_max_left _ _)
  have hN0 : 0 ≤ invAbsTailNorm a := invAbsTailNorm_nonneg a
  set C₁ : ℝ := Apow * (((2 + 1 / σ₀) / (2 * Real.pi)) * invAbsTailNorm a) * ‖g‖ with hC₁
  set C₂ : ℝ := ‖c‖ * ((1 / Real.pi) * (Apow / σ₀)) with hC₂
  set C₃ : ℝ := ‖d‖ * Bpow with hC₃
  have hC₁0 : 0 ≤ C₁ := by rw [hC₁]; positivity
  have hC₂0 : 0 ≤ C₂ := by rw [hC₂]; positivity
  have hC₃0 : 0 ≤ C₃ := by rw [hC₃]; positivity
  refine ⟨C₁ + C₂ + C₃, by linarith, ?_⟩
  intro s hs hsb ht
  have hs0 : 0 < s.re := lt_of_lt_of_le hσ₀ hs
  have hsn : (0 : ℝ) ≤ ‖s‖ := norm_nonneg s
  have hone : (1 : ℝ) ≤ 1 + ‖s‖ := by linarith
  have hApowle : a ^ (-s.re) ≤ Apow :=
    rpow_le_max_of_mem_Icc ha (by linarith : -b ≤ -s.re) (by linarith : -s.re ≤ -σ₀)
  have hBpowle : a ^ ((1 : ℝ) - s.re) ≤ Bpow :=
    rpow_le_max_of_mem_Icc ha (by linarith) (by linarith)
  -- piece 1
  have h1 : ‖soninMellinExtension g a s‖ ≤ C₁ * (1 + ‖s‖) := by
    refine (norm_soninMellinExtension_le ha hgmem hs0).trans ?_
    have hq1 : ‖s‖ / s.re ≤ (1 / σ₀) * ‖s‖ := by
      rw [div_eq_mul_inv, one_div, mul_comm]
      exact mul_le_mul_of_nonneg_right (inv_anti₀ hσ₀ hs) hsn
    have hq : (2 + ‖s‖ / s.re) ≤ (2 + 1 / σ₀) * (1 + ‖s‖) := by
      have hinv : (0 : ℝ) ≤ 1 / σ₀ := by positivity
      nlinarith
    have hq0 : (0 : ℝ) ≤ 2 + ‖s‖ / s.re := by positivity
    have hstep : a ^ (-s.re) * (((2 + ‖s‖ / s.re) / (2 * Real.pi)) * invAbsTailNorm a) * ‖g‖
        ≤ Apow * ((((2 + 1 / σ₀) * (1 + ‖s‖)) / (2 * Real.pi)) * invAbsTailNorm a) * ‖g‖ := by
      have hap : (0 : ℝ) ≤ a ^ (-s.re) := Real.rpow_nonneg ha.le _
      have hgn : (0 : ℝ) ≤ ‖g‖ := norm_nonneg g
      gcongr
    refine hstep.trans (le_of_eq ?_)
    rw [hC₁]
    ring
  -- piece 2
  have h2 : ‖c * sincMellin a s‖ ≤ C₂ * (1 + ‖s‖) := by
    have hsinc : ‖sincMellin a s‖ ≤ (1 / Real.pi) * (a ^ (-s.re) / s.re) := by
      rw [sincMellin_eq]
      exact norm_sincTail_le ha hs0 le_rfl
    have hle : (1 / Real.pi) * (a ^ (-s.re) / s.re) ≤ (1 / Real.pi) * (Apow / σ₀) := by
      have hpi : (0 : ℝ) ≤ 1 / Real.pi := by positivity
      have hap : (0 : ℝ) ≤ a ^ (-s.re) := Real.rpow_nonneg ha.le _
      gcongr
    have hfinal : ‖c‖ * ‖sincMellin a s‖ ≤ C₂ := by
      rw [hC₂]
      exact mul_le_mul_of_nonneg_left (hsinc.trans hle) (norm_nonneg c)
    rw [norm_mul]
    calc ‖c‖ * ‖sincMellin a s‖ ≤ C₂ := hfinal
      _ ≤ C₂ * (1 + ‖s‖) := by nlinarith
  -- piece 3
  have h3 : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ ≤ C₃ * (1 + ‖s‖) := by
    have hnum : ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s)‖ = ‖d‖ * a ^ ((1 : ℝ) - s.re) := by
      rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos ha]
      congr 2
    have hden : (1 : ℝ) ≤ ‖(1 : ℂ) - s‖ := by
      have him : ((1 : ℂ) - s).im = -s.im := by simp
      calc (1 : ℝ) ≤ |s.im| := ht
        _ = |((1 : ℂ) - s).im| := by rw [him, abs_neg]
        _ ≤ ‖(1 : ℂ) - s‖ := Complex.abs_im_le_norm _
    have hdn : (0 : ℝ) ≤ ‖d‖ := norm_nonneg d
    have hstep : ‖d‖ * a ^ ((1 : ℝ) - s.re) / ‖(1 : ℂ) - s‖ ≤ C₃ := by
      rw [hC₃, div_le_iff₀ (by linarith : (0:ℝ) < ‖(1 : ℂ) - s‖)]
      have hA : ‖d‖ * a ^ ((1 : ℝ) - s.re) ≤ ‖d‖ * Bpow :=
        mul_le_mul_of_nonneg_left hBpowle hdn
      nlinarith [mul_nonneg hdn hBpow0]
    rw [norm_div, hnum]
    calc ‖d‖ * a ^ ((1 : ℝ) - s.re) / ‖(1 : ℂ) - s‖ ≤ C₃ := hstep
      _ ≤ C₃ * (1 + ‖s‖) := by nlinarith
  calc ‖extendedMellinRight a c d f s‖
      ≤ ‖extendedTailMellin a c f s‖ + ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ := by
        rw [extendedMellinRight]
        exact norm_add_le _ _
    _ ≤ (‖soninMellinExtension g a s‖ + ‖c * sincMellin a s‖)
        + ‖d * ((a : ℝ) : ℂ) ^ ((1 : ℂ) - s) / (1 - s)‖ := by
        have hsub : ‖extendedTailMellin a c f s‖
            ≤ ‖soninMellinExtension g a s‖ + ‖c * sincMellin a s‖ := by
          rw [extendedTailMellin, ← hg]
          exact norm_add_le _ _
        linarith
    _ ≤ (C₁ * (1 + ‖s‖) + C₂ * (1 + ‖s‖)) + C₃ * (1 + ‖s‖) := by linarith
    _ = (C₁ + C₂ + C₃) * (1 + ‖s‖) := by ring

end RHTower

end
