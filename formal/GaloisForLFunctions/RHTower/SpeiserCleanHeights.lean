import GaloisForLFunctions.RHTower.SpeiserEventualEquivalence
import GaloisForLFunctions.RHTower.XiSliceCoeffDensity

/-!
# Clean horizontal lines at unshadowed heights

At an unshadowed height `T ≥ 101` (`SpeiserUnshadowed T`), the whole horizontal line `Im s = T`
carries the RH-equivalent signs at once (`cleanLine_of_speiserUnshadowed`):
- on `0 < Re s < 1/2`: `ζ ≠ 0`, `ζ' ≠ 0` and `Re ζ'/ζ < 0`, so `|ζ|` is strictly decreasing in
  `Re s` there;
- on `Re s > 1/2`: `ξ ≠ 0` and `Re ξ'/ξ ≥ 0` (Hadamard sign), from the disk criterion.

Unshadowed heights have lower density at least `29/50`
(`eventually_volume_speiserUnshadowed_ge`). This follows from the shadow measure bound
`vol(S ∩ [0,V]) ≤ 2 Σ m(β − 1/2)⁺ ≤ (42/100)(V + 1/2)`.

The unshadowed heights are exactly the complement of the de Bruijn shadow set
(`speiserUnshadowed_iff_not_mem_xiShadow`). So one exceptional set carries every local
RH-equivalent sign (`allRHSigns_of_speiserUnshadowed`):
- the first Laguerre inequality and vertical monotonicity of `|Ξ|`;
- nonnegativity of all horizontal slice coefficients;
- the Hadamard sign;
- the Speiser sign;
- horizontal monotonicity of `|ζ|`.
-/

open Complex Set Filter MeasureTheory
open scoped ComplexOrder

namespace RHTower

noncomputable section

/-- **Clean lines.** At an unshadowed height `T ≥ 101`, the Speiser sign holds on the left half of
the horizontal line, the modulus of `ζ` is strictly decreasing there, and the Hadamard sign holds
on the right half. -/
theorem cleanLine_of_speiserUnshadowed {T : ℝ} (hT : 101 ≤ T) (hu : SpeiserUnshadowed T) :
    (∀ σ : ℝ, 0 < σ → σ < 1 / 2 →
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧ deriv riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).re < 0) ∧
    (∀ a b : ℝ, 0 < a → b < 1 / 2 →
      StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ^ (2 : ℕ)) (Icc a b)) ∧
    (∀ σ : ℝ, 1 / 2 < σ → xi ((σ : ℂ) + T * I) ≠ 0 ∧
      0 ≤ (logDeriv xi ((σ : ℂ) + T * I)).re) := by
  refine ⟨fun σ h0 h1 => ?_, fun a b ha hb => ?_, fun σ hσ => ?_⟩
  · obtain ⟨hζ, hre⟩ := re_logDeriv_riemannZeta_neg_of_unshadowed (x := σ) (by linarith) hu h0 h1
    refine ⟨hζ, fun hd => ?_, hre⟩
    rw [logDeriv_apply, hd, zero_div, Complex.zero_re] at hre
    exact lt_irrefl 0 hre
  · refine strictAntiOn_normSq_riemannZeta_horizontal ha hb (by linarith) fun σ hσ ρ hρ _ _ => ?_
    have h1 := hu ρ hρ
    have h2 : 0 < (σ - 1 / 2) ^ 2 := by
      have : σ - 1 / 2 ≠ 0 := by linarith [hσ.2]
      positivity
    linarith
  · have hre : ((σ : ℂ) + T * I).re = σ := by simp
    have him : ((σ : ℂ) + T * I).im = T := by simp
    have hxi : xi ((σ : ℂ) + T * I) ≠ 0 := by
      intro h0
      have h1 := hu _ h0
      rw [hre, him, sub_self, zero_pow two_ne_zero] at h1
      have : σ - 1 / 2 ≠ 0 := by linarith
      have := pow_pos (abs_pos.mpr this) 2
      rw [sq_abs] at this
      linarith
    refine ⟨hxi, re_logDeriv_xi_nonneg_of_disk_bound (by rw [hre]; exact hσ) hxi fun q => ?_⟩
    have h1 := hu (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
    rw [hre, him]
    have h2 : 0 < (σ - 1 / 2) ^ 2 := by
      have : σ - 1 / 2 ≠ 0 := by linarith
      positivity
    linarith

/-- Unshadowed heights are exactly the complement of the de Bruijn shadow set. -/
theorem speiserUnshadowed_iff_not_mem_xiShadow {T : ℝ} :
    SpeiserUnshadowed T ↔ T ∉ DeBruijn.xiShadow := by
  refine ⟨fun hu hmem => ?_, speiserUnshadowed_of_not_mem_xiShadow⟩
  obtain ⟨z, hz, hlt⟩ := hmem
  have hρ : xi (1 / 2 + I * z) = 0 := by rw [← DeBruijn.riemannHeat_zero]; exact hz
  have h := hu _ hρ
  have hre : (1 / 2 + I * z).re = 1 / 2 - z.im := by simp; ring
  have him : (1 / 2 + I * z).im = z.re := by simp
  rw [hre, him] at h
  nlinarith

/-- **One exceptional set for all local RH signs.** At an unshadowed height `T ≥ 101`:
- the first Laguerre inequality holds for `Ξ = H_0` at `T`, and `y ↦ |Ξ(T + iy)|` is monotone;
- every horizontal slice coefficient `c_n(T)` is nonnegative;
- the Speiser sign, horizontal monotonicity of `|ζ|` and the Hadamard sign hold along the whole
  line `Im s = T` (`cleanLine_of_speiserUnshadowed`). -/
theorem allRHSigns_of_speiserUnshadowed {T : ℝ} (hT : 101 ≤ T) (hu : SpeiserUnshadowed T) :
    (MonotoneOn (fun y : ℝ => ‖DeBruijn.riemannHeat 0 ((T : ℂ) + I * y)‖) (Ici 0) ∧
      0 ≤ (deriv (DeBruijn.riemannHeat 0) T ^ 2 -
        DeBruijn.riemannHeat 0 T * deriv (deriv (DeBruijn.riemannHeat 0)) T).re) ∧
    (∀ n : ℕ, 0 ≤ xiSliceCoeff T n) ∧
    ((∀ σ : ℝ, 0 < σ → σ < 1 / 2 →
      riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧ deriv riemannZeta ((σ : ℂ) + T * I) ≠ 0 ∧
        (logDeriv riemannZeta ((σ : ℂ) + T * I)).re < 0) ∧
    (∀ a b : ℝ, 0 < a → b < 1 / 2 →
      StrictAntiOn (fun σ : ℝ => ‖riemannZeta ((σ : ℂ) + (T : ℂ) * I)‖ ^ (2 : ℕ)) (Icc a b)) ∧
    (∀ σ : ℝ, 1 / 2 < σ → xi ((σ : ℂ) + T * I) ≠ 0 ∧
      0 ≤ (logDeriv xi ((σ : ℂ) + T * I)).re)) := by
  have hsh := speiserUnshadowed_iff_not_mem_xiShadow.mp hu
  exact ⟨DeBruijn.monotoneOn_laguerre_of_not_mem_xiShadow hsh,
    DeBruijn.xiSliceCoeff_nonneg_of_not_mem_xiShadow hsh, cleanLine_of_speiserUnshadowed hT hu⟩

/-- **Density of clean heights.** Eventually, the unshadowed heights in `[0, V]` have measure at
least `(29/50) V − 21/100`. -/
theorem eventually_volume_speiserUnshadowed_ge :
    ∀ᶠ V in atTop, ENNReal.ofReal (29 / 50 * V - 21 / 100) ≤
      volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} := by
  have h := (tendsto_atTop_add_const_right atTop (1 / 2 : ℝ) tendsto_id).eventually
    ZetaGateProductAFE.eventually_offLineMoment_le
  filter_upwards [h, eventually_ge_atTop 0] with V hV hV0
  simp only [id] at hV
  have hsub : Icc 0 V ⊆ {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} ∪
      (DeBruijn.xiShadow ∩ Icc 0 V) := by
    intro T hT
    by_cases hS : T ∈ DeBruijn.xiShadow
    · exact Or.inr ⟨hS, hT⟩
    · exact Or.inl ⟨hT, speiserUnshadowed_of_not_mem_xiShadow hS⟩
  have hvol := (measure_mono (μ := volume) hsub).trans (measure_union_le _ _)
  rw [Real.volume_Icc] at hvol
  have hsh := DeBruijn.volume_xiShadow_inter_Icc_le_offLineMoment V
  have hsh' : volume (DeBruijn.xiShadow ∩ Icc 0 V) ≤ ENNReal.ofReal (42 / 100 * V + 21 / 100) :=
    hsh.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have htot : ENNReal.ofReal (V - 0) ≤ volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} +
      ENNReal.ofReal (42 / 100 * V + 21 / 100) := hvol.trans (add_le_add_right hsh' _)
  have hfin : volume {T : ℝ | T ∈ Icc 0 V ∧ SpeiserUnshadowed T} ≠ ⊤ := by
    refine ne_top_of_le_ne_top (b := volume (Icc (0 : ℝ) V)) ?_
      (measure_mono fun T hT => hT.1)
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  rw [← ENNReal.ofReal_toReal hfin] at htot ⊢
  rw [← ENNReal.ofReal_add ENNReal.toReal_nonneg (by linarith)] at htot
  have := (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp htot
  exact ENNReal.ofReal_le_ofReal (by linarith)

end

end RHTower
