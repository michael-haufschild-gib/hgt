import GaloisForLFunctions.RHTower.Heat.TheLocalDeBruijnNewmanConstant
import GaloisForLFunctions.RHTower.XiOrdinateBandCopies

/-!
# A heat coefficient gives an explicit zero-free strip

The local de Bruijn–Newman lower bound reads `c · depth² ≤ Λ_X log X` at a zero of height `X`, so a
ceiling `Λ_X log X ≤ κ` caps the depth of every zero above the height where it holds:

* `exists_abs_re_sub_half_le_of_heatCoefficient`: `|Re ρ − ½| ≤ √(κ/c)` for every zero with `|Im ρ| ≥ X₁`;
* `exists_zeroFreeStrip_of_heatCoefficient`: for `κ` below `c/4` the ceiling at all large heights gives a
  genuine zero-free half-plane `Re s > σ`, `σ < 1`, the finitely many lower zeros being absorbed;
* `exists_depth_tendsto_zero_of_heatCoefficient`: `Λ_X log X → 0` forces the depth of the zeros to
  tend to `0` with the height.

The coefficient `c` is the one of `exists_le_localNewmanConstant_of_offLine_zero`.
-/

open Complex Filter Topology Set

namespace RHTower.DeBruijn

noncomputable section

/-- **Strip from a heat coefficient.** With the constants of the local lower bound, a ceiling
`Λ_X log X ≤ κ` on `X ≥ X₁` confines every zero of `ξ` with `|Im ρ| ≥ X₁` to depth `√(κ/c)`. -/
theorem exists_abs_re_sub_half_le_of_heatCoefficient :
    ∃ c : ℝ, 0 < c ∧ ∃ X₀ : ℝ, 4096 ≤ X₀ ∧ ∀ κ X₁ : ℝ, 0 ≤ κ → X₀ ≤ X₁ →
      (∀ X, X₁ ≤ X → localNewmanConstant X * Real.log X ≤ κ) →
      ∀ ρ : ℂ, xi ρ = 0 → X₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ Real.sqrt (κ / c) := by
  obtain ⟨c, hc, X₀, hX₀, h⟩ := exists_le_localNewmanConstant_of_offLine_zero
  refine ⟨c, hc, X₀, hX₀, fun κ X₁ hκ hX₁ hceil ρ hρ him => ?_⟩
  -- reduce to the upper half-plane by conjugation
  obtain ⟨σ, hσ, hσim, hσre⟩ : ∃ σ : ℂ, xi σ = 0 ∧ X₁ ≤ σ.im ∧ σ.re = ρ.re := by
    rcases le_or_gt 0 ρ.im with hpos | hneg
    · exact ⟨ρ, hρ, by rwa [abs_of_nonneg hpos] at him, rfl⟩
    · refine ⟨(starRingEnd ℂ) ρ, ?_, ?_, by simp⟩
      · rw [xi_conj, hρ, map_zero]
      · rw [abs_of_neg hneg] at him
        simpa using him
  rw [← hσre]
  by_cases hline : σ.re = 1 / 2
  · rw [hline, sub_self, abs_zero]
    exact Real.sqrt_nonneg _
  have hX : X₀ ≤ σ.im := hX₁.trans hσim
  have hlow := h σ hσ hX hline
  have hup := hceil σ.im hσim
  have hL : 0 < Real.log σ.im := Real.log_pos (by linarith)
  have hmul : c * (σ.re - 1 / 2) ^ 2 ≤ κ := by
    have := mul_le_mul_of_nonneg_right hlow hL.le
    rw [div_mul_cancel₀ _ hL.ne'] at this
    exact this.trans hup
  apply Real.le_sqrt_of_sq_le
  rw [sq_abs, le_div_iff₀ hc]
  linarith only [hmul]

/-- **Strip strength of a small coefficient.** There is `κ₀ > 0` such that a ceiling
`Λ_X log X ≤ κ < κ₀` at all large heights gives a zero-free half-plane `Re s > σ` with `σ < 1`. -/
theorem exists_zeroFreeStrip_of_heatCoefficient :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 ≤ κ → κ < κ₀ →
      (∀ᶠ X in atTop, localNewmanConstant X * Real.log X ≤ κ) →
      ∃ σ : ℝ, σ < 1 ∧ ∀ ρ : ℂ, xi ρ = 0 → ρ.re ≤ σ := by
  obtain ⟨c, hc, X₀, hX₀, h⟩ := exists_abs_re_sub_half_le_of_heatCoefficient
  refine ⟨c / 4, by positivity, fun κ hκ hκ0 hev => ?_⟩
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp hev
  set X₁ := max X₀ X₂ with hX₁
  have hceil : ∀ X, X₁ ≤ X → localNewmanConstant X * Real.log X ≤ κ :=
    fun X hX => hX₂ X ((le_max_right _ _).trans hX)
  have hdepth := h κ X₁ hκ (le_max_left _ _) hceil
  -- the zeros below `X₁` are finitely many, each to the left of `Re s = 1`
  have hfin := (xiZerosUpTo_finite X₁).image Complex.re
  have hlt : ∀ ρ : ℂ, xi ρ = 0 → ρ.re < 1 := fun ρ hρ => by
    by_contra hge
    push Not at hge
    exact xi_ne_zero_of_one_le_re hge hρ
  have hsqrt : Real.sqrt (κ / c) < 1 / 2 := by
    rw [Real.sqrt_lt' (by norm_num), div_lt_iff₀ hc]
    linarith only [hκ0]
  obtain ⟨b, hbmem, hb⟩ : ∃ b : ℝ, b < 1 ∧
      ∀ y ∈ Complex.re '' {u : ℂ | xi u = 0 ∧ |u.im| ≤ X₁}, y ≤ b := by
    by_cases hne : (Complex.re '' {u : ℂ | xi u = 0 ∧ |u.im| ≤ X₁}).Nonempty
    · obtain ⟨y, hy, hmax⟩ := Set.exists_max_image _ id hfin hne
      obtain ⟨u, hu, rfl⟩ := hy
      exact ⟨u.re, hlt u hu.1, fun z hz => hmax z hz⟩
    · refine ⟨0, by norm_num, fun y hy => (hne ⟨y, hy⟩).elim⟩
  refine ⟨max b (1 / 2 + Real.sqrt (κ / c)), max_lt hbmem (by linarith only [hsqrt]), ?_⟩
  intro ρ hρ
  rcases le_or_gt |ρ.im| X₁ with hlow | hhigh
  · exact (hb _ ⟨ρ, ⟨hρ, hlow⟩, rfl⟩).trans (le_max_left _ _)
  · have := abs_le.mp (hdepth ρ hρ hhigh.le)
    exact le_trans (by linarith only [this.2]) (le_max_right _ _)

/-- `Λ_X log X → 0` forces the depth of the zeros to tend to `0` with the height. -/
theorem exists_depth_tendsto_zero_of_heatCoefficient :
    ∃ X₀ : ℝ, 4096 ≤ X₀ ∧
      (Tendsto (fun X => localNewmanConstant X * Real.log X) atTop (𝓝 0) →
        ∀ ε : ℝ, 0 < ε → ∃ X₁ : ℝ, X₀ ≤ X₁ ∧
          ∀ ρ : ℂ, xi ρ = 0 → X₁ ≤ |ρ.im| → |ρ.re - 1 / 2| ≤ ε) := by
  obtain ⟨c, hc, X₀, hX₀, h⟩ := exists_abs_re_sub_half_le_of_heatCoefficient
  refine ⟨X₀, hX₀, fun hlim ε hε => ?_⟩
  have hκ : 0 < c * ε ^ 2 := by positivity
  obtain ⟨X₂, hX₂⟩ := eventually_atTop.mp (hlim.eventually (gt_mem_nhds hκ))
  refine ⟨max X₀ X₂, le_max_left _ _, fun ρ hρ him => ?_⟩
  have hd := h (c * ε ^ 2) (max X₀ X₂) hκ.le (le_max_left _ _)
    (fun X hX => (hX₂ X ((le_max_right _ _).trans hX)).le) ρ hρ him
  rwa [mul_div_cancel_left₀ _ hc.ne', Real.sqrt_sq hε.le] at hd

end

end RHTower.DeBruijn

#print axioms RHTower.DeBruijn.exists_zeroFreeStrip_of_heatCoefficient
#print axioms RHTower.DeBruijn.exists_depth_tendsto_zero_of_heatCoefficient
