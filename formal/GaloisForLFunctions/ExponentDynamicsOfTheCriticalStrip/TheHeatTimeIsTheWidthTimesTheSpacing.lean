import GaloisForLFunctions.RHTower.XiSliceHeatNewmanCosModelFlow

/-!
# The heat time is the width times the spacing

The heat time (de Bruijn–Newman time) is a half ruler of the width: `Λ ≤ w²/2`. E1 asks for a
two-sided law. The dense single-defect models `F(z) = (z² + δ²) cos(Lz/2)` (`RHTower.DeBruijn.cosDefect`)
have width `δ`: their only non-real zeros are `±iδ` (`abs_im_le_of_cosDefect_eq_zero`,
`cosDefect_I_mul`), between real zeros of spacing `2π/L`. Their heat flow is real-rooted at time
`δ/L` and keeps a zero on the imaginary axis at time `μ/L` for `μ < δ` once `L > 2μ/(δ² − μ²)`
(`cosDefectFlow_collision`).

* **The two-sided law** (`le_cosDefectHeatTime`, `cosDefectHeatTime_le`,
  `tendsto_mul_cosDefectHeatTime`): `μ/L ≤ Λ_L ≤ δ/L` and `L Λ_L → δ`. The heat time reads the width
  times the zero spacing.
* **No law in the width alone** (`exists_cosDefect_width_heatTime_lt`): for every `δ > 0` and
  `ε > 0` a model of width `δ` has heat time below `ε`. No bound `Λ ≥ Φ(w)` with `Φ(δ) > 0` holds on
  the models; a two-sided law for `ζ` has to use the density `(log γ)/2π` of its zeros.
-/

open Complex Filter Topology RHTower.DeBruijn

namespace GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip

noncomputable section

/-- The zeros of the model lie in `|Im z| ≤ δ`: `z² + δ² = 0` gives `z = ±iδ`, and the zeros of
`cos(Lz/2)` are real. -/
theorem abs_im_le_of_cosDefect_eq_zero {δ L : ℝ} {z : ℂ} (hz : cosDefect δ L z = 0) :
    |z.im| ≤ |δ| := by
  rcases mul_eq_zero.1 hz with h | h
  · have h' : (z - I * δ) * (z + I * δ) = 0 := by
      have hI : I ^ 2 = -1 := I_sq
      linear_combination h - (δ : ℂ) ^ 2 * hI
    rcases mul_eq_zero.1 h' with h1 | h1
    · rw [sub_eq_zero.1 h1]; simp
    · rw [eq_neg_of_add_eq_zero_left h1]; simp
  · by_cases hL : L = 0
    · rw [hL] at h
      simp at h
    · obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.1 h
      have hLc : (L : ℂ) ≠ 0 := by exact_mod_cast hL
      have hz' : z = (((2 * k + 1) * Real.pi / L : ℝ) : ℂ) := by
        push_cast
        field_simp
        linear_combination 2 * hk
      rw [hz', ofReal_im, abs_zero]
      exact abs_nonneg δ

/-- The model has the zero `iδ`: its width is attained. -/
theorem cosDefect_I_mul (δ L : ℝ) : cosDefect δ L (I * δ) = 0 := by
  unfold cosDefect
  have hI : I ^ 2 = -1 := I_sq
  rw [show (I * (δ : ℂ)) ^ 2 + (δ : ℂ) ^ 2 = (δ : ℂ) ^ 2 * (I ^ 2 + 1) by ring, hI]
  ring

/-- The heat time of the model: the least time after which its flow is real-rooted. -/
def cosDefectHeatTime (δ L : ℝ) : ℝ :=
  sInf {t : ℝ | 0 < t ∧ ∀ z : ℂ, cosDefectFlow δ L t z = 0 → z.im = 0}

/-- The flow is real-rooted at time `δ/L`, so `Λ_L ≤ δ/L`. -/
theorem cosDefectHeatTime_le {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    cosDefectHeatTime δ L ≤ δ / L :=
  csInf_le ⟨0, fun _ ht => ht.1.le⟩
    ⟨div_pos hδ hL, (cosDefectFlow_collision hδ hL).1 le_rfl⟩

/-- For `0 < μ < δ` and `L > 2μ/(δ² − μ²)` the flow is not real-rooted before `μ/L`: `μ/L ≤ Λ_L`. -/
theorem le_cosDefectHeatTime {δ μ L : ℝ} (hδ : 0 < δ) (hμ : 0 < μ) (hμδ : μ < δ)
    (hL : 2 * μ / (δ ^ 2 - μ ^ 2) < L) : μ / L ≤ cosDefectHeatTime δ L := by
  have hden : 0 < δ ^ 2 - μ ^ 2 := by nlinarith
  have hL0 : 0 < L := lt_of_le_of_lt (by positivity) hL
  refine le_csInf ⟨δ / L, div_pos hδ hL0, (cosDefectFlow_collision hδ hL0).1 le_rfl⟩ fun t ht => ?_
  by_contra hlt
  rw [not_le] at hlt
  have hμ' : 0 < t * L := mul_pos ht.1 hL0
  have hμ'μ : t * L < μ := by rwa [lt_div_iff₀ hL0] at hlt
  have hL' : 2 * (t * L) / (δ ^ 2 - (t * L) ^ 2) < L := by
    refine lt_of_le_of_lt ?_ hL
    have hden' : 0 < δ ^ 2 - (t * L) ^ 2 := by nlinarith
    rw [div_le_div_iff₀ hden' hden]
    nlinarith [mul_pos (sub_pos.2 hμ'μ) (by positivity : (0 : ℝ) < δ ^ 2 + t * L * μ)]
  obtain ⟨Y, hY, hz⟩ := (cosDefectFlow_collision hδ hL0).2 hμ' (by linarith) hL'
  rw [mul_div_cancel_right₀ t hL0.ne'] at hz
  have := ht.2 _ hz
  simp at this
  exact hY.ne' this

/-- **The heat time is the width times the spacing:** `L Λ_L → δ`. -/
theorem tendsto_mul_cosDefectHeatTime {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun L => L * cosDefectHeatTime δ L) atTop (𝓝 δ) := by
  rw [tendsto_order]
  refine ⟨fun a ha => ?_, fun a ha => ?_⟩
  · set μ := (max a (δ / 2) + δ) / 2 with hμdef
    have hμ0 : 0 < μ := by have := le_max_right a (δ / 2); linarith
    have hμδ : μ < δ := by have := max_lt ha (by linarith : δ / 2 < δ); linarith
    have haμ : a < μ := by have := le_max_left a (δ / 2); have := max_lt ha (by linarith : δ / 2 < δ); linarith
    filter_upwards [eventually_gt_atTop (max (2 * μ / (δ ^ 2 - μ ^ 2)) 0)] with L hL
    have hL0 : 0 < L := lt_of_le_of_lt (le_max_right _ _) hL
    have h := le_cosDefectHeatTime hδ hμ0 hμδ (lt_of_le_of_lt (le_max_left _ _) hL)
    rw [div_le_iff₀ hL0] at h
    linarith
  · filter_upwards [eventually_gt_atTop 0] with L hL
    have h := cosDefectHeatTime_le hδ hL
    rw [le_div_iff₀ hL] at h
    linarith

/-- **No law in the width alone.** For every `δ > 0` and `ε > 0` there is a model whose zeros lie in
`|Im z| ≤ δ`, with a zero at `iδ`, whose heat time is below `ε`. -/
theorem exists_cosDefect_width_heatTime_lt {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ L : ℝ, 0 < L ∧ (∀ z : ℂ, cosDefect δ L z = 0 → |z.im| ≤ δ) ∧ cosDefect δ L (I * δ) = 0 ∧
      cosDefectHeatTime δ L < ε := by
  refine ⟨2 * δ / ε, by positivity, fun z hz => ?_, cosDefect_I_mul δ _, ?_⟩
  · have := abs_im_le_of_cosDefect_eq_zero hz
    rwa [abs_of_pos hδ] at this
  · refine lt_of_le_of_lt (cosDefectHeatTime_le hδ (by positivity)) ?_
    rw [div_div_eq_mul_div, div_lt_iff₀ (by positivity)]
    nlinarith

#print axioms tendsto_mul_cosDefectHeatTime
#print axioms exists_cosDefect_width_heatTime_lt

end

end GaloisForLFunctions.ExponentDynamicsOfTheCriticalStrip
