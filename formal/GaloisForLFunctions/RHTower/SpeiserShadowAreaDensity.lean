import GaloisForLFunctions.RHTower.SpeiserShadowExponentialDensity

/-!
# The Hadamard sign and Speiser's sign hold on almost all of the critical strip, by area

**Theorem** (`exists_hadamardSpeiser_area_density_one`). For every `ε > 0`, for all large `U`
there are admissible heights `T₁ ∈ (U/4, U/4 + 1)`, `T₂ ∈ (U/2 − 1, U/2)` such that the set of points
`s` with `0 < Re s < 1`, `T₁ + 1/2 ≤ Im s ≤ T₂ − 1/2` where a local RH sign fails has area at most
`ε (T₂ − T₁)`. The two signs are:
- the Hadamard sign `ξ(s) ≠ 0`, `Re(ξ'/ξ)(s) ≥ 0`, for `Re s > 1/2`;
- Speiser's sign `ζ'(s) ≠ 0`, for `Re s < 1/2`.

The total area of the window is `T₂ − T₁ − 1`. The previous corpus bound was `58%` of the area,
from the linear off-line moment.

**Proof.**
- Off the `κ`-shadow set of heights, both signs hold at horizontal distance `≥ κ/L` from the line
  (`signs_of_not_mem_kappaShadow`).
- So the failure set at distance `≥ κ/L` lies in `[0, 1] × (κ-shadow)`, of area at most the shadow
  measure `A'(T₂ − T₁)e^{−κ/2400} + K'L²` (`exists_speiserShadow_exponential_density`).
- The strip `|Re s − 1/2| < κ/L` has area `(2κ/L)(T₂ − T₁)`.
- Take `κ = 2400 log(2A'/ε)` (bounded, independent of `U`); then both parts are `≤ (ε/2)(T₂ − T₁)`
  for large `U`.
-/

open Complex Set MeasureTheory Filter

namespace RHTower

noncomputable section

/-- The failure set of the two local RH signs in the window `[T₁ + 1/2, T₂ − 1/2]`. -/
def localSignFailSet (T₁ T₂ : ℝ) : Set ℂ :=
  {s : ℂ | 0 < s.re ∧ s.re < 1 ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2 ∧
    ((1 / 2 < s.re ∧ ¬ (xi s ≠ 0 ∧ 0 ≤ (logDeriv xi s).re)) ∨
      (s.re < 1 / 2 ∧ deriv riemannZeta s = 0))}

/-- The product set `[0, 1] × H` in `ℂ` has area `vol H`. -/
theorem volume_reProdIm_Icc_zero_one (H : Set ℝ) (hH : MeasurableSet H) :
    volume (Icc (0 : ℝ) 1 ×ℂ H) = volume H := by
  rw [show (Icc (0 : ℝ) 1 ×ℂ H) = Complex.measurableEquivRealProd ⁻¹' (Icc 0 1 ×ˢ H) from rfl,
    Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod hH).nullMeasurableSet, Measure.volume_eq_prod, Measure.prod_prod,
    Real.volume_Icc]
  simp

/-- The near-line strip `|Re s − 1/2| < κ/L` of the window has area `(2κ/L)(T₂ − T₁ − 1)`. -/
theorem volume_nearLine_le {T₁ T₂ r : ℝ} (hr : 0 ≤ r) :
    volume {s : ℂ | |s.re - 1 / 2| < r ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2} ≤
      ENNReal.ofReal (2 * r * (T₂ - T₁)) := by
  have hsub : {s : ℂ | |s.re - 1 / 2| < r ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2} ⊆
      Complex.measurableEquivRealProd ⁻¹' (Icc (1 / 2 - r) (1 / 2 + r) ×ˢ Icc T₁ T₂) := by
    intro s ⟨h1, h2, h3⟩
    simp only [mem_preimage, Complex.measurableEquivRealProd_apply, mem_prod, mem_Icc]
    rw [abs_lt] at h1
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  refine (measure_mono hsub).trans ?_
  rw [Complex.volume_preserving_equiv_real_prod.measure_preimage
      (measurableSet_Icc.prod measurableSet_Icc).nullMeasurableSet, Measure.volume_eq_prod,
    Measure.prod_prod, Real.volume_Icc, Real.volume_Icc, ← ENNReal.ofReal_mul (by linarith)]
  exact le_of_eq (by ring_nf)

/-- **Area form of the exponential shadow density.** For every `2 ≤ κ ≤ L/2 − 2`, the failure set
at horizontal distance `≥ κ/L` from the line has area at most `A'(T₂ − T₁)e^{−κ/2400} + K'L²`. -/
theorem exists_localSignFail_far_area :
    ∃ A' K' : ℝ, 0 ≤ A' ∧ 0 ≤ K' ∧ ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        ∀ κ : ℝ, 2 ≤ κ → κ ≤ Real.log U / 2 - 2 →
          volume (localSignFailSet T₁ T₂ ∩ {s : ℂ | κ / Real.log U ≤ |s.re - 1 / 2|}) ≤
            ENNReal.ofReal (A' * (T₂ - T₁) * Real.exp (-(κ / 2400)) + K' * Real.log U ^ 2) := by
  obtain ⟨A', K', hA', hK', hev⟩ := exists_speiserShadow_exponential_density
  refine ⟨A', K', hA', hK', ?_⟩
  filter_upwards [hev, eventually_ge_atTop (800 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (4 : ℝ)] with U hU hU800 hL4
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, fun κ hκ hκL => ?_⟩
  set L := Real.log U with hL
  have hL0 : 0 < L := by linarith
  set H : Set ℝ := {t : ℝ | t ∈ Icc (T₁ + 1 / 2) (T₂ - 1 / 2) ∧ ∃ ρ : ℂ, xi ρ = 0 ∧
      κ / L ≤ |ρ.re - 1 / 2| ∧ |t - ρ.im| ≤ |ρ.re - 1 / 2|} with hH
  have hsub : localSignFailSet T₁ T₂ ∩ {s : ℂ | κ / L ≤ |s.re - 1 / 2|} ⊆
      (Icc (0 : ℝ) 1 ×ℂ toMeasurable volume H) := by
    rintro s ⟨⟨h0, h1, h2, h3, hfail⟩, hfar⟩
    refine Complex.mem_reProdIm.mpr ⟨⟨h0.le, h1.le⟩, subset_toMeasurable _ _ ⟨⟨h2, h3⟩, ?_⟩⟩
    by_contra hno
    have ht : 100 ≤ s.im := by linarith [hT₁.1]
    have hsigns := signs_of_not_mem_kappaShadow hL0 (by linarith) ht hno
    have hs : s = ((s.re : ℝ) : ℂ) + (s.im : ℝ) * I := (Complex.re_add_im s).symm
    have hfar' : κ / L ≤ |s.re - 1 / 2| := hfar
    rcases hfail with ⟨hr, hf⟩ | ⟨hr, hd⟩
    · apply hf
      have := hsigns.1 s.re (by rw [abs_of_pos (by linarith)] at hfar'; linarith)
      rw [← hs] at this
      exact this
    · apply hsigns.2 s.re h0 (by rw [abs_of_neg (by linarith)] at hfar'; linarith)
      rw [← hs]; exact hd
  refine (measure_mono hsub).trans ?_
  rw [volume_reProdIm_Icc_zero_one _ (measurableSet_toMeasurable _ _), measure_toMeasurable]
  exact hbound κ hκ hκL

/-- **The local RH signs hold on almost all of the strip, by area.** -/
theorem exists_hadamardSpeiser_area_density_one :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ U in atTop,
      ∃ T₁ ∈ Ioo (U / 4) (U / 4 + 1), ∃ T₂ ∈ Ioo (U / 2 - 1) (U / 2),
        volume (localSignFailSet T₁ T₂) ≤ ENNReal.ofReal (ε * (T₂ - T₁)) := by
  intro ε hε
  obtain ⟨A', K', hA', hK', hev⟩ := exists_localSignFail_far_area
  -- the fixed scale `κ`
  set κ : ℝ := max 2 (2400 * Real.log (4 * (A' + 1) / ε)) with hκ
  have hκ2 : 2 ≤ κ := le_max_left _ _
  have hexp : A' * Real.exp (-(κ / 2400)) ≤ ε / 4 := by
    have hy : 0 < 4 * (A' + 1) / ε := by positivity
    have h1 : Real.log (4 * (A' + 1) / ε) ≤ κ / 2400 := by
      have h := le_max_right (2 : ℝ) (2400 * Real.log (4 * (A' + 1) / ε))
      have h' : 2400 * Real.log (4 * (A' + 1) / ε) ≤ κ := by rw [hκ]; exact h
      linarith
    have h2 : Real.exp (-(κ / 2400)) ≤ ε / (4 * (A' + 1)) := by
      have e : ε / (4 * (A' + 1)) = Real.exp (-Real.log (4 * (A' + 1) / ε)) := by
        rw [Real.exp_neg, Real.exp_log hy]; field_simp
      rw [e]
      exact Real.exp_le_exp.mpr (by linarith)
    have h3 : A' * (ε / (4 * (A' + 1))) ≤ ε / 4 := by
      rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    calc A' * Real.exp (-(κ / 2400)) ≤ A' * (ε / (4 * (A' + 1))) :=
          mul_le_mul_of_nonneg_left h2 hA'
      _ ≤ ε / 4 := h3
  -- `U` large: `κ ≤ L/2 − 2`, `2κ/L ≤ ε/4`, `K'L² ≤ (ε/4)(U/4 − 2)`
  have hLtend := Real.tendsto_log_atTop
  have hratio : Tendsto (fun U : ℝ => Real.log U ^ 2 / U) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  filter_upwards [hev, hLtend.eventually_ge_atTop (2 * κ + 4),
    hLtend.eventually_ge_atTop (8 * κ / ε),
    hratio.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (32 * (K' + 1)) by positivity)),
    eventually_ge_atTop (64 : ℝ)] with U hU hL1 hL2 hL3 hU64
  obtain ⟨T₁, hT₁, T₂, hT₂, hbound⟩ := hU
  refine ⟨T₁, hT₁, T₂, hT₂, ?_⟩
  set L := Real.log U with hL
  have hL0 : 0 < L := by
    have : 0 < 2 * κ + 4 := by linarith
    linarith
  have hΔ : U / 4 - 2 ≤ T₂ - T₁ := by linarith [hT₁.2, hT₂.1]
  have hΔ0 : 0 < T₂ - T₁ := by linarith
  -- split by distance from the line
  have hsplit : localSignFailSet T₁ T₂ ⊆
      {s : ℂ | |s.re - 1 / 2| < κ / L ∧ T₁ + 1 / 2 ≤ s.im ∧ s.im ≤ T₂ - 1 / 2} ∪
        (localSignFailSet T₁ T₂ ∩ {s : ℂ | κ / L ≤ |s.re - 1 / 2|}) := by
    intro s hs
    by_cases h : κ / L ≤ |s.re - 1 / 2|
    · exact Or.inr ⟨hs, h⟩
    · exact Or.inl ⟨lt_of_not_ge h, hs.2.2.1, hs.2.2.2.1⟩
  refine (measure_mono hsplit).trans ((measure_union_le _ _).trans ?_)
  have hnear := volume_nearLine_le (T₁ := T₁) (T₂ := T₂) (r := κ / L) (div_nonneg (by linarith) hL0.le)
  have hfar := hbound κ hκ2 (by linarith)
  refine (add_le_add hnear hfar).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  -- the three terms
  have t1 : 2 * (κ / L) * (T₂ - T₁) ≤ ε / 4 * (T₂ - T₁) := by
    have h8 : 8 * κ ≤ ε * L := by
      have := hL2; rw [div_le_iff₀ hε] at this; linarith
    have : 2 * (κ / L) ≤ ε / 4 := by
      rw [show 2 * (κ / L) = (2 * κ) / L by ring, div_le_iff₀ hL0]; nlinarith
    exact mul_le_mul_of_nonneg_right this hΔ0.le
  have t2 : A' * (T₂ - T₁) * Real.exp (-(κ / 2400)) ≤ ε / 4 * (T₂ - T₁) := by
    calc A' * (T₂ - T₁) * Real.exp (-(κ / 2400)) = A' * Real.exp (-(κ / 2400)) * (T₂ - T₁) := by
          ring
      _ ≤ ε / 4 * (T₂ - T₁) := mul_le_mul_of_nonneg_right hexp hΔ0.le
  have t3 : K' * L ^ 2 ≤ ε / 2 * (T₂ - T₁) := by
    have hU0 : 0 < U := by linarith
    have h1 : L ^ 2 < ε / (32 * (K' + 1)) * U := by
      have := hL3; rw [div_lt_iff₀ hU0] at this; linarith
    have h2 : K' * L ^ 2 ≤ (K' + 1) * L ^ 2 := by nlinarith [sq_nonneg L]
    have h3 : (K' + 1) * L ^ 2 ≤ ε / 32 * U := by
      have := mul_lt_mul_of_pos_left h1 (by positivity : (0 : ℝ) < K' + 1)
      have e : (K' + 1) * (ε / (32 * (K' + 1)) * U) = ε / 32 * U := by field_simp
      linarith
    nlinarith
  linarith

end

end RHTower
