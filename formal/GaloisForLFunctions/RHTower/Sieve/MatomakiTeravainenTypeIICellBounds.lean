import GaloisForLFunctions.RHTower.Sieve.PrimePowerAmplifierScale

/-!
# Amplified cell bounds for Matomäki–Teräväinen §5.3

On a set `E` where an amplifier `G` satisfies `1 ≤ λ|G|²`:

* if `|F₁| ≤ Δ` on `E`, then `∫_E |F₁F₂|² ≤ Δ² λ ∫_{-T}^{T} |G F₂|²`;
* if moreover `Δ/2 ≤ |F₁|` and `|F₂| ≤ Γ` on `E`, then
  `∫_E |F₁F₂|² ≤ 2^{10} Γ² Δ^{-8} λ ∫_{-T}^{T} |G F₁^5|²`.

The exponent inequality `typeII_cell_min_le` shows that one of the two normalised bounds is
`≤ 8 X^{-δ₀}` whenever `6/a < 5 + 2σ₀` with room: this is the case analysis of §5.3, in the
logarithmic coordinates `log Δ`, `log M₁`, `log M₂`.
-/

namespace RHTower.Sieve

open MeasureTheory

noncomputable section

/-- **First cell bound** (the dense factor against the amplifier). -/
theorem setIntegral_normSq_mul_le_amplified {F₁ F₂ G : ℝ → ℂ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (hG : Continuous G) {E : Set ℝ} (hE : MeasurableSet E) {T Δ lam : ℝ}
    (hET : E ⊆ Set.Icc (-T) T) (hΔ : ∀ t ∈ E, ‖F₁ t‖ ≤ Δ) (hlam0 : 0 ≤ lam)
    (hlam : ∀ t ∈ E, 1 ≤ lam * ‖G t‖ ^ 2) :
    ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤ Δ ^ 2 * lam * ∫ t in Set.Icc (-T) T, ‖G t * F₂ t‖ ^ 2 := by
  have hcGF : Continuous fun t => ‖G t * F₂ t‖ ^ 2 := ((hG.mul hF₂).norm).pow 2
  have hIcc : IntegrableOn (fun t => ‖G t * F₂ t‖ ^ 2) (Set.Icc (-T) T) := hcGF.integrableOn_Icc
  have hLint : IntegrableOn (fun t => ‖F₁ t * F₂ t‖ ^ 2) E :=
    (((hF₁.mul hF₂).norm).pow 2).integrableOn_Icc.mono_set hET
  have hRint : IntegrableOn (fun t => Δ ^ 2 * lam * ‖G t * F₂ t‖ ^ 2) E :=
    (hIcc.mono_set hET).const_mul _
  calc ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤ ∫ t in E, Δ ^ 2 * lam * ‖G t * F₂ t‖ ^ 2 := by
        refine setIntegral_mono_on hLint hRint hE fun t ht => ?_
        rw [norm_mul, norm_mul, mul_pow, mul_pow]
        have h1 : ‖F₁ t‖ ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hΔ t ht) 2
        have h2 := hlam t ht
        have hF : 0 ≤ ‖F₂ t‖ ^ 2 := sq_nonneg _
        calc ‖F₁ t‖ ^ 2 * ‖F₂ t‖ ^ 2 ≤ Δ ^ 2 * ‖F₂ t‖ ^ 2 := mul_le_mul_of_nonneg_right h1 hF
          _ ≤ Δ ^ 2 * ‖F₂ t‖ ^ 2 * (lam * ‖G t‖ ^ 2) :=
              le_mul_of_one_le_right (mul_nonneg (sq_nonneg _) hF) h2
          _ = Δ ^ 2 * lam * (‖G t‖ ^ 2 * ‖F₂ t‖ ^ 2) := by ring
    _ = Δ ^ 2 * lam * ∫ t in E, ‖G t * F₂ t‖ ^ 2 := integral_const_mul _ _
    _ ≤ Δ ^ 2 * lam * ∫ t in Set.Icc (-T) T, ‖G t * F₂ t‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg (sq_nonneg _) hlam0)
        exact setIntegral_mono_set hIcc (Filter.Eventually.of_forall fun t => sq_nonneg _)
          (Filter.Eventually.of_forall hET)

/-- **Second cell bound** (the fifth power of the short factor against the amplifier). -/
theorem setIntegral_normSq_mul_le_amplified_pow {F₁ F₂ G : ℝ → ℂ} (hF₁ : Continuous F₁)
    (hF₂ : Continuous F₂) (hG : Continuous G) {E : Set ℝ} (hE : MeasurableSet E)
    {T Δ Γ lam : ℝ} (hET : E ⊆ Set.Icc (-T) T) (hΔ0 : 0 < Δ)
    (hlo : ∀ t ∈ E, Δ / 2 ≤ ‖F₁ t‖) (hhi : ∀ t ∈ E, ‖F₁ t‖ ≤ Δ) (hΓ : ∀ t ∈ E, ‖F₂ t‖ ≤ Γ)
    (hlam0 : 0 ≤ lam) (hlam : ∀ t ∈ E, 1 ≤ lam * ‖G t‖ ^ 2) :
    ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤
      2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * lam * ∫ t in Set.Icc (-T) T, ‖G t * F₁ t ^ 5‖ ^ 2 := by
  have hcGF : Continuous fun t => ‖G t * F₁ t ^ 5‖ ^ 2 := ((hG.mul (hF₁.pow 5)).norm).pow 2
  have hIcc : IntegrableOn (fun t => ‖G t * F₁ t ^ 5‖ ^ 2) (Set.Icc (-T) T) :=
    hcGF.integrableOn_Icc
  have hLint : IntegrableOn (fun t => ‖F₁ t * F₂ t‖ ^ 2) E :=
    (((hF₁.mul hF₂).norm).pow 2).integrableOn_Icc.mono_set hET
  set c := 2 ^ 10 * Γ ^ 2 * (Δ ^ 8)⁻¹ * lam with hc
  have hc0 : 0 ≤ c := by positivity
  have hRint : IntegrableOn (fun t => c * ‖G t * F₁ t ^ 5‖ ^ 2) E :=
    (hIcc.mono_set hET).const_mul _
  calc ∫ t in E, ‖F₁ t * F₂ t‖ ^ 2 ≤ ∫ t in E, c * ‖G t * F₁ t ^ 5‖ ^ 2 := by
        refine setIntegral_mono_on hLint hRint hE fun t ht => ?_
        have hx := hlo t ht
        have hy := hhi t ht
        have hΓt := hΓ t ht
        have hl := hlam t ht
        set x := ‖F₁ t‖ with hxdef
        have hx0 : 0 ≤ x := norm_nonneg _
        have hΓ0 : 0 ≤ Γ := (norm_nonneg _).trans hΓt
        have hratio : 1 ≤ (2 * x / Δ) ^ 10 := by
          refine one_le_pow₀ ?_
          rw [le_div_iff₀ hΔ0]; linarith
        rw [norm_mul, norm_mul, norm_pow, mul_pow, mul_pow, ← pow_mul]
        have hxy : x ^ 2 ≤ Δ ^ 2 := pow_le_pow_left₀ hx0 hy 2
        have hF2 : ‖F₂ t‖ ^ 2 ≤ Γ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hΓt 2
        have hstep : x ^ 2 * ‖F₂ t‖ ^ 2 ≤ Δ ^ 2 * Γ ^ 2 :=
          mul_le_mul hxy hF2 (sq_nonneg _) (sq_nonneg _)
        have hid : Δ ^ 2 * Γ ^ 2 * ((2 * x / Δ) ^ 10 * (lam * ‖G t‖ ^ 2)) =
            c * (‖G t‖ ^ 2 * x ^ (5 * 2)) := by
          rw [hc]; field_simp; ring
        calc x ^ 2 * ‖F₂ t‖ ^ 2 ≤ Δ ^ 2 * Γ ^ 2 := hstep
          _ ≤ Δ ^ 2 * Γ ^ 2 * ((2 * x / Δ) ^ 10 * (lam * ‖G t‖ ^ 2)) :=
              le_mul_of_one_le_right (by positivity) (one_le_mul_of_one_le_of_one_le hratio hl)
          _ = c * (‖G t‖ ^ 2 * x ^ (5 * 2)) := hid
    _ = c * ∫ t in E, ‖G t * F₁ t ^ 5‖ ^ 2 := integral_const_mul _ _
    _ ≤ c * ∫ t in Set.Icc (-T) T, ‖G t * F₁ t ^ 5‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ hc0
        exact setIntegral_mono_set hIcc (Filter.Eventually.of_forall fun t => sq_nonneg _)
          (Filter.Eventually.of_forall hET)

/-- **The §5.3 exponent inequality.**  With `M₁ ≥ X^{ε/2}`, `M₁^5 ≤ X^{1/a}`, `M₁M₂ ≥ X^{1-ζ}`,
a cell amplitude `Δ ≤ 2M₁^{-σ₀}` and `Γ ≤ X^ζ M₂^{-σ₀}`, one of the two normalised cell bounds is
at most `8X^{-δ₀}`, provided `δ₀ ≤ σ₀ε`, `δ₀ ≤ ε₁` and `6/a - 5 - 2σ₀ + 5ε₁ + 8ζ ≤ -δ₀`. -/
theorem typeII_cell_min_le {X M₁ M₂ Δ Γ a σ₀ ε ε₁ ζ δ₀ : ℝ} (hX : 1 < X) (hM₁ : 0 < M₁)
    (hM₂ : 0 < M₂) (hΔ : 0 < Δ) (hΓ : 0 < Γ) (hσ₀ : 0 ≤ σ₀) (hσ₀' : σ₀ ≤ 1 / 2)
    (hζ : 0 ≤ ζ) (h1 : X ^ (ε / 2) ≤ M₁) (h2 : M₁ ^ 5 ≤ X ^ (1 / a))
    (h3 : X ^ (1 - ζ) ≤ M₁ * M₂) (h4 : Δ ≤ 2 * M₁ ^ (-σ₀)) (h5 : Γ ≤ X ^ ζ * M₂ ^ (-σ₀))
    (m1 : δ₀ ≤ σ₀ * ε) (m2 : δ₀ ≤ ε₁) (m3 : 6 / a - 5 - 2 * σ₀ + 5 * ε₁ + 8 * ζ ≤ -δ₀) :
    min (Δ ^ 2 * (1 + X ^ (1 / a) / M₂)) (Γ ^ 2 * (Δ ^ 8)⁻¹ * (1 + X ^ (1 / a) / M₁ ^ 5)) ≤
      8 * X ^ (-δ₀) := by
  have hX0 : 0 < X := by linarith
  set lam := Real.log X with hlam
  have hl0 : 0 < lam := Real.log_pos hX
  set m₁ := Real.log M₁ with hm₁
  set m₂ := Real.log M₂ with hm₂
  set l := Real.log Δ with hl
  set g := Real.log Γ with hg
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  -- logarithmic forms of the hypotheses
  have h1' : ε / 2 * lam ≤ m₁ := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) h1
    rwa [Real.log_rpow hX0] at this
  have h2' : 5 * m₁ ≤ 1 / a * lam := by
    have := Real.log_le_log (pow_pos hM₁ 5) h2
    rwa [Real.log_pow, Real.log_rpow hX0] at this
  have h3' : (1 - ζ) * lam ≤ m₁ + m₂ := by
    have := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) h3
    rwa [Real.log_rpow hX0, Real.log_mul hM₁.ne' hM₂.ne'] at this
  have h4' : l ≤ Real.log 2 + -σ₀ * m₁ := by
    have := Real.log_le_log hΔ h4
    rwa [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hM₁ _).ne', Real.log_rpow hM₁] at this
  have h5' : g ≤ ζ * lam + -σ₀ * m₂ := by
    have := Real.log_le_log hΓ h5
    rwa [Real.log_mul (Real.rpow_pos_of_pos hX0 _).ne' (Real.rpow_pos_of_pos hM₂ _).ne',
      Real.log_rpow hX0, Real.log_rpow hM₂] at this
  have htarget : Real.log (4 * X ^ (-δ₀)) = 2 * Real.log 2 + -δ₀ * lam := by
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hX0 _).ne', Real.log_rpow hX0,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  have h4pos : 0 < 4 * X ^ (-δ₀) := by positivity
  set Q := Δ ^ 2 * X ^ (1 / a) / M₂ with hQ
  have hQpos : 0 < Q := by positivity
  have hlogQ : Real.log Q = 2 * l + 1 / a * lam - m₂ := by
    rw [hQ, Real.log_div (by positivity) hM₂.ne', Real.log_mul (by positivity)
      (Real.rpow_pos_of_pos hX0 _).ne', Real.log_pow, Real.log_rpow hX0]
    push_cast; ring
  by_cases hcase : Q ≤ X ^ (-ε₁)
  · refine (min_le_left _ _).trans ?_
    have hΔ2 : Δ ^ 2 ≤ 4 * X ^ (-δ₀) := by
      rw [← Real.log_le_log_iff (by positivity) h4pos, htarget, Real.log_pow]
      have hp : σ₀ * (ε / 2 * lam) ≤ σ₀ * m₁ := mul_le_mul_of_nonneg_left h1' hσ₀
      have hq : δ₀ * lam ≤ σ₀ * ε * lam := mul_le_mul_of_nonneg_right m1 hl0.le
      push_cast
      nlinarith
    have hQ' : Q ≤ X ^ (-δ₀) :=
      hcase.trans (Real.rpow_le_rpow_of_exponent_le hX.le (by linarith))
    have hsplit : Δ ^ 2 * (1 + X ^ (1 / a) / M₂) = Δ ^ 2 + Q := by rw [hQ]; ring
    rw [hsplit]
    have := Real.rpow_pos_of_pos hX0 (-δ₀)
    linarith
  · push Not at hcase
    refine (min_le_right _ _).trans ?_
    have hcase' : -ε₁ * lam < 2 * l + 1 / a * lam - m₂ := by
      have := Real.log_lt_log (Real.rpow_pos_of_pos hX0 _) hcase
      rwa [Real.log_rpow hX0, hlogQ] at this
    have hM5 : 0 < M₁ ^ 5 := pow_pos hM₁ 5
    have hone : 1 ≤ X ^ (1 / a) / M₁ ^ 5 := by rw [le_div_iff₀ hM5]; linarith
    set R := Γ ^ 2 * (Δ ^ 8)⁻¹ * (X ^ (1 / a) / M₁ ^ 5) with hR
    have hRpos : 0 < R := by positivity
    have hlogR : Real.log R = 2 * g - 8 * l + 1 / a * lam - 5 * m₁ := by
      rw [hR, Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity)
        (by positivity), Real.log_inv, Real.log_div (by positivity) hM5.ne', Real.log_pow,
        Real.log_pow, Real.log_pow, Real.log_rpow hX0]
      push_cast; ring
    have hRle : R ≤ 4 * X ^ (-δ₀) := by
      rw [← Real.log_le_log_iff hRpos h4pos, htarget, hlogR]
      have p1 : σ₀ * ((1 - ζ) * lam) ≤ σ₀ * (m₁ + m₂) := mul_le_mul_of_nonneg_left h3' hσ₀
      have p2 := mul_le_mul_of_nonneg_right m3 hl0.le
      have p3 : σ₀ * (ζ * lam) ≤ 1 / 2 * (ζ * lam) :=
        mul_le_mul_of_nonneg_right hσ₀' (mul_nonneg hζ hl0.le)
      linear_combination 2 * h5' + 5 * hcase' + 5 * h3' + 2 * p1 + 2 * h4' + 2 * p3 + p2
    have hsplit : Γ ^ 2 * (Δ ^ 8)⁻¹ * (1 + X ^ (1 / a) / M₁ ^ 5) ≤ 2 * R := by
      rw [hR]
      have : 0 ≤ Γ ^ 2 * (Δ ^ 8)⁻¹ := by positivity
      nlinarith
    linarith

end

end RHTower.Sieve
