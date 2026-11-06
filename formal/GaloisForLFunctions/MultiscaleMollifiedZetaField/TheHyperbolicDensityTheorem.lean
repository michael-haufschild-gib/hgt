import GaloisForLFunctions.MultiscaleMollifiedZetaField.TheVeryDeepZerosAreRare

/-!
# The hyperbolic density theorem

Put a zero `ρ` in the half plane `Re s > ½` with its pseudo-hyperbolic ratios `ϱ(ρ, ρ') = |ρ − ρ'|/|ρ + ρ̄' − 1|` to the other zeros.

**Theorem** (`exists_card_hyperbolically_isolated_zeros_unconditional_le`). Fix `0 < c ≤ 1/28800` and write `x = (1−3c)α`, `L = log T`. For `x ≤ (3/2) c L`,
separated zeros of depth in `[α/L, (α+1)/L]` with

`Π_{ρ'} ϱ(ρ, ρ') ≥ B₀ ≥ e^{−x/8}`, the product over the zeros deeper than `x/(2L)`,

number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³ T^{1/2}`.

This is the Density Hypothesis rate, up to the free `c`, for every zero that is hyperbolically isolated from the zeros at least half as deep as itself. Its only
condition is on the geometry of the zeros: the near-line zeros, the far zeros and the much deeper zeros need no hypothesis.
-/

noncomputable section

open Complex Set MeasureTheory Filter
open scoped Real
open RHTower Zeta23

namespace GaloisForLFunctions.MultiscaleMollifiedZetaField

variable {v : ℝ → ℝ}

/-- The exceptional set costs `(TLA₁ e_x + KL³ e_z)/X` in the count, for `v₀ = A/(3cL)`. -/
theorem bad_term_le {A₁ K c L T A X ex ez : ℝ} (hA₁ : 0 < A₁) (hK : 0 ≤ K) (hc0 : 0 < c) (hc : c ≤ 1 / 28800)
    (hL : 0 < L) (hT : 0 < T) (hA : 1 ≤ A) (hX : 0 < X) (hex : 0 ≤ ex) (hez : 0 ≤ ez) :
    π / (c * L) * (3 * (8 * T * A₁ / (4 * Real.pi * (A / (3 * c * L))) *
        (1 + 4800 / (A / (3 * c * L) * L)) * ex +
      2 * L * (K * (2 * L) / (Real.pi * (A / (3 * c * L))) * ez))) / (X / 2) * (5 * (c * L)) ≤
      (T * L * A₁ * ex + K * L ^ 3 * ez) / X := by
  have hA0 : 0 < A := by linarith
  have hpi := Real.pi_pos
  have e : π / (c * L) * (3 * (8 * T * A₁ / (4 * Real.pi * (A / (3 * c * L))) *
        (1 + 4800 / (A / (3 * c * L) * L)) * ex +
      2 * L * (K * (2 * L) / (Real.pi * (A / (3 * c * L))) * ez))) / (X / 2) * (5 * (c * L)) =
      180 * c / A * ((T * L * A₁ * ex) * (1 + 14400 * c / A) + 2 * (K * L ^ 3 * ez)) / X := by
    field_simp
    ring
  rw [e]
  have hr : 180 * c / A ≤ 1 / 160 := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have hs : 14400 * c / A ≤ 1 / 2 := by
    rw [div_le_iff₀ hA0]
    nlinarith
  have hr0 : 0 ≤ 180 * c / A := by positivity
  have ha : 0 ≤ T * L * A₁ * ex := by positivity
  have hb : 0 ≤ K * L ^ 3 * ez := by positivity
  refine div_le_div_of_nonneg_right ?_ hX.le
  have h1 : (T * L * A₁ * ex) * (1 + 14400 * c / A) + 2 * (K * L ^ 3 * ez) ≤
      2 * (T * L * A₁ * ex + K * L ^ 3 * ez) := by
    nlinarith [mul_le_mul_of_nonneg_left hs ha]
  calc 180 * c / A * ((T * L * A₁ * ex) * (1 + 14400 * c / A) + 2 * (K * L ^ 3 * ez))
      ≤ 180 * c / A * (2 * (T * L * A₁ * ex + K * L ^ 3 * ez)) :=
        mul_le_mul_of_nonneg_left h1 hr0
    _ ≤ 1 / 160 * (2 * (T * L * A₁ * ex + K * L ^ 3 * ez)) :=
        mul_le_mul_of_nonneg_right hr (by positivity)
    _ ≤ _ := by linarith

/-- The exceptional cost in the shape of the main term, at `X = I e^x B₀/(28 M √(α+1)) ≥ 2`. -/
theorem bad_final_le {A₁ K L T X Iv Mm B₀ x α ex ez R : ℝ} (hA₁ : 0 < A₁) (hK : 0 ≤ K) (hIv : 0 < Iv) (hMm : 0 < Mm)
    (hL : 0 ≤ L) (hT : 0 ≤ T) (hB₀ : 0 < B₀) (hB₀1 : B₀ ≤ 1) (hα : 1 ≤ α + 1)
    (hX : X = Iv * Real.exp x * B₀ / Real.sqrt (α + 1) / 28 / Mm) (hX2 : 2 ≤ X)
    (hex0 : 0 ≤ ex) (hex : ex ≤ Real.exp (-x)) (hez0 : 0 ≤ ez) (hez : ez ≤ R) :
    (T * L * A₁ * ex + K * L ^ 3 * ez) / X ≤
      28 * Mm * A₁ / Iv * (α + 1) * T * L * Real.exp (-(2 * x)) / B₀ ^ 2 + K * (L ^ 3 * R) := by
  have hX0 : 0 < X := by linarith
  have hα0 : 0 < α + 1 := by linarith
  have hs0 : 0 < Real.sqrt (α + 1) := Real.sqrt_pos.mpr hα0
  have hs1 : Real.sqrt (α + 1) ≤ α + 1 := by
    rw [Real.sqrt_le_left hα0.le]
    nlinarith
  rw [add_div]
  refine add_le_add ?_ ?_
  · have hE : Real.exp (-(2 * x)) = Real.exp (-x) * Real.exp (-x) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hE1 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    have hE0 := Real.exp_pos (-x)
    have e : T * L * A₁ * Real.exp (-x) / X =
        28 * Mm * A₁ / Iv * Real.sqrt (α + 1) * T * L * Real.exp (-(2 * x)) / B₀ := by
      rw [hX, hE]
      have hx : Real.exp x = (Real.exp (-x))⁻¹ := by
        rw [Real.exp_neg, inv_inv]
      rw [hx]
      field_simp
    have h1 : T * L * A₁ * ex / X ≤ T * L * A₁ * Real.exp (-x) / X :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hex (by positivity)) hX0.le
    refine h1.trans ?_
    rw [e]
    have hQ : 0 ≤ 28 * Mm * A₁ / Iv * T * L * Real.exp (-(2 * x)) := by positivity
    have h2 : Real.sqrt (α + 1) / B₀ ≤ (α + 1) / B₀ ^ 2 := by
      rw [div_le_div_iff₀ hB₀ (by positivity)]
      have h3 : Real.sqrt (α + 1) * B₀ ^ 2 ≤ (α + 1) * B₀ := by
        have h4 : B₀ ^ 2 ≤ B₀ := by nlinarith
        calc Real.sqrt (α + 1) * B₀ ^ 2 ≤ (α + 1) * B₀ ^ 2 :=
              mul_le_mul_of_nonneg_right hs1 (by positivity)
          _ ≤ (α + 1) * B₀ := mul_le_mul_of_nonneg_left h4 hα0.le
      exact h3
    calc 28 * Mm * A₁ / Iv * Real.sqrt (α + 1) * T * L * Real.exp (-(2 * x)) / B₀
        = (28 * Mm * A₁ / Iv * T * L * Real.exp (-(2 * x))) * (Real.sqrt (α + 1) / B₀) := by ring
      _ ≤ (28 * Mm * A₁ / Iv * T * L * Real.exp (-(2 * x))) * ((α + 1) / B₀ ^ 2) :=
          mul_le_mul_of_nonneg_left h2 hQ
      _ = _ := by ring
  · have hb : 0 ≤ K * L ^ 3 * ez := by positivity
    have h1 : K * L ^ 3 * ez / X ≤ K * L ^ 3 * ez := div_le_self hb (by linarith)
    have h2 : K * L ^ 3 * ez ≤ K * L ^ 3 * R := mul_le_mul_of_nonneg_left hez (by positivity)
    calc _ ≤ K * L ^ 3 * R := h1.trans h2
      _ = _ := by ring

/-- The depth beyond which the threshold `X` is at least `2`. -/
theorem exists_depth_threshold_two {c : ℝ} (hc : c ≤ 1 / 6) (B₁ : ℝ) :
    ∃ α₁ : ℝ, 4 ≤ α₁ ∧ ∀ α : ℝ, α₁ ≤ α → B₁ * (α + 1) ≤ Real.exp (7 / 8 * ((1 - 3 * c) * α)) := by
  have h13 : 0 < 7 / 8 * (1 - 3 * c) := by
    have : 0 < 1 - 3 * c := by linarith
    positivity
  obtain ⟨α₀, hα₀⟩ := eventually_atTop.mp (eventually_mul_add_one_le_exp h13 B₁)
  refine ⟨max α₀ 4, le_max_right _ _, fun α hα => ?_⟩
  have h := hα₀ α ((le_max_left _ _).trans hα)
  have e : 7 / 8 * (1 - 3 * c) * α = 7 / 8 * ((1 - 3 * c) * α) := by ring
  rwa [e] at h

/-- The threshold `X` is at least `2` at `B₀ ≥ e^{−x/8}`. -/
theorem two_le_threshold {Iv Mm x B₀ α : ℝ} (hI : 0 < Iv) (hMm : 0 < Mm) (hα : 1 ≤ α + 1)
    (hB₀ : Real.exp (-(x / 8)) ≤ B₀) (h : 56 * Mm / Iv * (α + 1) ≤ Real.exp (7 / 8 * x)) :
    2 ≤ Iv * Real.exp x * B₀ / Real.sqrt (α + 1) / 28 / Mm := by
  have hα0 : 0 < α + 1 := by linarith
  have hs0 : 0 < Real.sqrt (α + 1) := Real.sqrt_pos.mpr hα0
  have hs1 : Real.sqrt (α + 1) ≤ α + 1 := by
    rw [Real.sqrt_le_left hα0.le]
    nlinarith
  rw [le_div_iff₀ hMm, le_div_iff₀ (by norm_num), le_div_iff₀ hs0]
  have hexp : Real.exp x * Real.exp (-(x / 8)) = Real.exp (7 / 8 * x) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have h1 : Real.exp (7 / 8 * x) ≤ Real.exp x * B₀ := by
    rw [← hexp]
    exact mul_le_mul_of_nonneg_left hB₀ (Real.exp_pos _).le
  have h2 : 56 * Mm * (α + 1) ≤ Iv * Real.exp (7 / 8 * x) := by
    have h3 := mul_le_mul_of_nonneg_left h hI.le
    have e : Iv * (56 * Mm / Iv * (α + 1)) = 56 * Mm * (α + 1) := by
      field_simp
    linarith
  have h4 : 56 * Mm * Real.sqrt (α + 1) ≤ 56 * Mm * (α + 1) :=
    mul_le_mul_of_nonneg_left hs1 (by positivity)
  have h5 := mul_le_mul_of_nonneg_left h1 hI.le
  nlinarith

/-- The closing arithmetic above the depth threshold. -/
theorem large_regime_arith {C₁ C₂ K C α T L E B₀ R b : ℝ} (hC₁ : 0 ≤ C₁) (hK : 0 ≤ K) (hC : C₁ + C₂ ≤ C)
    (hC' : 2 * C₁ + K ≤ C) (hα : 1 ≤ α + 1) (hT : 0 ≤ T) (hL : 1 ≤ L) (hE : 0 ≤ E) (hR : 0 ≤ R)
    (hb : b ≤ C₂ * (α + 1) * T * L * E / B₀ ^ 2 + K * (L ^ 3 * R)) :
    C₁ * (α + 1) * T * L * E / B₀ ^ 2 + C₁ * (L * ((L + 1) * R)) + b ≤
      C * (α + 1) * T * L * E / B₀ ^ 2 + C * (L ^ 3 * R) := by
  have hL0 : 0 ≤ L := by linarith
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = (α + 1) * T * L * E / B₀ ^ 2 := ⟨_, rfl⟩
  have hQ0 : 0 ≤ Q := by
    rw [hQ]
    have : 0 ≤ α + 1 := by linarith
    positivity
  have e1 : C₁ * (α + 1) * T * L * E / B₀ ^ 2 = C₁ * Q := by
    rw [hQ]
    ring
  have e2 : C₂ * (α + 1) * T * L * E / B₀ ^ 2 = C₂ * Q := by
    rw [hQ]
    ring
  have e3 : C * (α + 1) * T * L * E / B₀ ^ 2 = C * Q := by
    rw [hQ]
    ring
  rw [e1, e3]
  rw [e2] at hb
  have hLL : L * ((L + 1) * R) ≤ 2 * (L ^ 3 * R) := by
    have h1 : L * (L + 1) ≤ 2 * L ^ 3 := by nlinarith [mul_nonneg hL0 hL0, mul_nonneg (mul_nonneg hL0 hL0) hL0]
    calc L * ((L + 1) * R) = (L * (L + 1)) * R := by ring
      _ ≤ (2 * L ^ 3) * R := mul_le_mul_of_nonneg_right h1 hR
      _ = _ := by ring
  have hS0 : 0 ≤ L ^ 3 * R := by positivity
  have h3 : C₁ * (L * ((L + 1) * R)) ≤ C₁ * (2 * (L ^ 3 * R)) := mul_le_mul_of_nonneg_left hLL hC₁
  have h4 : (C₁ + C₂) * Q ≤ C * Q := mul_le_mul_of_nonneg_right hC hQ0
  have h5 : (2 * C₁ + K) * (L ^ 3 * R) ≤ C * (L ^ 3 * R) := mul_le_mul_of_nonneg_right hC' hS0
  nlinarith

/-- Separated zeros in the range number at most `5cLT`. -/
theorem card_separated_le {c L T : ℝ} (hδ1 : 1 ≤ c * L) (hT0 : 0 < T) (S : Finset zetaZeroConfig.carrier)
    (hS : ∀ ρ ∈ S, T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1)
    (hsep : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * L)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) :
    (S.card : ℝ) ≤ T * (5 * (c * L)) := by
  obtain ⟨r, hr⟩ : ∃ r, r = 1 / (10 * (c * L)) := ⟨_, rfl⟩
  have hδ0 : 0 < c * L := by linarith
  have hr0 : 0 < r := by
    rw [hr]
    positivity
  have hr1 : r ≤ 1 := by
    rw [hr, div_le_one (by positivity)]
    linarith
  have h2r : (2 * r)⁻¹ = 5 * (c * L) := by
    rw [hr]
    field_simp
    norm_num
  have hsep' : ∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 2 * r ≤ |(ρ : ℂ).im - (ρ' : ℂ).im| := by
    intro ρ hρ ρ' hρ' hne
    have e : 2 * r = 1 / (5 * (c * L)) := by
      rw [hr]
      field_simp
      norm_num
    rw [e]
    exact hsep ρ hρ ρ' hρ' hne
  have hmem : ∀ ρ ∈ S, Ioo ((ρ : ℂ).im - r) ((ρ : ℂ).im + r) ⊆ Ioc T (2 * T) := by
    intro ρ hρ t ht
    obtain ⟨hlow, hhigh⟩ := hS ρ hρ
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  exact card_le_trivial S (fun ρ : zetaZeroConfig.carrier => (ρ : ℂ).im) h2r hr0 hT0 hsep' hmem

/-- **The hyperbolic density theorem.** Fix `0 < c ≤ 1/28800` and write `x = (1−3c)α`. For `x ≤ (3/2)c log T`, separated zeros of depth in `[α/L, (α+1)/L]` whose
pseudo-hyperbolic product over the zeros deeper than `x/(2L)` is at least `B₀ ≥ e^{−x/8}` number `≪_c (α+1) T L e^{−2(1−3c)α}/B₀² + L³ T^{1/2}`. -/
theorem exists_card_hyperbolically_isolated_zeros_unconditional_le (hv : ContDiff ℝ 2 v)
    (hsupp : ∀ u, v u ≠ 0 → |u| ≤ 1) (hv0 : ∀ u, 0 ≤ v u) (hI : 0 < ∫ u, v u) {c : ℝ} (hc0 : 0 < c)
    (hc : c ≤ 1 / 28800) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ α B₀ : ℝ, 0 ≤ α →
      (1 - 3 * c) * α ≤ 3 / 2 * (c * Real.log T) →
      Real.exp (-((1 - 3 * c) * α / 8)) ≤ B₀ → B₀ ≤ 1 →
      ∀ S : Finset zetaZeroConfig.carrier,
      (∀ ρ ∈ S, α / Real.log T ≤ (ρ : ℂ).re - 1 / 2 ∧ (ρ : ℂ).re - 1 / 2 ≤ (α + 1) / Real.log T ∧
        T + 1 ≤ (ρ : ℂ).im ∧ (ρ : ℂ).im ≤ 2 * T - 1 ∧
        ∀ D : Finset zetaZeroConfig.carrier, ρ ∈ D →
          (∀ ρ' ∈ D, (1 - 3 * c) * α / 2 / Real.log T ≤ (ρ' : ℂ).re - 1 / 2) →
          B₀ ≤ ∏ ρ' ∈ D.erase ρ, hyperbolicRatio (ρ : ℂ) (ρ' : ℂ)) →
      (∀ ρ ∈ S, ∀ ρ' ∈ S, ρ ≠ ρ' → 1 / (5 * (c * Real.log T)) ≤ |(ρ : ℂ).im - (ρ' : ℂ).im|) →
      (S.card : ℝ) ≤ C * (α + 1) * T * Real.log T * Real.exp (-(2 * (1 - 3 * c) * α)) / B₀ ^ 2 +
        C * (Real.log T ^ 3 * T ^ ((1 : ℝ) / 2)) := by
  classical
  obtain ⟨C₁, hC₁, hmain⟩ := exists_card_hyperbolically_isolated_zeros_le hv hsupp hv0 hI hc0
    (by linarith : c < 1 / 4)
  obtain ⟨A₁, K, hA₁, hK, hrare⟩ := exists_volume_very_deep_mass_gt_le
  have h13 : 1 / 2 ≤ 1 - 3 * c := by linarith
  have hPM := profileMass_nonneg v
  obtain ⟨Mm, hMm⟩ : ∃ Mm, Mm = profileMass v + 1 := ⟨_, rfl⟩
  have hMm0 : 0 < Mm := by linarith
  obtain ⟨Iv, hIv⟩ : ∃ Iv, Iv = ∫ u, v u := ⟨_, rfl⟩
  have hIv0 : 0 < Iv := by rw [hIv]; exact hI
  obtain ⟨α₁, hα₁4, hα₁⟩ := exists_depth_threshold_two (c := c) (by linarith) (56 * Mm / Iv)
  obtain ⟨X₀, hX₀⟩ : ∃ X₀, X₀ = Real.exp (2 * ((1 - 3 * c) * α₁)) := ⟨_, rfl⟩
  have hX₀1 : 0 < X₀ := by
    rw [hX₀]
    exact Real.exp_pos _
  obtain ⟨C₂, hC₂⟩ : ∃ C₂, C₂ = 28 * Mm * A₁ / Iv := ⟨_, rfl⟩
  have hC₂0 : 0 ≤ C₂ := by
    rw [hC₂]
    positivity
  refine ⟨3 * C₁ + C₂ + K + 5 * c * X₀, by positivity, ?_⟩
  filter_upwards [hmain, hrare, Real.tendsto_log_atTop.eventually_ge_atTop (1 / c),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop 3]
    with T hT₁ hT₂ hLc hL1 hT3 α B₀ hα hxL hB₀low hB₀1 S hS hsep
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log T := by linarith
  have hδ1 : 1 ≤ c * Real.log T := by
    rw [div_le_iff₀ hc0] at hLc
    linarith
  have hδ0 : 0 < c * Real.log T := by linarith
  have hB₀ : 0 < B₀ := lt_of_lt_of_le (Real.exp_pos _) hB₀low
  have hα1 : 1 ≤ α + 1 := by linarith
  have hR0 : 0 ≤ T ^ ((1 : ℝ) / 2) := by positivity
  rcases le_or_gt α₁ α with hbig | hsmall
  · -- the exceptional set of the very deep mass
    have hA1 : 1 ≤ (1 - 3 * c) * α / 2 := by nlinarith
    have hA0 : 0 < (1 - 3 * c) * α / 2 := by linarith
    obtain ⟨A, hAdef⟩ : ∃ A, A = (1 - 3 * c) * α / 2 := ⟨_, rfl⟩
    rw [← hAdef] at hA1 hA0
    obtain ⟨v₀, hv₀⟩ : ∃ v₀, v₀ = A / (3 * c * Real.log T) := ⟨_, rfl⟩
    have h3cL : 0 < 3 * c * Real.log T := by positivity
    have hv1 : 2 / Real.log T ≤ v₀ := by
      rw [hv₀, div_le_div_iff₀ hL0 h3cL]
      have : 2 * (3 * c * Real.log T) ≤ 1 * Real.log T :=
        by nlinarith
      nlinarith
    have hv2 : v₀ ≤ 1 / 4 := by
      rw [hv₀, div_le_iff₀ h3cL]
      nlinarith
    obtain ⟨X, hX⟩ : ∃ X, X = Iv * Real.exp ((1 - 3 * c) * α) * B₀ / Real.sqrt (α + 1) / 28 / Mm := ⟨_, rfl⟩
    have hX2 : 2 ≤ X := by
      rw [hX]
      exact two_le_threshold hIv0 hMm0 hα1 hB₀low (hα₁ α hbig)
    have hvol := hT₂ c v₀ X hc0 (by linarith) hδ1 hv1 hv2 hX2
    obtain ⟨Bad, hBad⟩ : ∃ Bad : Set ℝ, Bad = {t | t ∈ Ioc T (2 * T) ∧ ∃ V : Finset zetaZeroConfig.carrier,
        (∀ ρ' ∈ V, v₀ < (ρ' : ℂ).re - 1 / 2) ∧
        X < ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
          companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ'} := ⟨_, rfl⟩
    rw [← hBad] at hvol
    have hv0' : 0 < v₀ := by
      rw [hv₀]
      positivity
    have hX0 : 0 < X := by linarith
    obtain ⟨Bbad, hBbad⟩ : ∃ Bbad, Bbad = π / (c * Real.log T) *
        (3 * (8 * T * A₁ / (4 * Real.pi * v₀) * (1 + 4800 / (v₀ * Real.log T)) *
            Real.exp (-(v₀ * Real.log T / 4800)) +
          2 * Real.log T * (K * (2 * Real.log T) / (Real.pi * v₀) *
            Real.exp (3 * c * (2 * Real.log T))))) / (X / 2) := ⟨_, rfl⟩
    rw [← hBbad] at hvol
    have hBbad0 : 0 ≤ Bbad := by
      rw [hBbad]
      positivity
    have hres := hT₁ α A B₀ hα hA1 (le_of_eq hAdef) hB₀low hB₀1 Bbad hBbad0 Bad hvol S (fun ρ hρ => by
      obtain ⟨h1, h2, h3, h4, h5⟩ := hS ρ hρ
      refine ⟨h1, h2, h3, h4, ?_, fun t ht htBad V hV => ?_⟩
      · rw [hAdef]
        exact h5
      · have hr : 1 / (10 * (c * Real.log T)) ≤ 1 := by
          rw [div_le_one (by positivity)]
          linarith
        obtain ⟨ht1, ht2⟩ := abs_le.mp (ht.trans hr)
        have htI : t ∈ Ioc T (2 * T) := ⟨by linarith, by linarith⟩
        have hnot : ¬ X < ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
            companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' := fun hlt => htBad (by
          rw [hBad]
          exact ⟨htI, V, fun ρ' hρ' => by rw [hv₀]; exact hV ρ' hρ', hlt⟩)
        have hle := not_lt.mp hnot
        have hsum0 : profileMass v * ∑ ρ' ∈ V, (zetaZeroConfig.mult ρ' : ℝ) *
            companionWeight (c * Real.log T) (2 * (c * Real.log T)) t ρ' ≤ Mm * X := by
          refine (mul_le_mul_of_nonneg_left hle hPM).trans ?_
          exact mul_le_mul_of_nonneg_right (by linarith) hX0.le
        refine hsum0.trans (le_of_eq ?_)
        rw [hX, ← hIv]
        field_simp) hsep
    -- the cost of the exceptional set
    have hex : Real.exp (-(A / (3 * c * Real.log T) * Real.log T / 4800)) ≤
        Real.exp (-((1 - 3 * c) * α)) := by
      refine Real.exp_le_exp.2 (neg_le_neg ?_)
      have e : A / (3 * c * Real.log T) * Real.log T / 4800 = A / (14400 * c) := by
        field_simp
        ring
      rw [e, le_div_iff₀ (by positivity), hAdef]
      have hx0 : 0 ≤ (1 - 3 * c) * α := by positivity
      nlinarith
    have hez : Real.exp (3 * c * (2 * Real.log T)) ≤ T ^ ((1 : ℝ) / 2) := by
      rw [Real.rpow_def_of_pos hT0]
      refine Real.exp_le_exp.2 ?_
      nlinarith
    have hcost1 : Bbad * (5 * (c * Real.log T)) ≤ _ := by
      rw [hBbad, hv₀]
      exact bad_term_le (L := Real.log T) (A := A) hA₁ hK hc0 hc hL0 hT0 hA1 hX0
        (Real.exp_pos _).le (Real.exp_pos _).le
    have hcost2 := bad_final_le (L := Real.log T) (T := T) (α := α) (A₁ := A₁) (K := K) (B₀ := B₀)
      (x := (1 - 3 * c) * α) hA₁ hK hIv0 hMm0 hL0.le hT0.le hB₀ hB₀1 hα1 hX hX2
      (Real.exp_pos _).le hex (Real.exp_pos _).le hez
    have hcost := hcost1.trans hcost2
    have e2 : -(2 * (1 - 3 * c) * α) = -(2 * ((1 - 3 * c) * α)) := by ring
    rw [e2] at hres ⊢
    rw [← hC₂] at hcost
    refine hres.trans ?_
    refine large_regime_arith hC₁.le hK ?_ ?_ hα1 hT0.le hL1 (Real.exp_pos _).le hR0 hcost
    · have : 0 ≤ 5 * c * X₀ := by positivity
      linarith
    · have : 0 ≤ 5 * c * X₀ := by positivity
      linarith
  · have htriv := card_separated_le hδ1 hT0 S (fun ρ hρ => by
      obtain ⟨-, -, h3, h4, -⟩ := hS ρ hρ
      exact ⟨h3, h4⟩) hsep
    have hX : 1 ≤ X₀ * Real.exp (-(2 * (1 - 3 * c) * α)) := by
      rw [hX₀, ← Real.exp_add]
      refine Real.one_le_exp ?_
      nlinarith
    have hR2 : 0 ≤ Real.log T ^ 2 * T ^ ((1 : ℝ) / 2) := by positivity
    have hfin := shallow_regime_arith (C' := 3 * C₁ + C₂ + K) hc0 (by positivity) hX hX₀1.le hα1 hT0 hL0
      (Real.exp_pos _) hB₀ hB₀1 hR2 htriv
    refine hfin.trans (le_of_eq ?_)
    ring

end GaloisForLFunctions.MultiscaleMollifiedZetaField
