import GaloisForLFunctions.SquareRootThreshold.OneParameterLagFamilyRecordsAreVisibleAtAnExplicitLag

/-!
# The one-parameter lag family sees a wide zone below the top

The near-top theorems ask for a zero `½ + z₀` within `1/V` of the top. Here the zone has width
`μ/V` for any `μ`. The Legendre record then only keeps `|D(z*)| ≥ |D(z₀)|e^{−μ}`
(`exists_loud_record_of_zone`), and its loudness `a = 2η²e^{−μ}` and depth `Re z* ≥ Re z₀/2`
(`one_param_record_facts_of_zone`) feed `one_param_record_visible_at_explicit_lag`.

* **Zone visibility** (`one_param_zone_visible`). If every zero satisfies `Re ρ − ½ ≤ δ₀ + μ/V` with
  `V ≥ V_μ(w, η, δ₀) = V(2η²e^{−μ}, δ₀/2) + (2/δ₀)|log(80 log(180Γ)(e^{w/2}B_w)²/(2η²))|`
  (`zoneLag`), then `P_v < 0` for some `v ∈ [0, V]`.
* **Depth gap across a zone** (`one_param_zone_depth_gap`). If `P_v ≥ 0` on `[0, V]` and
  `V ≥ V_μ(w, η, δ₀)`, some zero lies more than `μ/V` to the right of `½ + z₀`.

Since the coherence of the record does not depend on its loudness, `log(1/a) = μ + log(1/(2η²))`
enters `V(a, σ)` only through `P ≍ log(1/a)`: `V_μ ≍_w (μ + log(1/η))² log(μ + log(1/η))/δ₀`. The
largest admissible `μ` is `≍ (δ₀V/log V)^{1/2}`, so positivity of `P_v` on `[0, V]` keeps such a zero
at depth `≥ c_w(δ₀/(V log V))^{1/2}` below the top, against `1/V` for `one_param_depth_gap_of_lag_positivity`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **A loud record across a zone of width `μ/V`.** If an exponent `z₀` right of the line is
`μ/V`-near the top, the Legendre record `z*` at lag `V` keeps `|D(z*)| ≥ |D(z₀)| e^{−μ}`. -/
theorem exists_loud_record_of_zone {b : ℝ → ℂ} (hb : ContDiff ℝ 2 b) {w : ℝ}
    (hbs : ∀ u, b u ≠ 0 → |u| ≤ w) {V : ℝ} (hV : 0 < V) {z₀ : ℂ}
    (hD₀ : evenCoeff zetaZeroConfig b z₀ ≠ 0) (hre₀ : 0 < z₀.re) {μ : ℝ}
    (htop : ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → z.re ≤ z₀.re + μ / V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig b z₁ ≠ 0 ∧ 0 < z₁.re ∧
      ‖evenCoeff zetaZeroConfig b z₀‖ * Real.exp (-μ) ≤ ‖evenCoeff zetaZeroConfig b z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig b z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig b z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig b z₁‖ * Real.exp (z₁.re * V) := by
  obtain ⟨z₁, hz₁, hre₁, hrec⟩ := exists_right_record zetaZeroConfig temperedConfig_zetaZeroConfig
    hb hbs hV.le hD₀ hre₀
  refine ⟨z₁, hz₁, hre₁, ?_, hrec⟩
  set D := evenCoeff zetaZeroConfig b with hDdef
  have h1 := hrec z₀ hD₀ hre₀
  have h3 : Real.exp (z₁.re * V) ≤ Real.exp (z₀.re * V) * Real.exp μ := by
    rw [← Real.exp_add]; refine Real.exp_le_exp.mpr ?_
    have : (z₁.re - z₀.re) * V ≤ μ := by
      have := mul_le_mul_of_nonneg_right (show z₁.re - z₀.re ≤ μ / V by linarith [htop z₁ hz₁])
        hV.le
      rwa [div_mul_cancel₀ _ hV.ne'] at this
    linarith
  have hE := Real.exp_pos (z₀.re * V)
  have h5 : ‖D z₀‖ ≤ ‖D z₁‖ * Real.exp μ := by
    have : ‖D z₀‖ * Real.exp (z₀.re * V) ≤ (‖D z₁‖ * Real.exp μ) * Real.exp (z₀.re * V) := by
      have := h1.trans (mul_le_mul_of_nonneg_left h3 (norm_nonneg (D z₁)))
      linarith
    exact le_of_mul_le_mul_right this hE
  have hEl : Real.exp μ * Real.exp (-μ) = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc ‖D z₀‖ * Real.exp (-μ) ≤ ‖D z₁‖ * Real.exp μ * Real.exp (-μ) :=
        mul_le_mul_of_nonneg_right h5 (Real.exp_pos _).le
    _ = ‖D z₁‖ := by rw [mul_assoc, hEl, mul_one]

/-- **Where the record sits for a wide zone.** Let `½ + z₀` be a zero right of the line, `μ/V`-near
the top, with `|h_w(−iz₀)| ≥ η > 0`, and `a = 2η²e^{−μ}`. Then the Legendre record `z*` of the
unmodulated family at lag `V` has `|D(z*)| ≥ a`, `|Im z*| ≤ Γ(a)`, and `Re z* ≥ Re z₀/2` once
`V Re z₀ ≥ 2 log(80 log(180Γ(a))(e^{w/2}B_w)²/(2η²))`. -/
theorem one_param_record_facts_of_zone {w V : ℝ} (hw : 0 < w) (hV : 0 < V) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re) {η : ℝ} (hη : 0 < η)
    (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖) {μ : ℝ}
    (htop : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → z.re ≤ z₀.re + μ / V)
    (hV2 : 2 * Real.log (80 * Real.log (180 * recordHeightOf w (2 * η ^ 2 * Real.exp (-μ))) *
        (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V) :
    ∃ z₁ : ℂ, evenCoeff zetaZeroConfig (modScaledBump w 0) z₁ ≠ 0 ∧ z₀.re / 2 ≤ z₁.re ∧
      |z₁.im| ≤ recordHeightOf w (2 * η ^ 2 * Real.exp (-μ)) ∧
      2 * η ^ 2 * Real.exp (-μ) ≤ ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ ∧
      ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 → 0 < z.re →
        ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z‖ * Real.exp (z.re * V) ≤
          ‖evenCoeff zetaZeroConfig (modScaledBump w 0) z₁‖ * Real.exp (z₁.re * V) := by
  set D := evenCoeff zetaZeroConfig (modScaledBump w 0) with hDdef
  set K₀ := (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 with hK₀
  set Γ := recordHeightOf w (2 * η ^ 2 * Real.exp (-μ)) with hΓdef
  have hK0 : 0 ≤ K₀ := by positivity
  have hD₀ : 2 * η ^ 2 ≤ ‖D z₀‖ := by
    refine le_trans ?_ (two_mul_sq_le_norm_evenCoeff_zero hw hz₀)
    have := pow_le_pow_left₀ hη.le hηle 2
    linarith
  have hD₀ne : D z₀ ≠ 0 := fun h => by
    rw [h, norm_zero] at hD₀; nlinarith [pow_pos hη 2]
  obtain ⟨z₁, hz₁, hre₁, hD₁', hrec⟩ := exists_loud_record_of_zone (contDiff_modScaledBump_two w 0)
    (modScaledBump_support hw 0) hV hD₀ne hre₀ htop
  have hD₁ : 2 * η ^ 2 * Real.exp (-μ) ≤ ‖D z₁‖ :=
    le_trans (mul_le_mul_of_nonneg_right hD₀ (Real.exp_pos _).le) hD₁'
  have hε : 0 < 2 * η ^ 2 * Real.exp (-μ) := by positivity
  have hup : |z₁.im| ≤ Γ := by
    have h := abs_im_le_of_norm_evenCoeff_modScaledBump_ge hw (c := 0) le_rfl hε hz₁ hD₁
    rw [mul_zero] at h
    refine h.trans (max_le ?_ le_rfl)
    rw [hΓdef, recordHeightOf]; positivity
  refine ⟨z₁, hz₁, ?_, hup, hD₁, hrec⟩
  have h4 : 4 ≤ |z₁.im| := four_le_abs_im_of_evenCoeff_zeta hz₁
  have hDmax : ‖D z₁‖ ≤ 80 * Real.log (180 * Γ) * K₀ := by
    refine (norm_evenCoeff_modScaledBump_le_log hw 0 hz₁).trans ?_
    have : Real.log (180 * |z₁.im|) ≤ Real.log (180 * Γ) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left this (by norm_num)) hK0
  have h1 := hrec z₀ hD₀ne hre₀
  have hD1pos : 0 < ‖D z₁‖ := norm_pos_iff.mpr hz₁
  have hq : 0 < 80 * Real.log (180 * Γ) * K₀ / (2 * η ^ 2) := by
    have : 0 < 80 * Real.log (180 * Γ) * K₀ := lt_of_lt_of_le hD1pos hDmax
    positivity
  have h2 : Real.exp ((z₀.re - z₁.re) * V) ≤ 80 * Real.log (180 * Γ) * K₀ / (2 * η ^ 2) := by
    have hE0 := Real.exp_pos (z₀.re * V)
    have hE1 := Real.exp_pos (z₁.re * V)
    have e : Real.exp ((z₀.re - z₁.re) * V) = Real.exp (z₀.re * V) / Real.exp (z₁.re * V) := by
      rw [← Real.exp_sub]; ring_nf
    rw [e, div_le_iff₀ hE1]
    have : 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ 80 * Real.log (180 * Γ) * K₀ * Real.exp (z₁.re * V) :=
      calc 2 * η ^ 2 * Real.exp (z₀.re * V) ≤ ‖D z₀‖ * Real.exp (z₀.re * V) :=
            mul_le_mul_of_nonneg_right hD₀ hE0.le
        _ ≤ ‖D z₁‖ * Real.exp (z₁.re * V) := h1
        _ ≤ _ := mul_le_mul_of_nonneg_right hDmax hE1.le
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
    nlinarith
  have h3 := Real.log_le_log (Real.exp_pos _) h2
  rw [Real.log_exp] at h3
  nlinarith

/-- The lag of the zone of width `μ/V`:
`V_μ(w, η, δ₀) = V(2η²e^{−μ}, δ₀/2) + (2/δ₀)|log(80 log(180Γ)(e^{w/2}B_w)²/(2η²))|`,
`Γ = Γ(2η²e^{−μ})`. -/
def zoneLag (w η μ δ₀ : ℝ) : ℝ :=
  recordLag w (2 * η ^ 2 * Real.exp (-μ)) (δ₀ / 2) +
    2 / δ₀ * |Real.log (80 * Real.log (180 * recordHeightOf w (2 * η ^ 2 * Real.exp (-μ))) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))|

/-- `V(a, σ) ≥ w` for `σ > 0`. -/
theorem le_recordLag {w : ℝ} (hw : 0 < w) (a : ℝ) {σ : ℝ} (hσ : 0 < σ) : w ≤ recordLag w a σ := by
  unfold recordLag
  have hJ0 : 0 ≤ bumpMass w := integral_nonneg fun u => abs_nonneg _
  have h1 : 0 ≤ 4 / σ * (13 * π * recordOrder w a + 4) := by positivity
  have h2 : 0 ≤ 8 * w * Real.exp (w / 2) * bumpMass w / recordScale w a :=
    div_nonneg (mul_nonneg (by positivity) hJ0) (Real.sqrt_nonneg _)
  linarith

/-- **The one-parameter family sees a zone of width `μ/V` below the top.** Let `½ + z₀` be a zero of
`ζ` right of the line, `δ₀ = Re z₀`, `0 < η ≤ |h_w(−iz₀)|`, `μ ∈ ℝ`, and let every zero satisfy
`Re ρ − ½ ≤ δ₀ + μ/V` for some `V ≥ V_μ(w, η, δ₀)` (`zoneLag`). Then `P_v < 0` for some
`v ∈ [0, V]`. -/
theorem one_param_zone_visible {w : ℝ} (hw : 0 < w) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖) {μ V : ℝ}
    (hV : zoneLag w η μ z₀.re ≤ V)
    (htop : ∀ ρ ∈ zetaZeroConfig.carrier, ρ.re - 1 / 2 ≤ z₀.re + μ / V) :
    ∃ v ∈ Icc (0 : ℝ) V, (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re < 0 := by
  have hσ : 0 < z₀.re / 2 := half_pos hre₀
  have hℓ : 0 ≤ 2 / z₀.re * |Real.log (80 * Real.log (180 * recordHeightOf w
      (2 * η ^ 2 * Real.exp (-μ))) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2))| := by
    positivity
  have hrl : recordLag w (2 * η ^ 2 * Real.exp (-μ)) (z₀.re / 2) ≤ V := by
    unfold zoneLag at hV; linarith
  have hV0 : 0 < V := lt_of_lt_of_le hw ((le_recordLag hw _ hσ).trans hrl)
  have hV2 : 2 * Real.log (80 * Real.log (180 * recordHeightOf w (2 * η ^ 2 * Real.exp (-μ))) *
      (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) ≤ z₀.re * V := by
    obtain ⟨ℓ, hℓdef⟩ : ∃ ℓ : ℝ, ℓ = Real.log (80 * Real.log (180 * recordHeightOf w
        (2 * η ^ 2 * Real.exp (-μ))) * (Real.exp (w / 2) * scaledBumpDecay w) ^ 2 / (2 * η ^ 2)) :=
      ⟨_, rfl⟩
    rw [← hℓdef] at hℓ ⊢
    have h1 : 2 / z₀.re * |ℓ| ≤ V := by
      unfold zoneLag at hV; rw [← hℓdef] at hV
      have := le_recordLag hw (2 * η ^ 2 * Real.exp (-μ)) hσ
      linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hre₀.le
    have e : z₀.re * (2 / z₀.re * |ℓ|) = 2 * |ℓ| := by field_simp
    linarith [le_abs_self ℓ]
  have htop' : ∀ z, evenCoeff zetaZeroConfig (modScaledBump w 0) z ≠ 0 →
      z.re ≤ z₀.re + μ / V := fun z hz => by
    have hmem : (1 / 2 + z) ∈ zetaZeroConfig.carrier := by
      rcases mem_of_evenCoeff_ne_zero hz with h | h
      · exact h
      · have := conj_mem_zetaZeroConfig h
        have e : conj (1 / 2 + conj z) = 1 / 2 + z := by apply Complex.ext <;> simp
        rwa [e] at this
    have := htop _ hmem
    have e : (1 / 2 + z).re = 1 / 2 + z.re := by simp
    linarith
  obtain ⟨z₁, hz₁, hre₁, hup, hD₁, hrec⟩ :=
    one_param_record_facts_of_zone hw hV0 hz₀ hre₀ hη hηle htop' hV2
  have hstrip := zetaZeroConfig.strip _ hz₀
  have hre₀1 : z₀.re ≤ 1 / 2 := by
    have e : (1 / 2 + z₀).re = 1 / 2 + z₀.re := by simp
    linarith [hstrip.2]
  exact one_param_record_visible_at_explicit_lag hw hz₁ hσ (by linarith) hre₁ (by positivity) hD₁
    hup hrec hrl

/-- **Depth gap across a zone.** If `P_v ≥ 0` for every `v ∈ [0, V]`, then every zero `½ + z₀` right
of the line with `V ≥ V_μ(w, η, Re z₀)` for some `0 < η ≤ |h_w(−iz₀)|` has a zero more than `μ/V`
to its right. -/
theorem one_param_zone_depth_gap {w : ℝ} (hw : 0 < w) {V : ℝ}
    (hpos : ∀ v ∈ Icc (0 : ℝ) V, 0 ≤ (zetaZeroConfig.W (twoBump (modScaledBump w 0) v (-1))
      (twoBump (modScaledBump w 0) v (-1))).re) {z₀ : ℂ}
    (hz₀ : (1 / 2 + z₀) ∈ zetaZeroConfig.carrier) (hre₀ : 0 < z₀.re)
    {η : ℝ} (hη : 0 < η) (hηle : η ≤ ‖paperFT (scaledBump w) (-(I * z₀))‖) {μ : ℝ}
    (hV : zoneLag w η μ z₀.re ≤ V) :
    ∃ ρ ∈ zetaZeroConfig.carrier, z₀.re + μ / V < ρ.re - 1 / 2 := by
  by_contra h
  push Not at h
  obtain ⟨v, hv, hneg⟩ := one_param_zone_visible hw hz₀ hre₀ hη hηle hV h
  exact absurd (hpos v hv) (not_le.mpr hneg)

end GaloisForLFunctions.SquareRootThreshold
