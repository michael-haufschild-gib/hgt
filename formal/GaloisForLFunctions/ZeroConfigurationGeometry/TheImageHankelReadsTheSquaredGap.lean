import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindowsVarySlowlyAtTheirTarget

/-!
# The image Hankel determinant reads the squared gap

A single configuration `Z` is compared with the empty configuration, so the image differences
`ΔW_j` are the image values `Z.W F_j G` themselves. For a two-point cluster `p₁, p₂` with
`a_i = γ_{p_i} − ω` the disc moments are `μ₀ = 2`, `μ₁ = a₁ + a₂`, `μ₂ = a₁² + a₂²`, and the
Hankel determinant `μ₀μ₂ − μ₁² = (a₁ − a₂)²` is the squared gap. The normalization `Φ` of the
camera cancels from the ratio

`𝓗 = 4 (ΔW₁² − ΔW₀ ΔW₂) / ΔW₀²`,

so the squared gap is read from three image values (`hankel_ratio_eq`, `norm_hankel_sub_le`).

**Theorem** (`pair_hankel_rvm`). For a tempered configuration with Riemann–von Mangoldt local
counts, every `T^{−M'}`-isolated cluster of two points within `r ≤ T^{−(M' + κ_λ + 1)}` of `z₀` has
windows of aperture `λ · ½ log(T/2π)` with
`|𝓗 − (γ_{p₁} − γ_{p₂})²| ≤ pairReadError r (2rP + E) (2r²P + E) (2r³P + E)`,
`P = T^{M' + κ_λ}`, `E = e^{−K' log³(T/2π)}`. The error is `O(r³P) + O(E)`.

For an on-line pair `(γ_{p₁} − γ_{p₂})² = (Im p₁ − Im p₂)² > 0`. For an FE pair
`(γ_{p₁} − γ_{p₂})² = −4(Re p₁ − ½)² < 0` (`sq_gammaOf_sub_reflect`). So the sign of `Re 𝓗`
separates on-line pairs from FE pairs once `|w²|` exceeds the error (`pair_type_of_hankel_rvm`).
For the zeros of `ζ` the image values are the arithmetic side of the explicit formula: the reality
of near-coincident pairs (B44) is the sign of an image Hankel determinant.
-/

open MeasureTheory Complex Set Filter
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-! ### The Hankel determinant of a pair -/

/-- The error of the pair readout: for moment errors `δ₀, δ₁, δ₂` at radius `r`,
`ε_H = δ₀(2r² + δ₂) + 2δ₂ + δ₁(4r + δ₁)` and `(4r² + ε_H)·5δ₀ + ε_H`. -/
def pairReadError (r δ₀ δ₁ δ₂ : ℝ) : ℝ :=
  (4 * r ^ 2 + (δ₀ * (2 * r ^ 2 + δ₂) + 2 * δ₂ + δ₁ * (4 * r + δ₁))) * (5 * δ₀) +
    (δ₀ * (2 * r ^ 2 + δ₂) + 2 * δ₂ + δ₁ * (4 * r + δ₁))

/-- **The Hankel determinant of approximate pair moments.** If `|m₀ − 2| ≤ δ₀ ≤ 1`,
`|m₁ − (a₁ + a₂)| ≤ δ₁`, `|m₂ − (a₁² + a₂²)| ≤ δ₂` and `|a_i| ≤ r`, then
`|4(m₀m₂ − m₁²)/m₀² − (a₁ − a₂)²| ≤ pairReadError r δ₀ δ₁ δ₂`. -/
theorem norm_hankel_sub_le {m₀ m₁ m₂ a₁ a₂ : ℂ} {r δ₀ δ₁ δ₂ : ℝ}
    (ha₁ : ‖a₁‖ ≤ r) (ha₂ : ‖a₂‖ ≤ r) (hδ₀1 : δ₀ ≤ 1) (h0 : ‖m₀ - 2‖ ≤ δ₀)
    (h1 : ‖m₁ - (a₁ + a₂)‖ ≤ δ₁) (h2 : ‖m₂ - (a₁ ^ 2 + a₂ ^ 2)‖ ≤ δ₂) :
    ‖4 * (m₀ * m₂ - m₁ ^ 2) / m₀ ^ 2 - (a₁ - a₂) ^ 2‖ ≤ pairReadError r δ₀ δ₁ δ₂ := by
  have hδ₀ : 0 ≤ δ₀ := (norm_nonneg _).trans h0
  have hδ₁ : 0 ≤ δ₁ := (norm_nonneg _).trans h1
  have hδ₂ : 0 ≤ δ₂ := (norm_nonneg _).trans h2
  set μ₁ := a₁ + a₂ with hμ₁
  set μ₂ := a₁ ^ 2 + a₂ ^ 2 with hμ₂
  have hμ₁r : ‖μ₁‖ ≤ 2 * r := le_trans (norm_add_le a₁ a₂) (by linarith)
  have hμ₂r : ‖μ₂‖ ≤ 2 * r ^ 2 := by
    refine le_trans (norm_add_le (a₁ ^ 2) (a₂ ^ 2)) ?_
    rw [norm_pow, norm_pow]
    have := pow_le_pow_left₀ (norm_nonneg _) ha₁ 2
    have := pow_le_pow_left₀ (norm_nonneg _) ha₂ 2
    linarith
  have hw : (a₁ - a₂) ^ 2 = 2 * μ₂ - μ₁ ^ 2 := by rw [hμ₁, hμ₂]; ring
  -- the Hankel determinant of the approximate moments
  set h := m₀ * m₂ - m₁ ^ 2 with hh
  set εH := δ₀ * (2 * r ^ 2 + δ₂) + 2 * δ₂ + δ₁ * (4 * r + δ₁) with hεH
  have hhw : ‖h - (a₁ - a₂) ^ 2‖ ≤ εH := by
    have e : h - (a₁ - a₂) ^ 2 = (m₀ - 2) * (μ₂ + (m₂ - μ₂)) + 2 * (m₂ - μ₂) -
        (m₁ - μ₁) * (2 * μ₁ + (m₁ - μ₁)) := by rw [hh, hw]; ring
    rw [e]
    have s1 := norm_sub_le ((m₀ - 2) * (μ₂ + (m₂ - μ₂)) + 2 * (m₂ - μ₂))
      ((m₁ - μ₁) * (2 * μ₁ + (m₁ - μ₁)))
    have s2 := norm_add_le ((m₀ - 2) * (μ₂ + (m₂ - μ₂))) (2 * (m₂ - μ₂))
    rw [norm_mul, norm_mul, Complex.norm_two] at s2
    rw [norm_mul] at s1
    have t1 : ‖μ₂ + (m₂ - μ₂)‖ ≤ 2 * r ^ 2 + δ₂ := le_trans (norm_add_le _ _) (by linarith)
    have t2 : ‖2 * μ₁ + (m₁ - μ₁)‖ ≤ 4 * r + δ₁ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_mul, Complex.norm_two]; linarith
    have p1 := mul_le_mul h0 t1 (norm_nonneg _) hδ₀
    have p2 := mul_le_mul h1 t2 (norm_nonneg _) hδ₁
    rw [hεH]
    linarith
  -- dividing by `m₀²/4`
  have hm₀ : 1 ≤ ‖m₀‖ := by
    have := norm_sub_norm_le (2 : ℂ) m₀
    rw [Complex.norm_two, norm_sub_rev] at this
    linarith
  have hm₀0 : m₀ ≠ 0 := norm_pos_iff.mp (by linarith)
  have h4 : ‖(4 : ℂ) - m₀ ^ 2‖ ≤ 5 * δ₀ := by
    have e : (4 : ℂ) - m₀ ^ 2 = -(m₀ - 2) * (m₀ + 2) := by ring
    rw [e, norm_mul, norm_neg]
    have h5 : ‖m₀ + 2‖ ≤ 5 := by
      have e1 := norm_add_le m₀ 2
      have e2 := norm_sub_norm_le m₀ 2
      rw [Complex.norm_two] at e1 e2
      linarith
    calc ‖m₀ - 2‖ * ‖m₀ + 2‖ ≤ δ₀ * 5 := mul_le_mul h0 h5 (norm_nonneg _) hδ₀
      _ = 5 * δ₀ := by ring
  have hhn : ‖h‖ ≤ 4 * r ^ 2 + εH := by
    have hw' : ‖(a₁ - a₂) ^ 2‖ ≤ 4 * r ^ 2 := by
      rw [norm_pow]
      have h' : ‖a₁ - a₂‖ ≤ 2 * r := le_trans (norm_sub_le a₁ a₂) (by linarith)
      calc ‖a₁ - a₂‖ ^ 2 ≤ (2 * r) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h' 2
        _ = 4 * r ^ 2 := by ring
    have := norm_sub_norm_le h ((a₁ - a₂) ^ 2)
    linarith
  have hm2 : m₀ ^ 2 ≠ 0 := pow_ne_zero 2 hm₀0
  have e : 4 * h / m₀ ^ 2 - (a₁ - a₂) ^ 2 = h * ((4 - m₀ ^ 2) / m₀ ^ 2) + (h - (a₁ - a₂) ^ 2) := by
    rw [sub_div, div_self hm2]
    ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  rw [norm_mul, norm_div, norm_pow]
  have hm₀2 : 1 ≤ ‖m₀‖ ^ 2 := one_le_pow₀ hm₀
  have hq : ‖(4 : ℂ) - m₀ ^ 2‖ / ‖m₀‖ ^ 2 ≤ 5 * δ₀ :=
    (div_le_self (norm_nonneg _) hm₀2).trans h4
  have := mul_le_mul hhn hq (by positivity) (by linarith [norm_nonneg h])
  unfold pairReadError
  rw [hεH] at hhw this
  linarith

/-- **The normalization of the camera cancels.** For `m_j = ΔW_j / ((−i)^j Φ)`,
`4(m₀m₂ − m₁²)/m₀² = 4(ΔW₁² − ΔW₀ΔW₂)/ΔW₀²`. -/
theorem hankel_ratio_eq {ΔW₀ ΔW₁ ΔW₂ Φ : ℂ} (hΦ : Φ ≠ 0) (h0 : ΔW₀ ≠ 0) :
    4 * (ΔW₀ / ((-I) ^ 0 * Φ) * (ΔW₂ / ((-I) ^ 2 * Φ)) - (ΔW₁ / ((-I) ^ 1 * Φ)) ^ 2) /
        (ΔW₀ / ((-I) ^ 0 * Φ)) ^ 2 =
      4 * (ΔW₁ ^ 2 - ΔW₀ * ΔW₂) / ΔW₀ ^ 2 := by
  have hI : (-I : ℂ) ^ 2 = -1 := by rw [neg_sq, Complex.I_sq]
  have e1 : (ΔW₁ / ((-I) ^ 1 * Φ)) ^ 2 = -(ΔW₁ ^ 2 / Φ ^ 2) := by
    rw [div_pow, mul_pow, pow_one, hI]
    ring
  rw [e1, pow_zero, one_mul, hI]
  field_simp
  ring

/-- The squared gap of an FE pair: `(γ_ρ − γ_{1 − ρ̄})² = −4(Re ρ − ½)²`. -/
theorem sq_gammaOf_sub_reflect (ρ : ℂ) :
    (gammaOf ρ - gammaOf (reflect ρ)) ^ 2 = -(4 * (ρ.re - 1 / 2) ^ 2 : ℝ) := by
  rw [gammaOf_reflect_eq_conj]
  have e : gammaOf ρ - conj (gammaOf ρ) = (2 * (gammaOf ρ).im : ℝ) * I := by
    apply Complex.ext
    · simp
    · simp; ring
  rw [e, mul_pow, Complex.I_sq, gammaOf_im]
  push_cast
  ring

/-- The squared gap of an on-line pair: `(γ_{p₁} − γ_{p₂})² = (Im p₁ − Im p₂)²`. -/
theorem sq_gammaOf_sub_of_onLine {p₁ p₂ : ℂ} (h₁ : p₁.re = 1 / 2) (h₂ : p₂.re = 1 / 2) :
    (gammaOf p₁ - gammaOf p₂) ^ 2 = ((p₁.im - p₂.im) ^ 2 : ℝ) := by
  have e : gammaOf p₁ - gammaOf p₂ = ((p₁.im - p₂.im : ℝ) : ℂ) := by
    apply Complex.ext
    · simp [Complex.sub_re, gammaOf_re]
    · simp [Complex.sub_im, gammaOf_im, h₁, h₂]
  rw [e]; push_cast; ring

/-! ### The pair readout uniformly in the height -/

theorem sum_pair_points {p₁ p₂ : ℂ} (f : ℂ → ℂ) :
    ∑ z ∈ ({p₁, p₂} : Finset ℂ), ((if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0) : ℂ) *
      f z = f p₁ + f p₂ := by
  classical
  simp only [add_mul, ite_mul, one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_insert, Finset.mem_singleton, true_or, or_true, if_true]

theorem sum_norm_pair_points_le {p₁ p₂ : ℂ} :
    ∑ z ∈ ({p₁, p₂} : Finset ℂ), ‖((if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0) : ℂ)‖ ≤
      2 := by
  classical
  have hδ : ∀ x : ℂ, ∑ z ∈ ({p₁, p₂} : Finset ℂ), ‖(if z = x then 1 else 0 : ℂ)‖ ≤ 1 := fun x => by
    have : ∀ z, ‖(if z = x then 1 else 0 : ℂ)‖ = if z = x then 1 else 0 := fun z => by
      split_ifs <;> simp
    simp only [this, Finset.sum_ite_eq']
    split_ifs <;> norm_num
  refine (Finset.sum_le_sum fun z _ => norm_add_le _ _).trans ?_
  rw [Finset.sum_add_distrib]
  linarith [hδ p₁, hδ p₂]

theorem exp_neg_le_half {x : ℝ} (hx : 1 ≤ x) : Real.exp (-x) ≤ 1 / 2 := by
  rw [Real.exp_neg, ← one_div, div_le_div_iff₀ (Real.exp_pos x) (by norm_num)]
  linarith [Real.add_one_le_exp x]

/-- **The image Hankel determinant reads the squared gap, uniformly in the height.** Let
`0 ≤ θ`, `λ > θ/2`, `A, S, M' ≥ 0` and `K' ≥ 1`. For all `T ≥ T₀`: let `Z` be a tempered
configuration with `Σ m(z)/(1 + |γ_z|²) ≤ S` and local count
`≤ (θ/2π) log(T/2π)(y − x) + A log(T/2π)` in `[T/2, 3T/2]`. Let `p₁, p₂` be the only points of
`Z` in the disc `‖z − z₀‖ ≤ r`, `r ≤ T^{−(M' + κ_λ + 1)}`, each of multiplicity one (or one double
point), with every other point in `[T/2, 3T/2]` at distance `≥ T^{−M'}` from `z₀`. Then windows
`F₀, F₁, F₂, G` of aperture `λ · ½ log(T/2π)` have `Z.W F₀ G ≠ 0` and
`|4(W₁² − W₀W₂)/W₀² − (γ_{p₁} − γ_{p₂})²| ≤ pairReadError r δ₀ δ₁ δ₂`, `W_j = Z.W F_j G`,
`δ_j = 2r^{j+1}T^{M' + κ_λ} + e^{−K' log³(T/2π)}`. -/
theorem pair_hankel_rvm {θ lam A S M' K' : ℝ} (hθ : 0 ≤ θ) (hlam : θ / 2 < lam) (hA : 0 ≤ A)
    (hS : 0 ≤ S) (hM' : 0 ≤ M') (hK' : 1 ≤ K') :
    ∃ T₀ : ℝ, 2 * π * Real.exp 1 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      ∀ Z : ZeroConfig, TemperedConfig Z →
        ∑' z, ‖multDiff Z emptyZeroConfig z‖ / (1 + Complex.normSq (gammaOf z)) ≤ S →
        (∀ (s : Finset ℂ) (x y : ℝ), x ≤ y →
          (∀ z ∈ s, multDiff Z emptyZeroConfig z ≠ 0 ∧ |z.im - T| ≤ T / 2 ∧ z.im ∈ Icc x y) →
            (s.card : ℝ) ≤ θ / (2 * π) * Real.log (T / (2 * π)) * (y - x) +
              A * Real.log (T / (2 * π))) →
        ∀ z₀ : ℂ, |z₀.im - T| ≤ T / 4 → |z₀.re - 1 / 2| ≤ 1 / 2 →
        ∀ r : ℝ, 0 ≤ r → r ≤ T ^ (-(M' + slowExponent lam + 1)) →
        (∀ z, multDiff Z emptyZeroConfig z ≠ 0 → |z.im - T| ≤ T / 2 →
          ‖z - z₀‖ ≤ r ∨ T ^ (-M') ≤ ‖z - z₀‖) →
        ∀ p₁ p₂ : ℂ, ‖p₁ - z₀‖ ≤ r → ‖p₂ - z₀‖ ≤ r →
        (∀ z, ‖z - z₀‖ ≤ r → multDiff Z emptyZeroConfig z =
          (if z = p₁ then 1 else 0) + (if z = p₂ then 1 else 0)) →
        ∃ F₀ F₁ F₂ G : ℝ → ℂ, ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₀ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₁ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) F₂ ∧
          ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) G ∧ Z.W F₀ G ≠ 0 ∧
          ‖4 * (Z.W F₁ G ^ 2 - Z.W F₀ G * Z.W F₂ G) / Z.W F₀ G ^ 2 -
              (gammaOf p₁ - gammaOf p₂) ^ 2‖ ≤
            pairReadError r
              (2 * r * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)))
              (2 * r ^ 2 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)))
              (2 * r ^ 3 * T ^ (M' + slowExponent lam) +
                Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3))) := by
  classical
  obtain ⟨T₀, hT₀, hread⟩ := discMoment_readout_rvm 2 hθ hlam hA hS hM' (by linarith : 0 ≤ K')
  refine ⟨T₀, hT₀, fun T hT Z hZ hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso p₁ p₂ hp₁ hp₂ hc => ?_⟩
  set s : Finset ℂ := {p₁, p₂} with hs
  have hsd : ∀ z ∈ s, ‖z - z₀‖ ≤ r := by
    intro z hz
    simp only [hs, Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> assumption
  have hds : ∀ z, multDiff Z emptyZeroConfig z ≠ 0 → ‖z - z₀‖ ≤ r → z ∈ s := by
    intro z hcz hzr
    by_contra hzs
    simp only [hs, Finset.mem_insert, Finset.mem_singleton, not_or] at hzs
    apply hcz
    rw [hc z hzr, if_neg hzs.1, if_neg hzs.2, add_zero]
  obtain ⟨F₁, G₁, -, hG₁, hΦ, hj⟩ := hread T hT Z emptyZeroConfig hZ temperedConfig_emptyZeroConfig
    hStail hcount z₀ hz₀ hz₀re r hr0 hr hiso s hsd hds
  obtain ⟨E, hE⟩ : ∃ E, E = Real.exp (-(K' * Real.log (T / (2 * π)) ^ 3)) := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P, P = T ^ (M' + slowExponent lam) := ⟨_, rfl⟩
  rw [← hE, ← hP] at hj ⊢
  -- the moments of the pair
  have hsum : ∀ f : ℂ → ℂ, ∑ z ∈ s, multDiff Z emptyZeroConfig z * f z = f p₁ + f p₂ := by
    intro f
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)], sum_pair_points]
  have hN : ∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖ ≤ 2 := by
    rw [Finset.sum_congr rfl fun z hz => by rw [hc z (hsd z hz)]]
    exact sum_norm_pair_points_le
  -- the scales
  have h2πe : 4 ≤ 2 * π * Real.exp 1 := by
    have h1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
    nlinarith [Real.pi_gt_three]
  have hT4 : 4 ≤ T := h2πe.trans (hT₀.trans hT)
  have hT0 : 0 < T := by linarith
  have hP0 : 0 ≤ P := by rw [hP]; exact Real.rpow_nonneg hT0.le _
  have hrP : r * P ≤ 1 / 4 := by
    have hprod : T ^ (-(M' + slowExponent lam + 1)) * P = T⁻¹ := by
      rw [hP, ← Real.rpow_add hT0, show -(M' + slowExponent lam + 1) + (M' + slowExponent lam) =
        -1 by ring, Real.rpow_neg_one]
    have h1 : r * P ≤ T⁻¹ := hprod ▸ mul_le_mul_of_nonneg_right hr hP0
    have h2 : T⁻¹ ≤ 1 / 4 := by
      rw [inv_le_comm₀ hT0 (by norm_num), one_div, inv_inv]; exact hT4
    linarith
  have hu1 : 1 ≤ Real.log (T / (2 * π)) := by
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith [hT₀, hT]
  have hE2 : E ≤ 1 / 2 := by
    rw [hE]
    refine exp_neg_le_half ?_
    have : 1 ≤ Real.log (T / (2 * π)) ^ 3 := one_le_pow₀ hu1
    nlinarith
  have hE0 : 0 ≤ E := by rw [hE]; exact (Real.exp_pos _).le
  -- the readout at orders `0, 1, 2`
  set ω := gammaOf z₀
  have ha : ∀ p, ‖p - z₀‖ ≤ r → ‖gammaOf p - ω‖ ≤ r := fun p hp => by
    rw [norm_gammaOf_sub]; exact hp
  have hδ : ∀ j : ℕ, (∑ z ∈ s, ‖multDiff Z emptyZeroConfig z‖) * r ^ (j + 1) * P + E ≤
      2 * r ^ (j + 1) * P + E := fun j => by
    have := mul_le_mul_of_nonneg_right hN (mul_nonneg (pow_nonneg hr0 (j + 1)) hP0)
    linarith
  obtain ⟨hF0, h0⟩ := hj 0 (by norm_num)
  obtain ⟨hF1, h1⟩ := hj 1 (by norm_num)
  obtain ⟨hF2, h2⟩ := hj 2 (by norm_num)
  rw [W_emptyZeroConfig, sub_zero, hsum] at h0 h1 h2
  have e0 : (gammaOf p₁ - ω) ^ 0 + (gammaOf p₂ - ω) ^ 0 = 2 := by norm_num
  have e1 : (gammaOf p₁ - ω) ^ 1 + (gammaOf p₂ - ω) ^ 1 = (gammaOf p₁ - ω) + (gammaOf p₂ - ω) := by
    ring
  rw [e0] at h0
  rw [e1] at h1
  have h0' := h0.trans (hδ 0)
  have h1' := h1.trans (hδ 1)
  have h2' := h2.trans (hδ 2)
  rw [zero_add] at h0'
  rw [show (1 + 1 : ℕ) = 2 by rfl] at h1'
  rw [show (2 + 1 : ℕ) = 3 by rfl] at h2'
  have hδ₀1 : 2 * r ^ 1 * P + E ≤ 1 := by rw [pow_one]; linarith
  have hH := norm_hankel_sub_le (a₁ := gammaOf p₁ - ω) (a₂ := gammaOf p₂ - ω)
    (ha p₁ hp₁) (ha p₂ hp₂) hδ₀1 h0' h1' h2'
  -- the normalization cancels
  have hm0 : ∀ x : ℂ, ‖x - 2‖ ≤ 1 → x ≠ 0 := fun x hx h => by
    rw [h, zero_sub, norm_neg, Complex.norm_two] at hx; linarith
  have hW0 : Z.W (localWindow z₀.im (annihilatePow (ω - z₀.im) 0 F₁))
      (localWindow z₀.im G₁) ≠ 0 := by
    intro h
    apply hm0 _ (h0'.trans hδ₀1)
    rw [h, zero_div]
  rw [hankel_ratio_eq hΦ hW0, show (gammaOf p₁ - ω) - (gammaOf p₂ - ω) = gammaOf p₁ - gammaOf p₂
    by ring] at hH
  refine ⟨_, _, _, _, hF0, hF1, hF2, apertureWindow_localWindow hG₁ _, hW0, ?_⟩
  simpa only [pow_one] using hH

/-- **The image separates on-line pairs from FE pairs.** In the setting of `pair_hankel_rvm`, with
`B` the readout error: an on-line pair has `Re 𝓗 ≥ (Im p₁ − Im p₂)² − B`, and an FE pair
`p₂ = 1 − p̄₁` has `Re 𝓗 ≤ −4(Re p₁ − ½)² + B`. -/
theorem pair_type_of_hankel {𝓗 : ℂ} {p₁ p₂ : ℂ} {B : ℝ}
    (h : ‖𝓗 - (gammaOf p₁ - gammaOf p₂) ^ 2‖ ≤ B) :
    (p₁.re = 1 / 2 → p₂.re = 1 / 2 → (p₁.im - p₂.im) ^ 2 - B ≤ 𝓗.re) ∧
      (p₂ = reflect p₁ → 𝓗.re ≤ -(4 * (p₁.re - 1 / 2) ^ 2) + B) := by
  have hre : |(𝓗 - (gammaOf p₁ - gammaOf p₂) ^ 2).re| ≤ B :=
    (Complex.abs_re_le_norm _).trans h
  rw [Complex.sub_re] at hre
  have hre' := abs_le.mp hre
  refine ⟨fun h₁ h₂ => ?_, fun hp => ?_⟩
  · rw [sq_gammaOf_sub_of_onLine h₁ h₂, Complex.ofReal_re] at hre'
    linarith [hre'.1]
  · rw [hp, sq_gammaOf_sub_reflect, Complex.neg_re, Complex.ofReal_re] at hre'
    linarith [hre'.2]

end GaloisForLFunctions.ZeroConfigurationGeometry
