import GaloisForLFunctions.RHTower.ZetaGridReindex
import GaloisForLFunctions.RHTower.ZetaWeightedFrobeniusPP
import GaloisForLFunctions.RHTower.ZetaWeightedTracePrime

/-!
# Non-close prime pairs in the weighted Frobenius norm

On the grid `τ_k = T + k h`, `h = 2π/L`, `k ∈ [0, d)`, with Jackson weights `W_k = W(τ_k)`, a grid double sum whose
summand is `W_k W_l e^{iθτ_l} B(k − l)` is reindexed by the offset `r = k − l` (`sum_sum_eq_sum_offset`).  For each
offset the admissible sum `Σ_l W(τ_l + rh) W(τ_l) e^{iθτ_l}` is the finite part of a lattice sum that vanishes whenever
`θ` is at distance `≥ 4b` from every alias `jL` (`hasSum_jacksonProduct_grid_char_eq_zero`), so it is bounded by twice
the outer Jackson mass `E` (`norm_sum_admissible_jacksonProduct_le`).  Hence (`norm_sum_sum_jacksonDifference_le`)

`‖Σ_{k,l} W_k W_l e^{iθτ_l} B(k − l)‖ ≤ 2E Σ_{|r|<d} ‖B(r)‖`.

For `z_n(k, l) = e^{iy_nτ_l} A_n(k − l)` the products `z_n z̄_m` and `z_n z_m` carry the frequencies `y_n − y_m` and
`y_n + y_m`, so a pair `(n, m)` whose difference and sum frequencies both avoid the aliases contributes at most
`2E Σ_r ‖A_n(r)‖ ‖A_m(r)‖` to the weighted prime–prime Frobenius sum (`abs_weighted_pair_le`).
-/

open Complex Real Finset

noncomputable section

namespace RHTower

namespace FejerWeight

variable {b s₀ s₁ : ℝ}

/-- `[0, d)` as the image of `range d` in `ℤ`. -/
theorem image_range_natCast_eq_Ico (d : ℕ) :
    (Finset.range d).image (fun k : ℕ => (k : ℤ)) = Finset.Ico (0 : ℤ) d := by
  ext k
  simp only [Finset.mem_image, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨n, hn, rfl⟩; exact ⟨by positivity, by exact_mod_cast hn⟩
  · rintro ⟨h0, h1⟩
    lift k to ℕ using h0
    exact ⟨k, by exact_mod_cast h1, rfl⟩

/-- Outer Jackson mass off `[0, d)`, written as an indicator sum. -/
theorem tsum_indicator_compl_jacksonWindow_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) :
    ∑' k, (((Finset.Ico (0 : ℤ) d : Finset ℤ) : Set ℤ)ᶜ).indicator
        (fun k : ℤ => jacksonWindow b s₀ s₁ (T + k * (2 * π / L))) k
      ≤ (jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)) := by
  have h := tsum_compl_jacksonWindow_le hb h01 hL hM d hs₀ hs₁
  rw [image_range_natCast_eq_Ico] at h
  rw [← _root_.tsum_subtype]
  exact h

/-- **Admissible product-window sums off the aliases.**  For an offset `r` and a frequency `y` at distance `≥ 4b` from
every alias `jL`, the sum of `W(τ_{l+r}) W(τ_l) e^{iyτ_l}` over the `l ∈ [0, d)` with `l + r ∈ [0, d)` is at most twice
the outer Jackson mass. -/
theorem norm_sum_admissible_jacksonProduct_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) (r : ℤ) {y : ℝ}
    (hy : ∀ j : ℤ, 4 * b ≤ |j * L - y|) :
    ‖∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
        ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
          * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ))‖
      ≤ 2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2))) := by
  have hc := hasSum_jacksonProduct_grid_char_eq_zero hb h01 (r * (2 * π / L)) hL T y hy
  have e : ∀ l : ℤ, T + l * (2 * π / L) + r * (2 * π / L) = T + ((l + r : ℤ) : ℝ) * (2 * π / L) := by
    intro l; push_cast; ring
  simp only [e] at hc
  set u : ℤ → ℝ := fun k => jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) with hu
  have hu0 : ∀ k, 0 ≤ u k := fun k => jacksonWindow_nonneg hb h01 _
  have hu1 : ∀ k, u k ≤ 1 := fun k => jacksonWindow_le_one hb h01 _
  have hus : Summable u := summable_jacksonWindow_grid hb h01 hL T
  have hnorm : ∀ l : ℤ, ‖((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
        * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
        * cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ))‖ = u (l + r) * u l := by
    intro l
    have h1 : ‖cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ))‖ = 1 := by
      rw [show I * (y : ℂ) * ((T + l * (2 * π / L) : ℝ) : ℂ)
          = ((y * (T + l * (2 * π / L)) : ℝ) : ℂ) * I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [norm_mul, h1, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hu0 (l + r)) (hu0 l))]
  have h := norm_sum_admissible_le hc hu0 hu0 hus hus r
    (fun l => by rw [hnorm]; exact mul_le_of_le_one_right (hu0 _) (hu1 l))
    (fun l => by rw [hnorm]; exact mul_le_of_le_one_left (hu0 l) (hu1 _)) (Finset.Ico (0 : ℤ) d)
  have hE := tsum_indicator_compl_jacksonWindow_le hb h01 hL hM d hs₀ hs₁
  refine h.trans ?_
  linarith

/-- **Grid double sums with a difference kernel off the aliases.** -/
theorem norm_sum_sum_jacksonDifference_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) {θ : ℝ}
    (hθ : ∀ j : ℤ, 4 * b ≤ |j * L - θ|) (B : ℤ → ℂ) :
    ‖∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        ((jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) * B (k - l)‖
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖B r‖)
          * (2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)))) := by
  rw [sum_sum_eq_sum_offset, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun r _ => ?_)
  have hterm : ∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
      ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
        * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) * B (l + r - l)
      = B r * ∑ l ∈ (Finset.Ico (0 : ℤ) d).filter (fun l => l + r ∈ Finset.Ico (0 : ℤ) d),
        ((jacksonWindow b s₀ s₁ (T + ((l + r : ℤ) : ℝ) * (2 * π / L))
          * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) : ℝ) : ℂ)
          * cexp (I * θ * ((T + l * (2 * π / L) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [add_sub_cancel_left]
    ring
  rw [hterm, norm_mul]
  exact mul_le_mul_of_nonneg_left
    (norm_sum_admissible_jacksonProduct_le hb h01 hL hM d hs₀ hs₁ r hθ) (norm_nonneg _)

/-- `e^{iyt} · conj(e^{iy't}) = e^{i(y − y')t}` for real `y, y', t`. -/
theorem cexp_mul_conj_cexp (y y' t : ℝ) :
    cexp (I * y * (t : ℂ)) * starRingEnd ℂ (cexp (I * y' * (t : ℂ)))
      = cexp (I * ((y - y' : ℝ) : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
  push_cast
  ring

/-- `e^{iyt} · e^{iy't} = e^{i(y + y')t}`. -/
theorem cexp_mul_cexp_I (y y' t : ℝ) :
    cexp (I * y * (t : ℂ)) * cexp (I * y' * (t : ℂ)) = cexp (I * ((y + y' : ℝ) : ℂ) * (t : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- A real weighted double sum of real parts is bounded by the norm of the complex double sum. -/
theorem abs_sum_sum_mul_re_le {S : Finset ℤ} (f : ℤ → ℤ → ℝ) (g : ℤ → ℤ → ℂ) :
    |∑ k ∈ S, ∑ l ∈ S, f k l * (g k l).re| ≤ ‖∑ k ∈ S, ∑ l ∈ S, (f k l : ℂ) * g k l‖ := by
  have e : ∑ k ∈ S, ∑ l ∈ S, f k l * (g k l).re = (∑ k ∈ S, ∑ l ∈ S, (f k l : ℂ) * g k l).re := by
    simp only [Complex.re_sum, Complex.re_ofReal_mul]
  rw [e]
  exact Complex.abs_re_le_norm _

/-- **A non-close prime pair in the weighted Frobenius sum.**  With `z_n(k, l) = e^{iy_nτ_l} A_n(k − l)`, if both
`y_n − y_m` and `y_n + y_m` are at distance `≥ 4b` from every alias `jL`, then the `(n, m)` entry of the weighted
expansion `Σ_{k,l} W_k W_l (Re(z_n z̄_m) + Re(z_n z_m))/2` is at most `2E Σ_{|r|<d} ‖A_n(r)‖ ‖A_m(r)‖`. -/
theorem abs_weighted_pair_le (hb : 0 < b) (h01 : s₀ ≤ s₁) {L T M : ℝ} (hL : 0 < L)
    (hM : 0 < M) (d : ℕ) (hs₀ : T + M ≤ s₀) (hs₁ : s₁ + M ≤ T + d * (2 * π / L)) {y y' : ℝ}
    (hminus : ∀ j : ℤ, 4 * b ≤ |j * L - (y - y')|) (hplus : ∀ j : ℤ, 4 * b ≤ |j * L - (y + y')|)
    (A A' : ℤ → ℂ) :
    |∑ k ∈ Finset.Ico (0 : ℤ) d, ∑ l ∈ Finset.Ico (0 : ℤ) d,
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L))
          * (((cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re
              + (cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re) / 2)|
      ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖A r‖ * ‖A' r‖)
          * (2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2)))) := by
  set E : ℝ := 2 * ((jacksonMass b)⁻¹ * (16 / (3 * b ^ 2)) * (1 / M ^ 3 + 2 / (2 * π / L * M ^ 2))) with hE
  set S := Finset.Ico (0 : ℤ) d with hS
  set τ : ℤ → ℝ := fun l => T + l * (2 * π / L) with hτ
  set w : ℤ → ℤ → ℝ := fun k l => jacksonWindow b s₀ s₁ (T + k * (2 * π / L))
    * jacksonWindow b s₀ s₁ (T + l * (2 * π / L)) with hw
  set g₁ : ℤ → ℤ → ℂ := fun k l => cexp (I * ((y - y' : ℝ) : ℂ) * ((τ l : ℝ) : ℂ))
    * (A (k - l) * starRingEnd ℂ (A' (k - l))) with hg₁
  set g₂ : ℤ → ℤ → ℂ := fun k l => cexp (I * ((y + y' : ℝ) : ℂ) * ((τ l : ℝ) : ℂ))
    * (A (k - l) * A' (k - l)) with hg₂
  have hsplit : ∑ k ∈ S, ∑ l ∈ S,
        jacksonWindow b s₀ s₁ (T + k * (2 * π / L)) * jacksonWindow b s₀ s₁ (T + l * (2 * π / L))
          * (((cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re
              + (cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
                * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l))).re) / 2)
      = ((∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re) + ∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re) / 2 := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun l _ => ?_
    have e₁ : cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
          * starRingEnd ℂ (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l)) = g₁ k l := by
      simp only [hg₁, hτ, map_mul]
      rw [← cexp_mul_conj_cexp]
      ring
    have e₂ : cexp (I * y * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A (k - l)
          * (cexp (I * y' * ((T + l * (2 * π / L) : ℝ) : ℂ)) * A' (k - l)) = g₂ k l := by
      simp only [hg₂, hτ]
      rw [← cexp_mul_cexp_I]
      ring
    rw [e₁, e₂]
    simp only [hw]
    ring
  rw [hsplit]
  have hbound : ∀ (θ : ℝ), (∀ j : ℤ, 4 * b ≤ |j * L - θ|) → ∀ B : ℤ → ℂ, (∀ r, ‖B r‖ = ‖A r‖ * ‖A' r‖) →
      |∑ k ∈ S, ∑ l ∈ S, w k l * (cexp (I * θ * ((τ l : ℝ) : ℂ)) * B (k - l)).re|
        ≤ (∑ r ∈ Finset.Ioo (-(d : ℤ)) d, ‖A r‖ * ‖A' r‖) * E := by
    intro θ hθ B hB
    refine (abs_sum_sum_mul_re_le w _).trans ?_
    have h := norm_sum_sum_jacksonDifference_le hb h01 hL hM d hs₀ hs₁ hθ B
    simp only [hB] at h
    refine le_of_eq_of_le ?_ h
    congr 1
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hw, hτ]
    push_cast
    ring
  have h₁ := hbound (y - y') hminus (fun r => A r * starRingEnd ℂ (A' r))
    (fun r => by rw [norm_mul, Complex.norm_conj])
  have h₂ := hbound (y + y') hplus (fun r => A r * A' r) (fun r => norm_mul _ _)
  rw [abs_div, abs_two]
  have := abs_add_le (∑ k ∈ S, ∑ l ∈ S, w k l * (g₁ k l).re) (∑ k ∈ S, ∑ l ∈ S, w k l * (g₂ k l).re)
  linarith

end FejerWeight

end RHTower
