import GaloisForLFunctions.MatomakiRadziwill.LFunctionThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.LandauRealPart

/-!
# The de la Vallée Poussin inequality for Dirichlet `L`-functions

Let `χ` be a character mod `q`, `σ = 1 + δ`, and suppose `L(β + iγ, χ) = 0` with `1 + δ − β ≤ R/2`.
If `‖L(·, χ)‖ < Φ` on the disc of radius `R₀ > R` about `σ + iγ` and `‖L(·, χ²)‖ < Φ` on the disc
about `σ + 2iγ`, then (`L_dlvp_inequality`)

`4/(1 + δ − β) ≤ 3/δ + 3A + (80/R)(log Φ + log(1 + 1/δ))`,

`A` the constant of the pole bound `Re(−ζ'/ζ(σ)) ≤ 1/(σ−1) + A`.  Landau's lemma
(`Sieve.neg_re_logDeriv_le`) at `σ + iγ` retains the zero; at `σ + 2iγ` nothing is retained; both
centres have `‖L‖ ≥ 1/(1 + 1/δ)` (`inv_le_norm_LFunction`), and the three-four-one inequality
(`three_four_one_logDeriv`) combines them with the pole bound for `χ₀`.
-/

open Complex Metric LSeries ArithmeticFunction RHTower.Sieve
open scoped LSeries.notation

namespace GaloisForLFunctions.MatomakiRadziwill

noncomputable section
set_option autoImplicit false

variable {q : ℕ} [NeZero q]

/-- `Re L(ψΛ, s) = −Re (L'/L)(s, ψ)` for `Re s > 1`. -/
theorem re_LSeries_twist_vonMangoldt_eq (ψ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 < s.re) :
    (LSeries (↗ψ * ↗Λ) s).re = -(logDeriv (DirichletCharacter.LFunction ψ) s).re := by
  rw [DirichletCharacter.LSeries_twist_vonMangoldt_eq ψ hs, logDeriv_apply,
    DirichletCharacter.deriv_LFunction_eq_deriv_LSeries ψ hs,
    DirichletCharacter.LFunction_eq_LSeries ψ hs, neg_div, Complex.neg_re]

/-- `L(·, ψ)` is analytic on any disc avoiding `1`. -/
theorem analyticOnNhd_LFunction_ball (ψ : DirichletCharacter ℂ q) {c : ℂ} {R₀ : ℝ}
    (hne : ∀ w ∈ ball c R₀, w ≠ 1) :
    AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) (ball c R₀) := by
  have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction ψ) (ball c R₀) := fun w hw =>
    (DirichletCharacter.differentiableAt_LFunction ψ w (Or.inl (hne w hw))).differentiableWithinAt
  exact hd.analyticOnNhd isOpen_ball

/-- A disc of radius at most `1` about a point of height at least `1` avoids `1`. -/
theorem ne_one_of_mem_ball {c w : ℂ} {R₀ γ : ℝ} (hcim : c.im = γ) (hγ : 1 ≤ γ) (hR₀ : R₀ ≤ 1)
    (hw : w ∈ ball c R₀) : w ≠ 1 := by
  rintro rfl
  have hd : ‖(1 : ℂ) - c‖ < R₀ := by simpa [dist_eq_norm] using hw
  have h1 : |((1 : ℂ) - c).im| ≤ ‖(1 : ℂ) - c‖ := Complex.abs_im_le_norm _
  rw [Complex.sub_im, hcim] at h1
  simp only [Complex.one_im, zero_sub, abs_neg] at h1
  rw [abs_of_pos (by linarith)] at h1
  linarith

/-- **The de la Vallée Poussin inequality for `L(s, χ)`.** -/
theorem L_dlvp_inequality (χ : DirichletCharacter ℂ q) {β γ dl A R R₀ Φ : ℝ}
    (hA : ∀ σ : ℝ, 1 < σ → σ ≤ 2 →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 1 / (σ - 1) + A)
    (hγ : 3 ≤ γ) (hd0 : 0 < dl) (hdl : dl ≤ 1 / 16)
    (hR0 : 0 < R) (hRR₀ : R < R₀) (hR₀1 : R₀ ≤ 1)
    (hΦ1 : ∀ w ∈ ball (((1 + dl : ℝ) : ℂ) + (γ : ℂ) * I) R₀,
      ‖DirichletCharacter.LFunction χ w‖ < Φ)
    (hΦ2 : ∀ w ∈ ball (((1 + dl : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R₀,
      ‖DirichletCharacter.LFunction (χ ^ 2) w‖ < Φ)
    (hβ1 : β ≤ 1) (hclose : 1 + dl - β ≤ R / 2)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * I) = 0) :
    4 / (1 + dl - β) ≤ 3 / dl + 3 * A + 80 / R * (Real.log Φ + Real.log (1 + 1 / dl)) := by
  set σ : ℝ := 1 + dl with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hσd : σ - 1 = dl := by rw [hσdef]; ring
  have hsb : 0 < σ - β := by rw [hσdef]; linarith
  set c₁ : ℂ := (σ : ℂ) + (γ : ℂ) * I with hc₁def
  set c₂ : ℂ := (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I with hc₂def
  have hc₁re : c₁.re = σ := by rw [hc₁def]; simp
  have hc₁im : c₁.im = γ := by rw [hc₁def]; simp
  have hc₂re : c₂.re = σ := by rw [hc₂def]; simp
  have hc₂im : c₂.im = 2 * γ := by rw [hc₂def]; simp
  have hne₁ : ∀ w ∈ ball c₁ R₀, w ≠ 1 := fun w hw =>
    ne_one_of_mem_ball hc₁im (by linarith) hR₀1 hw
  have hne₂ : ∀ w ∈ ball c₂ R₀, w ≠ 1 := fun w hw =>
    ne_one_of_mem_ball hc₂im (by linarith) hR₀1 hw
  -- the two centres: nonvanishing and lower bounds
  set Z : ℝ := 1 + 1 / dl with hZdef
  have hZ0 : 0 < Z := by rw [hZdef]; positivity
  have hlow₁ : Z⁻¹ ≤ ‖DirichletCharacter.LFunction χ c₁‖ := by
    have h := inv_le_norm_LFunction χ hσ1 γ
    have e : (1 + (σ - 1)⁻¹)⁻¹ = Z⁻¹ := by rw [hσd, hZdef, one_div]
    rw [e] at h
    exact h
  have hlow₂ : Z⁻¹ ≤ ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖ := by
    have h := inv_le_norm_LFunction (χ ^ 2) hσ1 (2 * γ)
    have e : (1 + (σ - 1)⁻¹)⁻¹ = Z⁻¹ := by rw [hσd, hZdef, one_div]
    rw [e] at h
    exact h
  have hpos₁ : 0 < ‖DirichletCharacter.LFunction χ c₁‖ := lt_of_lt_of_le (by positivity) hlow₁
  have hpos₂ : 0 < ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖ :=
    lt_of_lt_of_le (by positivity) hlow₂
  have hf₁c : DirichletCharacter.LFunction χ c₁ ≠ 0 := norm_pos_iff.mp hpos₁
  have hf₂c : DirichletCharacter.LFunction (χ ^ 2) c₂ ≠ 0 := norm_pos_iff.mp hpos₂
  have hΦc₁ : ‖DirichletCharacter.LFunction χ c₁‖ < Φ := hΦ1 c₁ (mem_ball_self (by linarith))
  have hΦc₂ : ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖ < Φ :=
    hΦ2 c₂ (mem_ball_self (by linarith))
  have hΦ0 : 0 < Φ := lt_trans hpos₁ hΦc₁
  set M₁ : ℝ := Φ / ‖DirichletCharacter.LFunction χ c₁‖ with hM₁def
  set M₂ : ℝ := Φ / ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖ with hM₂def
  have hM₁ : 1 < M₁ := by rw [hM₁def, lt_div_iff₀ hpos₁, one_mul]; exact hΦc₁
  have hM₂ : 1 < M₂ := by rw [hM₂def, lt_div_iff₀ hpos₂, one_mul]; exact hΦc₂
  have hlogM : ∀ {x : ℝ}, 0 < x → Z⁻¹ ≤ x → Real.log (Φ / x) ≤ Real.log Φ + Real.log Z := by
    intro x hx hxZ
    rw [Real.log_div hΦ0.ne' hx.ne']
    have h1 : Real.log Z⁻¹ ≤ Real.log x := Real.log_le_log (by positivity) hxZ
    rw [Real.log_inv] at h1
    linarith
  have hlog₁ := hlogM hpos₁ hlow₁
  have hlog₂ := hlogM hpos₂ hlow₂
  rw [← hM₁def] at hlog₁
  rw [← hM₂def] at hlog₂
  -- Landau at height `γ`, retaining the zero
  obtain ⟨Z₁, m₁, hZ₁, hz₁, hmem₁, hmult₁, hkey₁⟩ :=
    neg_re_logDeriv_le hR0 hRR₀ hM₁ (analyticOnNhd_LFunction_ball χ hne₁) hf₁c (fun w hw => by
      rw [hM₁def, div_mul_cancel₀ _ hpos₁.ne']; exact (hΦ1 w hw).le)
  have hρmem : ((β : ℂ) + (γ : ℂ) * I) ∈ Z₁ := by
    refine hmem₁ _ ?_ hzero
    have hdiff : ((β : ℂ) + (γ : ℂ) * I) - c₁ = (((β - σ : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hleft₁ : ∀ ρ ∈ Z₁, ρ.re ≤ c₁.re := by
    intro ρ hρ
    by_contra hcon
    rw [not_le, hc₁re] at hcon
    have hρball : ρ ∈ ball c₁ R₀ := by
      rw [mem_ball, dist_eq_norm]; have := hZ₁ ρ hρ; linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inr (hne₁ ρ hρball))
      (by linarith) (hz₁ ρ hρ)
  have hkey1 := hkey₁ c₁ (by rw [sub_self, norm_zero]; positivity) hf₁c hleft₁
    {(β : ℂ) + (γ : ℂ) * I} (Finset.singleton_subset_iff.mpr hρmem)
  have hsum₁ : ∑ ρ ∈ ({(β : ℂ) + (γ : ℂ) * I} : Finset ℂ), (m₁ ρ : ℝ) * ((c₁ - ρ)⁻¹).re =
      (m₁ ((β : ℂ) + (γ : ℂ) * I) : ℝ) * (1 / (σ - β)) := by
    rw [Finset.sum_singleton]
    congr 1
    have hdiff : c₁ - ((β : ℂ) + (γ : ℂ) * I) = (((σ - β : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hsum₁] at hkey1
  have hone : (1 : ℝ) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * I) : ℝ) := by exact_mod_cast hmult₁ _ hρmem
  -- Landau at height `2γ`, retaining nothing
  obtain ⟨Z₂, m₂, hZ₂, hz₂, _, _, hkey₂⟩ :=
    neg_re_logDeriv_le hR0 hRR₀ hM₂ (analyticOnNhd_LFunction_ball (χ ^ 2) hne₂) hf₂c
      (fun w hw => by rw [hM₂def, div_mul_cancel₀ _ hpos₂.ne']; exact (hΦ2 w hw).le)
  have hleft₂ : ∀ ρ ∈ Z₂, ρ.re ≤ c₂.re := by
    intro ρ hρ
    by_contra hcon
    rw [not_le, hc₂re] at hcon
    have hρball : ρ ∈ ball c₂ R₀ := by
      rw [mem_ball, dist_eq_norm]; have := hZ₂ ρ hρ; linarith
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re (χ ^ 2) (Or.inr (hne₂ ρ hρball))
      (by linarith) (hz₂ ρ hρ)
  have hkey2 := hkey₂ c₂ (by rw [sub_self, norm_zero]; positivity) hf₂c hleft₂ ∅
    (Finset.empty_subset _)
  rw [Finset.sum_empty, sub_zero] at hkey2
  -- three-four-one and the pole
  have h341 := three_four_one_logDeriv χ hσ1 γ
  rw [re_LSeries_twist_vonMangoldt_eq χ (by rw [← hc₁def, hc₁re]; exact hσ1),
    re_LSeries_twist_vonMangoldt_eq (χ ^ 2) (by rw [← hc₂def, hc₂re]; exact hσ1),
    ← hc₁def, ← hc₂def] at h341
  have hpole : (LSeries (↗(1 : DirichletCharacter ℂ q) * ↗Λ) (σ : ℂ)).re ≤ 1 / dl + A := by
    have h1 := re_LSeries_trivChar_vonMangoldt_le (q := q) hσ1
    have h2 := hA σ hσ1 hσ2
    rw [hσd] at h2
    linarith
  -- assembling
  set X : ℝ := Real.log Φ + Real.log Z with hXdef
  have hlogZ : Real.log Z = Real.log (1 + 1 / dl) := by rw [hZdef]
  have hk1 : -(logDeriv (DirichletCharacter.LFunction χ) c₁).re ≤ 16 * X / R - 1 / (σ - β) := by
    have hmono : 16 * Real.log M₁ / R ≤ 16 * X / R :=
      div_le_div_of_nonneg_right (by linarith) hR0.le
    have hpos : (0 : ℝ) < 1 / (σ - β) := by positivity
    nlinarith [hkey1, hone, hpos, hmono]
  have hk2 : -(logDeriv (DirichletCharacter.LFunction (χ ^ 2)) c₂).re ≤ 16 * X / R := by
    have hmono : 16 * Real.log M₂ / R ≤ 16 * X / R :=
      div_le_div_of_nonneg_right (by linarith) hR0.le
    linarith
  have hdiv : 4 / (1 + dl - β) = 4 * (1 / (σ - β)) := by rw [hσdef]; ring
  have hrw : (80 : ℝ) / R * (Real.log Φ + Real.log (1 + 1 / dl)) = 5 * (16 * X / R) := by
    rw [hXdef, hlogZ]; field_simp; ring
  have hd3 : (3 : ℝ) / dl = 3 * (1 / dl) := by ring
  rw [hdiv, hrw, hd3]
  set Y : ℝ := 16 * X / R with hYdef
  clear_value Y
  set d : ℝ := 1 / dl with hddef
  clear_value d
  set sb : ℝ := 1 / (σ - β) with hsbdef
  clear_value sb
  linarith only [h341, hpole, hk1, hk2]

end

end GaloisForLFunctions.MatomakiRadziwill
