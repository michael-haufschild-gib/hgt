import GaloisForLFunctions.ShortIntervalPrimesInProgressions.LittlewoodGrowth
import GaloisForLFunctions.RHTower.DirichletLThreeFourOne
import GaloisForLFunctions.RHTower.Sieve.LandauRealPart
import GaloisForLFunctions.RHTower.Sieve.ZetaLittlewoodRegion
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound
import GaloisForLFunctions.HTGeometry.PositiveEulerProductBudget

/-!
# Littlewood's zero-free region for Dirichlet `L`-functions

For every modulus `q` there are `c > 0` and `T₁` such that every zero `β + iγ` of `L(s, χ)`,
`χ ≠ 1` modulo `q`, with `|γ| ≥ T₁` has

`β ≤ 1 − c · log log |γ| / log |γ|`        (`exists_littlewood_zero_free_region_character`).

The proof is de la Vallée Poussin's argument with Landau's lemma at the radius of Littlewood's
growth region.  At `σ = 1 + δ` the `3-4-1` inequality for `χ₀, χ, χ²`, the pole bound
`Re(−L₀'/L₀)(σ) ≤ 1/δ` and Landau's lemma on discs of radius `R ≍ (log L)²/L` (`L = log γ`) give
`4/(1 + δ − β) ≤ 3/δ + 80 X/R` with `X = log Φ + log(1 + 1/δ) ≍ log L`
(`dlvp_inequality_character`).  The growth bound `Φ` is `(3 + 4888q)(2L)³` for the nonprincipal
characters (`norm_LFunction_le_littlewood`) and `2^q((L + 3)^{34} + 6)` for the principal one,
from the wide band of `ζ`.  The centre values satisfy `|L(1 + δ + iτ, ψ)|⁻¹ ≤ 1 + 1/δ`
(`inv_norm_LFunction_le`).
-/

open Complex Metric Filter

namespace GaloisForLFunctions.ShortIntervalPrimesInProgressions

noncomputable section

/-- **The centre value.**  `|L(s, ψ)|⁻¹ ≤ 1 + 1/(Re s − 1)` for every character and `Re s > 1`. -/
theorem inv_norm_LFunction_le {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) : ‖DirichletCharacter.LFunction ψ s‖⁻¹ ≤ 1 + (s.re - 1)⁻¹ := by
  open scoped ArithmeticFunction.Moebius in
  have hmul := DirichletCharacter.LSeries.mul_mu_eq_one ψ hs
  rw [DirichletCharacter.LFunction_eq_LSeries ψ hs]
  have hne : LSeries (fun n => ψ n) s ≠ 0 := DirichletCharacter.LSeries_ne_zero_of_one_lt_re ψ hs
  have hinv : ‖LSeries (fun n => ψ n) s‖⁻¹
      = ‖LSeries (fun n => ψ n * (ArithmeticFunction.moebius n : ℂ)) s‖ := by
    rw [← norm_inv, inv_eq_of_mul_eq_one_right hmul]
    rfl
  rw [hinv]
  have hσ : 1 < s.re := hs
  refine (RHTower.norm_lSeries_le_of_term_bound (u := fun n : ℕ => (n : ℝ) ^ (-s.re))
    (Real.summable_nat_rpow.mpr (by linarith)) fun n => ?_).trans
    (GaloisForLFunctions.HTGeometry.tsum_nat_rpow_neg_le_one_add_inv hσ)
  rw [LSeries.norm_term_eq]
  split_ifs with hn
  · exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    rw [Real.rpow_neg hn0.le, ← one_div]
    refine div_le_div_of_nonneg_right ?_ (Real.rpow_nonneg hn0.le _)
    rw [norm_mul]
    have h1 := DirichletCharacter.norm_le_one ψ n
    have h2 : ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_intCast]
      exact_mod_cast ArithmeticFunction.abs_moebius_le_one
    calc ‖ψ n‖ * ‖(ArithmeticFunction.moebius n : ℂ)‖ ≤ 1 * 1 :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = 1 := one_mul 1

/-- The Landau constant at a centre right of the one-line. -/
theorem log_div_norm_LFunction_le {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 1 < s.re) {Φ : ℝ} (hΦ : 0 < Φ) :
    Real.log (Φ / ‖DirichletCharacter.LFunction ψ s‖)
      ≤ Real.log Φ + Real.log (1 + (s.re - 1)⁻¹) := by
  have hne : DirichletCharacter.LFunction ψ s ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr (by
      intro h; rw [h, one_re] at hs; exact lt_irrefl 1 hs)) hs.le
  have hpos : 0 < ‖DirichletCharacter.LFunction ψ s‖ := norm_pos_iff.mpr hne
  rw [div_eq_mul_inv, Real.log_mul hΦ.ne' (inv_ne_zero hpos.ne')]
  have := inv_norm_LFunction_le ψ hs
  have h1 : Real.log ‖DirichletCharacter.LFunction ψ s‖⁻¹ ≤ Real.log (1 + (s.re - 1)⁻¹) :=
    Real.log_le_log (inv_pos.mpr hpos) this
  linarith

/-- Zeros of `L(s, ψ)` lie left of the one-line (away from the pole of the principal one). -/
theorem re_lt_one_of_LFunction_eq_zero {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {ρ : ℂ}
    (hρ1 : ρ ≠ 1) (hz : DirichletCharacter.LFunction ψ ρ = 0) : ρ.re < 1 := by
  by_contra h
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr hρ1) (not_lt.mp h) hz

/-- **Landau's lemma for `L(s, ψ)` at a centre right of the one-line.** -/
theorem L_landau {q : ℕ} [NeZero q] (ψ : DirichletCharacter ℂ q) {c : ℂ} {R R₀ Φ : ℝ}
    (hR : 0 < R) (hRR₀ : R < R₀) (hne : ∀ w ∈ ball c R₀, w ≠ 1)
    (hgrow : ∀ w ∈ ball c R₀, ‖DirichletCharacter.LFunction ψ w‖ < Φ) (hcre : 1 < c.re) :
    ∃ (Z₁ : Finset ℂ) (m : ℂ → ℕ),
      (∀ w : ℂ, ‖w - c‖ ≤ R / 2 → DirichletCharacter.LFunction ψ w = 0 → w ∈ Z₁) ∧
      (∀ ρ ∈ Z₁, 1 ≤ m ρ) ∧
      ∀ S ⊆ Z₁,
        -(logDeriv (DirichletCharacter.LFunction ψ) c).re
          ≤ 16 * Real.log (Φ / ‖DirichletCharacter.LFunction ψ c‖) / R
            - ∑ ρ ∈ S, (m ρ : ℝ) * ((c - ρ)⁻¹).re := by
  have hcR₀ : c ∈ ball c R₀ := mem_ball_self (by linarith)
  have hf : AnalyticOnNhd ℂ (DirichletCharacter.LFunction ψ) (ball c R₀) := by
    have hd : DifferentiableOn ℂ (DirichletCharacter.LFunction ψ) (ball c R₀) :=
      fun w hw => (DirichletCharacter.differentiableAt_LFunction ψ w
        (Or.inl (hne w hw))).differentiableWithinAt
    exact hd.analyticOnNhd isOpen_ball
  have hc1 : c ≠ 1 := hne c hcR₀
  have hfc : DirichletCharacter.LFunction ψ c ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re ψ (Or.inr hc1) hcre.le
  have hfcpos : 0 < ‖DirichletCharacter.LFunction ψ c‖ := norm_pos_iff.mpr hfc
  set M : ℝ := Φ / ‖DirichletCharacter.LFunction ψ c‖ with hMdef
  have hM1 : 1 < M := by
    rw [hMdef, lt_div_iff₀ hfcpos, one_mul]
    exact hgrow c hcR₀
  have hbound : ∀ w ∈ ball c R₀,
      ‖DirichletCharacter.LFunction ψ w‖ ≤ M * ‖DirichletCharacter.LFunction ψ c‖ := by
    intro w hw
    rw [hMdef, div_mul_cancel₀ _ hfcpos.ne']
    exact (hgrow w hw).le
  obtain ⟨Z₁, m, hZ₁, hzero, hmem, hmult, hkey⟩ :=
    RHTower.Sieve.neg_re_logDeriv_le hR hRR₀ hM1 hf hfc hbound
  refine ⟨Z₁, m, hmem, hmult, fun S hS => ?_⟩
  have hre : ∀ ρ ∈ Z₁, ρ.re ≤ c.re := by
    intro ρ hρ
    have hρball : ρ ∈ ball c R₀ := by
      rw [mem_ball, dist_eq_norm]
      have := hZ₁ ρ hρ
      linarith
    have := re_lt_one_of_LFunction_eq_zero ψ (hne ρ hρball) (hzero ρ hρ)
    linarith
  exact hkey c (by rw [sub_self, norm_zero]; positivity) hfc hre S hS

/-- **The de la Vallée Poussin inequality for a character.**  If `L(β + iγ, χ) = 0` with
`1 + δ − β ≤ R/2`, and `|L(·, χ)| < Φ`, `|L(·, χ²)| < Φ` on the discs of radius `R₀ > R` about
`1 + δ + iγ` and `1 + δ + 2iγ`, then
`4/(1 + δ − β) ≤ 3/δ + (80/R)(log Φ + log(1 + 1/δ))`. -/
theorem dlvp_inequality_character {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    {β γ δ R R₀ Φ : ℝ} (hγ : 3 ≤ γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    (hR0 : 0 < R) (hRR₀ : R < R₀) (hR₀1 : R₀ ≤ 1) (hΦ0 : 1 ≤ Φ)
    (hΦ1 : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (γ : ℂ) * I) R₀,
      ‖DirichletCharacter.LFunction χ w‖ < Φ)
    (hΦ2 : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R₀,
      ‖DirichletCharacter.LFunction (χ ^ 2) w‖ < Φ)
    (hclose : 1 + δ - β ≤ R / 2) (hβ : β < 1 + δ)
    (hzero : DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * I) = 0) :
    4 / (1 + δ - β) ≤ 3 / δ + 80 / R * (Real.log Φ + Real.log (1 + δ⁻¹)) := by
  set σ : ℝ := 1 + δ with hσdef
  have hσ1 : 1 < σ := by rw [hσdef]; linarith
  have hσ2 : σ ≤ 2 := by rw [hσdef]; linarith
  have hsb : 0 < σ - β := by linarith
  have hγ0 : (0 : ℝ) < γ := by linarith
  set c₁ : ℂ := (σ : ℂ) + (γ : ℂ) * I with hc₁def
  set c₂ : ℂ := (σ : ℂ) + ((2 * γ : ℝ) : ℂ) * I with hc₂def
  have hc₁re : c₁.re = σ := by simp [hc₁def]
  have hc₂re : c₂.re = σ := by simp [hc₂def]
  have hσδ : σ - 1 = δ := by rw [hσdef]; ring
  -- the discs avoid the pole
  have hne : ∀ (c : ℂ), 2 ≤ c.im → ∀ w ∈ ball c R₀, w ≠ 1 := by
    intro c hc w hw hw1
    rw [hw1, mem_ball, dist_eq_norm] at hw
    have h1 := Complex.abs_im_le_norm ((1 : ℂ) - c)
    rw [sub_im, one_im, zero_sub, abs_neg, abs_of_pos (by linarith)] at h1
    linarith
  have hc₁im : 2 ≤ c₁.im := by simp [hc₁def]; linarith
  have hc₂im : 2 ≤ c₂.im := by simp [hc₂def]; linarith
  -- Landau at height `γ`, retaining the zero
  obtain ⟨Z₁, m₁, hmem₁, hmult₁, hkey₁⟩ :=
    L_landau χ hR0 hRR₀ (hne c₁ hc₁im) hΦ1 (by rw [hc₁re]; exact hσ1)
  have hρmem : ((β : ℂ) + (γ : ℂ) * I) ∈ Z₁ := by
    refine hmem₁ _ ?_ hzero
    have hdiff : ((β : ℂ) + (γ : ℂ) * I) - c₁ = (((β - σ : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
    linarith
  have hkeyone := hkey₁ {(β : ℂ) + (γ : ℂ) * I} (Finset.singleton_subset_iff.mpr hρmem)
  rw [Finset.sum_singleton] at hkeyone
  have hinvre : ((c₁ - ((β : ℂ) + (γ : ℂ) * I))⁻¹).re = 1 / (σ - β) := by
    have hdiff : c₁ - ((β : ℂ) + (γ : ℂ) * I) = (((σ - β : ℝ)) : ℂ) := by
      rw [hc₁def]; push_cast; ring
    rw [hdiff, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [hinvre] at hkeyone
  have hone : (1 : ℝ) ≤ (m₁ ((β : ℂ) + (γ : ℂ) * I) : ℝ) := by exact_mod_cast hmult₁ _ hρmem
  -- Landau at height `2γ`, retaining nothing
  obtain ⟨Z₂, m₂, _, _, hkey₂⟩ :=
    L_landau (χ ^ 2) hR0 hRR₀ (hne c₂ hc₂im) hΦ2 (by rw [hc₂re]; exact hσ1)
  have hkeytwo := hkey₂ ∅ (Finset.empty_subset _)
  rw [Finset.sum_empty, sub_zero] at hkeytwo
  -- the `3-4-1` inequality and the pole
  have h341 := RHTower.three_four_one_logDeriv χ hσ1 γ
  have hc₂eq : (σ : ℂ) + 2 * (γ : ℂ) * I = c₂ := by rw [hc₂def]; push_cast; ring
  rw [hc₂eq] at h341
  have hpole := RHTower.neg_re_logDeriv_trivChar_real_le (q := q) hσ1 hσ2
  rw [hσδ] at hpole
  -- the Landau constants
  set X : ℝ := Real.log Φ + Real.log (1 + δ⁻¹) with hXdef
  have hΦpos : 0 < Φ := by linarith
  have hM₁ : Real.log (Φ / ‖DirichletCharacter.LFunction χ c₁‖) ≤ X := by
    have := log_div_norm_LFunction_le χ (s := c₁) (by rw [hc₁re]; exact hσ1) hΦpos
    rwa [hc₁re, hσδ] at this
  have hM₂ : Real.log (Φ / ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖) ≤ X := by
    have := log_div_norm_LFunction_le (χ ^ 2) (s := c₂) (by rw [hc₂re]; exact hσ1) hΦpos
    rwa [hc₂re, hσδ] at this
  have hk1 : -(logDeriv (DirichletCharacter.LFunction χ) c₁).re ≤ 16 * X / R - 1 / (σ - β) := by
    have hmono : 16 * Real.log (Φ / ‖DirichletCharacter.LFunction χ c₁‖) / R ≤ 16 * X / R :=
      div_le_div_of_nonneg_right (by linarith [hM₁]) hR0.le
    have hpos : (0 : ℝ) < 1 / (σ - β) := by positivity
    nlinarith [hkeyone, hone, hpos]
  have hk2 : -(logDeriv (DirichletCharacter.LFunction (χ ^ 2)) c₂).re ≤ 16 * X / R := by
    have hmono : 16 * Real.log (Φ / ‖DirichletCharacter.LFunction (χ ^ 2) c₂‖) / R
        ≤ 16 * X / R := div_le_div_of_nonneg_right (by linarith [hM₂]) hR0.le
    linarith
  have hneg1 : (-logDeriv (DirichletCharacter.LFunction χ) c₁).re
      = -(logDeriv (DirichletCharacter.LFunction χ) c₁).re := by simp
  have hneg2 : (-logDeriv (DirichletCharacter.LFunction (χ ^ 2)) c₂).re
      = -(logDeriv (DirichletCharacter.LFunction (χ ^ 2)) c₂).re := by simp
  have hc₁eq : (σ : ℂ) + (γ : ℂ) * I = c₁ := rfl
  rw [hc₁eq, hneg1, hneg2] at h341
  have hrw : (80 : ℝ) / R * X = 5 * (16 * X / R) := by field_simp; ring
  have hd3 : (3 : ℝ) / δ = 3 * (1 / δ) := by ring
  have hdiv : 4 / (1 + δ - β) = 4 * (1 / (σ - β)) := by rw [hσdef]; ring
  rw [hdiv, hrw, hd3]
  linarith

/-! ### The region -/

/-- On the band `γ − 1 ≤ y ≤ 3γ` Littlewood's width is at least `(log L)²/(8L)`, `L = log γ`. -/
theorem litEta_ge_of_band {γ y : ℝ} (hγ : 4 ≤ γ) (hL : 2 * Real.log 3 ≤ Real.log γ)
    (hℓ : 2 * Real.log 2 ≤ Real.log (Real.log γ)) (hy1 : γ - 1 ≤ y) (hy2 : y ≤ 3 * γ) :
    Real.log (Real.log γ) ^ 2 / (8 * Real.log γ) ≤ litEta y := by
  set L := Real.log γ with hLdef
  set ℓ := Real.log L with hℓdef
  have hγ0 : 0 < γ := by linarith
  have hy0 : 0 < y := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hl2' : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hL0 : 0 < L := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  -- `L/2 ≤ log y ≤ 2L`
  have hup : Real.log y ≤ 2 * L := by
    have := Real.log_le_log hy0 hy2
    rw [Real.log_mul (by norm_num) hγ0.ne'] at this
    linarith
  have hlow : L / 2 ≤ Real.log y := by
    have h1 : γ / 2 ≤ y := by linarith
    have := Real.log_le_log (by positivity) h1
    rw [Real.log_div hγ0.ne' (by norm_num)] at this
    linarith
  have hlogy0 : 0 < Real.log y := by linarith
  have hll : ℓ / 2 ≤ Real.log (Real.log y) := by
    have := Real.log_le_log (by positivity) hlow
    rw [Real.log_div hL0.ne' (by norm_num)] at this
    linarith
  unfold litEta
  rw [div_le_div_iff₀ (by positivity) hlogy0]
  have hsq : ℓ ^ 2 / 4 ≤ Real.log (Real.log y) ^ 2 := by nlinarith
  nlinarith

/-- **The growth on the Landau discs, nonprincipal characters.** -/
theorem norm_LFunction_le_on_band {q : ℕ} [NeZero q] {T₀ : ℝ}
    (hgrowth : ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ σ t : ℝ, T₀ ≤ |t| →
      1 - litEta |t| ≤ σ → σ ≤ 2 →
      ‖DirichletCharacter.LFunction χ ((σ : ℂ) + (t : ℂ) * I)‖
        ≤ (3 + 4888 * q) * Real.log |t| ^ 3)
    {ψ : DirichletCharacter ℂ q} (hψ : ψ ≠ 1) {γ : ℝ} (hγ : 4 ≤ γ) (hγT : T₀ + 1 ≤ γ)
    (hL : 2 * Real.log 3 ≤ Real.log γ) (hℓ : 2 * Real.log 2 ≤ Real.log (Real.log γ))
    {w : ℂ} (him1 : γ - 1 ≤ w.im) (him2 : w.im ≤ 3 * γ)
    (hre1 : 1 - Real.log (Real.log γ) ^ 2 / (8 * Real.log γ) ≤ w.re) (hre2 : w.re ≤ 2) :
    ‖DirichletCharacter.LFunction ψ w‖ ≤ 8 * (3 + 4888 * q) * Real.log γ ^ 3 := by
  have hγ0 : 0 < γ := by linarith
  have hy0 : 0 < w.im := by linarith
  have habs : |w.im| = w.im := abs_of_pos hy0
  have hη := litEta_ge_of_band hγ hL hℓ him1 him2
  have hw : w = ((w.re : ℝ) : ℂ) + ((w.im : ℝ) : ℂ) * I := (Complex.re_add_im w).symm
  have h := hgrowth ψ hψ w.re w.im (by rw [habs]; linarith) (by rw [habs]; linarith) hre2
  rw [← hw, habs] at h
  refine h.trans ?_
  have hl3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hlog : Real.log w.im ≤ 2 * Real.log γ := by
    have := Real.log_le_log hy0 him2
    rw [Real.log_mul (by norm_num) hγ0.ne'] at this
    linarith
  have hlog0 : 0 ≤ Real.log w.im := Real.log_nonneg (by linarith)
  have hC : (0 : ℝ) ≤ 3 + 4888 * q := by positivity
  calc (3 + 4888 * (q : ℝ)) * Real.log w.im ^ 3 ≤ (3 + 4888 * q) * (2 * Real.log γ) ^ 3 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlog0 hlog 3) hC
    _ = 8 * (3 + 4888 * q) * Real.log γ ^ 3 := by ring

/-- **The growth on the Landau discs, principal character.**  `L(w, χ₀) = ∏_{p ∣ q}(1 − p^{−w}) ζ(w)`
and the wide band of `ζ`. -/
theorem norm_LFunction_one_le_on_band {q : ℕ} [NeZero q] {γ δ : ℝ} (hγ : 16 * Real.pi + 1 ≤ γ)
    (hL : (10 : ℝ) ^ (16 : ℕ) + 1 ≤ RHTower.Sieve.wideScale γ) (hδ0 : 0 < δ) (hδ : δ ≤ 1 / 16)
    {w : ℂ} (hre1 : 1 - RHTower.Sieve.wideEta γ < w.re) (hre2 : w.re ≤ 2)
    (him1 : γ - 1 ≤ w.im) (him2 : w.im ≤ 5 * γ) :
    ‖DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w‖
      ≤ (2 : ℝ) ^ q.primeFactors.card * ((RHTower.Sieve.wideScale γ + 3) ^ (34 : ℕ) + 6) := by
  have hw1 : w ≠ 1 := by
    intro h; rw [h, one_im] at him1; linarith [Real.pi_pos]
  have hre0 : 0 ≤ w.re := by
    have := RHTower.Sieve.wideEta_le (t := γ) (by linarith)
    have h2 : RHTower.Sieve.wideEta γ ≤ 1 := by
      unfold RHTower.Sieve.wideEta
      rw [div_le_one (by positivity)]
      have : (1 : ℝ) ≤ 2 ^ RHTower.Sieve.wideOrder γ := one_le_pow₀ (by norm_num)
      linarith
    linarith
  rw [show DirichletCharacter.LFunction (1 : DirichletCharacter ℂ q) w
      = DirichletCharacter.LFunctionTrivChar q w from rfl,
    DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hw1, norm_mul]
  have hζ := RHTower.Sieve.wide_disc_growth hγ hL hδ0 hδ hre1 hre2 him1 him2
  have hprod : ‖∏ p ∈ q.primeFactors, (1 - (p : ℂ) ^ (-w))‖ ≤ (2 : ℝ) ^ q.primeFactors.card := by
    rw [norm_prod]
    calc ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-w)‖ ≤ ∏ _p ∈ q.primeFactors, (2 : ℝ) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun p hp => ?_
          have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
          have hpw : ‖(p : ℂ) ^ (-w)‖ ≤ 1 := by
            rw [Complex.norm_natCast_cpow_of_pos (by omega), neg_re]
            exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp1) (by linarith)
          calc ‖1 - (p : ℂ) ^ (-w)‖ ≤ ‖(1 : ℂ)‖ + ‖(p : ℂ) ^ (-w)‖ := norm_sub_le _ _
            _ ≤ 2 := by rw [norm_one]; linarith
      _ = (2 : ℝ) ^ q.primeFactors.card := Finset.prod_const 2
  exact mul_le_mul hprod hζ.le (norm_nonneg _) (by positivity)

/-- The conditions on `L = log γ` used by the region, eventually. -/
theorem eventually_region_conditions (C : ℝ) :
    ∀ᶠ L : ℝ in atTop, (10 : ℝ) ^ (17 : ℕ) ≤ L ∧ C + 34 ≤ Real.log L ∧
      Real.log L ^ 2 ≤ L := by
  have ho := (Real.isLittleO_pow_log_id_atTop (n := 2)).bound (c := 1) one_pos
  filter_upwards [eventually_ge_atTop ((10 : ℝ) ^ (17 : ℕ)),
    Real.tendsto_log_atTop.eventually_ge_atTop (C + 34), ho, eventually_ge_atTop 1]
    with L h1 h2 h3 h4
  refine ⟨h1, h2, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _), id,
    abs_of_nonneg (by linarith)] at h3
  linarith

/-- **Littlewood's region at positive heights.** -/
theorem exists_littlewood_region_pos (q : ℕ) [NeZero q] :
    ∃ T₁ : ℝ, 3 ≤ T₁ ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β γ : ℝ, T₁ ≤ γ →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * I) = 0 →
      β ≤ 1 - Real.log (Real.log γ) / (10 ^ 7 * Real.log γ) := by
  obtain ⟨T₀, hT₀, hgrowth⟩ := norm_LFunction_le_littlewood q
  set C₁ : ℝ := 3 + 4888 * q with hC₁
  set C₂ : ℝ := (2 : ℝ) ^ q.primeFactors.card * 7 + 8 * C₁ + 1 with hC₂
  have hC₁0 : 0 < C₁ := by positivity
  have hC₂1 : 1 ≤ C₂ := by rw [hC₂]; have := pow_pos (two_pos (α := ℝ)) q.primeFactors.card; linarith
  have hev : ∀ᶠ γ : ℝ in atTop,
      ((10 : ℝ) ^ (17 : ℕ) ≤ Real.log γ ∧ Real.log C₂ + 34 ≤ Real.log (Real.log γ) ∧
        Real.log (Real.log γ) ^ 2 ≤ Real.log γ) ∧ T₀ + 16 * Real.pi + 4 ≤ γ :=
    (Real.tendsto_log_atTop.eventually (eventually_region_conditions (Real.log C₂))).and
      (eventually_ge_atTop _)
  obtain ⟨T₁, hT₁⟩ := eventually_atTop.mp hev
  refine ⟨max T₁ 3, le_max_right _ _, ?_⟩
  intro χ hχ β γ hγT hzero
  obtain ⟨⟨hL17, hℓC, hℓL⟩, hγbig⟩ := hT₁ γ (le_of_max_le_left hγT)
  set L := Real.log γ with hLdef
  set ℓ := Real.log L with hℓdef
  have hπ := Real.pi_pos
  have hπ3 := Real.pi_gt_three
  have hγ4 : 4 ≤ γ := by linarith
  have hγ0 : 0 < γ := by linarith
  have hL0 : 0 < L := by linarith [show (0 : ℝ) < 10 ^ (17 : ℕ) by positivity]
  have hlogC₂ : 0 ≤ Real.log C₂ := Real.log_nonneg hC₂1
  have hℓ34 : 34 ≤ ℓ := by linarith
  have hℓ0 : 0 < ℓ := by linarith
  have hl2 := Real.log_two_lt_d9
  have hl3 : Real.log 3 < 2 := by
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 3 by norm_num); linarith
  -- the zero lies left of the one-line
  have hβ1 : β < 1 := by
    have hρ1 : (β : ℂ) + (γ : ℂ) * I ≠ 1 := by
      intro h
      have := congrArg Complex.im h
      simp at this
      linarith
    have := re_lt_one_of_LFunction_eq_zero χ hρ1 hzero
    simpa using this
  by_contra hcon
  push Not at hcon
  -- the parameters
  set R₀ : ℝ := ℓ ^ 2 / (8 * L) with hR₀
  set R : ℝ := ℓ ^ 2 / (16 * L) with hR
  set δ : ℝ := ℓ / (10 ^ 6 * L) with hδdef
  set Φ : ℝ := (2 : ℝ) ^ q.primeFactors.card * ((L + 3) ^ (34 : ℕ) + 6) + 8 * C₁ * L ^ 3 + 1
    with hΦdef
  have hR0 : 0 < R := by positivity
  have hRR₀ : R < R₀ := by
    rw [hR, hR₀]; apply div_lt_div_of_pos_left (by positivity) (by positivity); linarith
  have hR₀1 : R₀ ≤ 1 / 8 := by
    rw [hR₀, div_le_iff₀ (by positivity)]; linarith
  have hδ0 : 0 < δ := by positivity
  have hδ16 : δ ≤ 1 / 16 := by
    rw [hδdef, div_le_iff₀ (by positivity)]
    nlinarith
  have hδR₀ : δ ≤ R₀ := by
    rw [hδdef, hR₀, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hΦ1 : 1 ≤ Φ := by
    have : 0 ≤ (2 : ℝ) ^ q.primeFactors.card * ((L + 3) ^ (34 : ℕ) + 6) := by positivity
    have : 0 ≤ 8 * C₁ * L ^ 3 := by positivity
    linarith
  -- the band conditions
  have hLlog3 : 2 * Real.log 3 ≤ L := by linarith [show (4 : ℝ) ≤ 10 ^ (17 : ℕ) by norm_num]
  have hℓlog2 : 2 * Real.log 2 ≤ ℓ := by linarith
  have hγT₀ : T₀ + 1 ≤ γ := by linarith
  have hball : ∀ τ : ℝ, ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (τ : ℂ) * I) R₀,
      τ - R₀ < w.im ∧ w.im < τ + R₀ ∧ 1 - R₀ < w.re ∧ w.re ≤ 2 := by
    intro τ w hw
    rw [mem_ball, dist_eq_norm] at hw
    have him := Complex.abs_im_le_norm (w - (((1 + δ : ℝ) : ℂ) + (τ : ℂ) * I))
    have hre := Complex.abs_re_le_norm (w - (((1 + δ : ℝ) : ℂ) + (τ : ℂ) * I))
    simp only [sub_im, add_im, ofReal_im, mul_im, ofReal_re, I_re, I_im, mul_zero, mul_one,
      zero_add, sub_re, add_re, mul_re, ofReal_re, zero_mul, sub_zero] at him hre
    have h1 := abs_lt.mp (lt_of_le_of_lt him hw)
    have h2 := abs_lt.mp (lt_of_le_of_lt hre hw)
    refine ⟨by linarith, by linarith, by linarith, by linarith⟩
  have hgrowL : ∀ ψ : DirichletCharacter ℂ q, ψ ≠ 1 → ∀ τ : ℝ, γ ≤ τ → τ ≤ 2 * γ →
      ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + (τ : ℂ) * I) R₀,
        ‖DirichletCharacter.LFunction ψ w‖ < Φ := by
    intro ψ hψ τ hτ1 hτ2 w hw
    obtain ⟨h1, h2, h3, h4⟩ := hball τ w hw
    have := norm_LFunction_le_on_band hgrowth hψ hγ4 hγT₀ hLlog3 hℓlog2 (w := w)
      (by linarith) (by linarith) (by rw [← hR₀]; linarith) h4
    have hpos : 0 ≤ (2 : ℝ) ^ q.primeFactors.card * ((L + 3) ^ (34 : ℕ) + 6) := by positivity
    rw [hΦdef]
    linarith
  have hΦχ := hgrowL χ hχ γ le_rfl (by linarith)
  have hΦχ2 : ∀ w ∈ ball (((1 + δ : ℝ) : ℂ) + ((2 * γ : ℝ) : ℂ) * I) R₀,
      ‖DirichletCharacter.LFunction (χ ^ 2) w‖ < Φ := by
    by_cases hsq : χ ^ 2 = 1
    · intro w hw
      obtain ⟨h1, h2, h3, h4⟩ := hball (2 * γ) w hw
      rw [hsq]
      have hws : (10 : ℝ) ^ (16 : ℕ) + 1 ≤ RHTower.Sieve.wideScale γ := by
        unfold RHTower.Sieve.wideScale
        rw [Real.log_div hγ0.ne' (by positivity)]
        have : Real.log (2 * Real.pi) < 2 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
          linarith [Real.pi_lt_d2]
        have : (10 : ℝ) ^ (16 : ℕ) + 3 ≤ 10 ^ (17 : ℕ) := by norm_num
        linarith
      have hwsL : RHTower.Sieve.wideScale γ ≤ L := by
        unfold RHTower.Sieve.wideScale
        exact Real.log_le_log (by positivity) (div_le_self hγ0.le (by linarith))
      have hwsL2 : L / 2 ≤ RHTower.Sieve.wideScale γ := by
        unfold RHTower.Sieve.wideScale
        rw [Real.log_div hγ0.ne' (by positivity)]
        have : Real.log (2 * Real.pi) < 2 := by
          have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 * Real.pi by positivity)
          linarith [Real.pi_lt_d2]
        linarith [show (4 : ℝ) ≤ 10 ^ (17 : ℕ) by norm_num]
      have hwideEta : R₀ ≤ RHTower.Sieve.wideEta γ := by
        refine le_trans ?_ (RHTower.Sieve.wideEta_ge (by linarith))
        have hwpos : 0 < RHTower.Sieve.wideScale γ := by linarith
        have hlogws : ℓ / 2 ≤ Real.log (RHTower.Sieve.wideScale γ) := by
          have := Real.log_le_log (by positivity) hwsL2
          rw [Real.log_div hL0.ne' (by norm_num)] at this
          linarith
        rw [hR₀, div_le_div_iff₀ (by positivity) hwpos]
        have hsq' : ℓ ^ 2 / 4 ≤ Real.log (RHTower.Sieve.wideScale γ) ^ (2 : ℕ) := by nlinarith
        nlinarith
      have hb := norm_LFunction_one_le_on_band (q := q) (by linarith) hws hδ0 hδ16 (w := w)
        (by linarith) h4 (by linarith) (by linarith)
      have hmono : (RHTower.Sieve.wideScale γ + 3) ^ (34 : ℕ) ≤ (L + 3) ^ (34 : ℕ) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card := by positivity
      have : (2 : ℝ) ^ q.primeFactors.card * ((RHTower.Sieve.wideScale γ + 3) ^ (34 : ℕ) + 6)
          ≤ (2 : ℝ) ^ q.primeFactors.card * ((L + 3) ^ (34 : ℕ) + 6) :=
        mul_le_mul_of_nonneg_left (by linarith) h2pos.le
      have : 0 ≤ 8 * C₁ * L ^ 3 := by positivity
      rw [hΦdef]
      linarith
    · intro w hw
      have h := hgrowL (χ ^ 2) hsq (2 * γ) (by linarith) le_rfl w hw
      exact h
  -- the inequality
  have hδ' : 1 - β < ℓ / (10 ^ 7 * L) := by linarith
  have hsum : 1 + δ - β < 11 * ℓ / (10 ^ 7 * L) := by
    have : δ + ℓ / (10 ^ 7 * L) = 11 * ℓ / (10 ^ 7 * L) := by
      rw [hδdef]; field_simp; ring
    linarith
  have hclose : 1 + δ - β ≤ R / 2 := by
    refine hsum.le.trans ?_
    rw [hR, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hD := dlvp_inequality_character (χ := χ) (by linarith) hδ0 hδ16 hR0 hRR₀ (by linarith)
    hΦ1 hΦχ hΦχ2 hclose (by linarith) hzero
  -- bounding the right side by `3047360 L/ℓ`
  have hlogΦ : Real.log Φ ≤ 35 * ℓ := by
    have hL3 : 3 ≤ L := by linarith [show (3 : ℝ) ≤ 10 ^ (17 : ℕ) by norm_num]
    have hpow1 : 1 ≤ (L + 3) ^ (34 : ℕ) := one_le_pow₀ (by linarith)
    have hpow3 : L ^ 3 ≤ (L + 3) ^ (34 : ℕ) := by
      calc L ^ 3 ≤ (L + 3) ^ 3 := pow_le_pow_left₀ hL0.le (by linarith) 3
        _ ≤ (L + 3) ^ (34 : ℕ) := pow_le_pow_right₀ (by linarith) (by norm_num)
    have hΦle : Φ ≤ C₂ * (L + 3) ^ (34 : ℕ) := by
      rw [hΦdef, hC₂]
      have h2pos : (0 : ℝ) < (2 : ℝ) ^ q.primeFactors.card := by positivity
      nlinarith
    have hL3' : L + 3 ≤ 2 * L := by linarith
    calc Real.log Φ ≤ Real.log (C₂ * (L + 3) ^ (34 : ℕ)) :=
          Real.log_le_log (by linarith) hΦle
      _ = Real.log C₂ + 34 * Real.log (L + 3) := by
          rw [Real.log_mul (by linarith) (by positivity), Real.log_pow]; push_cast; ring
      _ ≤ Real.log C₂ + 34 * (Real.log 2 + ℓ) := by
          have := Real.log_le_log (by linarith) hL3'
          rw [Real.log_mul (by norm_num) hL0.ne'] at this
          linarith
      _ ≤ 35 * ℓ := by linarith
  have hlogδ : Real.log (1 + δ⁻¹) ≤ 2 * ℓ := by
    have hδinv : δ⁻¹ = 10 ^ 6 * L / ℓ := by rw [hδdef, inv_div]
    have h1 : 1 + δ⁻¹ ≤ 2 * 10 ^ 6 * L := by
      rw [hδinv]
      have : 10 ^ 6 * L / ℓ ≤ 10 ^ 6 * L := div_le_self (by positivity) (by linarith)
      linarith
    calc Real.log (1 + δ⁻¹) ≤ Real.log (2 * 10 ^ 6 * L) :=
          Real.log_le_log (by positivity) h1
      _ = Real.log (2 * 10 ^ 6) + ℓ := by rw [Real.log_mul (by norm_num) hL0.ne']
      _ ≤ 2 * ℓ := by
          have : Real.log (2 * 10 ^ 6) < 15 := by
            rw [Real.log_lt_iff_lt_exp (by norm_num)]
            have h := Real.add_one_le_exp (15 : ℝ)
            have h2 : Real.exp 15 = Real.exp 5 ^ 3 := by rw [← Real.exp_nat_mul]; norm_num
            have h3 : (148 : ℝ) < Real.exp 5 := by
              have := Real.exp_one_gt_d9
              have h5 : Real.exp 5 = Real.exp 1 ^ 5 := by rw [← Real.exp_nat_mul]; norm_num
              rw [h5]
              nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
                this.le 5]
            rw [h2]
            nlinarith
          linarith
  have hRHS : 3 / δ + 80 / R * (Real.log Φ + Real.log (1 + δ⁻¹)) ≤ 3047360 * L / ℓ := by
    have h1 : 3 / δ = 3 * 10 ^ 6 * L / ℓ := by rw [hδdef]; field_simp
    have h2 : 80 / R = 1280 * L / ℓ ^ 2 := by rw [hR]; field_simp; ring
    have h3 : 80 / R * (Real.log Φ + Real.log (1 + δ⁻¹)) ≤ 1280 * L / ℓ ^ 2 * (37 * ℓ) :=
      by rw [h2]; exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h4 : 1280 * L / ℓ ^ 2 * (37 * ℓ) = 47360 * L / ℓ := by field_simp; ring
    rw [h1]
    have h5 : 3 * 10 ^ 6 * L / ℓ + 47360 * L / ℓ = 3047360 * L / ℓ := by ring
    linarith
  have hLHS : 4 * 10 ^ 7 * L / (11 * ℓ) < 4 / (1 + δ - β) := by
    have hpos : 0 < 1 + δ - β := by linarith
    rw [div_lt_div_iff₀ (by positivity) hpos]
    have := mul_lt_mul_of_pos_left hsum (show (0 : ℝ) < 4 * (10 ^ 7 * L) by positivity)
    have h' : 4 * (10 ^ 7 * L) * (11 * ℓ / (10 ^ 7 * L)) = 4 * (11 * ℓ) := by
      field_simp
    nlinarith
  have hcmp : 3047360 * L / ℓ < 4 * 10 ^ 7 * L / (11 * ℓ) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- **Littlewood's zero-free region for Dirichlet `L`-functions.**  For every modulus `q` there is
`T₁` such that every zero `β + iγ` of `L(s, χ)`, `χ ≠ 1` modulo `q`, with `|γ| ≥ T₁` has
`β ≤ 1 − log log |γ| / (10⁷ log |γ|)`. -/
theorem exists_littlewood_zero_free_region_character (q : ℕ) [NeZero q] :
    ∃ T₁ : ℝ, 3 ≤ T₁ ∧ ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ β γ : ℝ, T₁ ≤ |γ| →
      DirichletCharacter.LFunction χ ((β : ℂ) + (γ : ℂ) * I) = 0 →
      β ≤ 1 - Real.log (Real.log |γ|) / (10 ^ 7 * Real.log |γ|) := by
  obtain ⟨T₁, hT₁, hpos⟩ := exists_littlewood_region_pos q
  refine ⟨T₁, hT₁, fun χ hχ β γ hγ hzero => ?_⟩
  rcases le_or_gt 0 γ with h0 | h0
  · rw [abs_of_nonneg h0] at hγ ⊢
    exact hpos χ hχ β γ hγ hzero
  · rw [abs_of_neg h0] at hγ ⊢
    have hinv : χ⁻¹ ≠ 1 := inv_ne_one.mpr hχ
    have h := RHTower.LFunction_inv_conj χ hχ ((β : ℂ) + (γ : ℂ) * I)
    rw [hzero, map_zero] at h
    have hconj : (starRingEnd ℂ) ((β : ℂ) + (γ : ℂ) * I) = (β : ℂ) + ((-γ : ℝ) : ℂ) * I := by
      apply Complex.ext <;> simp
    rw [hconj] at h
    exact hpos χ⁻¹ hinv β (-γ) hγ h

end

end GaloisForLFunctions.ShortIntervalPrimesInProgressions
