import GaloisForLFunctions.KodairaParshinAbc.TheLegendreInvariantOfTheModularLambdaFunction
import GaloisForLFunctions.RHTower.ArakelovModularLambdaFE

/-!
# The Legendre invariant of the Arakelov coordinate

The Legendre invariant `J(λ) = 256 (λ² - λ + 1)³ / (λ²(λ - 1)²)` is the quotient map of the
λ-line by the anharmonic group: in characteristic zero its fibres are exactly the anharmonic
orbits.  Concretely,

  `(y² - y + 1)³ x²(x-1)² - (x² - x + 1)³ y²(y-1)²
     = -(y - x)(y - 1 + x)(xy - 1)((1-x)y - 1)((x-1)y - x)(xy - x + 1)`,

so for `x, y ∉ {0, 1}`, `J(y) = J(x)` iff `y ∈ {x, 1-x, 1/x, 1/(1-x), x/(x-1), (x-1)/x}`
(`legendreInvariant_eq_iff`).

Applied to a complex point `ρ`: the Arakelov coordinate `w_ρ = 1 - 1/ρ` of the corpus and the
functional-equation partner `1 - ρ` lie in the orbit of `ρ`, so `J(w_ρ) = J(ρ) = J(1 - ρ)`; and
`J(ρ̄) = conj J(ρ)`.  Hence `J(ρ)` is real iff `ρ̄` lies in the orbit of `ρ`, which happens exactly on
four circles (`legendreInvariant_im_eq_zero_iff`):

  `J(ρ) ∈ ℝ ⟺ ρ ∈ ℝ ∨ Re ρ = 1/2 ∨ |ρ| = 1 ∨ |ρ - 1| = 1`.

In the strip `0 < Re ρ < 1` with `|Im ρ| ≥ 1` only the critical line survives
(`legendreInvariant_real_iff_critical`), and through the corpus modular lift `λ(τ) = w_ρ` this is
the reality of the level-one modular function `J(λ(τ))` (`exists_lift_lambdaInvariant_real_iff`).
-/

noncomputable section

open Complex

namespace GaloisForLFunctions.KodairaParshinAbc

/-! ## The fibres of `J` -/

/-- **The fibre identity** of the Legendre invariant. -/
theorem legendre_fibre_identity {F : Type*} [Field F] (x y : F) :
    (y ^ 2 - y + 1) ^ 3 * (x ^ 2 * (x - 1) ^ 2) - (x ^ 2 - x + 1) ^ 3 * (y ^ 2 * (y - 1) ^ 2) =
      -((y - x) * (y - 1 + x) * (x * y - 1) * ((1 - x) * y - 1) * ((x - 1) * y - x) *
        (x * y - x + 1)) := by
  ring

/-- **The fibres of `J` are the anharmonic orbits** (characteristic zero). -/
theorem legendreInvariant_eq_iff {F : Type*} [Field F] [CharZero F] {x y : F} (hx0 : x ≠ 0)
    (hx1 : x ≠ 1) (hy0 : y ≠ 0) (hy1 : y ≠ 1) :
    legendreInvariant y = legendreInvariant x ↔
      y = x ∨ y = 1 - x ∨ y = x⁻¹ ∨ y = (1 - x)⁻¹ ∨ y = x / (x - 1) ∨ y = (x - 1) / x := by
  have hx1' : x - 1 ≠ 0 := sub_ne_zero.mpr hx1
  have hx1'' : 1 - x ≠ 0 := sub_ne_zero.mpr (Ne.symm hx1)
  have hy1' : y - 1 ≠ 0 := sub_ne_zero.mpr hy1
  constructor
  · intro h
    unfold legendreInvariant at h
    rw [div_eq_div_iff (by positivity) (by positivity)] at h
    have h256 : (256 : F) * ((y ^ 2 - y + 1) ^ 3 * (x ^ 2 * (x - 1) ^ 2) -
        (x ^ 2 - x + 1) ^ 3 * (y ^ 2 * (y - 1) ^ 2)) = 0 := by linear_combination h
    have hP := (mul_eq_zero.mp h256).resolve_left (by norm_num)
    rw [legendre_fibre_identity, neg_eq_zero] at hP
    rcases mul_eq_zero.mp hP with hP | h6
    · rcases mul_eq_zero.mp hP with hP | h5
      · rcases mul_eq_zero.mp hP with hP | h4
        · rcases mul_eq_zero.mp hP with hP | h3
          · rcases mul_eq_zero.mp hP with h1 | h2
            · exact Or.inl (sub_eq_zero.mp h1)
            · exact Or.inr (Or.inl (by linear_combination h2))
          · exact Or.inr (Or.inr (Or.inl (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h3))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl
            (eq_inv_of_mul_eq_one_right (sub_eq_zero.mp h4)))))
      · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ?_))))
        rw [eq_div_iff hx1']
        linear_combination h5
    · refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ?_))))
      rw [eq_div_iff hx0]
      linear_combination h6
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · rfl
    · exact legendreInvariant_one_sub x
    · exact legendreInvariant_inv x
    · rw [legendreInvariant_inv, legendreInvariant_one_sub]
    · exact legendreInvariant_div_sub_one x
    · rw [show (x - 1) / x = (x / (x - 1))⁻¹ by rw [inv_div], legendreInvariant_inv,
        legendreInvariant_div_sub_one]

/-! ## The Arakelov coordinate and the functional equation -/

/-- `J(w_ρ) = J(ρ)`: the Arakelov coordinate lies in the anharmonic orbit of `ρ`. -/
theorem legendreInvariant_arakelovW (ρ : ℂ) :
    legendreInvariant (arakelovW ρ) = legendreInvariant ρ := by
  rw [arakelovW, legendreInvariant_one_sub, legendreInvariant_inv]

/-- `J(1 - ρ) = J(ρ)`: the Legendre invariant is invariant under the functional equation. -/
theorem legendreInvariant_sigma (ρ : ℂ) : legendreInvariant (sigma ρ) = legendreInvariant ρ := by
  rw [sigma, legendreInvariant_one_sub]

theorem legendreInvariant_conj (ρ : ℂ) :
    legendreInvariant (starRingEnd ℂ ρ) = starRingEnd ℂ (legendreInvariant ρ) := by
  unfold legendreInvariant
  simp [map_div₀, map_mul, map_pow, map_sub, map_add, map_one, map_ofNat]

/-! ## The real locus -/

theorem normSq_eq_sq_norm (ρ : ℂ) : ρ.re * ρ.re + ρ.im * ρ.im = ‖ρ‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]

theorem conj_eq_one_sub_iff (ρ : ℂ) : starRingEnd ℂ ρ = 1 - ρ ↔ ρ.re = 1 / 2 := by
  rw [Complex.ext_iff]
  simp only [conj_re, conj_im, sub_re, one_re, sub_im, one_im, zero_sub, and_true]
  constructor <;> intro h <;> linarith

theorem conj_eq_inv_iff {ρ : ℂ} (h0 : ρ ≠ 0) : starRingEnd ℂ ρ = ρ⁻¹ ↔ ‖ρ‖ = 1 := by
  have key : starRingEnd ℂ ρ = ρ⁻¹ ↔ starRingEnd ℂ ρ * ρ = 1 :=
    ⟨fun h => by rw [h, inv_mul_cancel₀ h0], eq_inv_of_mul_eq_one_left⟩
  rw [key, Complex.conj_mul']
  norm_cast
  exact pow_eq_one_iff_of_nonneg (norm_nonneg ρ) two_ne_zero

theorem conj_ne_inv_one_sub {ρ : ℂ} (h1 : ρ ≠ 1) : starRingEnd ℂ ρ ≠ (1 - ρ)⁻¹ := by
  intro h
  have h1ρ : 1 - ρ ≠ 0 := sub_ne_zero.mpr (Ne.symm h1)
  have hm : starRingEnd ℂ ρ * (1 - ρ) = 1 := by rw [h, inv_mul_cancel₀ h1ρ]
  rw [Complex.ext_iff] at hm
  simp only [mul_re, mul_im, conj_re, conj_im, sub_re, one_re, sub_im, one_im] at hm
  obtain ⟨hre, him⟩ := hm
  have hb : ρ.im = 0 := by linarith
  rw [hb] at hre
  nlinarith [sq_nonneg (ρ.re - 1 / 2)]

theorem conj_eq_div_sub_one_iff {ρ : ℂ} (h1 : ρ ≠ 1) :
    starRingEnd ℂ ρ = ρ / (ρ - 1) ↔ ‖ρ - 1‖ = 1 := by
  have hρ1 : ρ - 1 ≠ 0 := sub_ne_zero.mpr h1
  rw [eq_div_iff hρ1, Complex.ext_iff, ← pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero,
    ← normSq_eq_sq_norm]
  simp only [mul_re, mul_im, conj_re, conj_im, sub_re, one_re, sub_im, one_im, sub_zero]
  constructor
  · rintro ⟨hre, -⟩
    nlinarith
  · intro h
    exact ⟨by nlinarith, by ring⟩

theorem conj_ne_sub_one_div {ρ : ℂ} (h0 : ρ ≠ 0) : starRingEnd ℂ ρ ≠ (ρ - 1) / ρ := by
  intro h
  have hm : starRingEnd ℂ ρ * ρ = ρ - 1 := by rw [h, div_mul_cancel₀ _ h0]
  rw [Complex.ext_iff] at hm
  simp only [mul_re, mul_im, conj_re, conj_im, sub_re, one_re, sub_im, one_im, sub_zero] at hm
  obtain ⟨hre, him⟩ := hm
  have hb : ρ.im = 0 := by linarith
  rw [hb] at hre
  nlinarith [sq_nonneg (ρ.re - 1 / 2)]

/-- **The real locus of `J`**: for `ρ ∉ {0, 1}`, `J(ρ)` is real iff `ρ` is real, on the critical
line, or on one of the unit circles about `0` and `1`. -/
theorem legendreInvariant_im_eq_zero_iff {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    (legendreInvariant ρ).im = 0 ↔ ρ.im = 0 ∨ ρ.re = 1 / 2 ∨ ‖ρ‖ = 1 ∨ ‖ρ - 1‖ = 1 := by
  have hc0 : starRingEnd ℂ ρ ≠ 0 := by rwa [map_ne_zero]
  have hc1 : starRingEnd ℂ ρ ≠ 1 := by
    intro h
    apply h1
    rw [← (starRingEnd ℂ).injective.eq_iff, h, map_one]
  have hreal : (legendreInvariant ρ).im = 0 ↔
      legendreInvariant (starRingEnd ℂ ρ) = legendreInvariant ρ := by
    rw [legendreInvariant_conj, Complex.conj_eq_iff_im]
  rw [hreal, legendreInvariant_eq_iff h0 h1 hc0 hc1, Complex.conj_eq_iff_im, conj_eq_one_sub_iff,
    conj_eq_inv_iff h0, conj_eq_div_sub_one_iff h1]
  have h4 := conj_ne_inv_one_sub h1
  have h6 := conj_ne_sub_one_div h0
  tauto

/-- **In the strip away from `|Im ρ| < 1`, `J(ρ)` is real exactly on the critical line.** -/
theorem legendreInvariant_real_iff_critical {ρ : ℂ} (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (him : 1 ≤ |ρ.im|) : (legendreInvariant ρ).im = 0 ↔ ρ.re = 1 / 2 := by
  have h0 : ρ ≠ 0 := fun h => by rw [h, zero_re] at hre0; exact lt_irrefl 0 hre0
  have h1 : ρ ≠ 1 := fun h => by rw [h, one_re] at hre1; exact lt_irrefl 1 hre1
  have hb2 : 1 ≤ ρ.im ^ 2 := by nlinarith [sq_abs ρ.im, abs_nonneg ρ.im]
  rw [legendreInvariant_im_eq_zero_iff h0 h1]
  constructor
  · rintro (h | h | h | h)
    · rw [h, abs_zero] at him
      norm_num at him
    · exact h
    · have hn := normSq_eq_sq_norm ρ
      rw [h] at hn
      nlinarith
    · have hn := normSq_eq_sq_norm (ρ - 1)
      rw [h] at hn
      simp only [sub_re, one_re, sub_im, one_im, sub_zero] at hn
      nlinarith
  · intro h
    exact Or.inr (Or.inl h)

/-- **The modular lift of a point of the strip.**  The corpus lift `τ` with `λ(τ) = w_ρ` has
level-one modular invariant `J(λ(τ)) = J(ρ)`, which is real exactly on the four circles. -/
theorem exists_lift_lambdaInvariant_real_iff {ρ : ℂ} (h0 : ρ ≠ 0) (h1 : ρ ≠ 1) :
    ∃ τ : UpperHalfPlane, lambdaInvariant τ = legendreInvariant ρ ∧
      ((lambdaInvariant τ).im = 0 ↔ ρ.im = 0 ∨ ρ.re = 1 / 2 ∨ ‖ρ‖ = 1 ∨ ‖ρ - 1‖ = 1) := by
  obtain ⟨τ, hτ, -, -⟩ := exists_modularLambda_lift_FE_braid ρ h0 h1
  have hJ : lambdaInvariant τ = legendreInvariant ρ := by
    unfold lambdaInvariant
    rw [show Bottcher.modularLambda (τ : ℂ) = (Bottcher.lambdaPunct τ : ℂ) from rfl, hτ,
      legendreInvariant_arakelovW]
  exact ⟨τ, hJ, by rw [hJ]; exact legendreInvariant_im_eq_zero_iff h0 h1⟩

end GaloisForLFunctions.KodairaParshinAbc
