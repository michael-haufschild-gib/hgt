import GaloisForLFunctions.RHTower.DirichletLLogDerivativeStrip

/-!
# Reciprocal control of Dirichlet `L`-functions right of `Re s = 1`

For every character `χ` of a fixed modulus `Q`, `1/|L(σ + it, χ)| ≤ C log⁷|t|` on `1 ≤ σ ≤ 2`,
`|t| ≥ 9` (`exists_norm_inv_LFunction_le_log_pow`). Inside the logarithmic strip
`σ ≤ 1 + a/log⁹|t|` this is `norm_inv_LFunction_le_log_strip`. Beyond it, with `η = σ − 1`, the
3-4-1 product `|L(1 + η, χ₀)|³ |L(1 + η + it, χ)|⁴ |L(1 + η + 2it, χ²)| ≥ 1`, the pole bound
`|L(1 + η, χ₀)| ≤ K/η` and `|L(1 + η + 2it, χ²)| ≤ 2K log|t|` give
`|L(σ + it, χ)|⁴ ≥ η³/(2K⁴ log|t|) ≥ a³/(2K⁴ log²⁸|t|)`.

For `χ ≠ 1`, `L(·, χ)` is entire and zero-free on `Re s ≥ 1`, so `|L|` and `1/|L|` are bounded on every
box `1 ≤ Re s ≤ 2`, `|Im s| ≤ T` (`exists_norm_LFunction_le_box`).
-/

noncomputable section
open Filter Topology Complex Set

namespace RHTower

variable {Q : ℕ} [NeZero Q]

/-- **Reciprocal control right of the one-line.** For every character `χ` mod `Q` there is `C` with
`1/|L(σ + it, χ)| ≤ C log⁷|t|` for `1 ≤ σ ≤ 2`, `|t| ≥ 9`. -/
theorem exists_norm_inv_LFunction_le_log_pow (χ : DirichletCharacter ℂ Q) :
    ∃ C : ℝ, 0 < C ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 2 → 9 ≤ |t| →
      ‖(DirichletCharacter.LFunction χ (σ + t * I))⁻¹‖ ≤ C * Real.log |t| ^ (7 : ℕ) := by
  have hK1 : 1 ≤ characterLogStripConstant Q := one_le_characterLogStripConstant Q
  have hK : 0 < characterLogStripConstant Q := by linarith
  have ha : 0 < characterPerronWidth Q := characterPerronWidth_pos Q
  set K := characterLogStripConstant Q
  set a := characterPerronWidth Q
  have hc : 0 < a ^ 3 / (2 * K ^ 4) := by positivity
  set c : ℝ := a ^ 3 / (2 * K ^ 4)
  have hc' : 0 < min c 1 := lt_min hc one_pos
  refine ⟨1 / (16 * K * a) + 1 / min c 1, by positivity, fun σ t hσ1 hσ2 ht => ?_⟩
  have hL2 : 2 < Real.log |t| := by
    have h := Real.log_lt_log (Real.exp_pos 2)
      (lt_of_lt_of_le exp_two_lt_eight (by linarith : (8 : ℝ) ≤ |t|))
    rwa [Real.log_exp] at h
  set L := Real.log |t|
  have hL : 0 < L := by linarith
  have hL7 : 0 < L ^ (7 : ℕ) := by positivity
  have hA : 0 < 1 / (16 * K * a) := by positivity
  have hB : 0 < 1 / min c 1 := by positivity
  by_cases hstrip : σ ≤ 1 + a / L ^ (9 : ℕ)
  · have h := norm_inv_LFunction_le_log_strip χ ht
      (by have : 0 ≤ a / L ^ (9 : ℕ) := by positivity
          linarith) hstrip
    calc ‖(DirichletCharacter.LFunction χ (σ + t * I))⁻¹‖ ≤ L ^ (7 : ℕ) / (16 * K * a) := h
      _ = 1 / (16 * K * a) * L ^ (7 : ℕ) := by ring
      _ ≤ (1 / (16 * K * a) + 1 / min c 1) * L ^ (7 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) hL7.le
  · push Not at hstrip
    have hη0 : a / L ^ (9 : ℕ) < σ - 1 := by linarith
    have hη : 0 < σ - 1 := lt_trans (by positivity) hη0
    have hη1 : σ - 1 ≤ 1 := by linarith
    -- the three factors of the 3-4-1 product
    have hpole : ‖DirichletCharacter.LFunctionTrivChar Q (1 + ((σ - 1 : ℝ) : ℂ))‖ ≤ K / (σ - 1) :=
      norm_LFunctionTrivChar_one_add_le hη hη1
    have hhigh : ‖DirichletCharacter.LFunction (χ ^ 2)
        (((1 + (σ - 1) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I)‖ ≤ 2 * K * L := by
      have h2t : 8 ≤ |2 * t| := by rw [abs_mul, abs_two]; linarith
      have hlog2 : 0 < Real.log |2 * t| := Real.log_pos (by rw [abs_mul, abs_two]; linarith)
      have h := norm_LFunction_le_log (χ ^ 2) h2t
        (show 1 - 1 / Real.log |2 * t| ≤ 1 + (σ - 1) by
          have hinv : 0 < 1 / Real.log |2 * t| := by positivity
          linarith)
        (show 1 + (σ - 1) ≤ 2 by linarith)
      have hlog : Real.log |2 * t| ≤ 2 * L := by
        have hsq : |2 * t| ≤ |t| ^ (2 : ℕ) := by rw [abs_mul, abs_two]; nlinarith
        have he := Real.log_le_log (by rw [abs_mul, abs_two]; positivity : 0 < |2 * t|) hsq
        simpa only [Real.log_pow, Nat.cast_ofNat] using he
      change _ ≤ K * Real.log |2 * t| at h
      nlinarith
    have hprod := χ.norm_LFunction_product_ge_one hη t
    rw [norm_mul, norm_mul, norm_pow, norm_pow] at hprod
    have harg2 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) + I * t = (σ : ℂ) + t * I := by push_cast; ring
    have harg3 : (1 : ℂ) + ((σ - 1 : ℝ) : ℂ) + 2 * I * t =
        ((1 + (σ - 1) : ℝ) : ℂ) + ((2 * t : ℝ) : ℂ) * I := by push_cast; ring
    rw [harg2, harg3] at hprod
    set X := ‖DirichletCharacter.LFunction χ (σ + t * I)‖
    -- `X⁴ ≥ (σ − 1)³/(2K⁴L) ≥ c/L²⁸`
    have hchain : 1 ≤ (K / (σ - 1)) ^ 3 * X ^ 4 * (2 * K * L) :=
      le_trans hprod (mul_le_mul (mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) hpole 3) (by positivity)) hhigh (norm_nonneg _)
        (by positivity))
    have hη3 : (σ - 1) ^ 3 ≤ X ^ 4 * (2 * K ^ 4 * L) := by
      have h := mul_le_mul_of_nonneg_right hchain (pow_pos hη 3).le
      have e : (K / (σ - 1)) ^ 3 * X ^ 4 * (2 * K * L) * (σ - 1) ^ 3 = X ^ 4 * (2 * K ^ 4 * L) := by
        field_simp
      rwa [e, one_mul] at h
    have hX4 : c / L ^ (28 : ℕ) ≤ X ^ 4 := by
      have hpow : (a / L ^ (9 : ℕ)) ^ 3 ≤ (σ - 1) ^ 3 := pow_le_pow_left₀ (by positivity) hη0.le 3
      have hcL : c / L ^ (28 : ℕ) = (a / L ^ (9 : ℕ)) ^ 3 / (2 * K ^ 4 * L) := by
        simp only [c]; field_simp; ring
      rw [hcL, div_le_iff₀ (by positivity)]
      linarith
    -- hence `X ≥ min(c, 1)/L⁷`
    have hX : min c 1 / L ^ (7 : ℕ) ≤ X := by
      by_contra hlt
      push Not at hlt
      have h1 : X ^ 4 < (min c 1 / L ^ (7 : ℕ)) ^ 4 := pow_lt_pow_left₀ hlt (norm_nonneg _) (by norm_num)
      have h2 : (min c 1 / L ^ (7 : ℕ)) ^ 4 ≤ c / L ^ (28 : ℕ) := by
        rw [div_pow, ← pow_mul]
        refine div_le_div_of_nonneg_right ?_ (by positivity)
        calc min c 1 ^ 4 ≤ min c 1 := pow_le_of_le_one hc'.le (min_le_right _ _) (by norm_num)
          _ ≤ c := min_le_left _ _
      linarith
    rw [norm_inv]
    calc X⁻¹ ≤ (min c 1 / L ^ (7 : ℕ))⁻¹ := inv_anti₀ (by positivity) hX
      _ = 1 / min c 1 * L ^ (7 : ℕ) := by rw [inv_div]; ring
      _ ≤ (1 / (16 * K * a) + 1 / min c 1) * L ^ (7 : ℕ) :=
          mul_le_mul_of_nonneg_right (by linarith) hL7.le

/-- For `χ ≠ 1`, `|L(·, χ)|` and `1/|L(·, χ)|` are bounded on each box `1 ≤ Re s ≤ 2`, `|Im s| ≤ T`:
`L(·, χ)` is entire and zero-free on `Re s ≥ 1`. -/
theorem exists_norm_LFunction_le_box {χ : DirichletCharacter ℂ Q} (hχ : χ ≠ 1) (T : ℝ) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ s : ℂ, 1 ≤ s.re → s.re ≤ 2 → |s.im| ≤ T →
      ‖DirichletCharacter.LFunction χ s‖ ≤ M ∧ ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ M := by
  set B : Set ℂ := (Icc (1 : ℝ) 2) ×ℂ (Icc (-T) T)
  have hB : IsCompact B := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : Continuous (DirichletCharacter.LFunction χ) :=
    (DirichletCharacter.differentiable_LFunction hχ).continuous
  have hne : ∀ s ∈ B, DirichletCharacter.LFunction χ s ≠ 0 := fun s hs =>
    DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (Complex.mem_reProdIm.mp hs).1.1
  obtain ⟨M₁, hM₁⟩ := hB.exists_bound_of_continuousOn hcont.continuousOn
  obtain ⟨M₂, hM₂⟩ := hB.exists_bound_of_continuousOn
    (f := fun s => (DirichletCharacter.LFunction χ s)⁻¹)
    (fun s hs => (hcont.continuousAt.inv₀ (hne s hs)).continuousWithinAt)
  refine ⟨max (max M₁ M₂) 1, le_max_right _ _, fun s h1 h2 h3 => ?_⟩
  have hmem : s ∈ B := Complex.mem_reProdIm.mpr ⟨⟨h1, h2⟩, abs_le.mp h3⟩
  exact ⟨(hM₁ s hmem).trans ((le_max_left _ _).trans (le_max_left _ _)),
    (hM₂ s hmem).trans ((le_max_right _ _).trans (le_max_left _ _))⟩

end RHTower
