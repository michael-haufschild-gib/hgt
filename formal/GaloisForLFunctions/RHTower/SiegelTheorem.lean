import GaloisForLFunctions.RHTower.SiegelTheoremAux

/-!
# Siegel's theorem

**Theorem** (`siegel_LFunction_one`).  For every `ε > 0` there is `c(ε) > 0` such that
`L(1, χ) ≥ c(ε) N^{−ε}` for every nontrivial quadratic Dirichlet character `χ` modulo `N`.

Proof (Goldfeld's form).  Let `η = min(ε/16, δ₀/2, 1/8)`, where `ζ(σ) < 0` on `(1 − δ₀, 1)`.

* If some nontrivial quadratic `χ₁ mod N₁` has a real zero `β ∈ [1 − η, 1)`, fix it.
* Otherwise fix `χ₁ = χ₄` (modulo `4`) and `β = 1 − η`.

For `χ` with `χ₁χ` nonprincipal, `F = ζ L(·,χ₁) L(·,χ) L(·,χ₁χ)` satisfies `F(β) ≤ 0`: in the first
case `L(β, χ₁) = 0`; in the second the three L-values are positive (no real zeros in `[β, 1)`) and
`ζ(β) < 0`.  Goldfeld's inequality gives `λ = L(1,χ₁)L(1,χ)L(1,χ₁χ) ≥ (1−β)/(4e A^{4(1−β)})` with
`A = 8C₀(N₁N)² + 8`, and `L(1, χ₁χ) ≤ log(N₁N) + 5`.  Since `1 − β ≤ ε/16`, this gives
`L(1, χ) ≫_ε N^{−ε}`.  If `χ₁χ` is principal, `L(1, χ) ≥ L(1, χ₁) ∏_{p | N₁N}(1 − 1/p)²
≫_ε N^{−ε}`.  The constant is ineffective: it depends on `χ₁` and `β`.
-/

open DirichletCharacter Complex

noncomputable section

namespace RHTower

private lemma re_mul_of_im_eq_zero {z w : ℂ} (hz : z.im = 0) (hw : w.im = 0) :
    (z * w).re = z.re * w.re ∧ (z * w).im = 0 := by
  constructor <;> simp [Complex.mul_re, Complex.mul_im, hz, hw]

/-- The value of `F = ζ L(·,χ₁) L(·,χ) L(·,χ₁χ)` at a real point is real, with real part the product
of the real parts. -/
lemma re_siegelProduct {N₁ N : ℕ} [NeZero N₁] [NeZero N] {χ₁ : DirichletCharacter ℂ N₁}
    {χ : DirichletCharacter ℂ N} (hq₁ : χ₁ ^ 2 = 1) (hq : χ ^ 2 = 1) (h₁ : χ₁ ≠ 1) (hχ : χ ≠ 1)
    (h₁₂ : productChar χ₁ χ ≠ 1) {σ : ℝ} (hσ : 0 < σ) :
    (riemannZeta σ * (LFunction χ₁ σ * LFunction χ σ * LFunction (productChar χ₁ χ) σ)).re
      = (riemannZeta σ).re * ((LFunction χ₁ σ).re * (LFunction χ σ).re
          * (LFunction (productChar χ₁ χ) σ).re) := by
  have a := LFunction_ofReal_im hq₁ h₁ hσ
  have b := LFunction_ofReal_im hq hχ hσ
  have c := LFunction_ofReal_im (productChar_sq hq₁ hq) h₁₂ hσ
  have z := riemannZeta_ofReal_im σ
  obtain ⟨e1, i1⟩ := re_mul_of_im_eq_zero a b
  obtain ⟨e2, i2⟩ := re_mul_of_im_eq_zero i1 c
  obtain ⟨e3, _⟩ := re_mul_of_im_eq_zero z i2
  rw [e3, e2, e1]

/-- **The fixed auxiliary character.**  For `0 < η ≤ 1/8` with `ζ < 0` on `[1 − η, 1)` there are a
nontrivial quadratic `χ₁ mod N₁` and `β ∈ [1 − η, 1)` such that `F(β) ≤ 0` for every nontrivial
quadratic `χ` with `χ₁χ` nonprincipal. -/
theorem exists_siegel_auxiliary {η : ℝ} (hη : 0 < η) (hη8 : η ≤ 1 / 8)
    (hζ : ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 → (riemannZeta σ).re < 0) :
    ∃ (N₁ : ℕ) (_ : NeZero N₁) (χ₁ : DirichletCharacter ℂ N₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ 1 - η ≤ β ∧ β < 1 ∧
      ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
        productChar χ₁ χ ≠ 1 →
        (riemannZeta β * (LFunction χ₁ β * LFunction χ β
          * LFunction (productChar χ₁ χ) β)).re ≤ 0 := by
  by_cases hA : ∃ (N₁ : ℕ) (_ : NeZero N₁) (χ₁ : DirichletCharacter ℂ N₁) (β : ℝ),
      χ₁ ^ 2 = 1 ∧ χ₁ ≠ 1 ∧ 1 - η ≤ β ∧ β < 1 ∧ LFunction χ₁ β = 0
  · obtain ⟨N₁, hN₁, χ₁, β, hq₁, h₁, hβ1, hβ2, hz⟩ := hA
    refine ⟨N₁, hN₁, χ₁, β, hq₁, h₁, hβ1, hβ2, fun N _ χ _ _ _ => ?_⟩
    rw [hz]; simp
  · push Not at hA
    refine ⟨4, inferInstance, chiFourChar, 1 - η, chiFour_sq, chiFour_ne_one, le_rfl, by linarith,
      fun N _ χ hq hχ h₁₂ => ?_⟩
    have hβ0 : 0 < 1 - η := by linarith
    have hpos : ∀ {M : ℕ} [NeZero M] (ψ : DirichletCharacter ℂ M), ψ ^ 2 = 1 → ψ ≠ 1 →
        0 < (LFunction ψ (1 - η : ℝ)).re := by
      intro M _ ψ hqψ hψ
      exact LFunction_re_pos_of_no_zero hqψ hψ hβ0
        (fun σ h1 h2 => hA M inferInstance ψ σ hqψ hψ h1 h2) le_rfl (by linarith)
    rw [re_siegelProduct chiFour_sq hq chiFour_ne_one hχ h₁₂ hβ0]
    have h1 := hpos chiFourChar chiFour_sq chiFour_ne_one
    have h2 := hpos χ hq hχ
    have h3 := hpos (productChar chiFourChar χ) (productChar_sq chiFour_sq hq) h₁₂
    have h0 := hζ (1 - η) le_rfl (by linarith)
    have : 0 < (LFunction chiFourChar (1 - η : ℝ)).re * (LFunction χ (1 - η : ℝ)).re
        * (LFunction (productChar chiFourChar χ) (1 - η : ℝ)).re := by positivity
    nlinarith

/-- The numerical core of Siegel's theorem: from
`κ/(e₄ P) ≤ L₁ L L₁₂`, `P ≤ A M`, `L₁₂ ≤ B M`, `M² = Nε`, `Nε Nε' = 1` deduce
`κ/(e₄ A L₁ B) · Nε' ≤ L`. -/
lemma siegel_numeric {κ e₄ P A M B L₁ L L₁₂ Nε Nε' : ℝ} (hκ : 0 < κ) (he₄ : 0 < e₄)
    (hP : 0 < P) (hA : 0 < A) (hM : 0 < M) (hB : 0 < B) (hL₁ : 0 < L₁) (hL : 0 < L)
    (hNε' : 0 ≤ Nε') (hmain : κ / (e₄ * P) ≤ L₁ * L * L₁₂) (hPA : P ≤ A * M)
    (hL₁₂ : L₁₂ ≤ B * M) (hMM : M * M = Nε) (hNN : Nε * Nε' = 1) :
    κ / (e₄ * A * L₁ * B) * Nε' ≤ L := by
  have h1 : κ / (e₄ * (A * M)) ≤ κ / (e₄ * P) :=
    div_le_div_of_nonneg_left hκ.le (by positivity) (mul_le_mul_of_nonneg_left hPA he₄.le)
  have h2 : L₁ * L * L₁₂ ≤ L₁ * L * (B * M) :=
    mul_le_mul_of_nonneg_left hL₁₂ (by positivity)
  have h3 : κ ≤ (e₄ * A * L₁ * B) * L * Nε := by
    have := (h1.trans hmain).trans h2
    rw [div_le_iff₀ (by positivity)] at this
    calc κ ≤ L₁ * L * (B * M) * (e₄ * (A * M)) := this
      _ = (e₄ * A * L₁ * B) * L * (M * M) := by ring
      _ = (e₄ * A * L₁ * B) * L * Nε := by rw [hMM]
  have hD : 0 < e₄ * A * L₁ * B := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ hD]
  calc κ * Nε' ≤ (e₄ * A * L₁ * B) * L * Nε * Nε' := mul_le_mul_of_nonneg_right h3 hNε'
    _ = L * (e₄ * A * L₁ * B) := by rw [mul_assoc _ Nε, hNN]; ring

/-- **Siegel's theorem.**  For every `ε > 0` there is `c > 0` such that `L(1, χ) ≥ c N^{−ε}` for
every nontrivial quadratic Dirichlet character `χ` modulo `N`. -/
theorem siegel_LFunction_one {ε : ℝ} (hε : 0 < ε) :
    ∃ c : ℝ, 0 < c ∧ ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ ^ 2 = 1 → χ ≠ 1 →
      c * (N : ℝ) ^ (-ε) ≤ (LFunction χ 1).re := by
  obtain ⟨C₀, hC₀, hgold⟩ := siegel_goldfeld_bound
  obtain ⟨δ₀, hδ₀, -, hζ₀⟩ := exists_riemannZeta_neg
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = min (ε / 16) (min (δ₀ / 2) (1 / 8)) := ⟨_, rfl⟩
  have hη : 0 < η := by rw [hηdef]; positivity
  have hη8 : η ≤ 1 / 8 := hηdef ▸ (min_le_right _ _).trans (min_le_right _ _)
  have hηε : η ≤ ε / 16 := hηdef ▸ min_le_left _ _
  have hηδ : η ≤ δ₀ / 2 := hηdef ▸ (min_le_right _ _).trans (min_le_left _ _)
  have hζ : ∀ σ : ℝ, 1 - η ≤ σ → σ < 1 → (riemannZeta σ).re < 0 :=
    fun σ h1 h2 => hζ₀ σ (by linarith) h2
  obtain ⟨N₁, hN₁, χ₁, β, hq₁, h₁, hβ1, hβ2, hF⟩ := exists_siegel_auxiliary hη hη8 hζ
  obtain ⟨Cδ, hCδ, hEuler⟩ := exists_prod_one_sub_inv_ge (δ := ε / 2) (by positivity)
  obtain ⟨hL₁pos, hL₁im⟩ := LFunction_one_pos hq₁ h₁
  have hκ0 : 0 < 1 - β := by linarith
  have hN₁1 : (1 : ℝ) ≤ N₁ := by exact_mod_cast NeZero.one_le
  have hA₁1 : 1 ≤ 8 * C₀ * (N₁ : ℝ) ^ 2 + 8 := by
    have : 0 ≤ 8 * C₀ * (N₁ : ℝ) ^ 2 := by positivity
    linarith
  have hB0 : 0 < Real.log N₁ + 5 + 2 / ε := by have := Real.log_nonneg hN₁1; positivity
  refine ⟨min ((1 - β) / (4 * Real.exp 1 * (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) ^ (4 * η)
      * (LFunction χ₁ 1).re * (Real.log N₁ + 5 + 2 / ε)))
    ((LFunction χ₁ 1).re * Cδ ^ 2 * (N₁ : ℝ) ^ (-ε)), lt_min (by positivity) (by positivity),
    fun N _ χ hq hχ => ?_⟩
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast NeZero.one_le
  have hN0 : (0 : ℝ) < N := by linarith
  obtain ⟨hLpos, hLim⟩ := LFunction_one_pos hq hχ
  have hNε : 0 < (N : ℝ) ^ (-ε) := Real.rpow_pos_of_pos hN0 _
  by_cases h₁₂ : productChar χ₁ χ = 1
  · -- equivalent characters
    have hge := LFunction_one_ge_of_productChar_eq_one hq₁ hq h₁ hχ h₁₂
    have hP := hEuler (N₁ * N) (Nat.mul_ne_zero (NeZero.ne _) (NeZero.ne _))
    push_cast at hP
    have hx0 : (0 : ℝ) ≤ (N₁ : ℝ) * N := by positivity
    have hxx : (((N₁ : ℝ) * N) ^ (-(ε / 2))) ^ 2 = ((N₁ : ℝ) * N) ^ (-ε) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0]
      congr 1; push_cast; ring
    have hsq : (Cδ * ((N₁ : ℝ) * N) ^ (-(ε / 2))) ^ 2
        = Cδ ^ 2 * (N₁ : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε) := by
      rw [mul_pow, hxx, Real.mul_rpow (by positivity) (by positivity)]; ring
    have hP2 : Cδ ^ 2 * (N₁ : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε)
        ≤ (∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2 := by
      rw [← hsq]; exact pow_le_pow_left₀ (by positivity) hP 2
    calc _ ≤ (LFunction χ₁ 1).re * Cδ ^ 2 * (N₁ : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hNε.le
      _ = (LFunction χ₁ 1).re * (Cδ ^ 2 * (N₁ : ℝ) ^ (-ε) * (N : ℝ) ^ (-ε)) := by ring
      _ ≤ (LFunction χ₁ 1).re * (∏ p ∈ (N₁ * N).primeFactors, (1 - (p : ℝ)⁻¹)) ^ 2 :=
          mul_le_mul_of_nonneg_left hP2 hL₁pos.le
      _ ≤ (LFunction χ 1).re := hge
  · -- the main case
    have hg := hgold N₁ N χ₁ χ hq₁ hq h₁ hχ h₁₂ β (by linarith) hβ2
    have hFβ := hF N χ hq hχ h₁₂
    have hA1 : 1 ≤ 8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8 := by
      have : 0 ≤ 8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) := by positivity
      linarith
    have hApos : 0 < (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * (1 - β)) :=
      Real.rpow_pos_of_pos (by linarith) _
    -- the residue is bounded below
    have hlam_lb : (1 - β) / (4 * Real.exp 1 * (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * (1 - β)))
        ≤ (siegelRes χ₁ χ).re := by
      have h0 := hg.trans hFβ
      have h1 : 1 / 2 ≤ 2 * Real.exp 1 * (siegelRes χ₁ χ).re
          * (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * (1 - β)) / (1 - β) := by linarith
      rw [le_div_iff₀ hκ0] at h1
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    obtain ⟨h12pos, h12im⟩ := LFunction_one_pos (productChar_sq hq₁ hq) h₁₂
    have hlam_eq : (siegelRes χ₁ χ).re
        = (LFunction χ₁ 1).re * (LFunction χ 1).re * (LFunction (productChar χ₁ χ) 1).re := by
      rw [siegelRes_eq]
      obtain ⟨e1, i1⟩ := re_mul_of_im_eq_zero hL₁im hLim
      obtain ⟨e2, _⟩ := re_mul_of_im_eq_zero i1 h12im
      rw [e2, e1]
    have h12le : (LFunction (productChar χ₁ χ) 1).re ≤ Real.log ((N₁ : ℝ) * N) + 5 := by
      have := norm_LFunction_one_le_log h₁₂
      push_cast at this
      exact (Complex.re_le_norm _).trans this
    have hlogN : Real.log N ≤ (2 / ε) * (N : ℝ) ^ (ε / 2) := by
      have := Real.log_le_rpow_div hN0.le (by positivity : (0 : ℝ) < ε / 2)
      calc Real.log N ≤ (N : ℝ) ^ (ε / 2) / (ε / 2) := this
        _ = (2 / ε) * (N : ℝ) ^ (ε / 2) := by field_simp
    have hNh : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 (by positivity)
    have hlog12 : Real.log ((N₁ : ℝ) * N) + 5
        ≤ (Real.log N₁ + 5 + 2 / ε) * (N : ℝ) ^ (ε / 2) := by
      rw [Real.log_mul (by positivity) (by positivity)]
      have hl1 := Real.log_nonneg hN₁1
      nlinarith
    have hN2 : (1 : ℝ) ≤ (N : ℝ) ^ 2 := one_le_pow₀ hN1
    have hAle : 8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8 ≤ (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) * (N : ℝ) ^ 2 := by
      have e : (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) * (N : ℝ) ^ 2
          = 8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8 * (N : ℝ) ^ 2 := by ring
      rw [e]; linarith
    have hApow_le : (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * (1 - β))
        ≤ (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) ^ (4 * η) * (N : ℝ) ^ (ε / 2) := by
      calc (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * (1 - β))
          ≤ (8 * (C₀ * ((N₁ : ℝ) * N) ^ 2) + 8) ^ (4 * η) :=
            Real.rpow_le_rpow_of_exponent_le hA1 (by linarith)
        _ ≤ ((8 * C₀ * (N₁ : ℝ) ^ 2 + 8) * (N : ℝ) ^ 2) ^ (4 * η) :=
            Real.rpow_le_rpow (by linarith) hAle (by positivity)
        _ = (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) ^ (4 * η) * (N : ℝ) ^ (8 * η) := by
            rw [Real.mul_rpow (by positivity) (by positivity)]
            congr 1
            rw [← Real.rpow_natCast (N : ℝ) 2, ← Real.rpow_mul hN0.le]
            push_cast; ring_nf
        _ ≤ (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) ^ (4 * η) * (N : ℝ) ^ (ε / 2) :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
              (Real.rpow_nonneg (by linarith) _)
    have hMM : (N : ℝ) ^ (ε / 2) * (N : ℝ) ^ (ε / 2) = (N : ℝ) ^ ε := by
      rw [← Real.rpow_add hN0]; ring_nf
    have hNN : (N : ℝ) ^ ε * (N : ℝ) ^ (-ε) = 1 := by
      rw [← Real.rpow_add hN0]; simp
    have key := siegel_numeric hκ0 (by positivity : (0 : ℝ) < 4 * Real.exp 1) hApos
      (Real.rpow_pos_of_pos (by linarith) _) (by positivity) hB0 hL₁pos hLpos hNε.le
      (hlam_eq ▸ hlam_lb) hApow_le (h12le.trans hlog12) hMM hNN
    calc _ ≤ (1 - β) / (4 * Real.exp 1 * (8 * C₀ * (N₁ : ℝ) ^ 2 + 8) ^ (4 * η)
            * (LFunction χ₁ 1).re * (Real.log N₁ + 5 + 2 / ε)) * (N : ℝ) ^ (-ε) :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hNε.le
      _ ≤ (LFunction χ 1).re := key

end RHTower
