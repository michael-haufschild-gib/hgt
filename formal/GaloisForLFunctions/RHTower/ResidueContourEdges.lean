import GaloisForLFunctions.RHTower.ZetaInverseWideHorizontal
import GaloisForLFunctions.RHTower.LPropertyStrips

/-!
# The horizontal edges of Burnol's rectangle

Theorem 5.2 integrates `G(s)ζ(Z)/(ζ(s)(Z−s))` around the rectangle with corners `1/2 ± A ± iT_n`
and lets `n → ∞`.  The two horizontal edges disappear in the limit: `G` decreases faster than every
power of the height (Definition 12), `1/ζ` grows at most polynomially at the selected heights
(Proposition 5.1, extended to the whole segment in `ZetaInverseWideHorizontal`), and `1/(Z−s)`
decays like `1/T`.  Nothing here needs the integrand to be integrable: the estimate is the crude
`‖∫‖ ≤ length · sup`.

## Main results

* `tendsto_norm_horizontal_edge_zero`
-/

open Complex Filter Topology intervalIntegral

namespace RHTower

noncomputable section

/-- **The horizontal edges vanish.** -/
theorem tendsto_norm_horizontal_edge_zero {G : ℂ → ℂ} (hG : HasStripRapidDecrease G)
    {T : ℕ → ℝ} (htop : Tendsto T atTop atTop) (hT1 : ∀ k : ℕ, 1 ≤ T k)
    {C A b : ℝ} {k₀ : ℕ} (hC : 0 < C) (hA : 0 < A) (hb : 2 ≤ b)
    {ε : ℝ} (hε : |ε| = 1)
    (hzeta : ∀ k : ℕ, k₀ ≤ k → ∀ σ : ℝ, -b ≤ σ → σ ≤ b →
      ‖(riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖ ≤ C * (T k) ^ A)
    {x₁ x₂ : ℝ} (hx₁ : -b ≤ x₁) (hx₁' : x₁ ≤ b) (hx₂ : -b ≤ x₂) (hx₂' : x₂ ≤ b)
    (Z : ℂ) :
    Tendsto (fun k : ℕ => ‖∫ σ in x₁..x₂,
        G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I)
          * (riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹
          * (Z - ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖) atTop (𝓝 0) := by
  classical
  obtain ⟨N, hN⟩ := exists_nat_ge (A + 2)
  obtain ⟨Tg, Cg, hCg0, hGb⟩ := hG (-b) b N
  set D : ℝ := 2 * b * (Cg * C * 2) with hDdef
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have hneg : A - (N : ℝ) - 1 < 0 := by
    have : A + 2 ≤ (N : ℝ) := hN
    linarith
  have hmaj : Tendsto (fun k : ℕ => D * (T k) ^ (A - (N : ℝ) - 1)) atTop (𝓝 0) := by
    have hrpow : Tendsto (fun x : ℝ => x ^ (A - (N : ℝ) - 1)) atTop (𝓝 0) := by
      have h := tendsto_rpow_neg_atTop (y := -(A - (N : ℝ) - 1)) (by linarith)
      refine h.congr fun x => ?_
      rw [neg_neg]
    have := (hrpow.comp htop).const_mul D
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hmaj
    (Eventually.of_forall fun k => norm_nonneg _) ?_
  filter_upwards [Filter.eventually_ge_atTop k₀,
    htop.eventually_ge_atTop (max (max Tg 1) (2 * |Z.im| + 2))] with k hk hTk
  have hTk1 : (1 : ℝ) ≤ T k := hT1 k
  have hTk0 : (0 : ℝ) < T k := by linarith
  have hTg : Tg ≤ T k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hTk
  have hTZ : 2 * |Z.im| + 2 ≤ T k := le_trans (le_max_right _ _) hTk
  have hbound : ∀ σ ∈ Set.uIoc x₁ x₂,
      ‖G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I) * (riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹
        * (Z - ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖
        ≤ Cg * C * 2 * (T k) ^ (A - (N : ℝ) - 1) := by
    intro σ hσ
    rw [Set.mem_uIoc] at hσ
    have hσ1 : -b ≤ σ := by rcases hσ with ⟨h1, _⟩ | ⟨h1, _⟩ <;> linarith
    have hσ2 : σ ≤ b := by rcases hσ with ⟨_, h2⟩ | ⟨_, h2⟩ <;> linarith
    set s : ℂ := (σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I with hs
    have hsre : s.re = σ := by rw [hs]; simp
    have hsim : s.im = ε * T k := by rw [hs]; simp
    have habs : |ε * T k| = T k := by
      rw [abs_mul, hε, one_mul, abs_of_nonneg hTk0.le]
    have h1 : ‖G s‖ ≤ Cg * (1 + |s.im|) ^ (-(N : ℝ)) := by
      refine hGb s (by rw [hsre]; linarith) (by rw [hsre]; linarith) ?_
      rw [hsim, habs]
      exact hTg
    have h2 : ‖(riemannZeta s)⁻¹‖ ≤ C * (T k) ^ A := hzeta k hk σ hσ1 hσ2
    have h3 : ‖(Z - s)⁻¹‖ ≤ 2 * (T k) ^ (-(1 : ℝ)) := by
      have hZs : |Z.im - ε * T k| ≤ ‖Z - s‖ := by
        have him : (Z - s).im = Z.im - ε * T k := by rw [hs]; simp
        have hle := Complex.abs_im_le_norm (Z - s)
        rw [him] at hle
        exact hle
      have hlow : T k / 2 ≤ |Z.im - ε * T k| := by
        have h2 : |ε * T k| - |Z.im| ≤ |ε * T k - Z.im| := abs_sub_abs_le_abs_sub _ _
        rw [habs] at h2
        rw [abs_sub_comm]
        have hZ2 : |Z.im| ≤ T k / 2 := by linarith
        linarith
      have hhalf : T k / 2 ≤ ‖Z - s‖ := le_trans hlow hZs
      have hpos2 : (0 : ℝ) < T k / 2 := by linarith
      have hinv : ‖Z - s‖⁻¹ ≤ (T k / 2)⁻¹ := by gcongr
      have heq : (T k / 2)⁻¹ = 2 * (T k)⁻¹ := by field_simp
      rw [norm_inv, Real.rpow_neg_one]
      linarith [hinv, heq]
    have hpowG : (1 + |s.im|) ^ (-(N : ℝ)) ≤ (T k) ^ (-(N : ℝ)) := by
      rw [hsim, habs]
      exact Real.rpow_le_rpow_of_nonpos hTk0 (by linarith)
        (neg_nonpos.2 (Nat.cast_nonneg N))
    have hmul : (T k) ^ (-(N : ℝ)) * ((T k) ^ A * (T k) ^ (-(1 : ℝ)))
        = (T k) ^ (A - (N : ℝ) - 1) := by
      rw [← Real.rpow_add hTk0, ← Real.rpow_add hTk0]
      congr 1
      ring
    rw [norm_mul, norm_mul]
    have hG0 : (0 : ℝ) ≤ ‖G s‖ := norm_nonneg _
    have hZ0 : (0 : ℝ) ≤ ‖(Z - s)⁻¹‖ := norm_nonneg _
    have hζ0 : (0 : ℝ) ≤ ‖(riemannZeta s)⁻¹‖ := norm_nonneg _
    calc ‖G s‖ * ‖(riemannZeta s)⁻¹‖ * ‖(Z - s)⁻¹‖
        ≤ (Cg * (1 + |s.im|) ^ (-(N : ℝ))) * (C * (T k) ^ A) * (2 * (T k) ^ (-(1 : ℝ))) := by
          refine mul_le_mul (mul_le_mul h1 h2 hζ0 (by positivity)) h3 hZ0 (by positivity)
      _ ≤ (Cg * (T k) ^ (-(N : ℝ))) * (C * (T k) ^ A) * (2 * (T k) ^ (-(1 : ℝ))) := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ (by positivity))
            (by positivity)
          exact mul_le_mul_of_nonneg_left hpowG hCg0
      _ = Cg * C * 2 * ((T k) ^ (-(N : ℝ)) * ((T k) ^ A * (T k) ^ (-(1 : ℝ)))) := by ring
      _ = Cg * C * 2 * (T k) ^ (A - (N : ℝ) - 1) := by rw [hmul]
  have hlen : |x₂ - x₁| ≤ 2 * b := by
    rw [abs_le]
    constructor <;> linarith
  have hkey := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  have hcoef : (0 : ℝ) ≤ Cg * C * 2 * (T k) ^ (A - (N : ℝ) - 1) := by positivity
  calc ‖∫ σ in x₁..x₂, G ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I)
        * (riemannZeta ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹
        * (Z - ((σ : ℂ) + ((ε * T k : ℝ) : ℂ) * I))⁻¹‖
      ≤ Cg * C * 2 * (T k) ^ (A - (N : ℝ) - 1) * |x₂ - x₁| := hkey
    _ ≤ Cg * C * 2 * (T k) ^ (A - (N : ℝ) - 1) * (2 * b) := by
        exact mul_le_mul_of_nonneg_left hlen hcoef
    _ = D * (T k) ^ (A - (N : ℝ) - 1) := by rw [hDdef]; ring

end

end RHTower
