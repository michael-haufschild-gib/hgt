import GaloisForLFunctions.RHTower.Sieve.ZetaThinDisc

/-!
# The segment inside the thin disc

The horizontal segment from `σ₁ + iγ` to `σ + iγ`, with `σ₁ = 1 + 1/L²` and `|σ - 1| ≤ 1/L²`, has
length at most `2/L²` and therefore lies inside the disc of radius `3/L²` about `σ₁ + iγ`.

Each statement is separate so that the assembly of the `1/ζ` bound never has to elaborate a long
`have`-chain.
-/

namespace RHTower.Sieve

open Complex Metric

/-- The parametrised segment point, in real coordinates. -/
theorem thin_seg_pt (σ γ L t : ℝ) :
    (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      = ((((1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2)) : ℝ)) : ℂ) + (γ : ℂ) * Complex.I := by
  push_cast
  ring

/-- The segment stays between its endpoints. -/
theorem thin_seg_range {σ L t : ℝ} (hσ : σ ≤ 1 + 1 / L ^ 2) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    σ ≤ (1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2))
      ∧ (1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2)) ≤ 1 + 1 / L ^ 2 := by
  constructor
  · nlinarith [ht.1, ht.2, hσ]
  · nlinarith [ht.1, hσ]

/-- The distance between the endpoints. -/
theorem thin_seg_dist {σ γ L : ℝ} (hlow : 1 - 1 / L ^ 2 ≤ σ) (hσ : σ ≤ 1 + 1 / L ^ 2) :
    ‖((σ : ℂ) + (γ : ℂ) * Complex.I)
      - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)‖ ≤ 2 / L ^ 2 := by
  have hdiff : ((σ : ℂ) + (γ : ℂ) * Complex.I)
      - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
      = (((σ - (1 + 1 / L ^ 2) : ℝ)) : ℂ) := by push_cast; ring
  rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
  have hd2 : (2 : ℝ) / L ^ 2 = 2 * (1 / L ^ 2) := by ring
  linarith [hd2]

/-- The segment lies inside the thin disc. -/
theorem thin_seg_mem {σ γ L t : ℝ} (hL0 : 0 < L) (hlow : 1 - 1 / L ^ 2 ≤ σ)
    (hσ : σ ≤ 1 + 1 / L ^ 2) (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I))
      ∈ ball ((((1 + 1 / L ^ 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ 2) := by
  rw [thin_seg_pt]
  have hdiff : ((((1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2)) : ℝ)) : ℂ) + (γ : ℂ) * Complex.I
      - ((((1 + 1 / L ^ 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I)
      = (((t * (σ - (1 + 1 / L ^ 2)) : ℝ)) : ℂ) := by push_cast; ring
  rw [mem_ball_iff_norm, hdiff, Complex.norm_real, Real.norm_eq_abs]
  have hnp : t * (σ - (1 + 1 / L ^ 2)) ≤ 0 := by nlinarith [ht.1, hσ]
  rw [abs_of_nonpos hnp]
  obtain ⟨h1, h2⟩ := thin_seg_range hσ ht
  have hd2 : (2 : ℝ) / L ^ 2 = 2 * (1 / L ^ 2) := by ring
  have hd3 : (3 : ℝ) / L ^ 2 = 3 * (1 / L ^ 2) := by ring
  have hxpos : (0 : ℝ) < 1 / L ^ 2 := by positivity
  linarith [hd2, hd3, hxpos]

/-- The far endpoint lies inside the thin disc. -/
theorem thin_seg_endpoint {σ γ L : ℝ} (hL0 : 0 < L) (hlow : 1 - 1 / L ^ 2 ≤ σ)
    (hσ : σ ≤ 1 + 1 / L ^ 2) :
    ((σ : ℂ) + (γ : ℂ) * Complex.I)
      ∈ ball ((((1 + 1 / L ^ 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ 2) := by
  rw [mem_ball_iff_norm]
  have hdist := thin_seg_dist (σ := σ) (γ := γ) (L := L) hlow hσ
  have hd2 : (2 : ℝ) / L ^ 2 = 2 * (1 / L ^ 2) := by ring
  have hd3 : (3 : ℝ) / L ^ 2 = 3 * (1 / L ^ 2) := by ring
  have hxpos : (0 : ℝ) < 1 / L ^ 2 := by positivity
  linarith [hdist, hd2, hd3, hxpos]

/-- The centre lies inside the thin disc. -/
theorem thin_centre_mem {γ L : ℝ} (hL0 : 0 < L) :
    (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
      ∈ ball ((((1 + 1 / L ^ 2 : ℝ)) : ℂ) + (γ : ℂ) * Complex.I) (3 / L ^ 2) := by
  simpa using (by positivity : (0 : ℝ) < 3 / L ^ 2)

/-- **The logarithmic derivative along the segment**, given the region bound. -/
theorem thin_seg_logDeriv {c' C_D T₁ σ γ L : ℝ}
    (hLD : ∀ σ' γ' : ℝ, T₁ ≤ |γ'| → 1 - c' / Real.log |γ'| ≤ σ' → σ' ≤ 9 / 8 →
      ‖logDeriv riemannZeta ((σ' : ℂ) + (γ' : ℂ) * Complex.I)‖ ≤ C_D * Real.log |γ'| ^ 2)
    (hγT₁ : T₁ ≤ |γ|) (hLdef : L = Real.log |γ|) (hL3 : 3 ≤ L) (hc'0 : 0 < c')
    (hLc' : 1 / c' ≤ L) (hlow : 1 - 1 / L ^ 2 ≤ σ) (hσ : σ ≤ 1 + 1 / L ^ 2)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    ‖logDeriv riemannZeta ((((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)
        + (t : ℂ) * (((σ : ℂ) + (γ : ℂ) * Complex.I)
          - (((1 + 1 / L ^ 2 : ℝ) : ℂ) + (γ : ℂ) * Complex.I)))‖
      ≤ C_D * L ^ 2 := by
  have hL0 : (0 : ℝ) < L := by linarith
  rw [thin_seg_pt]
  obtain ⟨h1, h2⟩ := thin_seg_range hσ ht
  have hcmp : (1 : ℝ) / L ^ 2 ≤ c' / L := by
    rw [div_le_div_iff₀ (by positivity) hL0]
    have h5 : (1 : ℝ) ≤ c' * L := by
      rw [div_le_iff₀ hc'0] at hLc'
      nlinarith [hLc', hc'0]
    nlinarith [h5, hL0]
  have hlowu : 1 - c' / L ≤ (1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2)) := by
    linarith [hlow, h1]
  have hsq : (1 : ℝ) / L ^ 2 ≤ 1 / 9 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hL3]
  have hupu : (1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2)) ≤ 9 / 8 := by linarith [h2, hsq]
  have hres := hLD ((1 + 1 / L ^ 2) + t * (σ - (1 + 1 / L ^ 2))) γ hγT₁
    (by rw [← hLdef]; exact hlowu) hupu
  rw [← hLdef] at hres
  exact hres

end RHTower.Sieve
