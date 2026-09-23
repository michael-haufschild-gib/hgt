import GaloisForLFunctions.RHTower.Sieve.FibreIndexRange

/-!
# The bundled input reduces to one off-diagonal bound

`FrequencyMeanSquareSmall` bundles a length, a height, an affine majorant and a numeric inequality.
Unit 23 fixes the length (`M = ⌈√x + h⌉`) and the width (`fibreWidth ≤ h/√x`), which leaves only two
free numbers, and of those only the height-free part matters:

```text
OffDiagonalSmall f hh :=  ∀ ε > 0, ∀ᶠ x, ∃ α β,  0 ≤ α ≤ 50√x,  0 ≤ β ≤ ε·x,
    ∀ T > 0,  ∫_{|w| ≤ T} ‖ ∑_{n ≤ M} f(n) n^{2πiw} ‖² dw  ≤  α·T + β .
```

The diagonal coefficient `α` may sit at its baseline `≍ M ≍ √x`; the whole content is `β ≤ ε·x`,
i.e. the off-diagonal beats `M²`.  With the height `W₀ = ε√x/4000` the four terms of the Gallagher
budget come to `ε·h²/40`, `ε·h²/32`, `800000/(3ε)` and `10⁶/(9ε)`, and the last two are below
`ε·h²/32` as soon as `h ≥ 3000/ε` — which holds eventually because `h → ∞`.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Filter Topology Finset

/-- The off-diagonal of the frequency mean square beats `M²`, with the diagonal at its baseline. -/
def OffDiagonalSmall (f : ℕ → ℝ) (hh : ℝ → ℝ) : Prop :=
  ∀ ε > 0, ∀ᶠ x : ℝ in atTop, ∃ α β : ℝ,
    0 ≤ α ∧ 0 ≤ β ∧ α ≤ 50 * Real.sqrt x ∧ β ≤ ε * x
      ∧ ∀ T : ℝ, 0 < T →
          (∫ w in Set.Icc (-T) T,
            ‖logPoly (fun n => ((f n : ℝ) : ℂ))
              (Finset.Icc 1 ⌈Real.sqrt x + hh x⌉₊) w‖ ^ (2 : ℕ)) ≤ α * T + β

/-- **The bundled input follows from the off-diagonal bound alone.** -/
theorem frequencyMeanSquareSmall_of_offDiagonal {f : ℕ → ℝ} {hh : ℝ → ℝ}
    (hgrow : Tendsto hh atTop atTop) (hcap : ∀ᶠ x in atTop, hh x ≤ Real.sqrt x)
    (hoff : OffDiagonalSmall f hh) :
    FrequencyMeanSquareSmall f hh := by
  intro ε hε
  have hpi3 : (3 : ℝ) ≤ Real.pi ^ (2 : ℕ) := by nlinarith [Real.pi_gt_three]
  have hε64 : (0 : ℝ) < ε / 64 := by linarith
  filter_upwards [hoff (ε / 64) hε64, hcap, Filter.eventually_ge_atTop (16 : ℝ),
    hgrow.eventually_ge_atTop (3000 / ε)] with x hx hcx hx16 hhbig
  obtain ⟨α, β, hα, hβ, hαle, hβle, hT⟩ := hx
  set S : ℝ := Real.sqrt x with hSdef
  have hS4 : (4 : ℝ) ≤ S := by
    have h16 : Real.sqrt 16 = 4 := by
      rw [show (16 : ℝ) = 4 ^ (2 : ℕ) by norm_num, Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 4)]
    rw [hSdef, ← h16]
    exact Real.sqrt_le_sqrt hx16
  have hS0 : (0 : ℝ) < S := by linarith
  have hxS : x = S * S := by rw [hSdef, Real.mul_self_sqrt (by linarith)]
  have hx0 : (0 : ℝ) < x := by rw [hxS]; positivity
  set H : ℝ := hh x with hHdef
  have hHbig : 3000 / ε ≤ H := hhbig
  have hH0 : (0 : ℝ) < H := by
    have : (0 : ℝ) < 3000 / ε := by positivity
    linarith
  have hεH : (3000 : ℝ) ≤ ε * H := by
    rw [div_le_iff₀ hε] at hHbig
    linarith
  set W₀ : ℝ := ε * S / 4000 with hW₀def
  have hW₀ : (0 : ℝ) < W₀ := by rw [hW₀def]; positivity
  refine ⟨⌈S + H⌉₊, α, β, W₀, ?_, hW₀, hα, hβ, ?_, ?_⟩
  · intro a ha
    exact innerFibre_subset_Icc (by linarith) hH0.le ha
  · intro T hTW
    exact hT T (lt_of_lt_of_le hW₀ hTW)
  · set t : ℝ := fibreWidth x H with htdef
    have ht0 : 0 ≤ t := by
      rw [htdef, fibreWidth]
      refine Real.log_nonneg ?_
      have : (0 : ℝ) ≤ H / Real.sqrt x := by positivity
      linarith
    have htle : t ≤ H / S := by
      rw [htdef, hSdef]
      exact fibreWidth_le_div hx0 hH0.le
    have htsq : t ^ (2 : ℕ) ≤ H ^ (2 : ℕ) / x := by
      have hb := pow_le_pow_left₀ ht0 htle 2
      have hval : (H / S) ^ (2 : ℕ) = H ^ (2 : ℕ) / x := by
        rw [div_pow, hxS]
        ring
      linarith [hb, hval]
    -- term 1
    have hαW : α * W₀ ≤ ε * x / 80 := by
      have h1 : α * W₀ ≤ (50 * S) * W₀ := mul_le_mul_of_nonneg_right hαle hW₀.le
      have hval : (50 * S) * W₀ = ε * x / 80 := by
        rw [hW₀def, hxS]; ring
      linarith
    have hterm1 : 2 * t ^ (2 : ℕ) * (α * W₀) ≤ ε * H ^ (2 : ℕ) / 40 := by
      have h1 : 2 * t ^ (2 : ℕ) * (α * W₀) ≤ 2 * (H ^ (2 : ℕ) / x) * (α * W₀) := by
        have hnn : (0 : ℝ) ≤ α * W₀ := by positivity
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htsq (by norm_num : (0:ℝ) ≤ 2)) hnn
        linarith
      have h2 : 2 * (H ^ (2 : ℕ) / x) * (α * W₀) ≤ 2 * (H ^ (2 : ℕ) / x) * (ε * x / 80) := by
        have hnn : (0 : ℝ) ≤ 2 * (H ^ (2 : ℕ) / x) := by positivity
        exact mul_le_mul_of_nonneg_left hαW hnn
      have hval : 2 * (H ^ (2 : ℕ) / x) * (ε * x / 80) = ε * H ^ (2 : ℕ) / 40 := by
        field_simp; ring
      linarith
    -- term 2
    have hterm2 : 2 * t ^ (2 : ℕ) * β ≤ ε * H ^ (2 : ℕ) / 32 := by
      have h1 : 2 * t ^ (2 : ℕ) * β ≤ 2 * (H ^ (2 : ℕ) / x) * β := by
        have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left htsq (by norm_num : (0:ℝ) ≤ 2)) hβ
        linarith
      have h2 : 2 * (H ^ (2 : ℕ) / x) * β ≤ 2 * (H ^ (2 : ℕ) / x) * (ε / 64 * x) := by
        have hnn : (0 : ℝ) ≤ 2 * (H ^ (2 : ℕ) / x) := by positivity
        exact mul_le_mul_of_nonneg_left hβle hnn
      have hval : 2 * (H ^ (2 : ℕ) / x) * (ε / 64 * x) = ε * H ^ (2 : ℕ) / 32 := by
        field_simp; ring
      linarith
    -- term 3
    have hterm3 : 4 * α / (Real.pi ^ (2 : ℕ) * W₀) ≤ ε * H ^ (2 : ℕ) / 32 := by
      have hlow : 3 * (ε * S / 4000) ≤ Real.pi ^ (2 : ℕ) * W₀ := by
        rw [hW₀def]
        have hnn : (0 : ℝ) ≤ ε * S / 4000 := by positivity
        exact mul_le_mul_of_nonneg_right hpi3 hnn
      have hd0 : (0 : ℝ) < 3 * (ε * S / 4000) := by positivity
      have hnum : 4 * α ≤ 200 * S := by linarith
      have hchain : 4 * α / (Real.pi ^ (2 : ℕ) * W₀) ≤ 200 * S / (3 * (ε * S / 4000)) := by
        refine le_trans (div_le_div_of_nonneg_left (by positivity) hd0 hlow) ?_
        exact div_le_div_of_nonneg_right hnum hd0.le
      have hval : 200 * S / (3 * (ε * S / 4000)) = 800000 / (3 * ε) := by
        field_simp; ring
      rw [hval] at hchain
      have hfin : 800000 / (3 * ε) ≤ ε * H ^ (2 : ℕ) / 32 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hεH, hε.le, hH0.le]
      linarith
    -- term 4
    have hterm4 : 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ)) ≤ ε * H ^ (2 : ℕ) / 32 := by
      have hW₀sq : W₀ ^ (2 : ℕ) = ε ^ (2 : ℕ) * x / 16000000 := by
        rw [hW₀def, div_pow, mul_pow, hxS]
        ring
      have hlow : 9 * (ε ^ (2 : ℕ) * x / 16000000) ≤ 3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ) := by
        rw [hW₀sq]
        have hnn : (0 : ℝ) ≤ ε ^ (2 : ℕ) * x / 16000000 := by positivity
        nlinarith [hpi3, hnn]
      have hd0 : (0 : ℝ) < 9 * (ε ^ (2 : ℕ) * x / 16000000) := by positivity
      have hnum : 4 * β ≤ 4 * (ε / 64 * x) := by linarith
      have hchain : 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ))
          ≤ 4 * (ε / 64 * x) / (9 * (ε ^ (2 : ℕ) * x / 16000000)) := by
        refine le_trans (div_le_div_of_nonneg_left (by positivity) hd0 hlow) ?_
        exact div_le_div_of_nonneg_right hnum hd0.le
      have hval : 4 * (ε / 64 * x) / (9 * (ε ^ (2 : ℕ) * x / 16000000)) = 1000000 / (9 * ε) := by
        field_simp; ring
      rw [hval] at hchain
      have hfin : 1000000 / (9 * ε) ≤ ε * H ^ (2 : ℕ) / 32 := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [hεH, hε.le, hH0.le]
      linarith
    -- assemble
    have hsum : 2 * t ^ (2 : ℕ) * (α * W₀ + β)
          + (4 * α / (Real.pi ^ (2 : ℕ) * W₀) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ)))
        ≤ ε * H ^ (2 : ℕ) / 8 := by
      have hsplit : 2 * t ^ (2 : ℕ) * (α * W₀ + β) = 2 * t ^ (2 : ℕ) * (α * W₀) + 2 * t ^ (2 : ℕ) * β := by ring
      rw [hsplit]
      have hεH2 : (0 : ℝ) ≤ ε * H ^ (2 : ℕ) := by positivity
      linarith [hterm1, hterm2, hterm3, hterm4, hεH2]
    have hmul : 8 * S * (2 * t ^ (2 : ℕ) * (α * W₀ + β)
          + (4 * α / (Real.pi ^ (2 : ℕ) * W₀) + 4 * β / (3 * Real.pi ^ (2 : ℕ) * W₀ ^ (2 : ℕ))))
        ≤ 8 * S * (ε * H ^ (2 : ℕ) / 8) :=
      mul_le_mul_of_nonneg_left hsum (by linarith)
    have hval : 8 * S * (ε * H ^ (2 : ℕ) / 8) = ε * (H ^ (2 : ℕ) * S) := by ring
    linarith [hmul, hval]

end RHTower.Sieve

end
