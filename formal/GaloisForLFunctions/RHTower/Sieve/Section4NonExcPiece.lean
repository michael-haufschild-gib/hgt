import GaloisForLFunctions.RHTower.Sieve.StepMassCard

/-!
# The non-exceptional piece of one short block

The first of the five pieces of `Sieve/Section4BlockMaster.section4_block_master`, put in the shape
the assembly consumes: everything expressed through the block's harmonic mass `stepMass_j` and its
left endpoint `Pj0`, so that the weighted sum over the ladder telescopes.

Writing `V_j = #B_j / K` for the cancellation threshold of `(35)` and `E ≤ CE·B₁·W_Q² + CR` for the
cofactor's energy, the term is

```text
   V_j²·(5π/2·T₀ + 5e/2·B₁)·E
     ≤ stepMass_j²(1+η)²/K²·[ (5π/2)T₀·CE·B₀W_Q²·Pj0 + (5π/2)T₀·CR·Pj0²
                              + (5e/2)CE·B₀²W_Q² + (5e/2)CR·B₀·Pj0 ] ,
```

and dividing by the target `stepMass_j²·B₀²·W_Q²` the four brackets are `O(ω)`, `o(1)`, `O(1)`,
`o(1)` — so the piece costs `≍ ω/K²`, which is what fixes `K = ω`.
-/

namespace RHTower.Sieve

noncomputable section

/-- **The non-exceptional piece of one short block.** -/
theorem nonexceptional_piece_le {NB stepM Pj0 B₀ B₁ T₀ K E CE CR WQ ηf : ℝ}
    (hK : 0 < K) (hηf : 0 ≤ ηf) (hPj0 : 0 < Pj0)
    (hNB : NB ≤ stepM * (Pj0 * (1 + ηf))) (hNB0 : 0 ≤ NB)
    (hB₁ : B₁ ≤ B₀ / Pj0) (hB₁0 : 0 ≤ B₁) (hB0 : 0 ≤ B₀) (hT₀ : 0 ≤ T₀)
    (hE : E ≤ CE * B₁ * WQ ^ 2 + CR) (hE0 : 0 ≤ E) (hCE : 0 ≤ CE) (hCR : 0 ≤ CR) :
    (NB / K) ^ 2 * ((5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * B₁) * E)
      ≤ stepM ^ 2 * (1 + ηf) ^ 2 / K ^ 2
        * ((5 * Real.pi / 2) * T₀ * CE * B₀ * WQ ^ 2 * Pj0
          + (5 * Real.pi / 2) * T₀ * CR * Pj0 ^ 2
          + (5 * Real.exp 1 / 2) * CE * B₀ ^ 2 * WQ ^ 2
          + (5 * Real.exp 1 / 2) * CR * B₀ * Pj0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have he : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have hK2 : (0 : ℝ) < K ^ 2 := by positivity
  have hWQ2 : (0 : ℝ) ≤ WQ ^ 2 := sq_nonneg _
  -- the first factor
  have h1 : (NB / K) ^ 2 ≤ stepM ^ 2 * Pj0 ^ 2 * (1 + ηf) ^ 2 / K ^ 2 := by
    have hsq : NB ^ 2 ≤ (stepM * (Pj0 * (1 + ηf))) ^ 2 := by nlinarith [hNB, hNB0]
    rw [div_pow, div_le_div_iff₀ hK2 hK2]
    nlinarith [hsq, hK2]
  -- the second factor
  have hpre : 5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * B₁
      ≤ 5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * (B₀ / Pj0) := by
    have := mul_le_mul_of_nonneg_left hB₁ (by positivity : (0:ℝ) ≤ 5 * Real.exp 1 / 2)
    linarith
  have hEle : E ≤ CE * (B₀ / Pj0) * WQ ^ 2 + CR := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hB₁ hCE) hWQ2
    linarith [hE, this]
  have hpre0 : (0 : ℝ) ≤ 5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * B₁ := by positivity
  have h2 : (5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * B₁) * E
      ≤ (5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * (B₀ / Pj0))
        * (CE * (B₀ / Pj0) * WQ ^ 2 + CR) := by
    have hEr0 : (0 : ℝ) ≤ CE * (B₀ / Pj0) * WQ ^ 2 + CR := by
      have : (0 : ℝ) ≤ CE * (B₀ / Pj0) * WQ ^ 2 := by positivity
      linarith
    exact mul_le_mul hpre hEle hE0 (by linarith [hpre0, hpre])
  -- combine
  have hfirst0 : (0 : ℝ) ≤ (NB / K) ^ 2 := sq_nonneg _
  have hmajf : (0 : ℝ) ≤ stepM ^ 2 * Pj0 ^ 2 * (1 + ηf) ^ 2 / K ^ 2 := by positivity
  have hmajs : (0 : ℝ) ≤ (5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * (B₀ / Pj0))
      * (CE * (B₀ / Pj0) * WQ ^ 2 + CR) := by
    have ha : (0 : ℝ) ≤ 5 * Real.pi / 2 * T₀ + 5 * Real.exp 1 / 2 * (B₀ / Pj0) := by positivity
    have hb : (0 : ℝ) ≤ CE * (B₀ / Pj0) * WQ ^ 2 + CR := by positivity
    exact mul_nonneg ha hb
  have hcomb := mul_le_mul h1 h2 (mul_nonneg hpre0 hE0) hmajf
  refine hcomb.trans (le_of_eq ?_)
  field_simp
  ring

end

end RHTower.Sieve
