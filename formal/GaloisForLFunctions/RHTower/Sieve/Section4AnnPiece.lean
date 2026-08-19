import GaloisForLFunctions.RHTower.Sieve.Section4DiscPiece

/-!
# The exceptional-annulus piece of one short block

The third of the five pieces of `Sieve/Section4BlockMaster.section4_block_master`, and the one that
carries §4's actual saving.  On the annulus the short prime polynomial is bounded trivially and the
long one carries the Route-T factor `ρ'`, while Halász–Montgomery supplies the innermost cofactor's
mean square in terms of the exceptional measure.

Per long block the block scale again cancels between the two:

```text
   V_k²·I_k  ≤  (ρ'·Q_k)²·(2π)⁻¹·(2(B₁/Q_k) + C·|E|)·(B₁/Q_k)
             =  ρ'²·(2π)⁻¹·(2B₁² + C·|E|·B₁·Q_k) ,
```

the first summand carrying `ρ'²` — which beats every power of the logarithm — and the second being
the Halász–Montgomery cross term, `x^{1/4+o(1)}` against `B₀ = x^{1/2}`.
-/

namespace RHTower.Sieve

noncomputable section

/-- **One long block on the annulus.**  The block scale cancels in the first summand and survives
only in the Halász–Montgomery cross term. -/
theorem ann_term_le {Vk Qk0 B₁ ρ' Cw Ej Iann : ℝ}
    (hQk0 : 0 < Qk0) (hVk : Vk ≤ ρ' * Qk0) (hVk0 : 0 ≤ Vk)
    (hIann : Iann ≤ (2 * Real.pi)⁻¹ * (2 * (B₁ / Qk0) + Cw * Ej) * (B₁ / Qk0))
    (hIann0 : 0 ≤ Iann) :
    Vk ^ 2 * Iann ≤ ρ' ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B₁ ^ 2 + Cw * Ej * B₁ * Qk0)) := by
  have hVsq : Vk ^ 2 ≤ ρ' ^ 2 * Qk0 ^ 2 := by nlinarith [hVk, hVk0]
  have hmaj : (0 : ℝ) ≤ ρ' ^ 2 * Qk0 ^ 2 := by positivity
  have hstep : Vk ^ 2 * Iann
      ≤ (ρ' ^ 2 * Qk0 ^ 2)
        * ((2 * Real.pi)⁻¹ * (2 * (B₁ / Qk0) + Cw * Ej) * (B₁ / Qk0)) :=
    mul_le_mul hVsq hIann hIann0 hmaj
  refine hstep.trans (le_of_eq ?_)
  field_simp
  try ring

/-- **The annulus piece of one short block.**  The short scale cancels in the main term and leaves
one factor `Pj0` in the cross term. -/
theorem ann_block_le {NB stepM Pj0 Sig Dfct LQ ηP : ℝ}
    (hPj0 : 0 < Pj0)
    (hNB : NB ≤ stepM * (Pj0 * (1 + ηP))) (hNB0 : 0 ≤ NB)
    (hLQ : 0 ≤ LQ) (hDfct : 0 ≤ Dfct) (hSig0 : 0 ≤ Sig) {M : ℝ}
    (hSig : Sig ≤ M) :
    NB ^ 2 * (2 * (LQ * Sig) + 2 * Dfct)
      ≤ stepM ^ 2 * Pj0 ^ 2 * (1 + ηP) ^ 2 * (2 * (LQ * M) + 2 * Dfct) := by
  have hNBsq : NB ^ 2 ≤ stepM ^ 2 * Pj0 ^ 2 * (1 + ηP) ^ 2 := by
    have h1 : NB ^ 2 ≤ (stepM * (Pj0 * (1 + ηP))) ^ 2 := by nlinarith [hNB, hNB0]
    nlinarith [h1]
  have hsum0 : (0 : ℝ) ≤ 2 * (LQ * Sig) + 2 * Dfct := by
    have : (0 : ℝ) ≤ LQ * Sig := mul_nonneg hLQ hSig0
    linarith
  have hsumle : 2 * (LQ * Sig) + 2 * Dfct ≤ 2 * (LQ * M) + 2 * Dfct := by
    nlinarith [hSig, hLQ]
  have hmaj0 : (0 : ℝ) ≤ stepM ^ 2 * Pj0 ^ 2 * (1 + ηP) ^ 2 := by positivity
  exact mul_le_mul hNBsq hsumle hsum0 hmaj0

/-- **The main-term half of the annulus sum, with the short scale removed.** -/
theorem ann_main_le {Pj0 B₀ B₁ ρ' LQ ηP : ℝ} (hPj0 : 0 < Pj0) (hB₁ : B₁ ≤ B₀ / Pj0)
    (hB₁0 : 0 ≤ B₁) (hB₀ : 0 ≤ B₀) :
    Pj0 ^ 2 * (1 + ηP) ^ 2 * (2 * (LQ * (LQ * (ρ' ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B₁ ^ 2))))))
      ≤ (1 + ηP) ^ 2 * (2 * LQ ^ 2 * (ρ' ^ 2 * ((2 * Real.pi)⁻¹ * (2 * B₀ ^ 2)))) := by
  have hmul : Pj0 * B₁ ≤ B₀ := by
    have hstep := mul_le_mul_of_nonneg_left hB₁ hPj0.le
    rwa [mul_div_cancel₀ _ (ne_of_gt hPj0)] at hstep
  have hprod0 : (0 : ℝ) ≤ Pj0 * B₁ := mul_nonneg hPj0.le hB₁0
  have hsq : (Pj0 * B₁) ^ 2 ≤ B₀ ^ 2 := by nlinarith [hmul, hprod0, hB₀]
  have hB1sq : Pj0 ^ 2 * B₁ ^ 2 ≤ B₀ ^ 2 := by nlinarith [hsq]
  have hpi : (0 : ℝ) < (2 * Real.pi)⁻¹ := by positivity
  have hc : (0 : ℝ) ≤ (1 + ηP) ^ 2 * (4 * LQ ^ 2 * (ρ' ^ 2 * (2 * Real.pi)⁻¹)) := by positivity
  nlinarith [hB1sq, hc]

end

end RHTower.Sieve
