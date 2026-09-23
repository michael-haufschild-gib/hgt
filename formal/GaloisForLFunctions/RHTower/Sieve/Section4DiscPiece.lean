import GaloisForLFunctions.RHTower.Sieve.Section4NonExcPiece

/-!
# The disc piece of one short block

The second of the five pieces of `Sieve/Section4BlockMaster.section4_block_master`.  On the
low-frequency disc both prime polynomials are bounded trivially and the saving is entirely in the
cofactor, whose low-frequency bound `Sieve/CofactorLowFreqBound` gives a factor `S` better than
every power of the logarithm.

Per long block the two trivial factors cancel exactly:

```text
   (#Q_k)²·I_k  ≤  (Q_k(1+η_Q))²·((B₁/Q_k)·S)²·2w₀  =  (1+η_Q)²·B₁²·S²·2w₀ ,
```

so the sum over the `L_Q` long blocks is `L_Q·(1+η_Q)²B₁²S²·2w₀` — the block scale has vanished.
At the outer level `Pj1²·B₁² ≤ (1+η_P)²B₀²` collapses the short scale in the same way, leaving the
whole disc piece proportional to `stepMass_j²·B₀²·S²`, which beats the target
`ε·stepMass_j²·B₀²·W_Q²` because `S` beats every power of the logarithm.
-/

namespace RHTower.Sieve

noncomputable section

/-- **One long block on the disc.**  The block scale cancels. -/
theorem disc_term_le {NQ Qk0 B₁ S w₀ ηQ Idisc : ℝ}
    (hQk0 : 0 < Qk0) (hNQ : NQ ≤ Qk0 * (1 + ηQ)) (hNQ0 : 0 ≤ NQ)
    (hIdisc : Idisc ≤ (B₁ / Qk0 * S) ^ (2 : ℕ) * (2 * w₀)) (hIdisc0 : 0 ≤ Idisc) :
    NQ ^ (2 : ℕ) * Idisc ≤ (1 + ηQ) ^ (2 : ℕ) * B₁ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀) := by
  have hNQsq : NQ ^ (2 : ℕ) ≤ (Qk0 * (1 + ηQ)) ^ (2 : ℕ) := by nlinarith [hNQ, hNQ0]
  have hstep : NQ ^ (2 : ℕ) * Idisc ≤ (Qk0 * (1 + ηQ)) ^ (2 : ℕ) * ((B₁ / Qk0 * S) ^ (2 : ℕ) * (2 * w₀)) := by
    have h0 : (0 : ℝ) ≤ (Qk0 * (1 + ηQ)) ^ (2 : ℕ) := sq_nonneg _
    exact mul_le_mul hNQsq hIdisc hIdisc0 h0
  refine hstep.trans (le_of_eq ?_)
  field_simp
  try ring

/-- **The disc piece of one short block.**  The short scale cancels too. -/
theorem disc_block_le {NB stepM Pj0 B₀ B₁ Sig Dfct LQ S w₀ ηP ηQ : ℝ}
    (hPj0 : 0 < Pj0)
    (hNB : NB ≤ stepM * (Pj0 * (1 + ηP))) (hNB0 : 0 ≤ NB)
    (hB₁ : B₁ ≤ B₀ / Pj0) (hB₁0 : 0 ≤ B₁) (hB₀ : 0 ≤ B₀) (hLQ : 0 ≤ LQ) (hDfct : 0 ≤ Dfct)
    (hSig : Sig ≤ LQ * ((1 + ηQ) ^ (2 : ℕ) * B₁ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀))) (hSig0 : 0 ≤ Sig)
    (hw₀ : 0 ≤ w₀) :
    NB ^ (2 : ℕ) * (2 * (LQ * Sig) + 2 * Dfct)
      ≤ stepM ^ (2 : ℕ) * (1 + ηP) ^ (2 : ℕ)
          * (2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * B₀ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀)))
        + stepM ^ (2 : ℕ) * Pj0 ^ (2 : ℕ) * (1 + ηP) ^ (2 : ℕ) * (2 * Dfct) := by
  have hNBsq : NB ^ (2 : ℕ) ≤ stepM ^ (2 : ℕ) * Pj0 ^ (2 : ℕ) * (1 + ηP) ^ (2 : ℕ) := by
    have h1 : NB ^ (2 : ℕ) ≤ (stepM * (Pj0 * (1 + ηP))) ^ (2 : ℕ) := by nlinarith [hNB, hNB0]
    nlinarith [h1]
  have hS2 : (0 : ℝ) ≤ S ^ (2 : ℕ) := sq_nonneg _
  have hη2 : (0 : ℝ) ≤ (1 + ηQ) ^ (2 : ℕ) := sq_nonneg _
  have hB12 : (0 : ℝ) ≤ B₁ ^ (2 : ℕ) := sq_nonneg _
  -- the inner sum, with the short scale removed
  have hB1sq : Pj0 ^ (2 : ℕ) * B₁ ^ (2 : ℕ) ≤ B₀ ^ (2 : ℕ) := by
    have hmul : Pj0 * B₁ ≤ B₀ := by
      have hstep := mul_le_mul_of_nonneg_left hB₁ hPj0.le
      rwa [mul_div_cancel₀ _ (ne_of_gt hPj0)] at hstep
    have hprod0 : (0 : ℝ) ≤ Pj0 * B₁ := mul_nonneg hPj0.le hB₁0
    have hsq : (Pj0 * B₁) ^ (2 : ℕ) ≤ B₀ ^ (2 : ℕ) := by nlinarith [hmul, hprod0, hB₀]
    nlinarith [hsq]
  have hinner : Pj0 ^ (2 : ℕ) * (1 + ηP) ^ (2 : ℕ) * (2 * (LQ * Sig))
      ≤ (1 + ηP) ^ (2 : ℕ) * (2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * B₀ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀))) := by
    have hSigle : LQ * Sig ≤ LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * B₁ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀)) := by
      nlinarith [hSig, hLQ, hSig0]
    have hstep : Pj0 ^ (2 : ℕ) * (2 * (LQ * Sig))
        ≤ 2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * (Pj0 ^ (2 : ℕ) * B₁ ^ (2 : ℕ)) * S ^ (2 : ℕ) * (2 * w₀)) := by
      nlinarith [hSigle, hPj0, sq_nonneg Pj0]
    have hstep2 : 2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * (Pj0 ^ (2 : ℕ) * B₁ ^ (2 : ℕ)) * S ^ (2 : ℕ) * (2 * w₀))
        ≤ 2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * B₀ ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀)) := by
      have hc : (0 : ℝ) ≤ 2 * LQ ^ (2 : ℕ) * ((1 + ηQ) ^ (2 : ℕ) * S ^ (2 : ℕ) * (2 * w₀)) := by positivity
      nlinarith [hB1sq, hc]
    nlinarith [hstep, hstep2, sq_nonneg (1 + ηP)]
  have hsum0 : (0 : ℝ) ≤ 2 * (LQ * Sig) + 2 * Dfct := by
    have : (0 : ℝ) ≤ LQ * Sig := mul_nonneg hLQ hSig0
    linarith
  have hstepM : NB ^ (2 : ℕ) * (2 * (LQ * Sig) + 2 * Dfct)
      ≤ stepM ^ (2 : ℕ) * Pj0 ^ (2 : ℕ) * (1 + ηP) ^ (2 : ℕ) * (2 * (LQ * Sig) + 2 * Dfct) :=
    mul_le_mul_of_nonneg_right hNBsq hsum0
  refine hstepM.trans ?_
  have hstepM0 : (0 : ℝ) ≤ stepM ^ (2 : ℕ) := sq_nonneg _
  nlinarith [hinner, hstepM0]

end

end RHTower.Sieve
