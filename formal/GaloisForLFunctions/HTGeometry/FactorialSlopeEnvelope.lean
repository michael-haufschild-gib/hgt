import GaloisForLFunctions.HTGeometry.FactorialSlopeCoeffRatio
import GaloisForLFunctions.HTGeometry.FactorialRayEnvelope
import GaloisForLFunctions.HTGeometry.TruncatedJetCoeffBound

/-!
# The factorial envelope of a slope sequence

A sequence with a complex factorial slope is two-sidedly comparable, up to a fixed polynomial
factor, with the pure factorial envelope

`facEnv r 𝔞 n = (n!)^r · 𝔞ⁿ`,   `r = Re α`,  `𝔞 = ‖Λ‖ · e^{Re(α log α)}`.

Two inputs: the normalisation `aₙ / (C Λⁿ Γ(1+αn))` stays in a fixed annulus around `1` for `n ≥ 1`
because its defect is at most `e^{-c}`; and the modulus of the Gamma ray is the factorial envelope up
to a polynomial factor.  The geometric factors combine as
`‖Λ‖ⁿ · e^{n Re(α log α)} = 𝔞ⁿ`.

This is the form the endpoint remainder estimate consumes: it compares the remainder of an endpoint
expansion, bounded against `facEnv`, with the coefficient it is normalised by.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- The geometric ratio of the factorial envelope of a slope sequence. -/
def slopeRatio (α Λ : ℂ) : ℝ := ‖Λ‖ * Real.exp ((α * Complex.log α).re)

theorem slopeRatio_pos (hlam : Λ ≠ 0) : 0 < slopeRatio α Λ := by
  have h : (0 : ℝ) < ‖Λ‖ := norm_pos_iff.mpr hlam
  rw [slopeRatio]
  positivity

theorem norm_slopeModel (α Λ Cc : ℂ) (n : ℕ) :
    ‖slopeModel α Λ Cc n‖ = ‖Cc‖ * ‖Λ‖ ^ n * ‖Complex.Gamma (rayPoint α n)‖ := by
  rw [slopeModel, norm_mul, norm_mul, norm_pow]

/-- The geometric factors combine. -/
theorem pow_slopeRatio (α Λ : ℂ) (n : ℕ) :
    slopeRatio α Λ ^ n = ‖Λ‖ ^ n * Real.exp ((n : ℝ) * (α * Complex.log α).re) := by
  rw [slopeRatio, mul_pow, Real.exp_nat_mul]

/-- **The two-sided factorial envelope of a slope sequence.** -/
theorem exists_slope_envelope (hyp : FactorialSlope a α Λ Cc c) :
    ∃ (B : ℕ) (K : ℝ), 0 < K ∧ ∀ n : ℕ, 1 ≤ n →
      ‖a n‖ ≤ K * (n : ℝ) ^ B * facEnv α.re (slopeRatio α Λ) n
        ∧ facEnv α.re (slopeRatio α Λ) n ≤ K * (n : ℝ) ^ B * ‖a n‖ := by
  classical
  obtain ⟨B₁, C₁, hC₁, henv⟩ := exists_factorialRayEnvelope hyp.re_pos
  have hCc : (0 : ℝ) < ‖Cc‖ := norm_pos_iff.mpr hyp.Cc_ne
  have hlam : (0 : ℝ) < ‖Λ‖ := norm_pos_iff.mpr hyp.lam_ne
  have hc := hyp.c_pos
  -- the normalisation stays in a fixed annulus
  have hlow : (0 : ℝ) < 1 - Real.exp (-c) := by
    have : Real.exp (-c) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hann : ∀ n : ℕ, 1 ≤ n →
      (1 - Real.exp (-c)) ≤ ‖slopeNorm a α Λ Cc n‖ ∧ ‖slopeNorm a α Λ Cc n‖ ≤ 2 := by
    intro n hn
    have hdef := norm_slopeNorm_sub_one_le hyp n
    have hmono : Real.exp (-c * n) ≤ Real.exp (-c) := by
      refine Real.exp_le_exp.mpr ?_
      have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      nlinarith
    have hle1 : Real.exp (-c) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    have htri : (1 : ℝ) ≤ ‖slopeNorm a α Λ Cc n‖ + ‖slopeNorm a α Λ Cc n - 1‖ := by
      have h := norm_sub_le (slopeNorm a α Λ Cc n) (slopeNorm a α Λ Cc n - 1)
      simpa using h
    have hadd := norm_le_norm_add_norm_sub' (slopeNorm a α Λ Cc n) (1 : ℂ)
    rw [norm_one] at hadd
    constructor
    · linarith
    · linarith
  -- the model is the envelope
  have hmodel : ∀ n : ℕ, 1 ≤ n →
      ‖slopeModel α Λ Cc n‖ ≤ (‖Cc‖ * C₁) * (n : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) n
      ∧ facEnv α.re (slopeRatio α Λ) n
        ≤ (C₁ / ‖Cc‖) * (n : ℝ) ^ B₁ * ‖slopeModel α Λ Cc n‖ := by
    intro n hn
    obtain ⟨hup, hdown⟩ := henv n hn
    have hkey : facEnv α.re (slopeRatio α Λ) n
        = ‖Λ‖ ^ n * (((n.factorial : ℕ) : ℝ) ^ α.re
          * Real.exp ((n : ℝ) * (α * Complex.log α).re)) := by
      rw [facEnv, pow_slopeRatio]
      ring
    rw [norm_slopeModel, hkey]
    have hlamnn : (0 : ℝ) ≤ ‖Λ‖ ^ n := by positivity
    constructor
    · calc ‖Cc‖ * ‖Λ‖ ^ n * ‖Complex.Gamma (rayPoint α n)‖
          ≤ ‖Cc‖ * ‖Λ‖ ^ n * (C₁ * (n : ℝ) ^ B₁
            * (((n.factorial : ℕ) : ℝ) ^ α.re
              * Real.exp ((n : ℝ) * (α * Complex.log α).re))) := by
            have hnn : (0 : ℝ) ≤ ‖Cc‖ * ‖Λ‖ ^ n := by positivity
            exact mul_le_mul_of_nonneg_left hup hnn
        _ = ‖Cc‖ * C₁ * (n : ℝ) ^ B₁ * (‖Λ‖ ^ n * (((n.factorial : ℕ) : ℝ) ^ α.re
              * Real.exp ((n : ℝ) * (α * Complex.log α).re))) := by ring
    · calc ‖Λ‖ ^ n * (((n.factorial : ℕ) : ℝ) ^ α.re
            * Real.exp ((n : ℝ) * (α * Complex.log α).re))
          ≤ ‖Λ‖ ^ n * (C₁ * (n : ℝ) ^ B₁ * ‖Complex.Gamma (rayPoint α n)‖) :=
            mul_le_mul_of_nonneg_left hdown hlamnn
        _ = (C₁ / ‖Cc‖) * (n : ℝ) ^ B₁ * (‖Cc‖ * ‖Λ‖ ^ n * ‖Complex.Gamma (rayPoint α n)‖) := by
            field_simp
  -- assemble
  refine ⟨B₁, max (2 * (‖Cc‖ * C₁)) ((C₁ / ‖Cc‖) / (1 - Real.exp (-c))), ?_, ?_⟩
  · have h1 : (0 : ℝ) < 2 * (‖Cc‖ * C₁) := by positivity
    exact lt_of_lt_of_le h1 (le_max_left _ _)
  intro n hn
  obtain ⟨hlo, hhi⟩ := hann n hn
  obtain ⟨hmup, hmdown⟩ := hmodel n hn
  have hmodne := slopeModel_ne_zero hyp n
  have hmodpos : (0 : ℝ) < ‖slopeModel α Λ Cc n‖ := norm_pos_iff.mpr hmodne
  have hnorm : ‖a n‖ = ‖slopeNorm a α Λ Cc n‖ * ‖slopeModel α Λ Cc n‖ := by
    rw [slopeNorm, norm_div]
    field_simp
  have hnpow : (0 : ℝ) ≤ (n : ℝ) ^ B₁ := by positivity
  have hfacpos : 0 < facEnv α.re (slopeRatio α Λ) n :=
    facEnv_pos (r := α.re) (slopeRatio_pos hyp.lam_ne) n
  constructor
  · have hstep : ‖a n‖ ≤ 2 * ((‖Cc‖ * C₁) * (n : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) n) := by
      rw [hnorm]
      calc ‖slopeNorm a α Λ Cc n‖ * ‖slopeModel α Λ Cc n‖
          ≤ 2 * ‖slopeModel α Λ Cc n‖ :=
            mul_le_mul_of_nonneg_right hhi (le_of_lt hmodpos)
        _ ≤ 2 * ((‖Cc‖ * C₁) * (n : ℝ) ^ B₁ * facEnv α.re (slopeRatio α Λ) n) := by
            exact mul_le_mul_of_nonneg_left hmup (by norm_num)
    refine le_trans hstep ?_
    have hle := le_max_left (2 * (‖Cc‖ * C₁)) ((C₁ / ‖Cc‖) / (1 - Real.exp (-c)))
    nlinarith [hnpow, hfacpos, mul_nonneg hnpow (le_of_lt hfacpos)]
  · have hstep : facEnv α.re (slopeRatio α Λ) n
        ≤ ((C₁ / ‖Cc‖) / (1 - Real.exp (-c))) * (n : ℝ) ^ B₁ * ‖a n‖ := by
      have hmodle : ‖slopeModel α Λ Cc n‖ ≤ ‖a n‖ / (1 - Real.exp (-c)) := by
        rw [le_div_iff₀ hlow, hnorm]
        calc ‖slopeModel α Λ Cc n‖ * (1 - Real.exp (-c))
            ≤ ‖slopeModel α Λ Cc n‖ * ‖slopeNorm a α Λ Cc n‖ :=
              mul_le_mul_of_nonneg_left hlo (le_of_lt hmodpos)
          _ = ‖slopeNorm a α Λ Cc n‖ * ‖slopeModel α Λ Cc n‖ := by ring
      refine le_trans hmdown ?_
      have hfac : (0 : ℝ) ≤ (C₁ / ‖Cc‖) * (n : ℝ) ^ B₁ := by positivity
      calc (C₁ / ‖Cc‖) * (n : ℝ) ^ B₁ * ‖slopeModel α Λ Cc n‖
          ≤ (C₁ / ‖Cc‖) * (n : ℝ) ^ B₁ * (‖a n‖ / (1 - Real.exp (-c))) :=
            mul_le_mul_of_nonneg_left hmodle hfac
        _ = ((C₁ / ‖Cc‖) / (1 - Real.exp (-c))) * (n : ℝ) ^ B₁ * ‖a n‖ := by
            field_simp
    refine le_trans hstep ?_
    have hle := le_max_right (2 * (‖Cc‖ * C₁)) ((C₁ / ‖Cc‖) / (1 - Real.exp (-c)))
    nlinarith [hnpow, norm_nonneg (a n), mul_nonneg hnpow (norm_nonneg (a n))]

end

end GaloisForLFunctions.HTGeometry
