import GaloisForLFunctions.RHTower.SuzukiGammaCommutatorBlock
import GaloisForLFunctions.HTGeometry.ExpEnvelopeAlgebra

/-!
# The localized value estimate on a terminal ray

The block bound for the Gamma cutoff commutator is literally an exponential envelope at rate one,
and the terminal Gamma block's coercive lower bound divides out.  Together they turn the localized
value equation into

`f_m ≤ y_m + g_m + b · (E₁ f)_m`

on a terminal ray, with `b` proportional to the reciprocal of the growing coercive constant.  The
mixed-rate absorption then bounds the slow envelope of the value by twice the slow envelope of the
flux and the source — the card's `(11)`.

A profile carried on a terminal ray has vanishing blocks below the threshold, so the pointwise
inequality extends to the whole lattice for free and no separate treatment of the initial blocks is
needed.
-/

open scoped ENNReal NNReal

noncomputable section

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-! ## The commutator block bound is an envelope -/

omit [NormedSpace ℝ X] in
/-- The block bound of the Gamma cutoff commutator is the rate-one envelope of the block norms. -/
theorem blockSum_eq_expEnvelope {Λ : ℝ} (hΛ : 0 ≤ Λ) (F : ℝ → X) (n : ℤ) :
    (∑' m : ℤ, ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) * blockNorm F m)
      = ENNReal.ofReal (4 * Λ * Real.exp 1) * expEnvelopeZ 1 (blockNorm F) n := by
  have hfac : ∀ m : ℤ,
      ENNReal.ofReal (4 * Λ * Real.exp 1 * Real.exp (-|(n : ℝ) - m|)) * blockNorm F m
        = ENNReal.ofReal (4 * Λ * Real.exp 1) * (expKernel 1 n m * blockNorm F m) := by
    intro m
    have hA : (0 : ℝ) ≤ 4 * Λ * Real.exp 1 := by positivity
    have hk : expKernel 1 n m = ENNReal.ofReal (Real.exp (-|(n : ℝ) - m|)) := by
      rw [expKernel]
      congr 2
      ring
    rw [hk, ← mul_assoc, ← ENNReal.ofReal_mul hA]
  rw [tsum_congr hfac, ENNReal.tsum_mul_left, expEnvelopeZ]

/-- **The Gamma cutoff commutator obeys the rate-one envelope bound.** -/
theorem enorm_gammaWallCommutator_le_envelope {χ : ℝ → ℝ} {Λ : ℝ} {F : ℝ → X}
    (hlip : ∀ x y, |χ x - χ y| ≤ Λ * |x - y|)
    (hzero : ∀ x : ℝ, x ≤ 0 → χ x = 0) (hone : ∀ x : ℝ, 1 ≤ x → χ x = 1)
    (hΛ : 0 ≤ Λ) (hFm : Measurable fun x => ‖F x‖ₑ)
    {n : ℤ} {L : ℝ} (hL : L ∈ Set.Icc (n : ℝ) ((n : ℝ) + 1)) :
    ‖gammaWallCommutator χ F L‖ₑ
      ≤ ENNReal.ofReal (4 * Λ * Real.exp 1) * expEnvelopeZ 1 (blockNorm F) n := by
  rw [← blockSum_eq_expEnvelope hΛ F n]
  exact enorm_gammaWallCommutator_le_blockSum hlip hzero hone hΛ hFm hL

/-! ## Dividing out the coercive constant -/

/-- A coercive lower bound divides out of a block inequality. -/
theorem block_div_of_coercive {c f w : ℝ≥0∞} (hc : c ≠ 0) (hc' : c ≠ ⊤) (h : c * f ≤ w) :
    f ≤ c⁻¹ * w := by
  have hinv : c⁻¹ * (c * f) ≤ c⁻¹ * w := mul_le_mul' le_rfl h
  rwa [← mul_assoc, ENNReal.inv_mul_cancel hc hc', one_mul] at hinv

/-! ## The localized value estimate -/

/-- **`(11)` at the sequence level.**  A profile carried on a terminal ray, dominated blockwise by
the flux and the source plus a small multiple of its own rate-`μ` envelope, has slow envelope at
most twice the slow envelopes of the flux and the source. -/
theorem blockValue_absorb {μ ν : ℝ} (hν : 0 ≤ ν) {f y g : ℤ → ℝ≥0∞} {b : ℝ≥0∞} {N n : ℤ}
    (hzero : ∀ m, m < N → f m = 0)
    (hpt : ∀ m, N ≤ m → f m ≤ y m + g m + b * expEnvelopeZ μ f m)
    (hfin : expEnvelopeZ ν f n ≠ ⊤)
    (hsmall : b * expRowMass (μ - ν) ≤ 1 / 2) :
    expEnvelopeZ ν f n ≤ 2 * expEnvelopeZ ν y n + 2 * expEnvelopeZ ν g n := by
  have hall : ∀ m : ℤ, f m ≤ (y m + g m) + b * expEnvelopeZ μ f m := by
    intro m
    rcases lt_or_ge m N with hm | hm
    · rw [hzero m hm]
      simp
    · exact le_trans (hpt m hm) (le_of_eq (by ring))
  have habs := expEnvelopeZ_absorb (ν := ν) (μ := μ) hν hall hfin hsmall
  rw [expEnvelopeZ_add] at habs
  calc expEnvelopeZ ν f n ≤ 2 * (expEnvelopeZ ν y n + expEnvelopeZ ν g n) := habs
    _ = 2 * expEnvelopeZ ν y n + 2 * expEnvelopeZ ν g n := by ring

/-- **The localized value estimate with an explicit coercive constant.**  Dividing the blockwise
coercive bound by the terminal constant and absorbing the commutator envelope. -/
theorem blockValue_of_coercive {μ ν : ℝ} (hν : 0 ≤ ν)
    {f y g : ℤ → ℝ≥0∞} {c e : ℝ≥0∞} {N n : ℤ}
    (hc : c ≠ 0) (hc' : c ≠ ⊤)
    (hzero : ∀ m, m < N → f m = 0)
    (hpt : ∀ m, N ≤ m → c * f m ≤ y m + g m + e * expEnvelopeZ μ f m)
    (hfin : expEnvelopeZ ν f n ≠ ⊤)
    (hsmall : (c⁻¹ * e) * expRowMass (μ - ν) ≤ 1 / 2) :
    expEnvelopeZ ν f n
      ≤ 2 * expEnvelopeZ ν (fun m => c⁻¹ * y m) n
        + 2 * expEnvelopeZ ν (fun m => c⁻¹ * g m) n := by
  refine blockValue_absorb (μ := μ) hν (b := c⁻¹ * e) (N := N) ?_ ?_ hfin hsmall
  · exact hzero
  · intro m hm
    have hdiv := block_div_of_coercive hc hc' (hpt m hm)
    calc f m ≤ c⁻¹ * (y m + g m + e * expEnvelopeZ μ f m) := hdiv
      _ = c⁻¹ * y m + c⁻¹ * g m + (c⁻¹ * e) * expEnvelopeZ μ f m := by ring

end GaloisForLFunctions.RHTower
