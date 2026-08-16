import GaloisForLFunctions.HTGeometry.InverseFamilyDerivative

/-!
# The amplitude surviving two integrations by parts decays quadratically

After two integrations by parts against a phase whose generator `C` is invertible, the remaining
amplitude is `[C⁻¹(C⁻¹)']'`, whose norm is bounded by

`3‖C⁻¹‖⁴‖C'‖² + ‖C⁻¹‖³‖C''‖`.

If the generator is a symbol of order zero with a uniformly bounded inverse — its first derivative
of size `w` and its second of size `w²` — then both terms carry exactly two powers of `w`, so the
surviving amplitude is `O(w²)`.  This is the quadratic decay that makes the remaining integral
absolutely convergent against a propagator ratio of any exponent below `2`, and it is the only place
the second derivative of the symbol is used.

Nothing here depends on what the weight `w` is; the estimates are stated for an arbitrary positive
weight and specialised to `w = (1+t)^{-1}` at the end.  The generality is not idle: on the inward
frequency ray the same symbol decays in `|t|`, not in `t`, and only the weight changes.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {R : Type*} [NormedRing R] [NormedAlgebra ℝ R] [CompleteSpace R]

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The surviving amplitude of the two-fold integration by parts is `O(w²)`**, for whatever
positive weight `w` controls the symbol's derivatives. -/
theorem norm_invFamilyProductDeriv_le_of_symbolDecay_weight {C C₁ C₂ : ℝ → R} {Λ c₁ c₂ w : ℝ}
    {t : ℝ} (hw0 : 0 < w)
    (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * w)
    (h₂ : ‖C₂ t‖ ≤ c₂ * w ^ 2) :
    ‖invFamilyProductDeriv C C₁ C₂ t‖ ≤ (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂) * w ^ 2 := by
  have hΛ0 : 0 ≤ Λ := le_trans (norm_nonneg _) hΛ
  have hD := hΛ
  have hDnn : (0 : ℝ) ≤ ‖invFamily C t‖ := norm_nonneg _
  have hc₁ : 0 ≤ c₁ := by
    have := le_trans (norm_nonneg _) h₁
    nlinarith [hw0]
  have hw2 : (0 : ℝ) < w ^ 2 := by positivity
  have hc₂ : 0 ≤ c₂ := by
    have := le_trans (norm_nonneg _) h₂
    nlinarith [hw2]
  have h4 : ‖invFamily C t‖ ^ 4 ≤ Λ ^ 4 := pow_le_pow_left₀ hDnn hD 4
  have h3 : ‖invFamily C t‖ ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ hDnn hD 3
  have hs₁ : ‖C₁ t‖ ^ 2 ≤ c₁ ^ 2 * w ^ 2 := by
    have := pow_le_pow_left₀ (norm_nonneg _) h₁ 2
    calc ‖C₁ t‖ ^ 2 ≤ (c₁ * w) ^ 2 := this
      _ = c₁ ^ 2 * w ^ 2 := by ring
  have hbase := norm_invFamilyProductDeriv_le C C₁ C₂ t
  have hstep₁ : 3 * ‖invFamily C t‖ ^ 4 * ‖C₁ t‖ ^ 2 ≤ 3 * Λ ^ 4 * c₁ ^ 2 * w ^ 2 :=
    calc 3 * ‖invFamily C t‖ ^ 4 * ‖C₁ t‖ ^ 2
        ≤ 3 * Λ ^ 4 * ‖C₁ t‖ ^ 2 :=
          mul_le_mul_of_nonneg_right
            (by nlinarith [h4] : 3 * ‖invFamily C t‖ ^ 4 ≤ 3 * Λ ^ 4) (sq_nonneg _)
      _ ≤ 3 * Λ ^ 4 * (c₁ ^ 2 * w ^ 2) := mul_le_mul_of_nonneg_left hs₁ (by positivity)
      _ = 3 * Λ ^ 4 * c₁ ^ 2 * w ^ 2 := by ring
  have hstep₂ : ‖invFamily C t‖ ^ 3 * ‖C₂ t‖ ≤ Λ ^ 3 * c₂ * w ^ 2 :=
    calc ‖invFamily C t‖ ^ 3 * ‖C₂ t‖
        ≤ Λ ^ 3 * ‖C₂ t‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
      _ ≤ Λ ^ 3 * (c₂ * w ^ 2) := mul_le_mul_of_nonneg_left h₂ (by positivity)
      _ = Λ ^ 3 * c₂ * w ^ 2 := by ring
  calc ‖invFamilyProductDeriv C C₁ C₂ t‖
      ≤ 3 * ‖invFamily C t‖ ^ 4 * ‖C₁ t‖ ^ 2 + ‖invFamily C t‖ ^ 3 * ‖C₂ t‖ := hbase
    _ ≤ 3 * Λ ^ 4 * c₁ ^ 2 * w ^ 2 + Λ ^ 3 * c₂ * w ^ 2 := add_le_add hstep₁ hstep₂
    _ = (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂) * w ^ 2 := by ring

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The second boundary term decays like the weight.**  It carries only one power of the symbol
derivative, so it is one power of `w` smaller than the first boundary term and no smaller; that
single power is already enough for square integrability on a terminal ray. -/
theorem norm_invFamilyProduct_le_of_symbolDecay_weight {C C₁ : ℝ → R} {Λ c₁ w : ℝ}
    {t : ℝ}
    (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * w) :
    ‖invFamilyProduct C C₁ t‖ ≤ (Λ ^ 3 * c₁) * w := by
  have hDnn : (0 : ℝ) ≤ ‖invFamily C t‖ := norm_nonneg _
  have h3 : ‖invFamily C t‖ ^ 3 ≤ Λ ^ 3 := pow_le_pow_left₀ hDnn hΛ 3
  calc ‖invFamilyProduct C C₁ t‖
      ≤ ‖invFamily C t‖ ^ 3 * ‖C₁ t‖ := norm_invFamilyProduct_le C C₁ t
    _ ≤ Λ ^ 3 * ‖C₁ t‖ := mul_le_mul_of_nonneg_right h3 (norm_nonneg _)
    _ ≤ Λ ^ 3 * (c₁ * w) := by
        refine mul_le_mul_of_nonneg_left h₁ ?_
        have : (0 : ℝ) ≤ ‖invFamily C t‖ ^ 3 := by positivity
        nlinarith [h3, this]
    _ = (Λ ^ 3 * c₁) * w := by ring

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The surviving amplitude of the two-fold integration by parts is `O((1+t)^{-2})`.** -/
theorem norm_invFamilyProductDeriv_le_of_symbolDecay {C C₁ C₂ : ℝ → R} {Λ c₁ c₂ : ℝ}
    {t : ℝ} (ht : 0 ≤ t)
    (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * (1 + t)⁻¹)
    (h₂ : ‖C₂ t‖ ≤ c₂ * ((1 + t)⁻¹) ^ 2) :
    ‖invFamilyProductDeriv C C₁ C₂ t‖
      ≤ (3 * Λ ^ 4 * c₁ ^ 2 + Λ ^ 3 * c₂) * ((1 + t)⁻¹) ^ 2 :=
  norm_invFamilyProductDeriv_le_of_symbolDecay_weight (by positivity) hΛ h₁ h₂

omit [NormedAlgebra ℝ R] [CompleteSpace R] in
/-- **The second boundary term decays linearly.** -/
theorem norm_invFamilyProduct_le_of_symbolDecay {C C₁ : ℝ → R} {Λ c₁ : ℝ}
    {t : ℝ} (_ht : 0 ≤ t)
    (hΛ : ‖invFamily C t‖ ≤ Λ)
    (h₁ : ‖C₁ t‖ ≤ c₁ * (1 + t)⁻¹) :
    ‖invFamilyProduct C C₁ t‖ ≤ (Λ ^ 3 * c₁) * (1 + t)⁻¹ :=
  norm_invFamilyProduct_le_of_symbolDecay_weight hΛ h₁

end GaloisForLFunctions.HTGeometry
