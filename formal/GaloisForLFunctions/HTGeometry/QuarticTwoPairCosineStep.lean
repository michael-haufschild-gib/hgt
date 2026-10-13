import GaloisForLFunctions.HTGeometry.VerticalShiftEnergyQuarticFamily

/-!
# The cosine step on two non-real pairs: the resolvent bound

Centre a real quartic with two non-real pairs:
`p = ((X − ξ)² + Y₁)((X + ξ)² + Y₂)`. On quartics the cosine step is exactly
`cos(aD)p = p − (a²/2)p'' + (a⁴/24)p⁗` (`evenQuarticStep (a²/2) (a⁴/24)`). Suppose the stepped
quartic again has two non-real pairs, `((X − u)² + V₁)((X + u)² + V₂)` (it keeps the centroid).
Then

`V₁ + V₂ ≤ Y₁ + Y₂ − 2a²` (`add_le_of_evenQuarticStep_twoPair`),

i.e. the imaginary energy `V₁ + V₂` drops by at least `a²` per surviving pair.

**Proof.** Comparing coefficients, `S = V₁ + V₂`, `D = V₁ − V₂`, `t = u²` satisfy
`S − 2t = c₂`, `2uD = c₁`, `t² + tS + (S² − D²)/4 = c₀`, with
`c₂ = Y₁ + Y₂ − 2ξ² − 6a²`, `c₁ = 2ξ(Y₁ − Y₂)`, `c₀ = (ξ² + Y₁)(ξ² + Y₂) − a²(Y₁ + Y₂ − 2ξ²) + a⁴`.
Hence `t` is a root of the resolvent `φ(τ) = (2τ + c₂/2)² − c₁²/(16τ) − c₀` (for `t > 0`), and
the claim is `t ≤ T₀ = ξ² + 2a²`. One computes
`φ(T₀) = 2a²(Y₁ + Y₂) + a²(Y₁ − Y₂)²/(2(ξ² + 2a²)) > 0`, and `φ` is increasing on `[T₀, ∞)`
because `2T₀ + c₂/2 = ξ² + a² + (Y₁ + Y₂)/2 > 0`; so `t > T₀` would give `φ(t) > 0`.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The centred two-pair quartic `((X − ξ)² + Y₁)((X + ξ)² + Y₂)`. -/
def twoPairQuartic' (ξ Y₁ Y₂ : ℝ) : ℝ[X] := ((X - C ξ) ^ 2 + C Y₁) * ((X + C ξ) ^ 2 + C Y₂)

theorem twoPairQuartic'_eq (ξ Y₁ Y₂ : ℝ) :
    twoPairQuartic' ξ Y₁ Y₂ =
      X ^ 4 + C (Y₁ + Y₂ - 2 * ξ ^ 2) * X ^ 2 + C (2 * ξ * (Y₁ - Y₂)) * X +
        C ((ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂)) := by
  apply Polynomial.funext; intro x
  simp [twoPairQuartic']
  ring

theorem evenQuarticStep_twoPairQuartic' (a ξ Y₁ Y₂ : ℝ) :
    evenQuarticStep (a ^ 2 / 2) (a ^ 4 / 24) (twoPairQuartic' ξ Y₁ Y₂) =
      X ^ 4 + C (Y₁ + Y₂ - 2 * ξ ^ 2 - 6 * a ^ 2) * X ^ 2 + C (2 * ξ * (Y₁ - Y₂)) * X +
        C ((ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂) - a ^ 2 * (Y₁ + Y₂ - 2 * ξ ^ 2) + a ^ 4) := by
  rw [twoPairQuartic'_eq]
  apply Polynomial.funext; intro x
  simp [evenQuarticStep, derivative_mul, derivative_pow]
  ring

/-- Coefficients of a monic quartic `X⁴ + C c₂ X² + C c₁ X + C c₀`. -/
theorem coeff_quartic (c₂ c₁ c₀ : ℝ) :
    (X ^ 4 + C c₂ * X ^ 2 + C c₁ * X + C c₀ : ℝ[X]).coeff 2 = c₂ ∧
      (X ^ 4 + C c₂ * X ^ 2 + C c₁ * X + C c₀ : ℝ[X]).coeff 1 = c₁ ∧
      (X ^ 4 + C c₂ * X ^ 2 + C c₁ * X + C c₀ : ℝ[X]).coeff 0 = c₀ := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [coeff_X_pow, coeff_X, coeff_C]

/-- The resolvent inequality, in coefficient form. -/
theorem twoPair_resolvent_bound {a ξ Y₁ Y₂ u V₁ V₂ : ℝ} (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (h2 : V₁ + V₂ - 2 * u ^ 2 = Y₁ + Y₂ - 2 * ξ ^ 2 - 6 * a ^ 2)
    (h1 : 2 * u * (V₁ - V₂) = 2 * ξ * (Y₁ - Y₂))
    (h0 : (u ^ 2 + V₁) * (u ^ 2 + V₂) =
      (ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂) - a ^ 2 * (Y₁ + Y₂ - 2 * ξ ^ 2) + a ^ 4) :
    V₁ + V₂ ≤ Y₁ + Y₂ - 2 * a ^ 2 := by
  -- Equivalent to `u² ≤ ξ² + 2a²`.
  suffices hu : u ^ 2 ≤ ξ ^ 2 + 2 * a ^ 2 by linarith
  by_contra hcon
  replace hcon := lt_of_not_ge hcon
  obtain ⟨t, ht⟩ : ∃ t, t = u ^ 2 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T, T = ξ ^ 2 + 2 * a ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b, b = (Y₁ + Y₂ - 2 * ξ ^ 2 - 6 * a ^ 2) / 2 := ⟨_, rfl⟩
  obtain ⟨c₀, hc₀⟩ : ∃ c₀, c₀ = (ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂) - a ^ 2 * (Y₁ + Y₂ - 2 * ξ ^ 2) + a ^ 4 :=
    ⟨_, rfl⟩
  rw [← ht, ← hT] at hcon
  have htT : 0 < t - T := by linarith
  have hTnn : 0 ≤ T := by rw [hT]; positivity
  have htpos : 0 < t := by linarith
  -- `ψ(t) = 0`, `ψ(τ) = τ(2τ + b)² − (ξ(Y₁ − Y₂))²/4 − c₀τ`.
  have hψ : t * (2 * t + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * t = 0 := by
    have hD : (u * (V₁ - V₂)) ^ 2 = (ξ * (Y₁ - Y₂)) ^ 2 := by
      have : u * (V₁ - V₂) = ξ * (Y₁ - Y₂) := by linarith
      rw [this]
    have hb' : b = (V₁ + V₂ - 2 * u ^ 2) / 2 := by rw [hb, h2]
    rw [hc₀, ← h0, ← hD, ht, hb']
    ring
  -- `ψ(T) ≥ 0`, `B(T) ≥ 0`, and `ψ(t) = ψ(T) + (t − T)(B(T) + 4(t − T)(t + 2T + b))`.
  have hψT : T * (2 * T + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * T =
      2 * a ^ 2 * ((Y₁ + Y₂) * T + (Y₁ - Y₂) ^ 2 / 4) := by
    rw [hT, hb, hc₀]; ring
  have hBT : 4 * (T * T + T * T + T * T) + 4 * b * (T + T) + b ^ 2 - c₀ =
      2 * a ^ 2 * (Y₁ + Y₂) + (Y₁ - Y₂) ^ 2 / 4 + 4 * T * (2 * T + b) := by
    rw [hT, hb, hc₀]; ring
  have hsplit : t * (2 * t + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * t =
      (T * (2 * T + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * T) +
        (t - T) * ((4 * (T * T + T * T + T * T) + 4 * b * (T + T) + b ^ 2 - c₀) +
          (t - T) * (4 * (t + 2 * T + b))) := by
    ring
  have h2Tb : 0 < 2 * T + b := by
    rw [hT, hb]; nlinarith [sq_nonneg ξ, sq_nonneg a]
  have hA : 0 ≤ T * (2 * T + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * T := by
    rw [hψT]; positivity
  have hB : 0 ≤ 4 * (T * T + T * T + T * T) + 4 * b * (T + T) + b ^ 2 - c₀ := by
    rw [hBT]; have := mul_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 4) hTnn) h2Tb.le
    have : 0 ≤ 2 * a ^ 2 * (Y₁ + Y₂) := by positivity
    nlinarith [sq_nonneg (Y₁ - Y₂)]
  have hC : 0 < (t - T) * (4 * (t + 2 * T + b)) := mul_pos htT (by linarith)
  have hpos : 0 < t * (2 * t + b) ^ 2 - (ξ * (Y₁ - Y₂)) ^ 2 / 4 - c₀ * t := by
    rw [hsplit]
    have : 0 < (t - T) * ((4 * (T * T + T * T + T * T) + 4 * b * (T + T) + b ^ 2 - c₀) +
        (t - T) * (4 * (t + 2 * T + b))) := mul_pos htT (by linarith)
    linarith
  linarith

/-- **Two pairs under the cosine step.** If `cos(aD)` of the centred two-pair quartic
`((X − ξ)² + Y₁)((X + ξ)² + Y₂)` (`Y₁, Y₂ > 0`) is again a product of two non-real pairs
`((X − u)² + V₁)((X + u)² + V₂)`, then `V₁ + V₂ ≤ Y₁ + Y₂ − 2a²`. No sign is needed on
`V₁, V₂`; when both are positive they are the squared heights of the two surviving pairs. -/
theorem add_le_of_evenQuarticStep_twoPair {a ξ Y₁ Y₂ u V₁ V₂ : ℝ} (hY₁ : 0 < Y₁) (hY₂ : 0 < Y₂)
    (h : evenQuarticStep (a ^ 2 / 2) (a ^ 4 / 24) (twoPairQuartic' ξ Y₁ Y₂) =
      twoPairQuartic' u V₁ V₂) :
    V₁ + V₂ ≤ Y₁ + Y₂ - 2 * a ^ 2 := by
  rw [evenQuarticStep_twoPairQuartic', twoPairQuartic'_eq] at h
  obtain ⟨l2, l1, l0⟩ := coeff_quartic (Y₁ + Y₂ - 2 * ξ ^ 2 - 6 * a ^ 2) (2 * ξ * (Y₁ - Y₂))
    ((ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂) - a ^ 2 * (Y₁ + Y₂ - 2 * ξ ^ 2) + a ^ 4)
  obtain ⟨r2, r1, r0⟩ := coeff_quartic (V₁ + V₂ - 2 * u ^ 2) (2 * u * (V₁ - V₂))
    ((u ^ 2 + V₁) * (u ^ 2 + V₂))
  rw [h] at l2 l1 l0
  have e2 : V₁ + V₂ - 2 * u ^ 2 = Y₁ + Y₂ - 2 * ξ ^ 2 - 6 * a ^ 2 := by rw [← r2, l2]
  have e1 : 2 * u * (V₁ - V₂) = 2 * ξ * (Y₁ - Y₂) := by rw [← r1, l1]
  have e0 : (u ^ 2 + V₁) * (u ^ 2 + V₂) =
      (ξ ^ 2 + Y₁) * (ξ ^ 2 + Y₂) - a ^ 2 * (Y₁ + Y₂ - 2 * ξ ^ 2) + a ^ 4 := by rw [← r0, l0]
  exact twoPair_resolvent_bound hY₁ hY₂ e2 e1 e0

end

end GaloisForLFunctions.HTGeometry
