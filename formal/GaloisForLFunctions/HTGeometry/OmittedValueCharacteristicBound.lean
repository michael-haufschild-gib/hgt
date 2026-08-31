import GaloisForLFunctions.HTGeometry.LogDerivOmittedValue

/-!
# The characteristic bound for a function omitting two values

Assembling the omitting second main theorem with the logarithmic-derivative estimate at an omitted
value gives, for entire `F` omitting `a₁ ≠ a₂` with `F'` zero-free,

```text
T(r,F) ≤ (3/α)·log(1 + (2R/(R−r)²·(2 T(R,F) + C))^α) + C'
```

for every `0 < r < R` with `1 ≤ R`, with constants depending only on `α`, the two values, and the
germ of `F` at the origin.  No counting function appears anywhere: the two `N(r,a_j)` vanish because
the values are omitted, the ramification term is Jensen's, and the divisor term of the
logarithmic-derivative estimate vanishes because every denominator is taken at an omitted value.

Choosing `R = r + T(r)^{-α}` and applying the Borel growth lemma at exponent `α` collapses the right
side to `O(log r + log T(r))`, which forces `T(r) = O(log r)`.
-/

namespace GaloisForLFunctions.HTGeometry

open ValueDistribution Metric Real

/-- The characteristic of an entire function is nonnegative. -/
theorem characteristic_nonneg_of_entire {F : ℂ → ℂ} (hF : Differentiable ℂ F) (r : ℝ) :
    0 ≤ characteristic F ⊤ r := by
  rw [GaloisForLFunctions.Nevanlinna.characteristic_top_eq_proximity_of_analyticOnNhd
    (fun z _ => hF.analyticAt z)]
  rw [ValueDistribution.proximity_top]
  refine Real.circleAverage_nonneg_of_nonneg ?_
  intro z _
  exact Real.posLog_nonneg

/-- The shift costs a constant in the characteristic. -/
theorem characteristic_sub_const_le {F : ℂ → ℂ} (hF : Differentiable ℂ F) (a : ℂ) (r : ℝ) :
    characteristic (fun w => F w - a) ⊤ r
      ≤ characteristic F ⊤ r + (Real.posLog ‖a‖ + Real.log 2) := by
  have hAF : AnalyticOnNhd ℂ F Set.univ := fun z _ => hF.analyticAt z
  have hAc : AnalyticOnNhd ℂ (fun _ : ℂ => -a) Set.univ := fun z _ => analyticAt_const
  have hadd := GaloisForLFunctions.Nevanlinna.characteristic_add_le hAF hAc r
  have hconst := GaloisForLFunctions.Nevanlinna.characteristic_const_eq (-a) r
  have hfun : (fun z => F z + -a) = fun z => F z - a := by funext z; ring
  rw [hfun, hconst, norm_neg] at hadd
  linarith

set_option maxHeartbeats 1000000 in
/-- **The quantitative no-go inequality.**  For an entire `F` omitting two values with a zero-free
derivative, the characteristic at radius `r` is bounded by a logarithm of the characteristic at any
larger radius `R`.  Every zero-counting term has vanished. -/
theorem characteristic_le_log_of_omits_two {F : ℂ → ℂ} (hF : Differentiable ℂ F)
    {a₁ a₂ : ℂ} (hane : a₁ ≠ a₂) (h₁ : ∀ z, F z ≠ a₁) (h₂ : ∀ z, F z ≠ a₂)
    (hF' : ∀ z, deriv F z ≠ 0) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) {K : ℝ}
    {r R : ℝ} (hr : 0 < r) (hrR : r < R) (hR : 1 ≤ R)
    (hfmt : ∀ j : Fin 2, characteristic F ⊤ r
      ≤ characteristic F ((![a₁, a₂] j : ℂ) : WithTop ℂ) r + K) :
    characteristic F ⊤ r
      ≤ (3 / α) * Real.log (1 + (2 * R / (R - r) ^ 2
          * (2 * characteristic F ⊤ R
            + (2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
              + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖|))) ^ α)
        + ((2 * K + 2 * Real.posLog (2 / ‖a₁ - a₂‖)
            + Real.posLog (2 * (2 / ‖a₁ - a₂‖)) + Real.log 2 + Real.log 2)
          - Real.log ‖deriv F 0‖ + (Real.posLog ‖a₁‖ + Real.log 2)) := by
  classical
  set X : ℝ := 2 * R / (R - r) ^ 2 with hX
  have hRpos : (0 : ℝ) < R := by linarith
  have hRr : (0 : ℝ) < R - r := by linarith
  have hX0 : 0 < X := by
    rw [hX]
    positivity
  set Cbig : ℝ := 2 * (Real.posLog ‖a₁‖ + Real.log 2) + 2 * (Real.posLog ‖a₂‖ + Real.log 2)
    + |Real.log ‖F 0 - a₁‖| + |Real.log ‖F 0 - a₂‖| with hCbig
  have hTR : 0 ≤ characteristic F ⊤ R := characteristic_nonneg_of_entire hF R
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- each logarithmic derivative is bounded by the same expression
  have hkey : ∀ a : ℂ, a = a₁ ∨ a = a₂ →
      2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|
        ≤ 2 * characteristic F ⊤ R + Cbig := by
    intro a ha12
    have hshift := characteristic_sub_const_le hF a R
    have habs : (0 : ℝ) ≤ |Real.log ‖F 0 - a‖| := abs_nonneg _
    rcases ha12 with rfl | rfl
    · have h2 : (0 : ℝ) ≤ 2 * (Real.posLog ‖a₂‖ + Real.log 2) := by
        have := Real.posLog_nonneg (x := ‖a₂‖)
        linarith
      have h3 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₂‖| := abs_nonneg _
      rw [hCbig]
      linarith
    · have h2 : (0 : ℝ) ≤ 2 * (Real.posLog ‖a₁‖ + Real.log 2) := by
        have := Real.posLog_nonneg (x := ‖a₁‖)
        linarith
      have h3 : (0 : ℝ) ≤ |Real.log ‖F 0 - a₁‖| := abs_nonneg _
      rw [hCbig]
      linarith
  have hbound : ∀ a : ℂ, (∀ z, F z ≠ a) → a = a₁ ∨ a = a₂ →
      proximity (fun z => deriv F z / (F z - a)) ⊤ r
        ≤ (1 / α) * Real.log (1 + (X * (2 * characteristic F ⊤ R + Cbig)) ^ α) := by
    intro a ha ha12
    refine le_trans (proximity_logDeriv_le_of_omits hα0 hα1 hr hrR hR hF ha) ?_
    have hmono : X * (2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|)
        ≤ X * (2 * characteristic F ⊤ R + Cbig) :=
      mul_le_mul_of_nonneg_left (hkey a ha12) hX0.le
    have hnn : (0 : ℝ) ≤ X * (2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖|) := by
      have h0 : 0 ≤ characteristic (fun w => F w - a) ⊤ R :=
        characteristic_nonneg_of_entire (hF.sub_const a) R
      have h1 : (0 : ℝ) ≤ |Real.log ‖F 0 - a‖| := abs_nonneg _
      have : (0 : ℝ) ≤ 2 * characteristic (fun w => F w - a) ⊤ R + |Real.log ‖F 0 - a‖| := by
        linarith
      positivity
    have hrpow := Real.rpow_le_rpow hnn hmono hα0.le
    have hlogle : Real.log (1 + (X * (2 * characteristic (fun w => F w - a) ⊤ R
          + |Real.log ‖F 0 - a‖|)) ^ α)
        ≤ Real.log (1 + (X * (2 * characteristic F ⊤ R + Cbig)) ^ α) := by
      refine Real.log_le_log (by positivity) (by linarith)
    have hαinv : (0 : ℝ) ≤ 1 / α := by positivity
    exact mul_le_mul_of_nonneg_left hlogle hαinv
  have hsmt := characteristic_le_of_omits_two_shifted hF hane h₁ h₂ hF' (ne_of_gt hr) hfmt
  have hb1 := hbound a₁ h₁ (Or.inl rfl)
  have hb2 := hbound a₂ h₂ (Or.inr rfl)
  have hthree : (3 : ℝ) / α = 3 * (1 / α) := by ring
  rw [hthree]
  linarith [hsmt, hb1, hb2]

end GaloisForLFunctions.HTGeometry
