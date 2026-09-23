import GaloisForLFunctions.RHTower.XiMassJetProfile

/-!
# The caustic-null jet operator on height states

The gain of the caustic-null hierarchy is not in any single height derivative — `∂_w F` is the same
size as `F`, because `Z′ = w/Z` is bounded on the cone.  It is in the *combination*

`4a⁴ − ∂_w²`,

whose symbol on the exterior carrier is `4a⁴ − a²w²/Z²`, and that vanishes at the balance slope.

On height states the combination is again a polynomial map: two jet steps advance the exponent by
two, and the undifferentiated term is embedded at the same exponent by multiplying its coefficients
by `R²`.  So

```text
4a⁴·S − S″ = state( 4a⁴R²·P − P⁽²⁾ ,  4a⁴R²·Q − Q⁽²⁾ )  at exponent j+2,
```

with `P⁽²⁾, Q⁽²⁾` the twice-stepped coefficients.  Everything needed to iterate the operator is
therefore polynomial data, and the only analytic input is the size of the symbol.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-! ## Linearity and embedding in the height ring -/

theorem xiHeightCoeff_sub (τ : ℂ) (P₁ Q₁ P₂ Q₂ : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    xiHeightCoeff τ (P₁ - P₂) (Q₁ - Q₂) j w
      = xiHeightCoeff τ P₁ Q₁ j w - xiHeightCoeff τ P₂ Q₂ j w := by
  rw [xiHeightCoeff, xiHeightCoeff, xiHeightCoeff]
  simp only [Polynomial.eval_sub]
  ring

theorem xiHeightCoeff_const_mul (τ : ℂ) (c : ℂ) (P Q : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    xiHeightCoeff τ (Polynomial.C c * P) (Polynomial.C c * Q) j w
      = c * xiHeightCoeff τ P Q j w := by
  rw [xiHeightCoeff, xiHeightCoeff]
  simp only [Polynomial.eval_mul, Polynomial.eval_C]
  ring

theorem xiHeightCoeff_embed {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) (P Q : Polynomial ℂ)
    (j m : ℕ) :
    xiHeightCoeff τ (P * xiMassRadiusPoly τ ^ m) (Q * xiMassRadiusPoly τ ^ m) (j + m) w
      = xiHeightCoeff τ P Q j w := by
  have hRne : (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) ≠ 0 := by
    intro hcon
    rw [hcon] at hw
    simp at hw
  rw [xiHeightCoeff, xiHeightCoeff]
  simp only [Polynomial.eval_mul, Polynomial.eval_pow, xiMassRadiusPoly_eval]
  rw [pow_add]
  field_simp

/-! ## The caustic operator on the coefficient quadruple -/

/-- The twice-stepped even `K₀` coefficient. -/
def xiJetTwoPA (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiJetStepPA a τ (xiJetStepPA a τ PA QB j) (xiJetStepQB a τ PA QB j) (j + 1)

/-- The twice-stepped odd `K₀` coefficient. -/
def xiJetTwoQA (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiJetStepQA a τ (xiJetStepQA a τ QA PB j) (xiJetStepPB a τ QA PB j) (j + 1)

/-- The twice-stepped even `K₁` coefficient. -/
def xiJetTwoPB (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiJetStepPB a τ (xiJetStepQA a τ QA PB j) (xiJetStepPB a τ QA PB j) (j + 1)

/-- The twice-stepped odd `K₁` coefficient. -/
def xiJetTwoQB (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiJetStepQB a τ (xiJetStepPA a τ PA QB j) (xiJetStepQB a τ PA QB j) (j + 1)

/-- The even `K₀` coefficient of the caustic combination. -/
def xiCausticPA (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (PA * xiMassRadiusPoly τ ^ (2 : ℕ)) - xiJetTwoPA a τ PA QB j

/-- The odd `K₀` coefficient of the caustic combination. -/
def xiCausticQA (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (QA * xiMassRadiusPoly τ ^ (2 : ℕ)) - xiJetTwoQA a τ QA PB j

/-- The even `K₁` coefficient of the caustic combination. -/
def xiCausticPB (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (PB * xiMassRadiusPoly τ ^ (2 : ℕ)) - xiJetTwoPB a τ QA PB j

/-- The odd `K₁` coefficient of the caustic combination. -/
def xiCausticQB (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (QB * xiMassRadiusPoly τ ^ (2 : ℕ)) - xiJetTwoQB a τ PA QB j

/-- **The caustic combination of a height-ring coefficient.** -/
theorem xiCausticCoeff_eq {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re) (a : ℝ)
    (P Q P₂ Q₂ : Polynomial ℂ) (j : ℕ) :
    xiHeightCoeff τ (Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (P * xiMassRadiusPoly τ ^ (2 : ℕ)) - P₂)
        (Polynomial.C (4 * (a : ℂ) ^ (4 : ℕ)) * (Q * xiMassRadiusPoly τ ^ (2 : ℕ)) - Q₂) (j + 2) w
      = 4 * (a : ℂ) ^ (4 : ℕ) * xiHeightCoeff τ P Q j w - xiHeightCoeff τ P₂ Q₂ (j + 2) w := by
  rw [xiHeightCoeff_sub, xiHeightCoeff_const_mul, xiHeightCoeff_embed hw]

/-- **The caustic operator on states.**  Two jet steps and one embedding. -/
theorem xiCaustic_state_eq {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (PA QA PB QB : Polynomial ℂ) (j : ℕ) :
    xiMassBesselState a τ
        (xiHeightCoeff τ (xiCausticPA a τ PA QB j) (xiCausticQA a τ QA PB j) (j + 2))
        (xiHeightCoeff τ (xiCausticPB a τ QA PB j) (xiCausticQB a τ PA QB j) (j + 2)) w
      = 4 * (a : ℂ) ^ (4 : ℕ)
          * xiMassBesselState a τ (xiHeightCoeff τ PA QA j) (xiHeightCoeff τ PB QB j) w
        - xiMassBesselState a τ
            (xiHeightCoeff τ (xiJetTwoPA a τ PA QB j) (xiJetTwoQA a τ QA PB j) (j + 2))
            (xiHeightCoeff τ (xiJetTwoPB a τ QA PB j) (xiJetTwoQB a τ PA QB j) (j + 2)) w := by
  rw [xiMassBesselState, xiMassBesselState, xiMassBesselState, xiCausticPA, xiCausticQA,
    xiCausticPB, xiCausticQB, xiCausticCoeff_eq hw, xiCausticCoeff_eq hw]
  ring

/-- **Two height steps.**  The derivative of the once-stepped state is the twice-stepped state. -/
theorem hasDerivAt_xiJetState_two {a : ℝ} {τ w : ℂ} (ha : 0 < a) (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (PA QA PB QB : Polynomial ℂ) (j : ℕ) :
    HasDerivAt
      (xiMassBesselState a τ
        (xiHeightCoeff τ (xiJetStepPA a τ PA QB j) (xiJetStepQA a τ QA PB j) (j + 1))
        (xiHeightCoeff τ (xiJetStepPB a τ QA PB j) (xiJetStepQB a τ PA QB j) (j + 1)))
      (xiMassBesselState a τ
        (xiHeightCoeff τ (xiJetTwoPA a τ PA QB j) (xiJetTwoQA a τ QA PB j) (j + 2))
        (xiHeightCoeff τ (xiJetTwoPB a τ QA PB j) (xiJetTwoQB a τ PA QB j) (j + 2)) w) w := by
  have h := hasDerivAt_xiJetState (a := a) (τ := τ) (w := w) ha hw
    (xiJetStepPA a τ PA QB j) (xiJetStepQA a τ QA PB j)
    (xiJetStepPB a τ QA PB j) (xiJetStepQB a τ PA QB j) (j + 1)
  rw [xiJetTwoPA, xiJetTwoQA, xiJetTwoPB, xiJetTwoQB]
  exact h

end

end RHTower
