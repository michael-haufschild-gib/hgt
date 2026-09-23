import GaloisForLFunctions.RHTower.XiMassHeightCoeffRing

/-!
# The jet recursion on height states

A state `A·K₀(aZ) + B·K₁(aZ)` whose coefficients lie in the height ring differentiates to a state
whose coefficients lie in the height ring one exponent higher.  Writing both coefficients over the
common denominator `R^j` and using `Z² = R`,

`a(w/Z)·(P + QZ)/R^j = a w(QR + PZ)/R^{j+1}`,  `(w/Z²)·(P + QZ)/R^j = w(P + QZ)/R^{j+1}`,

so the whole step is the polynomial map

```text
PA ↦ PA′R − 2j·wPA − a·wQB·R
QA ↦ QA′R + (1−2j)wQA − a·wPB
PB ↦ PB′R − 2j·wPB − a·wQA·R − wPB
QB ↦ QB′R + (1−2j)wQB − a·wPA − wQB
```

with the exponent advancing by one.  Iterating this map is the caustic-null jet hierarchy: no
asymptotic expansion appears anywhere, only a fixed polynomial recursion.
-/

open Complex Polynomial

namespace RHTower

noncomputable section

/-- The even coefficient of `K₀` after one height step. -/
def xiJetStepPA (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiHeightCoeffDerivFst τ PA j - Polynomial.C (a : ℂ) * (Polynomial.X * QB) * xiMassRadiusPoly τ

/-- The odd coefficient of `K₀` after one height step. -/
def xiJetStepQA (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiHeightCoeffDerivSnd τ QA j - Polynomial.C (a : ℂ) * (Polynomial.X * PB)

/-- The even coefficient of `K₁` after one height step. -/
def xiJetStepPB (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiHeightCoeffDerivFst τ PB j - Polynomial.C (a : ℂ) * (Polynomial.X * QA) * xiMassRadiusPoly τ
    - Polynomial.X * PB

/-- The odd coefficient of `K₁` after one height step. -/
def xiJetStepQB (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) : Polynomial ℂ :=
  xiHeightCoeffDerivSnd τ QB j - Polynomial.C (a : ℂ) * (Polynomial.X * PA)
    - Polynomial.X * QB

theorem xiJetStepPA_eval (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiJetStepPA a τ PA QB j).eval w
      = PA.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) - 2 * (j : ℂ) * (w * PA.eval w)
        - (a : ℂ) * (w * QB.eval w) * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) := by
  rw [xiJetStepPA]
  simp [xiHeightCoeffDerivFst_eval, xiMassRadiusPoly_eval]

theorem xiJetStepQA_eval (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiJetStepQA a τ QA PB j).eval w
      = QA.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) + (1 - 2 * (j : ℂ)) * (w * QA.eval w)
        - (a : ℂ) * (w * PB.eval w) := by
  rw [xiJetStepQA]
  simp [xiHeightCoeffDerivSnd_eval]

theorem xiJetStepPB_eval (a : ℝ) (τ : ℂ) (QA PB : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiJetStepPB a τ QA PB j).eval w
      = PB.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) - 2 * (j : ℂ) * (w * PB.eval w)
        - (a : ℂ) * (w * QA.eval w) * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) - w * PB.eval w := by
  rw [xiJetStepPB]
  simp [xiHeightCoeffDerivFst_eval, xiMassRadiusPoly_eval]

theorem xiJetStepQB_eval (a : ℝ) (τ : ℂ) (PA QB : Polynomial ℂ) (j : ℕ) (w : ℂ) :
    (xiJetStepQB a τ PA QB j).eval w
      = QB.derivative.eval w * (τ ^ (2 : ℕ) + w ^ (2 : ℕ)) + (1 - 2 * (j : ℂ)) * (w * QB.eval w)
        - (a : ℂ) * (w * PA.eval w) - w * QB.eval w := by
  rw [xiJetStepQB]
  simp [xiHeightCoeffDerivSnd_eval]

/-- The `K₀` coefficient of the derivative, in the height ring. -/
theorem xiJetStep_fst {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (PA QA PB QB : Polynomial ℂ) (j : ℕ) :
    xiHeightCoeff τ (xiHeightCoeffDerivFst τ PA j) (xiHeightCoeffDerivSnd τ QA j) (j + 1) w
        - (a : ℂ) * (w / xiMassHeightRadius τ w) * xiHeightCoeff τ PB QB j w
      = xiHeightCoeff τ (xiJetStepPA a τ PA QB j) (xiJetStepQA a τ QA PB j) (j + 1) w := by
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZ2 : xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := xiMassHeightRadius_sq hw
  rw [xiHeightCoeff, xiHeightCoeff, xiHeightCoeff, xiHeightCoeffDerivFst_eval,
    xiHeightCoeffDerivSnd_eval, xiJetStepPA_eval, xiJetStepQA_eval, ← hZ2]
  field_simp
  ring

/-- The `K₁` coefficient of the derivative, in the height ring. -/
theorem xiJetStep_snd {a : ℝ} {τ w : ℂ} (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (PA QA PB QB : Polynomial ℂ) (j : ℕ) :
    xiHeightCoeff τ (xiHeightCoeffDerivFst τ PB j) (xiHeightCoeffDerivSnd τ QB j) (j + 1) w
        - (a : ℂ) * (w / xiMassHeightRadius τ w) * xiHeightCoeff τ PA QA j w
        - w / xiMassHeightRadius τ w ^ (2 : ℕ) * xiHeightCoeff τ PB QB j w
      = xiHeightCoeff τ (xiJetStepPB a τ QA PB j) (xiJetStepQB a τ PA QB j) (j + 1) w := by
  have hZne : xiMassHeightRadius τ w ≠ 0 := xiMassHeightRadius_ne_zero hw
  have hZ2 : xiMassHeightRadius τ w ^ (2 : ℕ) = τ ^ (2 : ℕ) + w ^ (2 : ℕ) := xiMassHeightRadius_sq hw
  rw [xiHeightCoeff, xiHeightCoeff, xiHeightCoeff, xiHeightCoeff, xiHeightCoeffDerivFst_eval,
    xiHeightCoeffDerivSnd_eval, xiJetStepPB_eval, xiJetStepQB_eval, ← hZ2]
  field_simp
  ring

/-- **One height step of a jet state.**  The derivative of a state with height-ring coefficients at
exponent `j` is the state with the stepped coefficients at exponent `j+1`. -/
theorem hasDerivAt_xiJetState {a : ℝ} {τ w : ℂ} (ha : 0 < a) (hw : 0 < (τ ^ (2 : ℕ) + w ^ (2 : ℕ)).re)
    (PA QA PB QB : Polynomial ℂ) (j : ℕ) :
    HasDerivAt
      (xiMassBesselState a τ (xiHeightCoeff τ PA QA j) (xiHeightCoeff τ PB QB j))
      (xiMassBesselState a τ
        (xiHeightCoeff τ (xiJetStepPA a τ PA QB j) (xiJetStepQA a τ QA PB j) (j + 1))
        (xiHeightCoeff τ (xiJetStepPB a τ QA PB j) (xiJetStepQB a τ PA QB j) (j + 1)) w) w := by
  have hA := hasDerivAt_xiHeightCoeff (τ := τ) (w := w) PA QA j hw
  have hB := hasDerivAt_xiHeightCoeff (τ := τ) (w := w) PB QB j hw
  have hstate := hasDerivAt_xiMassBesselState ha hw hA hB
  have hval : (xiHeightCoeff τ (xiHeightCoeffDerivFst τ PA j) (xiHeightCoeffDerivSnd τ QA j)
            (j + 1) w
          - (a : ℂ) * (w / xiMassHeightRadius τ w) * xiHeightCoeff τ PB QB j w)
        * xiMassHeightK0 a τ w
      + (xiHeightCoeff τ (xiHeightCoeffDerivFst τ PB j) (xiHeightCoeffDerivSnd τ QB j) (j + 1) w
          - (a : ℂ) * (w / xiMassHeightRadius τ w) * xiHeightCoeff τ PA QA j w
          - w / xiMassHeightRadius τ w ^ (2 : ℕ) * xiHeightCoeff τ PB QB j w)
        * xiMassHeightK1 a τ w
      = xiMassBesselState a τ
          (xiHeightCoeff τ (xiJetStepPA a τ PA QB j) (xiJetStepQA a τ QA PB j) (j + 1))
          (xiHeightCoeff τ (xiJetStepPB a τ QA PB j) (xiJetStepQB a τ PA QB j) (j + 1)) w := by
    rw [xiMassBesselState, xiJetStep_fst hw PA QA PB QB j, xiJetStep_snd hw PA QA PB QB j]
  rw [← hval]
  exact hstate

end

end RHTower
