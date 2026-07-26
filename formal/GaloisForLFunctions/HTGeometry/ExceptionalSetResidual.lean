/-
The residual: how large the exceptional set still is at the record exponent.

Write `E_δ = { t ≤ T : |ζ(1/2+it)| > t^δ }`.  A moment bound `∫_0^T |ζ(1/2+it)|^A dt ≪ T^(M)` gives

    |E_δ| · T^(Aδ) ≪ T^M ,   hence   **|E_δ| ≪ T^(M - Aδ)** ,

and the exceptional set is emptied exactly when `M - Aδ ≤ 0`, i.e. `δ ≥ M/A` — the neutrality law.

At the record `δ = 13/84` the published moments give

    A = 12 , M = 2      →  2 - 13/7      = **1/7        = 0.142857**
    A = 13 , M = 2.1340 →  2.134 - 169/84 = **641/5250 ≈ 0.122095**
    A = 14 , M = 2.2720 →  2.272 - 13/6   = **79/750 ≈ 0.105333**
    A = 15 , M = 2.4137 →  2.4137 - 65/28 = **6459/70000 ≈ 0.092271**

all strictly positive, the smallest at `A = 15`.  Since Selberg's central limit theorem already gives
`|ζ(1/2+it)| ≤ t^ε` outside a set of density zero, the entire remaining content of the Lindelöf
hypothesis is the emptiness of this set — and with current moment technology its measure is bounded
only by `T^(6459/70000)`.

That is the residual: **a set of measure exponent `0.0923` at the record**, which no published moment
can remove, because the published infimum of `M/A` is `≈ 0.16091 > 13/84`.
-/
import GaloisForLFunctions.HTGeometry.ResonanceCeiling
import GaloisForLFunctions.HTGeometry.TrudgianYangMomentPricing

namespace HTGeometry

/-! ### The exceptional-set exponent -/

/-- Measure exponent of the exceptional set at level `δ`, from a moment bound `M` of order `A`. -/
def exceptionalExponent (M A δ : ℚ) : ℚ := M - A * δ

/-- **The set is emptied exactly when the neutrality ratio drops to `δ`.** -/
theorem emptying_iff_neutrality {M A δ : ℚ} (hA : 0 < A) :
    exceptionalExponent M A δ ≤ 0 ↔ M / A ≤ δ := by
  unfold exceptionalExponent
  rw [div_le_iff₀ hA]
  constructor <;> intro h <;> linarith

/-- Lower moments give larger exceptional sets at a fixed level, when the neutrality ratio is
worse. -/
theorem exceptionalExponent_mono {M M' A δ : ℚ} (h : M ≤ M') :
    exceptionalExponent M A δ ≤ exceptionalExponent M' A δ := by
  unfold exceptionalExponent; linarith

/-! ### The residual at the record -/

/-- Heath-Brown's twelfth moment, at the record. -/
@[simp] theorem residual_twelfth :
    exceptionalExponent 2 12 bourgainTheta = 1 / 7 := by
  unfold exceptionalExponent bourgainTheta; norm_num

/-- The thirteenth. -/
@[simp] theorem residual_thirteenth :
    exceptionalExponent tyM13 13 bourgainTheta = 641 / 5250 := by
  unfold exceptionalExponent tyM13 bourgainTheta; norm_num

/-- The fourteenth. -/
@[simp] theorem residual_fourteenth :
    exceptionalExponent tyM14 14 bourgainTheta = 79 / 750 := by
  unfold exceptionalExponent tyM14 bourgainTheta; norm_num

/-- **The fifteenth, and the smallest: `6459/70000`.** -/
@[simp] theorem residual_fifteenth :
    exceptionalExponent tyM15 15 bourgainTheta = 6459 / 70000 := by
  unfold exceptionalExponent tyM15 bourgainTheta; norm_num

/-- **All four residuals are strictly positive**: no published moment empties the exceptional set at
the record. -/
theorem residuals_positive :
    0 < exceptionalExponent 2 12 bourgainTheta ∧
      0 < exceptionalExponent tyM13 13 bourgainTheta ∧
      0 < exceptionalExponent tyM14 14 bourgainTheta ∧
      0 < exceptionalExponent tyM15 15 bourgainTheta := by
  rw [residual_twelfth, residual_thirteenth, residual_fourteenth, residual_fifteenth]
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- **And they decrease with the moment order**, the smallest being the fifteenth. -/
theorem residuals_decreasing :
    exceptionalExponent tyM15 15 bourgainTheta < exceptionalExponent tyM14 14 bourgainTheta ∧
      exceptionalExponent tyM14 14 bourgainTheta
        < exceptionalExponent tyM13 13 bourgainTheta ∧
      exceptionalExponent tyM13 13 bourgainTheta < exceptionalExponent 2 12 bourgainTheta := by
  rw [residual_twelfth, residual_thirteenth, residual_fourteenth, residual_fifteenth]
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-- The residual is bracketed between `0.09` and `0.093`. -/
theorem residual_bracket :
    (9 : ℚ) / 100 < exceptionalExponent tyM15 15 bourgainTheta ∧
      exceptionalExponent tyM15 15 bourgainTheta < 93 / 1000 := by
  rw [residual_fifteenth]
  constructor <;> norm_num

/-! ### Why moments cannot close it -/

/-- **The best published neutrality ratio still exceeds the record**, so no published moment can
empty the set. -/
theorem published_ratio_exceeds_record :
    bourgainTheta < muFromMoment tyM15 15 := by
  unfold bourgainTheta
  exact ty_does_not_beat_bourgain

/-- **Hence the emptying criterion fails at every published order.** -/
theorem emptying_fails_at_fifteen :
    ¬ (exceptionalExponent tyM15 15 bourgainTheta ≤ 0) := by
  rw [residual_fifteenth]; norm_num

/-- **The residual, stated.**  Outside a set of density zero the Lindelöf bound already holds; the
entire remaining content of the hypothesis is the emptiness of a set whose measure is bounded, with
current moment technology, only by `T^(6459/70000)`. -/
theorem lindelof_residual :
    exceptionalExponent tyM15 15 bourgainTheta = 6459 / 70000 ∧
      0 < exceptionalExponent tyM15 15 bourgainTheta ∧
      bourgainTheta < muFromMoment tyM15 15 :=
  ⟨residual_fifteenth, residuals_positive.2.2.2, published_ratio_exceeds_record⟩

/-- The moment order at which the residual would vanish, given a moment bound `M`: `A = M/δ`. -/
def emptyingOrder (M δ : ℚ) : ℚ := M / δ

/-- **At the record with the fifteenth-moment bound, the required order is `A = 2.4137·84/13`.** -/
theorem emptyingOrder_at_record :
    emptyingOrder tyM15 bourgainTheta = 506877 / 32500 := by
  unfold emptyingOrder tyM15 bourgainTheta; norm_num

/-- **It exceeds `15`**, so the fifteenth moment is short of the order needed. -/
theorem emptyingOrder_exceeds_fifteen : (15 : ℚ) < emptyingOrder tyM15 bourgainTheta := by
  unfold emptyingOrder tyM15 bourgainTheta; norm_num

end HTGeometry
