import GaloisForLFunctions.RHTower.ChenGuptaLiLemma62TailEulerSourceBounds

/-!
# Chen--Gupta--Li Lemma 6.2: primitive-conductor arithmetic

The primitive functional-conductor factor and the imprimitive Euler quotient
combine to at most the ambient conductor power required by CGL's `I₂` bound.
-/

open Complex MeasureTheory Filter Set Asymptotics LSeries
open scoped Topology LSeries.notation BigOperators

namespace RHTower

noncomputable section

/-- The factors `(q*)^(1/2+2k)` and `(q/q*)^(2k+2)` are bounded by
`q^(2k+2)` when `q*` divides `q`. -/
theorem cglLemma62_primitiveConductor_eulerQuotient_le_ambient_power
    (B : CGLLemma62InducedCharacter) (d : CGLLemma62TailContourDepth) :
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) ≤
      (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
  have hprimitiveOneNat : 1 ≤ B.primitive.modulus.value :=
    Nat.succ_le_iff.mpr B.primitive.modulus.positive
  have hprimitiveOne : (1 : ℝ) ≤ B.primitive.modulus.value := by
    exact_mod_cast hprimitiveOneNat
  have hprimitiveNonneg : 0 ≤ (B.primitive.modulus.value : ℝ) := by positivity
  have hquotientNonneg : 0 ≤
      ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) := by positivity
  have hexponent : 1 / 2 + 2 * (d.value : ℝ) ≤ 2 * (d.value : ℝ) + 2 := by
    linarith
  have hprimitivePower := Real.rpow_le_rpow_of_exponent_le hprimitiveOne hexponent
  have hquotientPower : 0 ≤
      ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
        (2 * (d.value : ℝ) + 2) :=
    Real.rpow_nonneg hquotientNonneg _
  calc
    (B.primitive.modulus.value : ℝ) ^ (1 / 2 + 2 * (d.value : ℝ)) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
          (2 * (d.value : ℝ) + 2) ≤
        (B.primitive.modulus.value : ℝ) ^ (2 * (d.value : ℝ) + 2) *
          ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ) ^
            (2 * (d.value : ℝ) + 2) :=
      mul_le_mul_of_nonneg_right hprimitivePower hquotientPower
    _ = ((B.primitive.modulus.value : ℝ) *
        ((B.ambient.value / B.primitive.modulus.value : ℕ) : ℝ)) ^
          (2 * (d.value : ℝ) + 2) := by
      rw [Real.mul_rpow hprimitiveNonneg hquotientNonneg]
    _ = (B.ambient.value : ℝ) ^ (2 * (d.value : ℝ) + 2) := by
      congr 1
      norm_cast
      rw [Nat.mul_comm, Nat.div_mul_cancel B.conductor_dvd_ambient]

end

end RHTower
