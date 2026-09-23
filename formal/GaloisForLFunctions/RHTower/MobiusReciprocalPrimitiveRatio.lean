import GaloisForLFunctions.RHTower.Sieve.PrimitiveRatioDecomposition
import GaloisForLFunctions.RHTower.Sieve.MoebiusScaledReindex

/-!
# Primitive-ratio localization of the reciprocal Möbius moment

The near-endpoint reciprocal moment has a homogeneous additive kernel. The exact gcd
reindexing below places every Möbius sign on a primitive coprime pair; the common
scale contributes only a nonnegative squarefree coefficient and a positive power.
This is a finite identity and asserts no bound on the remaining primitive-pair sum.
-/

open Finset

namespace RHTower

noncomputable section

/-- Real Möbius coefficient on positive integers. -/
def mobiusRealCoefficient (n : ℕ) : ℝ := ((ArithmeticFunction.moebius n : ℤ) : ℝ)

private theorem mobius_pair_scaled (d a b : ℕ) :
    mobiusRealCoefficient (d * a) * mobiusRealCoefficient (d * b) =
      if Nat.Coprime d a ∧ Nat.Coprime d b then mobiusRealCoefficient d ^ 2 * mobiusRealCoefficient a * mobiusRealCoefficient b else 0 := by
  by_cases hda : Nat.Coprime d a
  · by_cases hdb : Nat.Coprime d b
    · have h1 := Sieve.moebius_mul_of_coprime hda
      have h2 := Sieve.moebius_mul_of_coprime hdb
      have hboth : Nat.Coprime d a ∧ Nat.Coprime d b := ⟨hda, hdb⟩
      simp only [mobiusRealCoefficient, h1, h2, if_pos hboth]
      push_cast
      ring
    · have h0 := Sieve.moebius_mul_eq_zero_of_not_coprime hdb
      simp [mobiusRealCoefficient, h0, hdb]
  · have h0 := Sieve.moebius_mul_eq_zero_of_not_coprime hda
    simp [mobiusRealCoefficient, h0, hda]

/-- Positive homogeneous pair kernel of the order-three near-endpoint moment. -/
def cubicMomentKernel (δ : ℝ) (m n : ℕ) : ℝ :=
  (((m : ℝ) * (n : ℝ)) ^ (2 - δ)) /
    (((m : ℝ) + (n : ℝ)) ^ (5 - δ))

/-- Common gcd scaling contributes the exact power `d^(-1-δ)`. -/
theorem cubicMomentKernel_scale (δ : ℝ) {d a b : ℕ}
    (hd : 0 < d) (ha : 0 < a) (hb : 0 < b) :
    cubicMomentKernel δ (d * a) (d * b) =
      (d : ℝ) ^ (-1 - δ) * cubicMomentKernel δ a b := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hpow : ((d : ℝ) ^ (2 : ℕ)) ^ (2 - δ) /
      (d : ℝ) ^ (5 - δ) = (d : ℝ) ^ (-1 - δ) := by
    rw [show ((d : ℝ) ^ (2 : ℕ)) = (d : ℝ) ^ ((2 : ℕ) : ℝ) by
        rw [Real.rpow_natCast],
      ← Real.rpow_mul hdR.le, ← Real.rpow_sub hdR]
    congr 1
    ring
  unfold cubicMomentKernel
  push_cast
  rw [show ((d : ℝ) * (a : ℝ)) * ((d : ℝ) * (b : ℝ)) =
      (d : ℝ) ^ (2 : ℕ) * ((a : ℝ) * (b : ℝ)) by ring,
    show (d : ℝ) * (a : ℝ) + (d : ℝ) * (b : ℝ) =
      (d : ℝ) * ((a : ℝ) + (b : ℝ)) by ring,
    Real.mul_rpow (sq_nonneg _) (mul_nonneg haR.le hbR.le),
    Real.mul_rpow hdR.le (add_nonneg haR.le hbR.le)]
  rw [show ((d : ℝ) ^ (2 : ℕ)) ^ (2 - δ) *
      (((a : ℝ) * (b : ℝ)) ^ (2 - δ)) /
      ((d : ℝ) ^ (5 - δ) * (((a : ℝ) + (b : ℝ)) ^ (5 - δ))) =
      (((d : ℝ) ^ (2 : ℕ)) ^ (2 - δ) / (d : ℝ) ^ (5 - δ)) *
        ((((a : ℝ) * (b : ℝ)) ^ (2 - δ)) /
          (((a : ℝ) + (b : ℝ)) ^ (5 - δ))) by ring]
  rw [hpow]

/-- Literal signed off-diagonal of the finite reciprocal moment quadratic form. -/
def finiteCubicMomentOffDiagonal (δ : ℝ) (N : ℕ) : ℝ :=
  ∑ p ∈ Sieve.offDiagPairs N,
    mobiusRealCoefficient p.1 * mobiusRealCoefficient p.2 * cubicMomentKernel δ p.1 p.2

/-- Finite source signs factor through gcd and the primitive ratio. -/
theorem finiteCubicMomentOffDiagonal_eq_primitive (δ : ℝ) (N : ℕ) :
    finiteCubicMomentOffDiagonal δ N =
      ∑ t ∈ Sieve.primitiveTriples N,
        (if Nat.Coprime t.1 t.2.1 ∧ Nat.Coprime t.1 t.2.2
         then mobiusRealCoefficient t.1 ^ 2 * mobiusRealCoefficient t.2.1 * mobiusRealCoefficient t.2.2 else 0) *
          cubicMomentKernel δ (t.1 * t.2.1) (t.1 * t.2.2) := by
  calc
    finiteCubicMomentOffDiagonal δ N =
        ∑ t ∈ Sieve.primitiveTriples N,
          mobiusRealCoefficient (t.1 * t.2.1) * mobiusRealCoefficient (t.1 * t.2.2) *
            cubicMomentKernel δ (t.1 * t.2.1) (t.1 * t.2.2) := by
      simpa only [finiteCubicMomentOffDiagonal] using
        (Sieve.sum_offDiagPairs_eq_sum_primitiveTriples N
          (fun m n => mobiusRealCoefficient m * mobiusRealCoefficient n * cubicMomentKernel δ m n))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [mobius_pair_scaled]

/-- **Signed primitive-ratio law.** The common scale has nonnegative Möbius square and
positive homogeneous weight; all remaining signs belong to the coprime ratio. -/
theorem finiteCubicMomentOffDiagonal_eq_scaledPrimitive (δ : ℝ) (N : ℕ) :
    finiteCubicMomentOffDiagonal δ N =
      ∑ t ∈ Sieve.primitiveTriples N,
        (if Nat.Coprime t.1 t.2.1 ∧ Nat.Coprime t.1 t.2.2
         then mobiusRealCoefficient t.1 ^ 2 * mobiusRealCoefficient t.2.1 * mobiusRealCoefficient t.2.2 else 0) *
          (t.1 : ℝ) ^ (-1 - δ) * cubicMomentKernel δ t.2.1 t.2.2 := by
  rw [finiteCubicMomentOffDiagonal_eq_primitive]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_filter.mp ht
  have ht'' := Finset.mem_product.mp ht'.1
  have hd : 0 < t.1 := (Finset.mem_Icc.mp ht''.1).1
  have hrest := Finset.mem_product.mp ht''.2
  have ha : 0 < t.2.1 := (Finset.mem_Icc.mp hrest.1).1
  have hb : 0 < t.2.2 := (Finset.mem_Icc.mp hrest.2).1
  rw [cubicMomentKernel_scale δ hd ha hb]
  ring

/-- Nonnegative common-scale mass attached to one primitive coprime pair. -/
def primitiveCubicScaleWeight (δ : ℝ) (N a b : ℕ) : ℝ :=
  ∑ d ∈ Sieve.ratioScales N a b,
    if Nat.Coprime d a ∧ Nat.Coprime d b
    then mobiusRealCoefficient d ^ 2 * (d : ℝ) ^ (-1 - δ)
    else 0

theorem primitiveCubicScaleWeight_nonneg (δ : ℝ) (N a b : ℕ) :
    0 ≤ primitiveCubicScaleWeight δ N a b := by
  unfold primitiveCubicScaleWeight
  apply Finset.sum_nonneg
  intro d hd
  split_ifs
  · exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  · rfl

/-- Grouped form of the literal signed moment: all scale weights are nonnegative,
and all remaining signs lie on coprime primitive pairs. -/
theorem finiteCubicMomentOffDiagonal_eq_primitiveScaleWeight (δ : ℝ) (N : ℕ) :
    finiteCubicMomentOffDiagonal δ N =
      ∑ q ∈ Sieve.primitiveRatioPairs N,
        mobiusRealCoefficient q.1 * mobiusRealCoefficient q.2 *
          cubicMomentKernel δ q.1 q.2 *
          primitiveCubicScaleWeight δ N q.1 q.2 := by
  calc
    finiteCubicMomentOffDiagonal δ N =
        ∑ q ∈ Sieve.primitiveRatioPairs N,
          ∑ d ∈ Sieve.ratioScales N q.1 q.2,
            mobiusRealCoefficient (d * q.1) * mobiusRealCoefficient (d * q.2) *
              cubicMomentKernel δ (d * q.1) (d * q.2) := by
      simpa only [finiteCubicMomentOffDiagonal] using
        (Sieve.sum_offDiagPairs_eq_sum_ratio N
          (fun m n => mobiusRealCoefficient m * mobiusRealCoefficient n *
            cubicMomentKernel δ m n))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      have hq' := Finset.mem_filter.mp hq
      have hq'' := Finset.mem_product.mp hq'.1
      have ha : 0 < q.1 := (Finset.mem_Icc.mp hq''.1).1
      have hb : 0 < q.2 := (Finset.mem_Icc.mp hq''.2).1
      unfold primitiveCubicScaleWeight
      calc
        (∑ d ∈ Sieve.ratioScales N q.1 q.2,
            mobiusRealCoefficient (d * q.1) * mobiusRealCoefficient (d * q.2) *
              cubicMomentKernel δ (d * q.1) (d * q.2)) =
          ∑ d ∈ Sieve.ratioScales N q.1 q.2,
            (mobiusRealCoefficient q.1 * mobiusRealCoefficient q.2 *
              cubicMomentKernel δ q.1 q.2) *
              (if Nat.Coprime d q.1 ∧ Nat.Coprime d q.2
               then mobiusRealCoefficient d ^ 2 * (d : ℝ) ^ (-1 - δ)
               else 0) := by
          apply Finset.sum_congr rfl
          intro d hd
          have hd' := Finset.mem_filter.mp hd
          have hdpos : 0 < d := (Finset.mem_Icc.mp hd'.1).1
          rw [mobius_pair_scaled, cubicMomentKernel_scale δ hdpos ha hb]
          split_ifs <;> ring
        _ = _ := by rw [Finset.mul_sum]

end
end RHTower
