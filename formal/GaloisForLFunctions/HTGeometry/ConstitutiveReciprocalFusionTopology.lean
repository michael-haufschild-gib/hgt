import GaloisForLFunctions.HTGeometry.ConstitutiveSelfDualFactorizationGeometry

/-!
# Reciprocal-fusion formation work

The reciprocal semantic/lineage factorization has a canonical normalized work
`2 * (cosh x - 1)`.  Direct and reflected formation obey one exact binary fusion law.  For finite
packets, that law survives arbitrary source-complexity weights, while the squared separation of
the exact-recovery legs is exactly the packet work.  Reciprocal positive Grams reconstruct every
radial coordinate.

This file certifies the finite algebraic/factorization core of ULF-RFTM-1.  It contains no RH
parameter and no analytic selection premise.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Normalized scalar work forced by reciprocal direct/reflected fusion. -/
def reciprocalFusionWork (x : ℝ) : ℝ := 2 * (Real.cosh x - 1)

/-- Exponential form of reciprocal fusion work. -/
theorem reciprocalFusionWork_exp (x : ℝ) :
    reciprocalFusionWork x = Real.exp x + Real.exp (-x) - 2 := by
  rw [reciprocalFusionWork, Real.cosh_eq]
  ring

/-- **Local fusion law.**  Direct and reflected compositions determine their joint work exactly. -/
theorem reciprocalFusionWork_fusion (x y : ℝ) :
    reciprocalFusionWork (x + y) + reciprocalFusionWork (x - y) =
      reciprocalFusionWork x * reciprocalFusionWork y +
        2 * reciprocalFusionWork x + 2 * reciprocalFusionWork y := by
  simp only [reciprocalFusionWork, Real.cosh_add, Real.cosh_sub]
  ring

/-- Reciprocal work is nonnegative. -/
theorem reciprocalFusionWork_nonneg (x : ℝ) : 0 ≤ reciprocalFusionWork x := by
  rw [reciprocalFusionWork]
  nlinarith [Real.one_le_cosh x]

/-- Reversal preserves reciprocal work. -/
theorem reciprocalFusionWork_neg (x : ℝ) :
    reciprocalFusionWork (-x) = reciprocalFusionWork x := by
  simp [reciprocalFusionWork]

/-- Reciprocal work vanishes only at the balanced factorization. -/
theorem reciprocalFusionWork_eq_zero_iff (x : ℝ) :
    reciprocalFusionWork x = 0 ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hstrict : 1 < Real.cosh x := (Real.one_lt_cosh).2 hx
    rw [reciprocalFusionWork] at h
    nlinarith
  · rintro rfl
    simp [reciprocalFusionWork]

variable {ι : Type*} [Fintype ι]

/-- Source-complexity-weighted work of a finite radial packet. -/
def reciprocalPacketWork (a : ι → ℝ) (x : ι → ℝ) : ℝ :=
  ∑ i, (a i) ^ 2 * reciprocalFusionWork (x i)

/-- Nonlinear interaction term in the packet fusion law. -/
def reciprocalPacketInteraction (a : ι → ℝ) (x y : ι → ℝ) : ℝ :=
  ∑ i, (a i) ^ 2 * reciprocalFusionWork (x i) * reciprocalFusionWork (y i)

/-- **Finite packet fusion.**  Arbitrary marked weights preserve the exact local fusion identity. -/
theorem reciprocalPacketWork_fusion (a : ι → ℝ) (x y : ι → ℝ) :
    reciprocalPacketWork a (x + y) + reciprocalPacketWork a (x - y) =
      reciprocalPacketInteraction a x y +
        2 * reciprocalPacketWork a x + 2 * reciprocalPacketWork a y := by
  rw [reciprocalPacketWork, reciprocalPacketWork, ← Finset.sum_add_distrib]
  rw [reciprocalPacketInteraction, reciprocalPacketWork, reciprocalPacketWork]
  calc
    (∑ i, ((a i) ^ 2 * reciprocalFusionWork ((x + y) i) +
      (a i) ^ 2 * reciprocalFusionWork ((x - y) i))) =
        ∑ i, ((a i) ^ 2 * reciprocalFusionWork (x i) * reciprocalFusionWork (y i) +
          2 * ((a i) ^ 2 * reciprocalFusionWork (x i)) +
          2 * ((a i) ^ 2 * reciprocalFusionWork (y i))) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp only [Pi.add_apply, Pi.sub_apply]
            calc
              (a i) ^ 2 * reciprocalFusionWork (x i + y i) +
                  (a i) ^ 2 * reciprocalFusionWork (x i - y i) =
                (a i) ^ 2 * (reciprocalFusionWork (x i + y i) +
                  reciprocalFusionWork (x i - y i)) := by ring
              _ = _ := by rw [reciprocalFusionWork_fusion]; ring
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.mul_sum]

/-- Positive semantic leg of the reciprocal exact-recovery factorization. -/
def reciprocalSemanticLeg (x : ℝ) : ℝ := Real.exp (x / 2)

/-- Positive lineage leg of the reciprocal exact-recovery factorization. -/
def reciprocalLineageLeg (x : ℝ) : ℝ := Real.exp (-x / 2)

/-- The semantic and lineage legs recover the identity exactly. -/
theorem reciprocalLeg_exactRecovery (x : ℝ) :
    reciprocalSemanticLeg x * reciprocalLineageLeg x = 1 := by
  rw [reciprocalSemanticLeg, reciprocalLineageLeg, ← Real.exp_add]
  ring_nf
  exact Real.exp_zero

/-- Reciprocal positive Grams multiply to the identity. -/
theorem reciprocalLeg_gram_product (x : ℝ) :
    reciprocalSemanticLeg x ^ 2 * reciprocalLineageLeg x ^ 2 = 1 := by
  rw [← mul_pow, reciprocalLeg_exactRecovery]
  norm_num

/-- Semantic positive Gram coordinate. -/
theorem reciprocalSemanticGram (x : ℝ) :
    reciprocalSemanticLeg x ^ 2 = Real.exp x := by
  rw [reciprocalSemanticLeg, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- Lineage positive Gram coordinate. -/
theorem reciprocalLineageGram (x : ℝ) :
    reciprocalLineageLeg x ^ 2 = Real.exp (-x) := by
  rw [reciprocalLineageLeg, pow_two, ← Real.exp_add]
  congr 1
  ring

/-- **Gram reconstruction.**  The semantic positive Gram retains the full radial coordinate. -/
theorem reciprocalSemanticGram_reconstructs (x : ℝ) :
    Real.log (reciprocalSemanticLeg x ^ 2) = x := by
  rw [reciprocalSemanticGram, Real.log_exp]

/-- Functional reversal exchanges semantic and lineage legs. -/
theorem reciprocalLeg_reversal_semantic (x : ℝ) :
    reciprocalSemanticLeg (-x) = reciprocalLineageLeg x := by
  rw [reciprocalSemanticLeg, reciprocalLineageLeg]

/-- Squared leg separation equals reciprocal work. -/
theorem reciprocalLeg_separation_sq (x : ℝ) :
    (reciprocalSemanticLeg x - reciprocalLineageLeg x) ^ 2 = reciprocalFusionWork x := by
  rw [reciprocalSemanticLeg, reciprocalLineageLeg, reciprocalFusionWork_exp]
  have hmul : Real.exp (x / 2) * Real.exp (-x / 2) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hpos : Real.exp (x / 2) ^ 2 = Real.exp x := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have hneg : Real.exp (-x / 2) ^ 2 = Real.exp (-x) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  nlinarith

/-- Weighted squared separation of all exact-recovery legs is exactly packet work. -/
theorem reciprocalPacket_separation_sq (a : ι → ℝ) (x : ι → ℝ) :
    (∑ i, (a i) ^ 2 *
      (reciprocalSemanticLeg (x i) - reciprocalLineageLeg (x i)) ^ 2) =
        reciprocalPacketWork a x := by
  simp_rw [reciprocalLeg_separation_sq]
  rfl

/-- Semantic formation composes by addition of radial coordinates. -/
theorem reciprocalLeg_composition (x y : ℝ) :
    reciprocalSemanticLeg (x + y) = reciprocalSemanticLeg x * reciprocalSemanticLeg y := by
  rw [reciprocalSemanticLeg, reciprocalSemanticLeg, reciprocalSemanticLeg, ← Real.exp_add]
  congr 1
  ring

end

end GaloisForLFunctions.HTGeometry
