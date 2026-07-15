import GaloisForLFunctions.HTGeometry.GammaPeriodicConstraintCorona

/-!
# Boundary tomography for rank-one difference coefficients

For a scalar shift equation `f(z+1)=a(z)f(z)`, multiplication by the coefficient `a` acts on raw
differential jets by the binomial Leibniz matrix.  This file proves that its forward-clock defect
always lands in one new boundary coordinate, but its incoming covector records every positive
derivative of `a` visible at that resolution.  Pairing with Taylor curvature preserves this
oriented covector.  Consequently equality of the paired boundary currents reconstructs the whole
positive coefficient-jet packet.

The rank-one output is universal; the orientation of that line is source-specific.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Finite raw-jet prolongation of multiplication by a scalar coefficient whose differential jet
at the observation point is `c`.  This is the binomial Leibniz matrix. -/
def rankOneCoefficientClockMultiplication (c : ℕ → ℂ) (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun a i := ∑ k : Fin (n + 1),
    if (k : ℕ) ≤ (i : ℕ) then
      ((Nat.choose (i : ℕ) (k : ℕ) : ℕ) : ℂ) * c ((i : ℕ) - (k : ℕ)) * a k
    else 0
  map_add' a b := by
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs <;> simp [mul_add]
  map_smul' s a := by
    funext i
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    split_ifs
    · ring
    · simp

/-- **Pro-flatness for every scalar coefficient.**  Binomial coefficient prolongation commutes
exactly with forgetting the highest raw derivative. -/
theorem rankOneCoefficientClockMultiplication_truncate (c : ℕ → ℂ) (n : ℕ) :
    (gammaClockTruncate (n + 1)).comp
        (rankOneCoefficientClockMultiplication c (n + 1)) =
      (rankOneCoefficientClockMultiplication c n).comp
        (gammaClockTruncate (n + 1)) := by
  apply LinearMap.ext
  intro a
  funext i
  change (∑ k : Fin (n + 2),
      if (k : ℕ) ≤ (i : ℕ) then
        ((Nat.choose (i : ℕ) (k : ℕ) : ℕ) : ℂ) *
          c ((i : ℕ) - (k : ℕ)) * a k
      else 0) =
    ∑ k : Fin (n + 1),
      if (k : ℕ) ≤ (i : ℕ) then
        ((Nat.choose (i : ℕ) (k : ℕ) : ℕ) : ℂ) *
          c ((i : ℕ) - (k : ℕ)) * a k.castSucc
      else 0
  rw [Fin.sum_univ_castSucc]
  simp [Nat.not_le_of_lt i.isLt]

/-- The oriented incoming boundary covector.  Its coefficients are the positive derivative jet of
the scalar source coefficient, reversed and rescaled by nonzero binomial factors. -/
def rankOneCoefficientIncomingCovector (c : ℕ → ℂ) (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ where
  toFun a := ∑ k : Fin (n + 1),
    ((Nat.choose (n + 1) (k : ℕ) : ℕ) : ℂ) * c (n + 1 - (k : ℕ)) * a k
  map_add' a b := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' s a := by
    simp only [Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

/-- Forward-extension defect for a general scalar coefficient prolongation. -/
def rankOneCoefficientIncoming (c : ℕ → ℂ) (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 2) → ℂ) :=
  (rankOneCoefficientClockMultiplication c (n + 1)).comp
      (gammaClockExtendZero (n + 1)) -
    (gammaClockExtendZero (n + 1)).comp
      (rankOneCoefficientClockMultiplication c n)

/-- The general rank-one coefficient defect vanishes on every retained output coordinate. -/
theorem rankOneCoefficientIncoming_apply_castSucc (c : ℕ → ℂ) (n : ℕ)
    (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    rankOneCoefficientIncoming c n a i.castSucc = 0 := by
  simp only [rankOneCoefficientIncoming, LinearMap.sub_apply, LinearMap.comp_apply]
  change (∑ k : Fin (n + 2),
      if (k : ℕ) ≤ (i : ℕ) then
        ((Nat.choose (i : ℕ) (k : ℕ) : ℕ) : ℂ) * c ((i : ℕ) - (k : ℕ)) *
          (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) k
      else 0) -
    (Fin.snoc (rankOneCoefficientClockMultiplication c n a) (0 : ℂ) :
      Fin (n + 2) → ℂ) i.castSucc = 0
  rw [Fin.sum_univ_castSucc]
  simp [rankOneCoefficientClockMultiplication, Nat.not_le_of_lt i.isLt]

/-- The new boundary coordinate is exactly the oriented Leibniz covector. -/
theorem rankOneCoefficientIncoming_apply_last (c : ℕ → ℂ) (n : ℕ)
    (a : Fin (n + 1) → ℂ) :
    rankOneCoefficientIncoming c n a (Fin.last (n + 1)) =
      rankOneCoefficientIncomingCovector c n a := by
  simp only [rankOneCoefficientIncoming, LinearMap.sub_apply, LinearMap.comp_apply]
  change rankOneCoefficientClockMultiplication c (n + 1)
      (Fin.snoc a (0 : ℂ)) (Fin.last (n + 1)) -
      (Fin.snoc (rankOneCoefficientClockMultiplication c n a) (0 : ℂ) :
        Fin (n + 2) → ℂ) (Fin.last (n + 1)) = _
  rw [Fin.snoc_last, sub_zero]
  change (∑ k : Fin (n + 2),
      if (k : ℕ) ≤ n + 1 then
        ((Nat.choose (n + 1) (k : ℕ) : ℕ) : ℂ) * c (n + 1 - (k : ℕ)) *
          (Fin.snoc a (0 : ℂ) : Fin (n + 2) → ℂ) k
      else 0) = _
  rw [Fin.sum_univ_castSucc]
  simp [rankOneCoefficientIncomingCovector]

/-- Evaluation on one coordinate reads the corresponding positive derivative of the source
coefficient, multiplied by a known nonzero binomial factor. -/
theorem rankOneCoefficientIncomingCovector_single (c : ℕ → ℂ) (n : ℕ)
    (k : Fin (n + 1)) :
    rankOneCoefficientIncomingCovector c n (Pi.single k 1) =
      ((Nat.choose (n + 1) (k : ℕ) : ℕ) : ℂ) * c (n + 1 - (k : ℕ)) := by
  classical
  change (∑ k₁ : Fin (n + 1),
    ((Nat.choose (n + 1) (k₁ : ℕ) : ℕ) : ℂ) * c (n + 1 - (k₁ : ℕ)) *
      (Pi.single k (1 : ℂ) : Fin (n + 1) → ℂ) k₁) = _
  rw [Finset.sum_eq_single k]
  · simp
  · intro b hb hbk
    simp [hbk]
  · simp

/-- **Incoming seam tomography.**  Equality of oriented incoming covectors forces equality of
every positive coefficient derivative visible at that clock level.  Rank alone would see none of
this information. -/
theorem rankOneCoefficientJet_eq_of_incomingCovector_eq (c d : ℕ → ℂ) (n : ℕ)
    (h : rankOneCoefficientIncomingCovector c n =
      rankOneCoefficientIncomingCovector d n)
    (k : Fin (n + 1)) :
    c (n + 1 - (k : ℕ)) = d (n + 1 - (k : ℕ)) := by
  have hvalue := LinearMap.congr_fun h (Pi.single k 1)
  rw [rankOneCoefficientIncomingCovector_single,
    rankOneCoefficientIncomingCovector_single] at hvalue
  apply mul_left_cancel₀ _ hvalue
  exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt k.isLt)

/-- Pair the source-specific incoming covector with the universal outgoing Taylor curvature. -/
def rankOneCoefficientPairedBoundaryCurrent (c : ℕ → ℂ) (n : ℕ) :
    (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  (gammaClockCurvature (n + 1)).comp (rankOneCoefficientIncoming c n)

/-- The paired current is the incoming source covector times the universal factorial-tail outgoing
symbol. -/
theorem rankOneCoefficientPairedBoundaryCurrent_apply (c : ℕ → ℂ) (n : ℕ)
    (a : Fin (n + 1) → ℂ) (i : Fin (n + 1)) :
    rankOneCoefficientPairedBoundaryCurrent c n a i =
      rankOneCoefficientIncomingCovector c n a /
        ((n + 1 - i).factorial : ℂ) := by
  rw [rankOneCoefficientPairedBoundaryCurrent, LinearMap.comp_apply,
    gammaClockCurvature_apply, rankOneCoefficientIncoming_apply_last]

theorem rankOneCoefficientPairedBoundaryCurrent_eq_outerProduct
    (c : ℕ → ℂ) (n : ℕ) (a : Fin (n + 1) → ℂ) :
    rankOneCoefficientPairedBoundaryCurrent c n a =
      rankOneCoefficientIncomingCovector c n a •
        gammaClockBoundaryVector (n + 1) := by
  funext i
  rw [rankOneCoefficientPairedBoundaryCurrent_apply]
  simp [gammaClockBoundaryVector, div_eq_mul_inv]

/-- **Paired-current tomography.**  Equality of the full oriented boundary currents reconstructs
the positive source-coefficient jet.  The universal rank-one output line has not erased the source:
its input orientation carries the complete finite coefficient data. -/
theorem rankOneCoefficientJet_eq_of_pairedBoundaryCurrent_eq (c d : ℕ → ℂ) (n : ℕ)
    (h : rankOneCoefficientPairedBoundaryCurrent c n =
      rankOneCoefficientPairedBoundaryCurrent d n)
    (k : Fin (n + 1)) :
    c (n + 1 - (k : ℕ)) = d (n + 1 - (k : ℕ)) := by
  have hvalue := congrFun
    (LinearMap.congr_fun h (Pi.single k 1)) (Fin.last n)
  rw [rankOneCoefficientPairedBoundaryCurrent_apply,
    rankOneCoefficientPairedBoundaryCurrent_apply,
    rankOneCoefficientIncomingCovector_single,
    rankOneCoefficientIncomingCovector_single] at hvalue
  simp only [Fin.val_last, Nat.add_sub_cancel_left, Nat.factorial_one,
    Nat.cast_one, div_one] at hvalue
  apply mul_left_cancel₀ _ hvalue
  exact_mod_cast Nat.choose_ne_zero (Nat.le_of_lt k.isLt)

end

end GaloisForLFunctions.HTGeometry
