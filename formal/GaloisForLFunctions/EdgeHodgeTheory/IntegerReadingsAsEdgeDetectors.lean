import GaloisForLFunctions.EdgeHodgeTheory.TheEdgeIsAThresholdCurve
import GaloisForLFunctions.HeckeKreinToeplitz.HeatCollisionsCountTheIndex
import GaloisForLFunctions.ConjugateDiagonalGeometry.IntegerThetaCollisionFredholmIndex
import GaloisForLFunctions.ArithmeticOrientationGeometry.TheIndexExit

/-!
# Integer readings as edge detectors

The horizontal collision charge of a window of height `T` is an integer read from finitely many
integer theta coefficients: the Fredholm index of a Wiener–Hopf operator built from a theta prefix
(ConjugateDiagonalGeometry). It bounds the Krein–Langer index of `ζ` (HKT), and the Krein–Langer
index bounds every Hodge defect at every resolution.

* **The readings are Fredholm indices** (`exists_fredholmIndex_eq_collisionCharge`).
* **Every horizon defect is bounded by the readings** (`horizonDefect_le_iSup_collisionCharge`):
  at every width and every horizon the Hodge defect of the horizon family is at most the largest
  collision charge.
* **Vanishing readings give positivity at every resolution**
  (`positiveAt_of_collisionCharge_eq_zero`): if every collision charge is `0`, every complete Weil
  family is positive semidefinite at every resolution — the edge is at infinity for every profile.
* **Precision below two suffices** (`riemannHypothesis_of_collisionCharge_le_one`): if every reading
  is at most `1`, RH holds. The zeros right of the line pair up under conjugation, so a finite
  Krein–Langer index is even, and an index at most `1` is `0`.

These are integer statements: they hold at the edge because they are about integers, and a reading
needs precision `< 1/2` to be exact.
-/

noncomputable section

open Filter Topology

namespace GaloisForLFunctions.EdgeHodgeTheory

open ArithmeticCastelnuovoSeveri (realTests rightZeros)
open ArithmeticOrientationGeometry (seenRightZeros)
open Zeta23

/-- **The readings are Fredholm indices** of integer-theta Wiener–Hopf operators. -/
theorem exists_fredholmIndex_eq_collisionCharge (T : ℝ) :
    ∃ n N : ℕ, HTGeometry.fredholmIndex
        (ConjugateDiagonalGeometry.integerThetaCollisionOperator T n N) =
      (_root_.RHTower.xiHorizontalCollisionCharge T : ℤ) :=
  ⟨_, _, ConjugateDiagonalGeometry.fredholmIndex_integerThetaCollisionOperator_eq_charge T le_rfl
    le_rfl⟩

/-- The seen right zeros of a test are among the right zeros of `ζ`. -/
theorem seen_encard_le_negIndex_zetaKernel (f : ℝ → ℝ) :
    (seenRightZeros zetaZeroConfig f).encard ≤
      HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel := by
  rw [HeckeKreinToeplitz.negIndex_zetaKernel]
  exact Set.encard_le_encard fun ρ hρ => ⟨hρ.1, hρ.2.1⟩

/-- **Every horizon defect is bounded by the collision charges.** -/
theorem horizonDefect_le_iSup_collisionCharge {f : ℝ → ℝ} (hf : f ∈ realTests) (N : ℕ) :
    (horizonDefect f N : ℕ∞) ≤ ⨆ T : ℝ, (_root_.RHTower.xiHorizontalCollisionCharge T : ℕ∞) :=
  ((horizonDefect_le_seen hf N).trans (seen_encard_le_negIndex_zetaKernel f)).trans
    HeckeKreinToeplitz.negIndex_zetaKernel_le_iSup_horizontalCollisionCharge

/-- **Vanishing readings give positivity at every resolution.** -/
theorem positiveAt_of_collisionCharge_eq_zero
    (h : ∀ T : ℝ, _root_.RHTower.xiHorizontalCollisionCharge T = 0) {φ : ℝ → ℝ}
    (hφ : Admissible φ) {c : ℝ} (hc : 0 < c) {N : ℕ} (hN : 1 ≤ N) : PositiveAt φ c N := by
  have hw : 0 < c / N := div_pos hc (by exact_mod_cast hN)
  have hle := horizonDefect_le_iSup_collisionCharge (atomDilate_mem_realTests' hφ hw) N
  have h0 : ⨆ T : ℝ, (_root_.RHTower.xiHorizontalCollisionCharge T : ℕ∞) = 0 :=
    ENat.iSup_eq_zero.mpr fun T => by rw [h T]; rfl
  rw [h0, nonpos_iff_eq_zero, Nat.cast_eq_zero] at hle
  rw [positiveAt_iff_lt_horizonThreshold hφ hc hN]
  exact (horizonDefect_eq_zero_iff_lt_horizonThreshold _ N).mp hle

/-- **Precision below two suffices.** If every collision charge is at most `1`, RH holds. -/
theorem riemannHypothesis_of_collisionCharge_le_one
    (h : ∀ T : ℝ, _root_.RHTower.xiHorizontalCollisionCharge T ≤ 1) : RiemannHypothesis := by
  have hκ : HeckeKreinToeplitz.negIndex HeckeKreinToeplitz.zetaKernel ≤ 1 :=
    HeckeKreinToeplitz.negIndex_zetaKernel_le_iSup_horizontalCollisionCharge.trans
      (iSup_le fun T => by exact_mod_cast h T)
  rw [HeckeKreinToeplitz.negIndex_zetaKernel] at hκ
  have hfin : (rightZeros zetaZeroConfig).Finite :=
    Set.encard_lt_top_iff.mp (lt_of_le_of_lt hκ (by decide))
  have heven := ArithmeticOrientationGeometry.even_ncard_rightZeros hfin
  rw [Set.Finite.encard_eq_coe_toFinset_card hfin] at hκ
  have hle : hfin.toFinset.card ≤ 1 := by exact_mod_cast hκ
  have hzero : hfin.toFinset.card = 0 := by
    obtain ⟨k, hk⟩ := heven
    omega
  refine HeckeKreinToeplitz.riemannHypothesis_iff_negIndex_zetaKernel_eq_zero.mpr ?_
  rw [HeckeKreinToeplitz.negIndex_zetaKernel, Set.Finite.encard_eq_coe_toFinset_card hfin, hzero]
  rfl

end GaloisForLFunctions.EdgeHodgeTheory
