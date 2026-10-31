import GaloisForLFunctions.AdelicKreinGeometry.TheHeatDeformedArchimedeanState
import GaloisForLFunctions.RenormalizedIntersectionTheory.TheRenormalizedHodgeIndex

/-!
# The heat flow is a homotopy of Hodge defects

The de Bruijn–Newman heat flow `H_t` deforms Weil's dilation correlation into the heat dilation
kernel `K_t` (`AdelicKreinGeometry.heatDilationKernel`), built from `H_t` alone; its archimedean
glue is the heat-deformed state (`AdelicKreinGeometry.heatArchState`). The **Hodge defect** of
`K_t` is its index on the pole-orthogonal hyperplane, `boostPolarIndex K_t`; the renormalized Hodge
index is the vanishing of the defect (`RenormalizedHodgeIndex`).

* **The defect counts zeros** (`boostPolarIndex_heatDilationKernel`): for `t > 0` the Hodge defect
  of `K_t` is the number of nonreal right zeros of `H_t`, with multiplicity, and is finite.
* **The Hodge index holds at large time** (`renormalizedHodgeIndex_heat_of_eighth_le`): for
  `t ≥ 1/8`, where `H_t` has only real zeros.
* **The defect is the collision count** (`boostPolarIndex_heat_eq_sum_collisionPairs`): the defect at
  `t` is the number of conjugate pairs that collide on the real line after time `t`.
* **Monotone homotopy with jumps at collisions** (`antitoneOn_boostPolarIndex_heat`,
  `exists_left_boostPolarIndex_heat_eq_add_collisionPairs`): the defect is nonincreasing in `t` and
  drops at a collision time by the number of pairs colliding there; it is locally constant
  otherwise.
* **RH** (`riemannHypothesis_iff_forall_renormalizedHodgeIndex_heat`): the Hodge index holds along the
  whole flow `t > 0` iff RH. The Hodge defect of Weil's correlation is finite iff the defects of the
  flow are bounded (`boostPolarIndex_ratCorr_lt_top_iff_bdd_heat`).

So the heat flow is a homotopy of finite-index Pontryagin states from `t = 0⁺` to the Hodge-index
state at `t = 1/8`; every unit of Hodge defect is paid by one collision of a conjugate pair.
-/

open Set
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HeckeKreinToeplitz
open GaloisForLFunctions.AdelicKreinGeometry GaloisForLFunctions.ArithmeticPositiveDuality
open RHTower RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

/-- The glued heat state has index one more than the Hodge defect of `K_t`. -/
theorem negIndex_heatArchState_eq_boostPolarIndex_add_one (t : ℝ) :
    negIndex (heatArchState 1 t) = boostPolarIndex (heatDilationKernel t) + 1 :=
  negIndex_archGlue_eq (isHermKernel_heatDilationKernel t) one_pos

/-- **The Hodge defect of the heat kernel counts the nonreal right zeros of `H_t`.** -/
theorem boostPolarIndex_heatDilationKernel {t : ℝ} (ht : 0 < t) :
    boostPolarIndex (heatDilationKernel t) = (heatRightZeroMultiplicity t : ℕ∞) := by
  have h := negIndex_heatArchState_eq one_pos ht
  rw [negIndex_heatArchState_eq_boostPolarIndex_add_one] at h
  push_cast at h
  exact WithTop.add_right_cancel ENat.one_ne_top h

/-- The Hodge index holds for `K_t` iff `H_t` has only real zeros. -/
theorem renormalizedHodgeIndex_heat_iff {t : ℝ} (ht : 0 < t) :
    RenormalizedHodgeIndex (heatDilationKernel t) ↔ nonrealZeroCount t = 0 := by
  rw [RenormalizedHodgeIndex, boostPolarIndex_heatDilationKernel ht, Nat.cast_eq_zero,
    ← two_mul_heatRightZeroMultiplicity t]
  omega

/-- **The Hodge index holds at large heat time.** -/
theorem renormalizedHodgeIndex_heat_of_eighth_le {t : ℝ} (ht : 1 / 8 ≤ t) :
    RenormalizedHodgeIndex (heatDilationKernel t) :=
  (renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one (isHermKernel_heatDilationKernel t)
    one_pos).mpr (negIndex_heatArchState_eq_one_of_eighth_le one_pos ht)

/-- **The Hodge defect is the number of pairs colliding after time `t`.** -/
theorem boostPolarIndex_heat_eq_sum_collisionPairs {t : ℝ} (ht : 0 < t) :
    boostPolarIndex (heatDilationKernel t) =
      ((∑ s ∈ (finite_collisionTimes ht).toFinset, heatCollisionPairs s : ℕ) : ℕ∞) := by
  rw [boostPolarIndex_heatDilationKernel ht, heatRightZeroMultiplicity_eq_sum_collisionPairs ht]

/-- **The Hodge defect is nonincreasing along the flow.** -/
theorem antitoneOn_boostPolarIndex_heat :
    AntitoneOn (fun t => boostPolarIndex (heatDilationKernel t)) (Ioi 0) := by
  intro s hs t ht hst
  dsimp only
  rw [boostPolarIndex_heatDilationKernel hs, boostPolarIndex_heatDilationKernel ht,
    heatRightZeroMultiplicity_eq_div, heatRightZeroMultiplicity_eq_div]
  exact Nat.cast_le.mpr (Nat.div_le_div_right (nonrealZeroCount_antitoneOn hs ht hst))

/-- **Jump law**: just before a collision time `t`, the Hodge defect exceeds its value at `t` by the
number of conjugate pairs colliding at `t`. -/
theorem exists_left_boostPolarIndex_heat_eq_add_collisionPairs {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, ∀ s, t - δ < s → s < t →
      boostPolarIndex (heatDilationKernel s) =
        boostPolarIndex (heatDilationKernel t) + (heatCollisionPairs t : ℕ∞) := by
  obtain ⟨δ, hδ, h⟩ := exists_left_negIndex_heatArchState_eq_add_collisionPairs one_pos ht
  refine ⟨δ, hδ, fun s h₁ h₂ => ?_⟩
  have e := h s h₁ h₂
  rw [negIndex_heatArchState_eq_boostPolarIndex_add_one,
    negIndex_heatArchState_eq_boostPolarIndex_add_one, add_right_comm] at e
  exact WithTop.add_right_cancel ENat.one_ne_top e

/-- **RH is the Hodge index along the whole heat flow.** -/
theorem riemannHypothesis_iff_forall_renormalizedHodgeIndex_heat :
    RiemannHypothesis ↔ ∀ t > 0, RenormalizedHodgeIndex (heatDilationKernel t) := by
  rw [riemannHypothesis_iff_forall_negIndex_heatArchState_eq_one one_pos]
  refine forall₂_congr fun t _ => ?_
  rw [renormalizedHodgeIndex_iff_negIndex_archGlue_eq_one (isHermKernel_heatDilationKernel t)
    one_pos]
  rfl

/-- **Finite Hodge defect of Weil's correlation is bounded defects along the flow.** -/
theorem boostPolarIndex_ratCorr_lt_top_iff_bdd_heat :
    boostPolarIndex ratCorr < ⊤ ↔
      ∃ M : ℕ, ∀ t > 0, boostPolarIndex (heatDilationKernel t) ≤ M := by
  have h := negIndex_weilArchState_lt_top_iff_bdd (c := 1) one_pos
  rw [negIndex_weilArchState_eq_add_one one_pos] at h
  rw [boostPolarIndex_ratCorr]
  constructor
  · intro hlt
    obtain ⟨M, hM⟩ := h.mp (ENat.add_lt_top.mpr ⟨hlt, ENat.one_lt_top⟩)
    refine ⟨M, fun t ht => ?_⟩
    have := hM t ht
    rw [negIndex_heatArchState_eq_boostPolarIndex_add_one] at this
    exact le_self_add.trans this
  · rintro ⟨M, hM⟩
    refine lt_of_le_of_lt le_self_add (h.mpr ⟨M + 1, fun t ht => ?_⟩)
    rw [negIndex_heatArchState_eq_boostPolarIndex_add_one]
    push_cast
    exact add_le_add (hM t ht) le_rfl

end GaloisForLFunctions.RenormalizedIntersectionTheory
