import GaloisForLFunctions.HeckeKreinToeplitz.TheFiniteIndexStratumOfZetaIsLindelofDeep

/-!
# Heat collisions count the index

The deformation side of the theory. Along the de Bruijn–Newman heat flow `H_t` the nonreal zeros
collide on the real axis and leave; the collision mass after time `t` counts them. Read through the
Weil kernel of `ζ`:

* **Two collisions per negative square** (`eventually_collisionMassAfter_eq_index`): on the finite
  stratum, for all small `t > 0` the collision mass after `t` is `2(κ(K_ζ) + E)`, `E` the
  multiplicity excess of the right zeros; in particular `2κ(K_ζ) ≤ collisionMass(t)`
  (`two_mul_negIndex_zetaKernel_le_collisionMassAfter`).
* **Infinite index is unbounded collision mass** (`tendsto_collisionMassAfter_of_negIndex_eq_top`).
* **The horizontal collision charge dominates the index**
  (`negIndex_zetaKernel_le_iSup_horizontalCollisionCharge`): a charge bound below `2` gives
  `κ(K_ζ) ≤ 1`, hence RH (`riemannHypothesis_of_horizontalCollisionCharge_le_one`).

So the index drop of the heat deformation is counted by collisions, two per negative square, and
the finite-index stratum is the stratum of bounded collision mass.
-/

open Filter Topology
open Zeta23
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (rightZeros)
open GaloisForLFunctions.ArithmeticOrientationGeometry (eventually_collisionMassAfter_eq
  tendsto_collisionMassAfter_atTop encard_rightZeros_le_iSup_horizontalCollisionCharge xiMult)
open RHTower RHTower.BacklundConverse RHTower.LindelofSparse RHTower.DeBruijn

noncomputable section

namespace GaloisForLFunctions.HeckeKreinToeplitz

/-- **The index exit identity for the Weil kernel.** On the finite stratum the collision mass after
small `t` is twice the index plus twice the multiplicity excess. -/
theorem eventually_collisionMassAfter_eq_index (h : negIndex zetaKernel < ⊤) :
    ∃ hfin : (rightZeros zetaZeroConfig).Finite,
      negIndex zetaKernel = hfin.toFinset.card ∧
      ∀ᶠ t in 𝓝[>] (0 : ℝ), collisionMassAfter t =
        2 * (hfin.toFinset.card + ∑ ρ ∈ hfin.toFinset, (xiMult ρ - 1)) := by
  rw [negIndex_zetaKernel] at h ⊢
  have hfin := Set.encard_lt_top_iff.mp h
  exact ⟨hfin, hfin.encard_eq_coe_toFinset_card, eventually_collisionMassAfter_eq hfin⟩

/-- **Two collisions per negative square.** -/
theorem two_mul_negIndex_zetaKernel_le_collisionMassAfter (h : negIndex zetaKernel < ⊤) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), 2 * negIndex zetaKernel ≤ (collisionMassAfter t : ℕ∞) := by
  obtain ⟨hfin, hκ, hev⟩ := eventually_collisionMassAfter_eq_index h
  filter_upwards [hev] with t ht
  rw [hκ, ht]
  push_cast
  exact mul_le_mul_right le_self_add 2

/-- **Infinite index is unbounded collision mass.** -/
theorem tendsto_collisionMassAfter_of_negIndex_eq_top (h : negIndex zetaKernel = ⊤) :
    Tendsto collisionMassAfter (𝓝[>] 0) atTop := by
  rw [negIndex_zetaKernel, Set.encard_eq_top_iff] at h
  exact tendsto_collisionMassAfter_atTop h

/-- **The horizontal collision charge dominates the index.** -/
theorem negIndex_zetaKernel_le_iSup_horizontalCollisionCharge :
    negIndex zetaKernel ≤ ⨆ T : ℝ, (xiHorizontalCollisionCharge T : ℕ∞) := by
  rw [negIndex_zetaKernel]
  exact encard_rightZeros_le_iSup_horizontalCollisionCharge

/-- A horizontal collision charge at most one at every height gives RH. -/
theorem riemannHypothesis_of_horizontalCollisionCharge_le_one
    (h : ∀ T : ℝ, xiHorizontalCollisionCharge T ≤ 1) : RiemannHypothesis := by
  rw [riemannHypothesis_iff_negIndex_zetaKernel_eq_zero, ← negIndex_zetaKernel_le_one_iff]
  exact negIndex_zetaKernel_le_iSup_horizontalCollisionCharge.trans
    (iSup_le fun T => by exact_mod_cast h T)

end GaloisForLFunctions.HeckeKreinToeplitz
