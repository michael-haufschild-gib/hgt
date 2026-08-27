import GaloisForLFunctions.HTGeometry.InfiniteNetworkExhaustion
import Mathlib.Order.Interval.Set.IsoIoo
import Mathlib.Topology.Algebra.GroupWithZero

/-!
# Bounded simultaneous generic selection

A countable coefficient field can satisfy countably many residual conditions on literal finite
coordinate restrictions while remaining inside an independently prescribed open interval at every
coordinate.  The proof squeezes each real coordinate into its interval by a continuous open map,
pulls every finite residual condition back through the corresponding finite product map, and then
uses the ambient residual-atlas theorem.

This is stronger than unbounded simultaneous genericity: the selected field can be forced
arbitrarily close, coordinate by coordinate, to a fixed compatible background field.
-/

open Set Topology Filter

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Squeeze one real coordinate into the open interval of radius `radius` around `center`. -/
def boundedGenericCoordinate (center radius x : ℝ) : ℝ :=
  center + radius * (orderIsoIooNegOneOne ℝ x).1

theorem continuous_boundedGenericCoordinate (center radius : ℝ) :
    Continuous (boundedGenericCoordinate center radius) := by
  unfold boundedGenericCoordinate
  fun_prop

/-- A nondegenerate coordinate squeeze is open, although it is not onto all of `ℝ`. -/
theorem isOpenMap_boundedGenericCoordinate (center radius : ℝ) (hradius : radius ≠ 0) :
    IsOpenMap (boundedGenericCoordinate center radius) := by
  have horder : IsOpenMap (orderIsoIooNegOneOne ℝ) :=
    (orderIsoIooNegOneOne ℝ).toHomeomorph.isOpenMap
  have hval : IsOpenMap ((↑) : Ioo (-1 : ℝ) 1 → ℝ) :=
    isOpen_Ioo.isOpenMap_subtype_val
  have hmul : IsOpenMap fun x : ℝ => radius * x :=
    (Homeomorph.mulLeft₀ radius hradius).isOpenMap
  have hadd : IsOpenMap fun x : ℝ => center + x :=
    (Homeomorph.addLeft center).isOpenMap
  exact hadd.comp (hmul.comp (hval.comp horder))

/-- Coordinatewise bounded squeeze on a product of real lines. -/
def boundedGenericPi {ι : Type*} (center radius : ι → ℝ) (x : ι → ℝ) : ι → ℝ :=
  fun i => boundedGenericCoordinate (center i) (radius i) (x i)

theorem continuous_boundedGenericPi {ι : Type*} (center radius : ι → ℝ) :
    Continuous (boundedGenericPi center radius) := by
  exact Continuous.piMap fun i =>
    continuous_boundedGenericCoordinate (center i) (radius i)

/-- A finite product of nondegenerate coordinate squeezes is open.  Finiteness makes the
eventual-surjectivity side condition of `IsOpenMap.piMap` vacuous. -/
theorem isOpenMap_boundedGenericPi {ι : Type*} [Finite ι]
    (center radius : ι → ℝ) (hradius : ∀ i, radius i ≠ 0) :
    IsOpenMap (boundedGenericPi center radius) := by
  apply IsOpenMap.piMap
  · exact fun i =>
      isOpenMap_boundedGenericCoordinate (center i) (radius i) (hradius i)
  · simp

theorem boundedGenericCoordinate_mem_openBall (center radius x : ℝ)
    (hradius : 0 < radius) :
    |boundedGenericCoordinate center radius x - center| < radius := by
  rw [boundedGenericCoordinate]
  have hx : |((orderIsoIooNegOneOne ℝ x).1 : ℝ)| < 1 :=
    abs_lt.2 (orderIsoIooNegOneOne ℝ x).2
  rw [add_sub_cancel_left, abs_mul, abs_of_pos hradius]
  nlinarith

/-- **Bounded residual atlas law.**  Given countably many residual conditions on injectively
selected finite coordinate packets, one ambient field satisfies all conditions simultaneously
while staying inside every prescribed positive-radius coordinate box. -/
theorem exists_bounded_ambientRestrictedGood
    {ι Λ : Type*} [Countable ι] [Countable Λ]
    {n : Λ → ℕ}
    (Good : ∀ a : Λ, Set (Fin (n a) → ℝ))
    (e : ∀ a : Λ, Fin (n a) → ι)
    (he : ∀ a, Function.Injective (e a))
    (center radius : ι → ℝ) (hradius : ∀ i, 0 < radius i)
    (hres : ∀ a, Good a ∈ residual (Fin (n a) → ℝ)) :
    ∃ p : ι → ℝ,
      (∀ i, |p i - center i| < radius i) ∧
      ∀ a, coefficientRestrict (e a) p ∈ Good a := by
  let RawGood : ∀ a : Λ, Set (Fin (n a) → ℝ) := fun a =>
    boundedGenericPi (coefficientRestrict (e a) center)
      (coefficientRestrict (e a) radius) ⁻¹' Good a
  have hRawRes : ∀ a, RawGood a ∈ residual (Fin (n a) → ℝ) := by
    intro a
    apply preimage_mem_residual_of_isOpenMap
    · exact continuous_boundedGenericPi _ _
    · apply isOpenMap_boundedGenericPi
      intro i
      exact (hradius (e a i)).ne'
    · exact hres a
  have hAtlas := ambientRestrictedGoodSet_residual RawGood e he hRawRes
  obtain ⟨x, hx⟩ := hAtlas.2.nonempty
  refine ⟨boundedGenericPi center radius x, ?_, ?_⟩
  · intro i
    exact boundedGenericCoordinate_mem_openBall
      (center i) (radius i) (x i) (hradius i)
  · intro a
    have hxa := hx a
    change boundedGenericPi (coefficientRestrict (e a) center)
        (coefficientRestrict (e a) radius) (coefficientRestrict (e a) x) ∈ Good a at hxa
    have heq : coefficientRestrict (e a) (boundedGenericPi center radius x) =
        boundedGenericPi (coefficientRestrict (e a) center)
          (coefficientRestrict (e a) radius) (coefficientRestrict (e a) x) := rfl
    rw [heq]
    exact hxa

end

end GaloisForLFunctions.HTGeometry
