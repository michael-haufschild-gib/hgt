import GaloisForLFunctions.RepresentationLifting.Lattices.RegularRootWeight
import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicMovingGram

/-!
# The weight lattice is the integral dual of the moving lattice

Pairing a weight with a zero-sum regular vector is independent of the diagonal
representative. This pairing is perfect. The natural root-to-weight map is
therefore the metric map into the integral dual, and its cyclic cokernel is
the discriminant group of the moving lattice.
-/

noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry.IntegralZeroSum
namespace GaloisForLFunctions.RepresentationLifting
variable (G : Type) [CommGroup G] [Fintype G]

/-- Weights act on integral moving vectors by the coordinate pairing. -/
def regularWeightToDual (p : G) :
    coordinateWeightLattice G p →ₗ[ℤ] Module.Dual ℤ (CyclicIntegralMoving G) where
  toFun w :=
    { toFun v := pairing w.val (cyclicMovingProfile G v)
      map_add' v u := by
        simp only [pairing, map_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      map_smul' c v := by
        simp only [pairing, map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun _ _ => by ring }
  map_add' v w := by
    ext u
    change (∑ g, (v.val g + w.val g) * cyclicMovingProfile G u g) =
      (∑ g, v.val g * cyclicMovingProfile G u g) +
        ∑ g, w.val g * cyclicMovingProfile G u g
    simp only [add_mul, Finset.sum_add_distrib]
  map_smul' c w := by
    ext u
    change (∑ g, (c * w.val g) * cyclicMovingProfile G u g) =
      c * ∑ g, w.val g * cyclicMovingProfile G u g
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun _ _ => mul_assoc _ _ _

/-- Coordinate roots read off weight differences. -/
theorem regularWeightToDual_root (p : G) (w : coordinateWeightLattice G p) (a b : G) :
    regularWeightToDual G p w (cyclicRootVector G a b) = w.val a - w.val b := by
  change pairing w.val (cyclicMovingProfile G (cyclicRootVector G a b)) = _
  rw [cyclicMovingProfile_root, pairing_root_right]

theorem regularWeightToDual_injective (p : G) : Function.Injective (regularWeightToDual G p) := by
  intro v w h
  apply Subtype.ext
  funext g
  have he := congrArg (fun f => f (cyclicRootVector G g p)) h
  rw [regularWeightToDual_root, regularWeightToDual_root] at he
  have hv : v.val p = 0 := v.property
  have hw : w.val p = 0 := w.property
  simpa only [hv, hw, sub_zero] using he

/-- Values on the coordinate roots reconstruct every integral linear functional. -/
theorem regularWeightToDual_surjective (p : G) : Function.Surjective (regularWeightToDual G p) := by
  classical
  intro f
  let w : coordinateWeightLattice G p :=
    ⟨fun g => f (cyclicRootVector G g 1) - f (cyclicRootVector G p 1), sub_self _⟩
  refine ⟨w, (cyclicMovingBasis G).ext fun i => ?_⟩
  rw [cyclicMovingBasis_apply, regularWeightToDual_root]
  have hz : f (cyclicRootVector G 1 1) = 0 := by
    have hr : cyclicRootVector G 1 1 = 0 := Subtype.ext (sub_self _)
    rw [hr, map_zero]
  change (f (cyclicRootVector G i.val 1) - f (cyclicRootVector G p 1)) -
    (f (cyclicRootVector G 1 1) - f (cyclicRootVector G p 1)) = _
  rw [hz]
  abel

/-- The pointed weight lattice is the full integral dual of the norm kernel. -/
def regularWeightDualEquiv (p : G) :
    coordinateWeightLattice G p ≃ₗ[ℤ] Module.Dual ℤ (CyclicIntegralMoving G) :=
  LinearEquiv.ofBijective (regularWeightToDual G p)
    ⟨regularWeightToDual_injective G p, regularWeightToDual_surjective G p⟩

/-- The root-to-weight inclusion is the metric map to the integral dual. -/
theorem regularWeightToDual_rootToWeight (p : G) (v u : CyclicIntegralMoving G) :
    regularWeightToDual G p (regularRootToWeight G p v) u = cyclicMovingForm G v u := by
  change (∑ g, (cyclicMovingProfile G v g - cyclicMovingProfile G v p) *
    cyclicMovingProfile G u g) = ∑ g, cyclicMovingProfile G v g * cyclicMovingProfile G u g
  simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum,
    cyclicMovingProfile_sum, mul_zero, sub_zero]

theorem regularWeightDualEquiv_map_range (p : G) :
    Submodule.map (regularWeightDualEquiv G p).toLinearMap
      (LinearMap.range (regularRootToWeight G p)) = LinearMap.range (cyclicMovingForm G) := by
  ext f
  constructor
  · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
    refine ⟨v, ?_⟩
    ext u
    exact (regularWeightToDual_rootToWeight G p v u).symm
  · rintro ⟨v, rfl⟩
    refine ⟨regularRootToWeight G p v, ⟨v, rfl⟩, ?_⟩
    ext u
    exact regularWeightToDual_rootToWeight G p v u

/-- The discriminant group of the integral moving lattice is cyclic of order `|G|`. -/
def regularDiscriminantEquiv [Nontrivial G] (p : G) :
    (Module.Dual ℤ (CyclicIntegralMoving G) ⧸ LinearMap.range (cyclicMovingForm G)) ≃ₗ[ℤ]
      ZMod (Fintype.card G) :=
  (Submodule.Quotient.equiv _ _ (regularWeightDualEquiv G p)
    (regularWeightDualEquiv_map_range G p)).symm.trans (regularRootWeightCokernelEquiv G p)

#print axioms regularWeightDualEquiv
#print axioms regularWeightToDual_rootToWeight
#print axioms regularDiscriminantEquiv
end GaloisForLFunctions.RepresentationLifting
