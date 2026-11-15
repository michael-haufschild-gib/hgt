import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicRealLattice
import GaloisForLFunctions.HTGeometry.IntrinsicLatticeTheta

/-!
# Gaussian theta inversion for cyclic difference lattices

Orthonormal coordinates identify integral cyclic difference vectors with
the actual points of a full coordinate lattice. Their squared norms are
the integral energies. The existing Poisson formula therefore gives
absolute summability and theta inversion, with covolume `sqrt(|G|^3)`.
-/

open scoped BigOperators Matrix
open Module
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry HTGeometry.IntegerLatticePoisson
variable (G : Type) [CommGroup G] [Fintype G] [IsCyclic G] [DecidableEq G]

/-- Orthonormal coordinates of the actual integral lattice vectors. -/
def cyclicDifferenceCoordinates : CyclicDifferenceLattice G →ₗ[ℤ] (CyclicMovingIndex G → ℝ) :=
  ((EuclideanLattice.coordinates (cyclicDifferenceRealBasis G)).restrictScalars ℤ).toLinearMap.comp
    (cyclicDifferenceRealMap G)

/-- The cyclic lattice in orthonormal coordinates. -/
def cyclicDifferenceCoordinateLattice : Submodule ℤ (CyclicMovingIndex G → ℝ) :=
  LinearMap.range (cyclicDifferenceCoordinates G)

theorem cyclicDifferenceCoordinates_injective : Function.Injective (cyclicDifferenceCoordinates G) :=
  (EuclideanLattice.coordinates (cyclicDifferenceRealBasis G)).injective.comp
    (cyclicDifferencePoint_injective G)

theorem cyclicDifferenceCoordinates_norm_sq (v : CyclicDifferenceLattice G) :
    ‖WithLp.toLp 2 (cyclicDifferenceCoordinates G v)‖ ^ 2 = (cyclicMovingEnergy G v : ℝ) := by
  change ‖WithLp.toLp 2 (EuclideanLattice.coordinates (cyclicDifferenceRealBasis G)
    (cyclicDifferenceRealMap G v))‖ ^ 2 = _
  rw [EuclideanLattice.norm_coordinates, ← real_inner_self_eq_norm_sq,
    cyclicDifferenceRealMap_inner, cyclicDifferenceForm_diag]

theorem cyclicDifferenceCoordinateLattice_eq_span :
    cyclicDifferenceCoordinateLattice G = Submodule.span ℤ
      (Set.range (EuclideanLattice.coordinateBasis (cyclicDifferenceRealBasis G))) := by
  have h := Submodule.map_span (cyclicDifferenceCoordinates G) (Set.range (cyclicDifferenceBasis G))
  rw [(cyclicDifferenceBasis G).span_eq, Submodule.map_top] at h
  rw [cyclicDifferenceCoordinateLattice, h]
  congr 1
  have hf (i : CyclicMovingIndex G) :
      EuclideanLattice.coordinateBasis (cyclicDifferenceRealBasis G) i =
        cyclicDifferenceCoordinates G (cyclicDifferenceBasis G i) := by
    rw [EuclideanLattice.coordinateBasis, Basis.map_apply, cyclicDifferenceRealBasis_apply]
    rfl
  ext x
  simp only [Set.mem_image, Set.mem_range, exists_exists_eq_and, hf]

theorem cyclicDifferenceCoordinateLattice_covolume :
    ZLattice.covolume (cyclicDifferenceCoordinateLattice G) = Real.sqrt ((Fintype.card G : ℝ)^3) := by
  rw [cyclicDifferenceCoordinateLattice_eq_span, EuclideanLattice.covolume_coordinateBasis,
    ← cyclicDifferenceRealLattice_eq_span, cyclicDifferenceRealLattice_covolume]

/-- The coordinate dual tests the original Euclidean inner product. -/
theorem cyclicDifferenceCoordinates_pair (v : CyclicDifferenceLattice G)
    (x : CyclicRealHyperplane G) :
    DualZLattice.pair (cyclicDifferenceCoordinates G v)
      (EuclideanLattice.coordinates (cyclicDifferenceRealBasis G) x) =
      inner ℝ (cyclicDifferenceRealMap G v) x := by
  change (∑ i, EuclideanLattice.coordinates (cyclicDifferenceRealBasis G)
    (cyclicDifferenceRealMap G v) i *
    EuclideanLattice.coordinates (cyclicDifferenceRealBasis G) x i) = _
  simp only [EuclideanLattice.coordinates, Basis.equivFun_apply,
    OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_apply_apply]
  simpa only [real_inner_comm (EuclideanLattice.basisOrthonormal (cyclicDifferenceRealBasis G) _)]
    using (EuclideanLattice.basisOrthonormal (cyclicDifferenceRealBasis G)).sum_inner_mul_inner
      (cyclicDifferenceRealMap G v) x

/-- Membership in the dual means integer inner products with every original lattice vector. -/
theorem cyclicDifferenceDual_mem (x : CyclicRealHyperplane G) :
    EuclideanLattice.coordinates (cyclicDifferenceRealBasis G) x ∈
      DualZLattice.dual (cyclicDifferenceCoordinateLattice G) ↔
    ∀ v : CyclicDifferenceLattice G, ∃ m : ℤ,
      inner ℝ (cyclicDifferenceRealMap G v) x = (m : ℝ) := by
  rw [DualZLattice.mem_dual]
  constructor
  · intro h v
    simpa only [cyclicDifferenceCoordinates_pair] using
      h (cyclicDifferenceCoordinates G v) ⟨v, rfl⟩
  · rintro h y ⟨v, rfl⟩
    simpa only [cyclicDifferenceCoordinates_pair] using h v

/-- Integral vectors and geometric lattice points have identical multiplicities. -/
def cyclicDifferenceCoordinateEquiv : CyclicDifferenceLattice G ≃ₗ[ℤ]
    cyclicDifferenceCoordinateLattice G :=
  LinearEquiv.ofInjective (cyclicDifferenceCoordinates G) (cyclicDifferenceCoordinates_injective G)

/-- Gaussian theta summed directly over the integral cyclic difference module. -/
def cyclicDifferenceTheta (t : ℝ) : ℝ :=
  ∑' v : CyclicDifferenceLattice G, Real.exp (-(Real.pi * t) * (cyclicMovingEnergy G v : ℝ))

theorem cyclicDifferenceTheta_eq (t : ℝ) :
    cyclicDifferenceTheta G t = intrinsicLatticeTheta (cyclicDifferenceCoordinateLattice G) t := by
  calc
    cyclicDifferenceTheta G t = ∑' v : CyclicDifferenceLattice G,
        Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (cyclicDifferenceCoordinates G v)‖ ^ 2) :=
      tsum_congr fun v => by rw [cyclicDifferenceCoordinates_norm_sq]
    _ = _ := (cyclicDifferenceCoordinateEquiv G).toEquiv.tsum_eq
      (fun x : cyclicDifferenceCoordinateLattice G =>
        Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (x : CyclicMovingIndex G → ℝ)‖ ^ 2))

/-- The intrinsic integral theta series converges at every positive parameter. -/
theorem summable_cyclicDifferenceTheta {t : ℝ} (ht : 0 < t) :
    Summable (fun v : CyclicDifferenceLattice G =>
      Real.exp (-(Real.pi * t) * (cyclicMovingEnergy G v : ℝ))) := by
  have hs := summable_intrinsicLatticeTheta_basis
    (EuclideanLattice.coordinateBasis (cyclicDifferenceRealBasis G)) ht
  rw [← cyclicDifferenceCoordinateLattice_eq_span] at hs
  have h : Summable (fun v : CyclicDifferenceLattice G =>
      Real.exp (-(Real.pi * t) * ‖WithLp.toLp 2 (cyclicDifferenceCoordinates G v)‖ ^ 2)) :=
    (cyclicDifferenceCoordinateEquiv G).toEquiv.summable_iff.mpr hs
  exact h.congr fun v => by rw [cyclicDifferenceCoordinates_norm_sq]

/-- Poisson inversion with the explicit arithmetic covolume and the integer dual. -/
theorem cyclicDifferenceTheta_inversion {t : ℝ} (ht : 0 < t) :
    cyclicDifferenceTheta G t = (Real.sqrt ((Fintype.card G : ℝ)^3))⁻¹ *
      t ^ (-((Fintype.card (CyclicMovingIndex G) : ℝ) / 2)) *
      intrinsicLatticeTheta (DualZLattice.dual (cyclicDifferenceCoordinateLattice G)) (1 / t) := by
  have h := intrinsicLatticeTheta_basis_inversion
    (EuclideanLattice.coordinateBasis (cyclicDifferenceRealBasis G)) ht
  rw [← cyclicDifferenceCoordinateLattice_eq_span, cyclicDifferenceCoordinateLattice_covolume,
    ← cyclicDifferenceTheta_eq] at h
  simpa only [finrank_euclideanSpace] using h

/-- Theta inversion for the rank `n + 3` unit-ball packing family. -/
theorem cyclicPackingTheta_inversion (n : ℕ) {t : ℝ} (ht : 0 < t) :
    cyclicDifferenceTheta (CyclicPackingGroup n) t = (Real.sqrt ((n + 4 : ℝ)^3))⁻¹ *
      t ^ (-((n + 3 : ℝ) / 2)) *
      intrinsicLatticeTheta (DualZLattice.dual
        (cyclicDifferenceCoordinateLattice (CyclicPackingGroup n))) (1 / t) := by
  have hc : Fintype.card (CyclicMovingIndex (CyclicPackingGroup n)) = n + 3 := by
    have h : Fintype.card (CyclicMovingIndex (CyclicPackingGroup n)) + 1 = n + 4 :=
      (card_subtype_ne_succ (1 : CyclicPackingGroup n)).trans (cyclicPackingGroup_card n)
    omega
  simpa only [cyclicPackingGroup_card, hc, Nat.cast_add, Nat.cast_ofNat] using
    cyclicDifferenceTheta_inversion (CyclicPackingGroup n) ht

#print axioms cyclicDifferenceDual_mem
#print axioms summable_cyclicDifferenceTheta
#print axioms cyclicDifferenceTheta_inversion
#print axioms cyclicPackingTheta_inversion
end GaloisForLFunctions.RepresentationLifting
