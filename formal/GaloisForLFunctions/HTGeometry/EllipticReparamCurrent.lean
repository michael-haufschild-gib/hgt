import GaloisForLFunctions.HTGeometry.EllipticVelocityTail

/-!
# The Weierstrass relation and the transported current on the generic reparametrisation

On the generic reparametrisation of the meromorphic plane field the Weierstrass coordinates satisfy
their algebraic relation, the derivative of `℘` acquires the velocity factor, and the square of the
velocity is the rational current of the coordinate:

`(P′)² = (4P³ - g₂P - g₃) · (u′)²`.

This is the `(2,2,2,2)` transported current, now on a carrier where the coordinate is a
differential-generic point rather than a fixed function.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open scoped Differential

/-- Off a point, the lattice is eventually avoided. -/
theorem eventually_notMem_lattice (L : PeriodPair) (x : ℂ) :
    ∀ᶠ z in 𝓝[≠] x, z ∉ L.lattice := by
  have hmem := L.compl_lattice_sdiff_singleton_mem_nhds x
  filter_upwards [mem_nhdsWithin_of_mem_nhds hmem, self_mem_nhdsWithin] with z hz hzx
  intro hcon
  exact hz ⟨hcon, hzx⟩

/-- The Weierstrass relation, as an identity of meromorphic germs. -/
theorem weierstrass_relation_plane (L : PeriodPair) :
    (derivWeierstrassPElement L) ^ 2
      = 4 * (weierstrassPElement L) ^ 3
        - constPlane L.g₂ * weierstrassPElement L - constPlane L.g₃ := by
  have hlhs : (derivWeierstrassPElement L) ^ 2
      = ofMeromorphic (fun z => L.derivWeierstrassP z ^ 2)
        (fun z => (L.meromorphic_derivWeierstrassP z).pow 2) := rfl
  have hrhs : 4 * (weierstrassPElement L) ^ 3
        - constPlane L.g₂ * weierstrassPElement L - constPlane L.g₃
      = ofMeromorphic (fun z => 4 * L.weierstrassP z ^ 3 - L.g₂ * L.weierstrassP z - L.g₃)
        (fun z => (((MeromorphicAt.const (4 : ℂ) z).mul
            ((L.meromorphic_weierstrassP z).pow 3)).sub
          ((MeromorphicAt.const L.g₂ z).mul (L.meromorphic_weierstrassP z))).sub
            (MeromorphicAt.const L.g₃ z)) := rfl
  rw [hlhs, hrhs]
  refine (ofMeromorphic_eq_iff _ _).mpr fun x => ?_
  filter_upwards [eventually_notMem_lattice L x] with z hz
  exact L.derivWeierstrassP_sq z hz

/-- The derivative of `℘` in the plane field is `℘'`. -/
theorem deriv_weierstrassPElement (L : PeriodPair) :
    Differential.deriv (weierstrassPElement L) = derivWeierstrassPElement L := by
  show meromorphicPlaneDeriv _ = _
  rw [weierstrassPElement, meromorphicPlaneDeriv_ofMeromorphic]
  refine (ofMeromorphic_eq_iff _ _).mpr fun x => ?_
  refine Filter.Eventually.of_forall fun z => ?_
  exact congrFun L.deriv_weierstrassP z

/-- The Weierstrass coordinate of the generic reparametrisation. -/
noncomputable def reparamWeierstrassP (L : PeriodPair) : ReparamField MeromorphicPlane :=
  algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (weierstrassPElement L)

/-- The derivative coordinate of the generic reparametrisation. -/
noncomputable def reparamDerivWeierstrassP (L : PeriodPair) : ReparamField MeromorphicPlane :=
  algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (derivWeierstrassPElement L)

/-- **The chain rule for the Weierstrass coordinate.** -/
theorem deriv_reparamWeierstrassP (L : PeriodPair) :
    Differential.deriv (reparamWeierstrassP L)
      = reparamDerivWeierstrassP L * ReparamField.jet 0 := by
  rw [reparamWeierstrassP, reparamDerivWeierstrassP]
  show ReparamField.fieldDerivation MeromorphicPlane _ = _
  rw [← ReparamField.deriv_eq, ReparamField.deriv_algebraMap, deriv_weierstrassPElement]

/-- **The Weierstrass relation on the generic reparametrisation.** -/
theorem weierstrass_relation_reparam (L : PeriodPair) :
    (reparamDerivWeierstrassP L) ^ 2
      = 4 * (reparamWeierstrassP L) ^ 3
        - algebraMap ℂ (ReparamField MeromorphicPlane) L.g₂ * reparamWeierstrassP L
        - algebraMap ℂ (ReparamField MeromorphicPlane) L.g₃ := by
  have hbase : ∀ c : ℂ, algebraMap ℂ (ReparamField MeromorphicPlane) c
      = algebraMap MeromorphicPlane (ReparamField MeromorphicPlane) (constPlane c) := by
    intro c
    rw [IsScalarTower.algebraMap_apply ℂ MeromorphicPlane (ReparamField MeromorphicPlane)]
    rfl
  rw [reparamWeierstrassP, reparamDerivWeierstrassP, hbase, hbase]
  have hmap := congrArg (algebraMap MeromorphicPlane (ReparamField MeromorphicPlane))
    (weierstrass_relation_plane L)
  simp only [map_pow, map_sub, map_mul, map_ofNat] at hmap
  exact hmap

/-- **The `(2,2,2,2)` transported current.**  The square of the velocity is the rational current of
the Weierstrass coordinate. -/
theorem weierstrass_square_current_reparam (L : PeriodPair) :
    (Differential.deriv (reparamWeierstrassP L)) ^ 2
      = (4 * (reparamWeierstrassP L) ^ 3
          - algebraMap ℂ (ReparamField MeromorphicPlane) L.g₂ * reparamWeierstrassP L
          - algebraMap ℂ (ReparamField MeromorphicPlane) L.g₃)
        * (ReparamField.jet 0) ^ 2 := by
  rw [deriv_reparamWeierstrassP, mul_pow, weierstrass_relation_reparam]

end GaloisForLFunctions.HTGeometry
