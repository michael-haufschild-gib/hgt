import GaloisForLFunctions.RepresentationLifting.Lattices.CyclicFirstMoment
import GaloisForLFunctions.HTGeometry.Lattices.IntegralZeroSumEnergy

/-!
# Rootless cyclic difference lattices

The norm kernel in the integral regular representation consists of zero-sum
vectors. Its norm-two vectors are precisely coordinate differences. The
first-moment obstruction excludes every nonzero root from the restricted
cyclic difference image. This image is therefore even and rootless, with
minimum squared norm four whenever the cyclic group has at least four elements.

These are explicit positive definite lattices satisfying the rootlessness
condition used in Section 3 of Auel–Shaikh (https://arxiv.org/abs/2611.13468).
-/

open scoped BigOperators
noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open HTGeometry.IntegralZeroSum
variable (G : Type) [CommGroup G] [Fintype G]

/-- Integral coordinates of a moving regular vector. -/
def cyclicMovingProfile : CyclicIntegralMoving G →ₗ[ℤ] (G → ℤ) where
  toFun v g := v.val.coeff g
  map_add' v w := by
    ext g
    change (v.val + w.val).coeff g = _
    rw [MonoidAlgebra.coeff_add]
    rfl
  map_smul' c v := by
    ext g
    change (c • v.val).coeff g = c • v.val.coeff g
    rw [MonoidAlgebra.coeff_smul]
    rfl

theorem cyclicMovingProfile_injective : Function.Injective (cyclicMovingProfile G) := by
  intro v w h
  apply Subtype.ext
  ext g
  exact congrFun h g

/-- The moving condition is zero coordinate sum. -/
theorem cyclicMovingProfile_sum (v : CyclicIntegralMoving G) :
    ∑ g, cyclicMovingProfile G v g = 0 :=
  (cyclicRegularNorm_eq_zero_iff G v).mp v.property

theorem cyclicMovingProfile_root (a b : G) :
    cyclicMovingProfile G (cyclicRootVector G a b) = root a b := by
  classical
  ext g
  change (MonoidAlgebra.single a (1 : ℤ) - MonoidAlgebra.single b 1).coeff g = _
  rw [MonoidAlgebra.coeff_sub, MonoidAlgebra.coeff_single, MonoidAlgebra.coeff_single]
  simp [root, Finsupp.single_apply, Pi.single_apply, eq_comm]

/-- The squared Euclidean norm in regular coordinates. -/
def cyclicMovingEnergy (v : CyclicIntegralMoving G) : ℤ := energy (cyclicMovingProfile G v)

theorem cyclicMovingEnergy_eq_zero_iff (v : CyclicIntegralMoving G) :
    cyclicMovingEnergy G v = 0 ↔ v = 0 := by
  rw [cyclicMovingEnergy, energy_eq_zero_iff]
  exact ⟨fun h => cyclicMovingProfile_injective G (h.trans (map_zero _).symm),
    fun h => h ▸ map_zero _⟩

theorem cyclicMovingEnergy_even (v : CyclicIntegralMoving G) : Even (cyclicMovingEnergy G v) :=
  energy_even (cyclicMovingProfile_sum G v)

/-- The norm-two moving vectors are exactly the nonzero coordinate roots. -/
theorem cyclicMovingEnergy_two_iff (v : CyclicIntegralMoving G) :
    cyclicMovingEnergy G v = 2 ↔ ∃ a b, a ≠ b ∧ v = cyclicRootVector G a b := by
  classical
  constructor
  · intro h
    obtain ⟨a, b, hab, hv⟩ := exists_root_of_energy_two (cyclicMovingProfile_sum G v) h
    exact ⟨a, b, hab, cyclicMovingProfile_injective G (hv.trans (cyclicMovingProfile_root G a b).symm)⟩
  · rintro ⟨a, b, hab, rfl⟩
    rw [cyclicMovingEnergy, cyclicMovingProfile_root, energy_root, if_neg hab]

variable [IsCyclic G]

/-- The image of cyclic difference restricted to the augmentation lattice. -/
def CyclicDifferenceLattice := LinearMap.range (cyclicMovingDelta G)

/-- Every nonzero vector in the cyclic difference image has squared norm at least four. -/
theorem cyclicDifference_energy_ge_four (v : CyclicDifferenceLattice G) (hv : v ≠ 0) :
    4 ≤ cyclicMovingEnergy G v := by
  apply four_le_energy_of_no_root (cyclicMovingProfile_sum G v)
  · intro h
    exact hv (Subtype.ext (cyclicMovingProfile_injective G (h.trans (map_zero _).symm)))
  · intro a b hab he
    have he' : v.val = cyclicRootVector G a b :=
      cyclicMovingProfile_injective G (he.trans (cyclicMovingProfile_root G a b).symm)
    have hm := v.property
    rw [he'] at hm
    exact hab ((cyclicRootVector_mem_range_iff G a b).mp hm)

/-- A cyclic difference of a root is the translated root minus the original root. -/
theorem cyclicMovingDelta_root (a b : G) :
    cyclicMovingDelta G (cyclicRootVector G a b) =
      cyclicRootVector G (cyclicRegularGenerator G * a) (cyclicRegularGenerator G * b) -
        cyclicRootVector G a b := by
  apply Subtype.ext
  simp only [cyclicMovingDelta, cyclicDeltaToMoving, cyclicRootVector,
    LinearMap.comp_apply, LinearMap.codRestrict_apply, Submodule.subtype_apply]
  have hd (v : CyclicRegular ℤ G) : cyclicRegularDelta ℤ G v =
      Representation.leftRegular ℤ G (cyclicRegularGenerator G) v - v := rfl
  rw [hd, map_sub, Representation.ofMulAction_single, Representation.ofMulAction_single]
  rfl

/-- Four distinct consecutive powers give a vector of squared norm four. -/
theorem cyclicDifference_energy_four_exists (hn : 4 ≤ Fintype.card G) :
    ∃ v : CyclicDifferenceLattice G, cyclicMovingEnergy G v = 4 := by
  classical
  let σ := cyclicRegularGenerator G
  have hne (a b : ℕ) (ha : a < 4) (hb : b < 4) (hab : a ≠ b) : σ ^ a ≠ σ ^ b := by
    intro h
    apply hab
    exact pow_injOn_Iio_orderOf
      (by change a < orderOf σ; rw [cyclicRegularGenerator_order]; omega)
      (by change b < orderOf σ; rw [cyclicRegularGenerator_order]; omega) h
  have h01 := hne 0 1 (by omega) (by omega) (by omega)
  have h02 := hne 0 2 (by omega) (by omega) (by omega)
  have h03 := hne 0 3 (by omega) (by omega) (by omega)
  have h12 := hne 1 2 (by omega) (by omega) (by omega)
  have h13 := hne 1 3 (by omega) (by omega) (by omega)
  have h23 := hne 2 3 (by omega) (by omega) (by omega)
  simp only [pow_zero, pow_one] at h01 h02 h03 h12 h13
  refine ⟨⟨cyclicMovingDelta G (cyclicRootVector G 1 (σ^2)), ⟨_, rfl⟩⟩, ?_⟩
  change energy (cyclicMovingProfile G (cyclicMovingDelta G (cyclicRootVector G 1 (σ^2)))) = 4
  rw [cyclicMovingDelta_root, map_sub, cyclicMovingProfile_root, cyclicMovingProfile_root]
  change energy (root (σ * 1) (σ * σ^2) - root 1 (σ^2)) = 4
  rw [mul_one, ← pow_succ', energy_sub, energy_root, energy_root,
    if_neg h13, if_neg h02, pairing_root_left]
  simp [root, h01, h03, h12, h23]

#print axioms cyclicDifference_energy_four_exists

#print axioms cyclicDifference_energy_ge_four
#print axioms cyclicMovingEnergy_two_iff
end GaloisForLFunctions.RepresentationLifting
