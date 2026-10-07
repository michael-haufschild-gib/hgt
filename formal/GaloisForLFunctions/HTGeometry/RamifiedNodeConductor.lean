import GaloisForLFunctions.HTGeometry.ConductorNearbyCycleSpecialization

/-!
# Ramification and the conductor invariant channel

The `k`-fold ordinary-node shear fixes exactly pairs whose second coordinate is killed by `k`.
Its invariant module splits into the conductor line and the coefficient `k`-torsion. In
characteristic zero domains the conductor line exhausts the invariants at every positive
ramification order; after reduction modulo that order the entire plane is invariant.

These are coefficient-level statements. Identifying a concrete analytic family's geometric
monodromy with the shear requires a separate comparison.
-/

namespace GaloisForLFunctions.HTGeometry

variable (A : Type*) [CommRing A]

/-- Each turn adds one copy of the transverse coordinate. -/
theorem universalNodePicardLefschetzMonodromy_pow_apply (k : ℕ) (v : A × A) :
    (universalNodePicardLefschetzMonodromy A ^ k) v =
      (v.1 + (k : A) * v.2, v.2) := by
  induction k generalizing v with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    simp only [universalNodePicardLefschetzMonodromy_apply, Nat.cast_add, Nat.cast_one]
    apply Prod.ext
    · ring
    · rfl

/-- Fixed module after `k` turns of the nodal shear. -/
def ramifiedNodeMonodromyInvariants (k : ℕ) : Submodule A (A × A) :=
  LinearMap.ker (universalNodePicardLefschetzMonodromy A ^ k - LinearMap.id)

/-- The additional fixed coordinate is exactly coefficient torsion. -/
@[simp]
theorem mem_ramifiedNodeMonodromyInvariants_iff (k : ℕ) (v : A × A) :
    v ∈ ramifiedNodeMonodromyInvariants A k ↔ (k : A) * v.2 = 0 := by
  rw [ramifiedNodeMonodromyInvariants, LinearMap.mem_ker]
  simp only [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero,
    universalNodePicardLefschetzMonodromy_pow_apply]
  constructor
  · intro h
    have hfirst := congrArg Prod.fst h
    simpa using hfirst
  · intro h
    apply Prod.ext
    · simp [h]
    · rfl

/-- Coefficients annihilated by the ramification order. -/
def nodeCoefficientTorsion (k : ℕ) : Submodule A A :=
  LinearMap.ker ((k : A) • (LinearMap.id : A →ₗ[A] A))

@[simp]
theorem mem_nodeCoefficientTorsion_iff (k : ℕ) (b : A) :
    b ∈ nodeCoefficientTorsion A k ↔ (k : A) * b = 0 := by
  simp [nodeCoefficientTorsion]

/-- Complete invariant module: conductor coefficients and the transverse torsion channel. -/
def ramifiedNodeInvariantEquiv (k : ℕ) :
    ramifiedNodeMonodromyInvariants A k ≃ₗ[A] A × nodeCoefficientTorsion A k where
  toFun v := (v.1.1, ⟨v.1.2, (mem_nodeCoefficientTorsion_iff A k _).2
    ((mem_ramifiedNodeMonodromyInvariants_iff A k _).1 v.2)⟩)
  invFun v := ⟨(v.1, v.2.1), (mem_ramifiedNodeMonodromyInvariants_iff A k _).2
    ((mem_nodeCoefficientTorsion_iff A k _).1 v.2.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem mem_universalNodeConductorSpecialization_range_iff (v : A × A) :
    v ∈ LinearMap.range (universalNodeConductorSpecialization A) ↔ v.2 = 0 := by
  rw [universalNodeConductorSpecialization_range_eq_monodromyInvariants,
    mem_universalNodeMonodromyInvariants_iff]

/-- Conductor exhaustion holds exactly when the ramification order kills no coefficient. -/
theorem universalNodeConductorSpecialization_range_eq_ramified_iff (k : ℕ) :
    LinearMap.range (universalNodeConductorSpecialization A) =
      ramifiedNodeMonodromyInvariants A k ↔
        ∀ b : A, (k : A) * b = 0 → b = 0 := by
  constructor
  · intro h b hb
    have hv : (0, b) ∈ ramifiedNodeMonodromyInvariants A k :=
      (mem_ramifiedNodeMonodromyInvariants_iff A k _).2 hb
    rw [← h, mem_universalNodeConductorSpecialization_range_iff] at hv
    exact hv
  · intro h
    ext v
    rw [mem_universalNodeConductorSpecialization_range_iff,
      mem_ramifiedNodeMonodromyInvariants_iff]
    exact ⟨fun hv => by rw [hv, mul_zero], h v.2⟩

/-- Ramification never removes a conductor coefficient from the fixed module. -/
theorem universalNodeConductorSpecialization_ramified_fixed (k : ℕ) (a : A) :
    (universalNodePicardLefschetzMonodromy A ^ k)
        (universalNodeConductorSpecialization A a) =
      universalNodeConductorSpecialization A a := by
  simp [universalNodePicardLefschetzMonodromy_pow_apply]

/-- Over characteristic-zero domains, every positive order retains exactly the conductor line. -/
theorem universalNodeConductorSpecialization_range_eq_ramified_succ
    [IsDomain A] [CharZero A] (m : ℕ) :
    LinearMap.range (universalNodeConductorSpecialization A) =
      ramifiedNodeMonodromyInvariants A (m + 1) := by
  rw [universalNodeConductorSpecialization_range_eq_ramified_iff]
  intro b hb
  exact (mul_eq_zero.mp hb).resolve_left (Nat.cast_ne_zero.mpr (Nat.succ_ne_zero m))

/-- Reduction modulo the ramification order makes the whole plane invariant. -/
theorem ramifiedNodeMonodromyInvariants_zmod (k : ℕ) :
    ramifiedNodeMonodromyInvariants (ZMod k) k = ⊤ := by
  ext v
  simp

/-- The squared shear has strictly more invariants than conductor coefficients modulo two. -/
theorem universalNodeConductorSpecialization_range_ne_ramified_mod_two :
    LinearMap.range (universalNodeConductorSpecialization (ZMod 2)) ≠
      ramifiedNodeMonodromyInvariants (ZMod 2) 2 := by
  intro h
  have hb := (universalNodeConductorSpecialization_range_eq_ramified_iff (ZMod 2) 2).1
    h 1 ((mul_one (2 : ZMod 2)).trans (ZMod.natCast_self 2))
  exact one_ne_zero hb

end GaloisForLFunctions.HTGeometry
