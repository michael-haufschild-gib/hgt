import GaloisForLFunctions.HTGeometry.HiggsCausalOrbit
import GaloisForLFunctions.HTGeometry.HiggsMechanism

/-!
# Quaternionic non-Abelian Higgs mechanism

The unit quaternions act on event quaternions by left multiplication.  The radial
quartic potential has the unit sphere as one vacuum orbit, the vacuum `1` has
trivial stabilizer, and its infinitesimal orbit is exactly the existing
three-dimensional imaginary-quaternion plane.
-/

open scoped Quaternion RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev QuaternionGaugeGroup := Metric.sphere (0 : EventQuaternion) 1

instance : SMul QuaternionGaugeGroup EventQuaternion :=
  ⟨fun u q => (u.1 : EventQuaternion) * q⟩

instance : MulAction QuaternionGaugeGroup EventQuaternion where
  one_smul q := by
    change (1 : EventQuaternion) * q = q
    simp
  mul_smul u v q := by
    change ((u.1 * v.1) * q) = u.1 * (v.1 * q)
    rw [mul_assoc]

def quaternionHiggsPotential (q : EventQuaternion) : ℝ :=
  (Quaternion.normSq q - 1) ^ 2

def quaternionHiggsVacuum : EventQuaternion := 1

theorem quaternionGauge_normSq (u : QuaternionGaugeGroup) :
    Quaternion.normSq (u : EventQuaternion) = 1 := by
  have hnorm : ‖(u : EventQuaternion)‖ = 1 :=
    mem_sphere_zero_iff_norm.mp u.property
  rw [Quaternion.normSq_eq_norm_mul_self, hnorm, mul_one]

theorem quaternionHiggsPotential_gaugeInvariant (u : QuaternionGaugeGroup)
    (q : EventQuaternion) : quaternionHiggsPotential (u • q) = quaternionHiggsPotential q := by
  change quaternionHiggsPotential ((u : EventQuaternion) * q) = quaternionHiggsPotential q
  rw [quaternionHiggsPotential, quaternionHiggsPotential, map_mul,
    quaternionGauge_normSq, one_mul]

theorem quaternionHiggsPotential_vacuum : quaternionHiggsPotential quaternionHiggsVacuum = 0 := by
  norm_num [quaternionHiggsPotential, quaternionHiggsVacuum, Quaternion.normSq]

theorem quaternionHiggsPotential_nonneg (q : EventQuaternion) :
    0 ≤ quaternionHiggsPotential q := sq_nonneg _

def quaternionHiggsMechanism : HiggsMechanism QuaternionGaugeGroup EventQuaternion where
  vacuum := quaternionHiggsVacuum
  potential := quaternionHiggsPotential
  gauge_invariant := quaternionHiggsPotential_gaugeInvariant
  vacuum_zero := quaternionHiggsPotential_vacuum
  potential_nonneg := quaternionHiggsPotential_nonneg

theorem quaternionHiggs_unbroken_eq_bot : quaternionHiggsMechanism.unbroken = ⊥ := by
  ext u
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    change (u : EventQuaternion) * 1 = 1 at h
    rw [mul_one] at h
    exact Subtype.ext h
  · intro hu
    have hu1 : u = 1 := by simpa using hu
    rw [hu1]
    exact one_smul _ _

theorem quaternionHiggsPotential_eq_zero_iff (q : EventQuaternion) :
    quaternionHiggsPotential q = 0 ↔ Quaternion.normSq q = 1 := by
  rw [quaternionHiggsPotential, sq_eq_zero_iff, sub_eq_zero]

theorem quaternionHiggs_mem_vacuumOrbit_iff (q : EventQuaternion) :
    q ∈ quaternionHiggsMechanism.vacuumOrbit ↔ Quaternion.normSq q = 1 := by
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨u, rfl⟩
    change Quaternion.normSq ((u : EventQuaternion) * 1) = 1
    rw [map_mul, quaternionGauge_normSq]
    norm_num [Quaternion.normSq]
  · intro hq
    have hnorm : ‖q‖ = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self] at hq
      nlinarith [norm_nonneg q]
    let u : QuaternionGaugeGroup := ⟨q, mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨u, ?_⟩
    change (u : EventQuaternion) * 1 = q
    simp [u]

def quaternionGaugeIValue : EventQuaternion := ⟨0, 1, 0, 0⟩
def quaternionGaugeJValue : EventQuaternion := ⟨0, 0, 1, 0⟩

theorem norm_quaternionGaugeIValue : ‖quaternionGaugeIValue‖ = 1 := by
  have hsq : Quaternion.normSq quaternionGaugeIValue = 1 := by
    norm_num [quaternionGaugeIValue, Quaternion.normSq_def']
  rw [Quaternion.normSq_eq_norm_mul_self] at hsq
  nlinarith [norm_nonneg quaternionGaugeIValue]

theorem norm_quaternionGaugeJValue : ‖quaternionGaugeJValue‖ = 1 := by
  have hsq : Quaternion.normSq quaternionGaugeJValue = 1 := by
    norm_num [quaternionGaugeJValue, Quaternion.normSq_def']
  rw [Quaternion.normSq_eq_norm_mul_self] at hsq
  nlinarith [norm_nonneg quaternionGaugeJValue]

def quaternionGaugeI : QuaternionGaugeGroup :=
  ⟨quaternionGaugeIValue, mem_sphere_zero_iff_norm.mpr norm_quaternionGaugeIValue⟩

def quaternionGaugeJ : QuaternionGaugeGroup :=
  ⟨quaternionGaugeJValue, mem_sphere_zero_iff_norm.mpr norm_quaternionGaugeJValue⟩

theorem quaternionGaugeGroup_nonabelian :
    ¬ ∀ u v : QuaternionGaugeGroup, u * v = v * u := by
  intro h
  have huv := congrArg (fun u : QuaternionGaugeGroup => (u.1 : EventQuaternion))
    (h quaternionGaugeI quaternionGaugeJ)
  have himK := congrArg (fun q : EventQuaternion => q.imK) huv
  norm_num [quaternionGaugeI, quaternionGaugeJ, quaternionGaugeIValue,
    quaternionGaugeJValue, QuaternionAlgebra.mk_mul_mk] at himK

theorem quaternionHiggs_goldstoneSpace (x : EventQuaternion) :
    inner ℝ quaternionHiggsVacuum x = 0 ↔
      ∃ a ∈ eventQuaternionImaginary, a * quaternionHiggsVacuum = x := by
  apply pointedSpatial_iff_quaternionLeftOrbitDirection
  simp [quaternionHiggsVacuum]

end GaloisForLFunctions.HTGeometry
