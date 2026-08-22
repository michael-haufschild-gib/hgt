import GaloisForLFunctions.HTGeometry.QuaternionHiggsMechanism
import GaloisForLFunctions.HTGeometry.AbelianHiggsMechanism

/-!
# Quaternionic electroweak-style Higgs mechanism

The product of unit quaternions and the complex unit circle acts on an event
quaternion by left and right multiplication.  The radial vacuum sphere is one
orbit.  A diagonal circle embeds in the residual subgroup, while an explicit
quaternion generator is broken.  The resulting mechanism is partially broken
and retains the existing three-dimensional infinitesimal orbit.
-/

open scoped Quaternion

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev ElectroweakGaugeGroup := QuaternionGaugeGroup × Circle

theorem quaternionNormSq_coeCircle (z : Circle) :
    Quaternion.normSq (((z : ℂ) : EventQuaternion)) = 1 := by
  simpa [Quaternion.normSq_def', Complex.normSq_apply, pow_two] using Circle.normSq_coe z

instance : SMul ElectroweakGaugeGroup EventQuaternion :=
  ⟨fun g q => (g.1.1 : EventQuaternion) * q * (((g.2 : Circle) : ℂ) : EventQuaternion)⟩

instance : MulAction ElectroweakGaugeGroup EventQuaternion where
  one_smul q := by
    change (1 : EventQuaternion) * q * (((1 : Circle) : ℂ) : EventQuaternion) = q
    simp [Quaternion.coeComplex_one]
  mul_smul g h q := by
    change ((g.1.1 * h.1.1 : EventQuaternion) * q *
        ((((g.2 * h.2 : Circle) : ℂ)) : EventQuaternion)) =
      (g.1.1 : EventQuaternion) *
        ((h.1.1 : EventQuaternion) * q * (((h.2 : Circle) : ℂ) : EventQuaternion)) *
          (((g.2 : Circle) : ℂ) : EventQuaternion)
    have hc : (((((g.2 * h.2 : Circle) : ℂ)) : EventQuaternion)) =
        (((h.2 : Circle) : ℂ) : EventQuaternion) *
          (((g.2 : Circle) : ℂ) : EventQuaternion) := by
      rw [← Quaternion.coeComplex_mul]
      congr 2
      exact mul_comm _ _
    rw [hc]
    simp only [mul_assoc]

def electroweakHiggsPotential : EventQuaternion → ℝ := quaternionHiggsPotential

theorem electroweakHiggsPotential_gaugeInvariant (g : ElectroweakGaugeGroup)
    (q : EventQuaternion) :
    electroweakHiggsPotential (g • q) = electroweakHiggsPotential q := by
  change quaternionHiggsPotential
      ((g.1.1 : EventQuaternion) * q * (((g.2 : Circle) : ℂ) : EventQuaternion)) =
    quaternionHiggsPotential q
  simp [quaternionHiggsPotential, map_mul, quaternionGauge_normSq,
    quaternionNormSq_coeCircle]

def electroweakHiggsMechanism : HiggsMechanism ElectroweakGaugeGroup EventQuaternion where
  vacuum := quaternionHiggsVacuum
  potential := electroweakHiggsPotential
  gauge_invariant := electroweakHiggsPotential_gaugeInvariant
  vacuum_zero := quaternionHiggsPotential_vacuum
  potential_nonneg := quaternionHiggsPotential_nonneg

private def circleQuaternion (z : Circle) : QuaternionGaugeGroup := by
  have hsq : Quaternion.normSq (((z : ℂ) : EventQuaternion)) = 1 :=
    quaternionNormSq_coeCircle z
  have hnorm : ‖(((z : ℂ) : EventQuaternion))‖ = 1 := by
    rw [Quaternion.normSq_eq_norm_mul_self] at hsq
    nlinarith [norm_nonneg (((z : ℂ) : EventQuaternion))]
  exact ⟨((z : ℂ) : EventQuaternion), mem_sphere_zero_iff_norm.mpr hnorm⟩

def electroweakResidual (z : Circle) : ElectroweakGaugeGroup :=
  (circleQuaternion z⁻¹, z)

theorem electroweakResidual_fixes_vacuum (z : Circle) :
    electroweakResidual z • quaternionHiggsVacuum = quaternionHiggsVacuum := by
  change (((z⁻¹ : Circle) : ℂ) : EventQuaternion) * 1 *
      (((z : Circle) : ℂ) : EventQuaternion) = 1
  rw [mul_one, ← Quaternion.coeComplex_mul]
  simp

theorem electroweakResidual_mem_unbroken (z : Circle) :
    electroweakResidual z ∈ electroweakHiggsMechanism.unbroken := by
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  exact electroweakResidual_fixes_vacuum z

theorem electroweakResidual_injective : Function.Injective electroweakResidual := by
  intro z w h
  exact congrArg Prod.snd h

theorem circle_negOne_ne_one : (-1 : Circle) ≠ 1 := by
  intro h
  have hc := congrArg (fun z : Circle => (z : ℂ)) h
  norm_num [Complex.ext_iff] at hc

theorem electroweakResidual_negOne_ne_one : electroweakResidual (-1) ≠ 1 := by
  intro h
  apply circle_negOne_ne_one
  exact congrArg Prod.snd h

theorem electroweakHiggs_unbroken_ne_bot : electroweakHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem := electroweakResidual_mem_unbroken (-1)
  rw [hbot] at hmem
  exact electroweakResidual_negOne_ne_one (by simpa using hmem)

def electroweakBrokenWitness : ElectroweakGaugeGroup := (quaternionGaugeI, 1)

theorem electroweakBrokenWitness_not_fix :
    electroweakBrokenWitness • quaternionHiggsVacuum ≠ quaternionHiggsVacuum := by
  intro h
  change quaternionGaugeIValue * 1 * (1 : EventQuaternion) = 1 at h
  simp only [mul_one] at h
  have himI := congrArg (fun q : EventQuaternion => q.imI) h
  norm_num [quaternionGaugeIValue] at himI

theorem electroweakHiggs_unbroken_ne_top : electroweakHiggsMechanism.unbroken ≠ ⊤ := by
  intro htop
  apply electroweakBrokenWitness_not_fix
  have hmem : electroweakBrokenWitness ∈ electroweakHiggsMechanism.unbroken := by
    rw [htop]
    simp
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff] at hmem
  exact hmem

theorem electroweakHiggs_partiallyBroken : electroweakHiggsMechanism.IsPartiallyBroken :=
  ⟨electroweakHiggs_unbroken_ne_bot, electroweakHiggs_unbroken_ne_top⟩

theorem electroweakGaugeGroup_nonabelian :
    ¬ ∀ g h : ElectroweakGaugeGroup, g * h = h * g := by
  intro hcomm
  apply quaternionGaugeGroup_nonabelian
  intro u v
  have h := congrArg Prod.fst (hcomm (u, 1) (v, 1))
  simpa using h

theorem electroweakHiggs_mem_vacuumOrbit_iff (q : EventQuaternion) :
    q ∈ electroweakHiggsMechanism.vacuumOrbit ↔ Quaternion.normSq q = 1 := by
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    change Quaternion.normSq
      ((g.1.1 : EventQuaternion) * 1 * (((g.2 : Circle) : ℂ) : EventQuaternion)) = 1
    rw [map_mul, map_mul, quaternionGauge_normSq, quaternionNormSq_coeCircle]
    norm_num [Quaternion.normSq]
  · intro hq
    have hnorm : ‖q‖ = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self] at hq
      nlinarith [norm_nonneg q]
    let u : QuaternionGaugeGroup := ⟨q, mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨(u, 1), ?_⟩
    change (u : EventQuaternion) * 1 * (((1 : Circle) : ℂ) : EventQuaternion) = q
    simp [u, Quaternion.coeComplex_one]

theorem electroweakHiggs_goldstoneSpace (x : EventQuaternion) :
    inner ℝ quaternionHiggsVacuum x = 0 ↔
      ∃ a ∈ eventQuaternionImaginary, a * quaternionHiggsVacuum = x :=
  quaternionHiggs_goldstoneSpace x

end GaloisForLFunctions.HTGeometry
