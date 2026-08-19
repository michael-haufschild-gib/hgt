import GaloisForLFunctions.HTGeometry.QuaternionicActualityGraphLock
import GaloisForLFunctions.HTGeometry.QuaternionHiggsMechanism

/-!
# Spin(4) Higgs mechanism

The product of two unit-quaternion groups acts by the corpus's Spin(4) pair
action.  The radial quartic vacuum breaks this product to the exact diagonal
unit-quaternion subgroup.  Its unit-sphere vacuum orbit and `1+3` graph lock
are inherited from existing quaternionic geometry.
-/

open scoped Quaternion RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

abbrev SpinFourGaugeGroup := QuaternionGaugeGroup × QuaternionGaugeGroup

instance : SMul SpinFourGaugeGroup EventQuaternion :=
  ⟨fun g q => spinFourPairAction g.1.1 g.2.1 q⟩

instance : MulAction SpinFourGaugeGroup EventQuaternion where
  one_smul q := by
    change spinFourPairAction (1 : EventQuaternion) (1 : EventQuaternion) q = q
    simp [spinFourPairAction]
  mul_smul g h q := by
    change spinFourPairAction (g.1.1 * h.1.1) (g.2.1 * h.2.1) q =
      spinFourPairAction g.1.1 g.2.1 (spinFourPairAction h.1.1 h.2.1 q)
    simp only [spinFourPairAction, star_mul]
    simp only [mul_assoc]

def spinFourHiggsPotential : EventQuaternion → ℝ := quaternionHiggsPotential

theorem spinFourHiggsPotential_gaugeInvariant (g : SpinFourGaugeGroup)
    (q : EventQuaternion) : spinFourHiggsPotential (g • q) = spinFourHiggsPotential q := by
  change quaternionHiggsPotential
      (spinFourPairAction (g.1.1 : EventQuaternion) (g.2.1 : EventQuaternion) q) =
    quaternionHiggsPotential q
  simp [spinFourPairAction, quaternionHiggsPotential, map_mul, Quaternion.normSq_star,
    quaternionGauge_normSq]

def spinFourHiggsMechanism : HiggsMechanism SpinFourGaugeGroup EventQuaternion where
  vacuum := quaternionHiggsVacuum
  potential := spinFourHiggsPotential
  gauge_invariant := spinFourHiggsPotential_gaugeInvariant
  vacuum_zero := quaternionHiggsPotential_vacuum
  potential_nonneg := quaternionHiggsPotential_nonneg

theorem mem_spinFourHiggs_unbroken_iff_diagonal (g : SpinFourGaugeGroup) :
    g ∈ spinFourHiggsMechanism.unbroken ↔ g.2 = g.1 := by
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  change spinFourPairAction (g.1.1 : EventQuaternion) (g.2.1 : EventQuaternion)
      quaternionHiggsVacuum = quaternionHiggsVacuum ↔ g.2 = g.1
  have hfix := spinFourPairAction_fixes_iff_graph
    (g.1.1 : EventQuaternion) (g.2.1 : EventQuaternion) quaternionHiggsVacuum
    (quaternionGauge_normSq g.1) (quaternionGauge_normSq g.2)
    (by norm_num [quaternionHiggsVacuum, Quaternion.normSq])
  rw [hfix]
  change (g.2.1 : EventQuaternion) = star quaternionHiggsVacuum * g.1.1 *
      quaternionHiggsVacuum ↔ g.2 = g.1
  simp [quaternionHiggsVacuum, Subtype.ext_iff]

def spinFourDiagonalResidual (u : QuaternionGaugeGroup) : SpinFourGaugeGroup := (u, u)

theorem spinFourDiagonalResidual_mem_unbroken (u : QuaternionGaugeGroup) :
    spinFourDiagonalResidual u ∈ spinFourHiggsMechanism.unbroken := by
  rw [mem_spinFourHiggs_unbroken_iff_diagonal]
  rfl

theorem spinFourDiagonalResidual_injective : Function.Injective spinFourDiagonalResidual := by
  intro u v h
  exact congrArg Prod.fst h

theorem quaternionGaugeI_ne_one : quaternionGaugeI ≠ 1 := by
  intro h
  have hq := congrArg (fun u : QuaternionGaugeGroup => (u.1 : EventQuaternion)) h
  have himI := congrArg (fun q : EventQuaternion => q.imI) hq
  norm_num [quaternionGaugeI, quaternionGaugeIValue] at himI

theorem spinFourDiagonalI_ne_one : spinFourDiagonalResidual quaternionGaugeI ≠ 1 := by
  intro h
  apply quaternionGaugeI_ne_one
  exact congrArg Prod.fst h

theorem spinFourHiggs_unbroken_ne_bot : spinFourHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem := spinFourDiagonalResidual_mem_unbroken quaternionGaugeI
  rw [hbot] at hmem
  exact spinFourDiagonalI_ne_one (by simpa using hmem)

def spinFourBrokenWitness : SpinFourGaugeGroup := (quaternionGaugeI, 1)

theorem spinFourBrokenWitness_not_mem_unbroken :
    spinFourBrokenWitness ∉ spinFourHiggsMechanism.unbroken := by
  rw [mem_spinFourHiggs_unbroken_iff_diagonal]
  exact quaternionGaugeI_ne_one.symm

theorem spinFourHiggs_unbroken_ne_top : spinFourHiggsMechanism.unbroken ≠ ⊤ := by
  intro htop
  apply spinFourBrokenWitness_not_mem_unbroken
  rw [htop]
  simp

theorem spinFourHiggs_partiallyBroken : spinFourHiggsMechanism.IsPartiallyBroken :=
  ⟨spinFourHiggs_unbroken_ne_bot, spinFourHiggs_unbroken_ne_top⟩

theorem spinFourGaugeGroup_nonabelian :
    ¬ ∀ g h : SpinFourGaugeGroup, g * h = h * g := by
  intro hcomm
  apply quaternionGaugeGroup_nonabelian
  intro u v
  have h := congrArg Prod.fst (hcomm (u, 1) (v, 1))
  simpa using h

theorem spinFourHiggs_mem_vacuumOrbit_iff (q : EventQuaternion) :
    q ∈ spinFourHiggsMechanism.vacuumOrbit ↔ Quaternion.normSq q = 1 := by
  rw [HiggsMechanism.vacuumOrbit, MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨g, rfl⟩
    change Quaternion.normSq
      (spinFourPairAction (g.1.1 : EventQuaternion) (g.2.1 : EventQuaternion)
        quaternionHiggsVacuum) = 1
    rw [spinFourPairAction, map_mul, map_mul, Quaternion.normSq_star,
      quaternionGauge_normSq, quaternionGauge_normSq]
    norm_num [quaternionHiggsVacuum, Quaternion.normSq]
  · intro hq
    have hnorm : ‖q‖ = 1 := by
      rw [Quaternion.normSq_eq_norm_mul_self] at hq
      nlinarith [norm_nonneg q]
    let u : QuaternionGaugeGroup := ⟨q, mem_sphere_zero_iff_norm.mpr hnorm⟩
    refine ⟨(u, 1), ?_⟩
    change spinFourPairAction (u : EventQuaternion) (1 : EventQuaternion)
      quaternionHiggsVacuum = q
    simp [spinFourPairAction, quaternionHiggsVacuum, u]

theorem spinFourHiggs_one_plus_three :
    (∀ u : QuaternionGaugeGroup,
      spinFourPairAction (u : EventQuaternion) (u : EventQuaternion)
        quaternionHiggsVacuum = quaternionHiggsVacuum) ∧
    (∀ u : QuaternionGaugeGroup, ∀ x : EventQuaternion,
      inner ℝ quaternionHiggsVacuum x = 0 →
      inner ℝ quaternionHiggsVacuum
        (spinFourPairAction (u : EventQuaternion) (u : EventQuaternion) x) = 0) := by
  constructor
  · intro u
    simpa [quaternionHiggsVacuum] using
      spinFourPairAction_graph_fixes (u : EventQuaternion) quaternionHiggsVacuum
        (quaternionGauge_normSq u)
        (by norm_num [quaternionHiggsVacuum, Quaternion.normSq])
  · intro u x hx
    simpa [quaternionHiggsVacuum] using
      spinFourPairAction_graph_preserves_spatial
        (u : EventQuaternion) quaternionHiggsVacuum x
        (by norm_num [quaternionHiggsVacuum, Quaternion.normSq]) hx

end GaloisForLFunctions.HTGeometry
