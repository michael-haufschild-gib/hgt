import GaloisForLFunctions.HTGeometry.ClockCalibrationHolonomy
import GaloisForLFunctions.HTGeometry.HiggsMechanism

/-!
# Adjoint Higgs mechanism for clock holonomy

Non-Abelian clock holonomy transforms by conjugation.  A selected holonomy therefore
acts as an adjoint Higgs vacuum: its unbroken subgroup is its centralizer.  For an
explicit transposition in `S₃`, this residual subgroup is nontrivial and proper.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry

@[ext]
structure AdjointHiggsField (G : Type*) where
  val : G

instance {G : Type*} [Group G] : SMul G (AdjointHiggsField G) :=
  ⟨fun g x => ⟨g * x.val * g⁻¹⟩⟩

instance {G : Type*} [Group G] : MulAction G (AdjointHiggsField G) where
  one_smul x := by
    apply AdjointHiggsField.ext
    change 1 * x.val * 1⁻¹ = x.val
    simp
  mul_smul g h x := by
    apply AdjointHiggsField.ext
    change (g * h) * x.val * (g * h)⁻¹ = g * (h * x.val * h⁻¹) * g⁻¹
    group

def clockAdjointVacuum : AdjointHiggsField (Equiv.Perm (Fin 3)) :=
  ⟨Equiv.swap 0 1⟩

def clockAdjointHiggsMechanism :
    HiggsMechanism (Equiv.Perm (Fin 3)) (AdjointHiggsField (Equiv.Perm (Fin 3))) :=
  HiggsMechanism.canonicalOrbitWell clockAdjointVacuum

theorem mem_clockAdjoint_unbroken_iff_commute (g : Equiv.Perm (Fin 3)) :
    g ∈ clockAdjointHiggsMechanism.unbroken ↔
      g * clockAdjointVacuum.val = clockAdjointVacuum.val * g := by
  rw [HiggsMechanism.unbroken, MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hval := congrArg AdjointHiggsField.val h
    change g * clockAdjointVacuum.val * g⁻¹ = clockAdjointVacuum.val at hval
    calc
      g * clockAdjointVacuum.val = (g * clockAdjointVacuum.val * g⁻¹) * g := by simp
      _ = clockAdjointVacuum.val * g := by rw [hval]
  · intro h
    apply AdjointHiggsField.ext
    change g * clockAdjointVacuum.val * g⁻¹ = clockAdjointVacuum.val
    calc
      g * clockAdjointVacuum.val * g⁻¹ =
          (clockAdjointVacuum.val * g) * g⁻¹ := by rw [h]
      _ = clockAdjointVacuum.val := by simp

theorem clockAdjointVacuum_ne_one : clockAdjointVacuum.val ≠ 1 := by
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) h
  simp [clockAdjointVacuum] at h0

theorem clockAdjointVacuum_mem_unbroken :
    clockAdjointVacuum.val ∈ clockAdjointHiggsMechanism.unbroken := by
  rw [mem_clockAdjoint_unbroken_iff_commute]

theorem clockAdjointHiggs_unbroken_ne_bot :
    clockAdjointHiggsMechanism.unbroken ≠ ⊥ := by
  intro hbot
  have hmem := clockAdjointVacuum_mem_unbroken
  rw [hbot] at hmem
  exact clockAdjointVacuum_ne_one (by simpa using hmem)

def clockAdjointBrokenWitness : Equiv.Perm (Fin 3) := Equiv.swap 1 2

theorem clockAdjointBrokenWitness_not_mem_unbroken :
    clockAdjointBrokenWitness ∉ clockAdjointHiggsMechanism.unbroken := by
  rw [mem_clockAdjoint_unbroken_iff_commute]
  intro h
  have h0 := congrArg (fun σ : Equiv.Perm (Fin 3) => σ 0) h
  simp [clockAdjointBrokenWitness, clockAdjointVacuum, Equiv.swap_apply_def] at h0

theorem clockAdjointHiggs_unbroken_ne_top :
    clockAdjointHiggsMechanism.unbroken ≠ ⊤ := by
  intro htop
  apply clockAdjointBrokenWitness_not_mem_unbroken
  rw [htop]
  simp

theorem clockAdjointHiggs_partiallyBroken :
    clockAdjointHiggsMechanism.IsPartiallyBroken :=
  ⟨clockAdjointHiggs_unbroken_ne_bot, clockAdjointHiggs_unbroken_ne_top⟩

def clockAdjointHiggsReadout (a : Equiv.Perm (Fin 3)) : ℝ :=
  clockAdjointHiggsMechanism.potential ⟨a⟩

theorem clockAdjointHiggsReadout_conjugationInvariant :
    ConjugationInvariantClockReadout clockAdjointHiggsReadout := by
  intro g a
  have h := clockAdjointHiggsMechanism.gauge_invariant g⁻¹ (AdjointHiggsField.mk a)
  change clockAdjointHiggsMechanism.potential ⟨g⁻¹ * a * (g⁻¹)⁻¹⟩ =
    clockAdjointHiggsMechanism.potential ⟨a⟩ at h
  simpa [clockAdjointHiggsReadout] using h

theorem clockAdjointHiggsReadout_gaugeInvariant {V : Type*}
    {G : SimpleGraph V} (g : V → Equiv.Perm (Fin 3))
    (c : V → V → Equiv.Perm (Fin 3)) (u : V) (p : G.Walk u u) :
    clockAdjointHiggsReadout
        (clockWalkTransport (clockCalibrationGauge g c) p) =
      clockAdjointHiggsReadout (clockWalkTransport c p) :=
  clockClosedReadout_gauge_invariant clockAdjointHiggsReadout
    clockAdjointHiggsReadout_conjugationInvariant g c u p

end GaloisForLFunctions.HTGeometry
