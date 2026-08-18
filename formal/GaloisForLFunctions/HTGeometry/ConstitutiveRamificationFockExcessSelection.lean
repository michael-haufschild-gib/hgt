import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.RamificationBooleanSupport
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessDirichlet
import GaloisForLFunctions.HTGeometry.ComplexTimeEulerShellGeneration

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower
open _root_.HTGeometry.ConstraintFrameRelativity

noncomputable section

open scoped Classical in
/-- Perfect-power (fermionic Fock) part of the level-`m` shell mass. -/
noncomputable def ramificationFockMass (m : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  if IsRPow m N then shellMass m σ N else 0

open scoped Classical in
/-- Mixed-exponent complement of the perfect-power Fock part. -/
noncomputable def ramificationInteractionMass (m : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  if IsRPow m N then 0 else shellMass m σ N

/-- One-particle sector: perfect powers whose root is one prime. -/
def IsRamificationOneParticle (m N : ℕ) : Prop :=
  ∃ p : ℕ, p.Prime ∧ p ^ m = N

open scoped Classical in
/-- Prime/Mass/phase layer of the source-selected Fock sector. -/
noncomputable def ramificationOneParticleMass (m : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  if IsRamificationOneParticle m N then ramificationFockMass m σ N else 0

open scoped Classical in
/-- Multi-particle hard-core Boolean layer of the source-selected Fock sector. -/
noncomputable def ramificationManyParticleMass (m : ℕ) (σ : ℝ) (N : ℕ) : ℝ :=
  if IsRamificationOneParticle m N then 0 else ramificationFockMass m σ N

@[simp] theorem ramificationOneParticleMass_add_manyParticleMass
    (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationOneParticleMass m σ N + ramificationManyParticleMass m σ N =
      ramificationFockMass m σ N := by
  classical
  by_cases h : IsRamificationOneParticle m N <;>
    simp [ramificationOneParticleMass, ramificationManyParticleMass, h]

@[simp] theorem ramificationFockMass_add_interactionMass (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationFockMass m σ N + ramificationInteractionMass m σ N = shellMass m σ N := by
  classical
  by_cases h : IsRPow m N <;> simp [ramificationFockMass, ramificationInteractionMass, h]

/-- Exact three-layer source reconstruction. -/
theorem ramification_threeLayer_reconstruction (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationOneParticleMass m σ N + ramificationManyParticleMass m σ N +
        ramificationInteractionMass m σ N = shellMass m σ N := by
  rw [ramificationOneParticleMass_add_manyParticleMass,
    ramificationFockMass_add_interactionMass]

/-- On `m`-th powers, the Fock mass is exactly the level-one squarefree mass at dilated exponent. -/
theorem ramificationFockMass_pow {m : ℕ} (hm : m ≠ 0) (σ : ℝ) (k : ℕ) :
    ramificationFockMass m σ (k ^ m) = shellMass 1 ((m : ℝ) * σ) k := by
  rw [ramificationFockMass, if_pos (isRPow_pow m k)]
  unfold shellMass
  have hs := shellIndicator_pow (m := 1) hm k
  simp only [mul_one] at hs
  rw [hs]
  rcases eq_or_ne k 0 with rfl | hk
  · rw [zero_pow hm]
    simp
  · rw [Nat.cast_pow, Real.rpow_mul (Nat.cast_nonneg k), Real.rpow_natCast]

/-- The Fock image is supported on the range of `k ↦ k^m`. -/
theorem ramificationFockMass_eq_zero_of_not_mem_range {m : ℕ} (σ : ℝ) {N : ℕ}
    (hN : N ∉ Set.range fun k : ℕ => k ^ m) : ramificationFockMass m σ N = 0 := by
  rw [ramificationFockMass, if_neg]
  rintro ⟨k, rfl⟩
  exact hN ⟨k, rfl⟩

/-- The whole perfect-power Fock image is summable at the ambient shell wall. -/
theorem summable_ramificationFockMass_at_wall {m : ℕ} (hm : 2 ≤ m) :
    Summable (ramificationFockMass m 1) := by
  have hinj : Function.Injective (fun k : ℕ => k ^ m) :=
    Nat.pow_left_injective (by omega)
  rw [← hinj.summable_iff (fun N hN => ramificationFockMass_eq_zero_of_not_mem_range 1 hN)]
  have hbase := summable_shellMass 1 (show 1 < (m : ℝ) by exact_mod_cast hm)
  exact hbase.congr fun k => by
    rw [Function.comp_apply, ramificationFockMass_pow (by omega) 1]
    simp

theorem ramificationFockMass_nonneg (m : ℕ) (σ : ℝ) (N : ℕ) :
    0 ≤ ramificationFockMass m σ N := by
  classical
  by_cases h : IsRPow m N <;>
    simp [ramificationFockMass, h, shellMass_nonneg]

theorem ramificationOneParticleMass_nonneg (m : ℕ) (σ : ℝ) (N : ℕ) :
    0 ≤ ramificationOneParticleMass m σ N := by
  classical
  by_cases h : IsRamificationOneParticle m N <;>
    simp [ramificationOneParticleMass, h, ramificationFockMass_nonneg]

theorem ramificationOneParticleMass_le_fockMass (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationOneParticleMass m σ N ≤ ramificationFockMass m σ N := by
  classical
  by_cases h : IsRamificationOneParticle m N <;>
    simp [ramificationOneParticleMass, h, ramificationFockMass_nonneg]

theorem ramificationManyParticleMass_nonneg (m : ℕ) (σ : ℝ) (N : ℕ) :
    0 ≤ ramificationManyParticleMass m σ N := by
  classical
  by_cases h : IsRamificationOneParticle m N <;>
    simp [ramificationManyParticleMass, h, ramificationFockMass_nonneg]

theorem ramificationManyParticleMass_le_fockMass (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationManyParticleMass m σ N ≤ ramificationFockMass m σ N := by
  classical
  by_cases h : IsRamificationOneParticle m N <;>
    simp [ramificationManyParticleMass, h, ramificationFockMass_nonneg]

/-- Both the one-particle prime layer and the multi-particle Boolean layer remain summable at the
ambient shell wall. -/
theorem summable_ramification_particleLayers_at_wall {m : ℕ} (hm : 2 ≤ m) :
    Summable (ramificationOneParticleMass m 1) ∧
      Summable (ramificationManyParticleMass m 1) := by
  have hfock := summable_ramificationFockMass_at_wall hm
  exact ⟨Summable.of_nonneg_of_le (ramificationOneParticleMass_nonneg m 1)
      (ramificationOneParticleMass_le_fockMass m 1) hfock,
    Summable.of_nonneg_of_le (ramificationManyParticleMass_nonneg m 1)
      (ramificationManyParticleMass_le_fockMass m 1) hfock⟩

/-- The interaction complement is a nonnegative submass of the full shell. -/
theorem ramificationInteractionMass_nonneg (m : ℕ) (σ : ℝ) (N : ℕ) :
    0 ≤ ramificationInteractionMass m σ N := by
  classical
  by_cases h : IsRPow m N <;> simp [ramificationInteractionMass, h, shellMass_nonneg]

theorem ramificationInteractionMass_le_shellMass (m : ℕ) (σ : ℝ) (N : ℕ) :
    ramificationInteractionMass m σ N ≤ shellMass m σ N := by
  classical
  by_cases h : IsRPow m N <;> simp [ramificationInteractionMass, h, shellMass_nonneg]

/-- Above the wall, the mixed interaction complement is summable. -/
theorem summable_ramificationInteractionMass {m : ℕ} {σ : ℝ} (hσ : 1 < σ) :
    Summable (ramificationInteractionMass m σ) :=
  Summable.of_nonneg_of_le (ramificationInteractionMass_nonneg m σ)
    (ramificationInteractionMass_le_shellMass m σ) (summable_shellMass m hσ)

/-- **Critical carrier transfer.** The perfect-power Fock sector remains summable at `σ=1`,
so the full shell's critical divergence is forced entirely into the mixed-exponent interaction
complement. -/
theorem not_summable_ramificationInteractionMass_at_wall {m : ℕ} (hm : 12 ≤ m) :
    ¬ Summable (ramificationInteractionMass m 1) := by
  intro hexcess
  have hsum := (summable_ramificationFockMass_at_wall (show 2 ≤ m by omega)).add hexcess
  have hfull : Summable (shellMass m 1) := hsum.congr fun N => by
    exact ramificationFockMass_add_interactionMass m 1 N
  exact not_summable_shellMass_at_wall hm hfull

/-- **Three-organ carrier classification.** Prime and Boolean formation layers stay finite at the
critical wall; their mixed-exponent interaction complement is the unique divergent layer in the
exact source partition. -/
theorem ramificationCriticalCarrierClassification {m : ℕ} (hm : 12 ≤ m) :
    Summable (ramificationOneParticleMass m 1) ∧
      Summable (ramificationManyParticleMass m 1) ∧
      ¬ Summable (ramificationInteractionMass m 1) := by
  obtain ⟨h1, hmany⟩ := summable_ramification_particleLayers_at_wall (show 2 ≤ m by omega)
  exact ⟨h1, hmany, not_summable_ramificationInteractionMass_at_wall hm⟩

/-- Bilateral global admission of the interaction complement. -/
def BilateralInteractionAdmission (m : ℕ) (t : ℝ) : Prop :=
  ∀ σ : ℝ, 1 < σ →
    Summable (ramificationInteractionMass m (σ + t)) ∧
    Summable (ramificationInteractionMass m (σ - t))

/-- The mixed-exponent interaction carrier alone selects the neutral reflected grade. -/
theorem bilateralInteractionAdmission_iff {m : ℕ} (hm : 12 ≤ m) (t : ℝ) :
    BilateralInteractionAdmission m t ↔ t = 0 := by
  constructor
  · intro h
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · have hσ : 1 < 1 - t := by linarith
      have hbad := (h (1 - t) hσ).1
      have heq : 1 - t + t = 1 := by ring
      rw [heq] at hbad
      exact absurd hbad (not_summable_ramificationInteractionMass_at_wall hm)
    · rfl
    · have hσ : 1 < 1 + t := by linarith
      have hbad := (h (1 + t) hσ).2
      have heq : 1 + t - t = 1 := by ring
      rw [heq] at hbad
      exact absurd hbad (not_summable_ramificationInteractionMass_at_wall hm)
  · rintro rfl
    intro σ hσ
    simpa using And.intro (summable_ramificationInteractionMass (m := m) hσ)
      (summable_ramificationInteractionMass (m := m) hσ)

/-- Capstone: exact three-layer reconstruction, critical carrier transfer, and bilateral global
selection hold for one source-generated formation. -/
theorem ramificationFockExcessSelection_capstone {m : ℕ} (hm : 12 ≤ m) (t : ℝ) :
    (∀ σ : ℝ, ∀ N : ℕ,
      ramificationOneParticleMass m σ N + ramificationManyParticleMass m σ N +
          ramificationInteractionMass m σ N = shellMass m σ N) ∧
      (Summable (ramificationOneParticleMass m 1) ∧
        Summable (ramificationManyParticleMass m 1) ∧
        ¬ Summable (ramificationInteractionMass m 1)) ∧
      (BilateralInteractionAdmission m t ↔ t = 0) := by
  exact ⟨ramification_threeLayer_reconstruction m,
    ramificationCriticalCarrierClassification hm,
    bilateralInteractionAdmission_iff hm t⟩

end
end GaloisForLFunctions.HTGeometry
