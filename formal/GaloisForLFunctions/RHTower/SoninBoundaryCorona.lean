import GaloisForLFunctions.RHTower.SoninCouplingNonannihilation

/-!
# The phase-space boundary corona

Bounded families of even vectors modulo families whose norms vanish.  Two families define the same
boundary class exactly when their difference is norm-null, so the asymptotic statements about the
wavepacket family become literal equalities of classes in this quotient.

This is the completion that retains the escaping packets: ordinary weak limits lose them, since
they converge weakly to zero, but their boundary classes are nonzero.
-/

noncomputable section

set_option maxHeartbeats 1000000

namespace RHTower

open Filter
open scoped Topology

/-- Bounded families of even vectors. -/
def soninBoundedFamilies : Submodule ℂ (ℕ → evenSubspace) where
  carrier := {f | ∃ M : ℝ, ∀ n, ‖f n‖ ≤ M}
  add_mem' := by
    rintro f g ⟨M, hM⟩ ⟨N, hN⟩
    refine ⟨M + N, fun n => ?_⟩
    exact (norm_add_le _ _).trans (add_le_add (hM n) (hN n))
  zero_mem' := ⟨0, fun n => by simp⟩
  smul_mem' := by
    rintro c f ⟨M, hM⟩
    refine ⟨‖c‖ * max M 0, fun n => ?_⟩
    have hle : ‖f n‖ ≤ max M 0 := (hM n).trans (le_max_left _ _)
    calc ‖(c • f) n‖ = ‖c‖ * ‖f n‖ := by
          rw [Pi.smul_apply, norm_smul]
      _ ≤ ‖c‖ * max M 0 := by
          exact mul_le_mul_of_nonneg_left hle (norm_nonneg c)

/-- Families whose norms vanish. -/
def soninNullFamilies : Submodule ℂ (ℕ → evenSubspace) where
  carrier := {f | Tendsto (fun n => ‖f n‖) atTop (𝓝 0)}
  add_mem' := by
    intro f g hf hg
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_) (by simpa using hf.add hg)
    exact norm_add_le _ _
  zero_mem' := by
    simp
  smul_mem' := by
    intro c f hf
    have : Tendsto (fun n => ‖c‖ * ‖f n‖) atTop (𝓝 0) := by
      simpa using hf.const_mul ‖c‖
    refine this.congr fun n => ?_
    rw [Pi.smul_apply, norm_smul]

theorem soninNullFamilies_le_soninBoundedFamilies :
    soninNullFamilies ≤ soninBoundedFamilies := by
  intro f hf
  have hlt : ∀ᶠ n in atTop, ‖f n‖ < 1 :=
    (hf : Tendsto (fun n => ‖f n‖) atTop (𝓝 0)).eventually_lt_const (by norm_num)
  rw [eventually_atTop] at hlt
  obtain ⟨N, hN⟩ := hlt
  refine ⟨max 1 (Finset.sup' (Finset.range (N + 1)) (by simp) fun i => ‖f i‖), fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact le_trans (hN n hn).le (le_max_left _ _)
  · refine le_trans ?_ (le_max_right _ _)
    exact Finset.le_sup' (fun i => ‖f i‖) (Finset.mem_range.mpr (by omega))

/-- The null families sitting inside the bounded families. -/
def soninNullInBounded : Submodule ℂ soninBoundedFamilies :=
  Submodule.comap soninBoundedFamilies.subtype soninNullFamilies

/-- **The boundary corona.**  Bounded families modulo null families. -/
abbrev SoninCorona : Type := soninBoundedFamilies ⧸ soninNullInBounded

/-- The boundary class of a bounded family. -/
def soninBoundaryClass (f : soninBoundedFamilies) : SoninCorona :=
  Submodule.Quotient.mk f

/-- **Classes agree exactly when the difference is norm-null.** -/
theorem soninBoundaryClass_eq_iff (f g : soninBoundedFamilies) :
    soninBoundaryClass f = soninBoundaryClass g ↔
      Tendsto (fun n => ‖(f : ℕ → evenSubspace) n - (g : ℕ → evenSubspace) n‖) atTop (𝓝 0) := by
  rw [soninBoundaryClass, soninBoundaryClass, Submodule.Quotient.eq]
  constructor
  · intro h
    exact h
  · intro h
    exact h

end RHTower
