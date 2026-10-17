import GaloisForLFunctions.BiScaleUncertainty.DivisorGridTraceData
import Mathlib.Tactic.Push

/-!
# Consecutive-run geometry of arbitrary divisor families

The least uniform exclusion length is the attained maximum active run length.
Without such a bound, every finite run length is realized.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def divisorGridRunBound (d : ℕ) (D : Set ℕ) (n : ℕ) : Prop :=
  ∀ k, ∃ i ≤ n, ¬ divisorGridActive d D (k + i)

def divisorGridBoundedRuns (d : ℕ) (D : Set ℕ) : Prop :=
  ∃ n, divisorGridRunBound d D n

def divisorGridHasRun (d : ℕ) (D : Set ℕ) (n : ℕ) : Prop :=
  ∃ a, ∀ j < n, divisorGridActive d D (a + j)

def divisorGridRunLength (d : ℕ) (D : Set ℕ) : ℕ :=
  if h : divisorGridBoundedRuns d D then Nat.find h else 0

theorem divisorGridRunLength_gap (d : ℕ) (D : Set ℕ)
    (h : divisorGridBoundedRuns d D) :
    divisorGridRunBound d D (divisorGridRunLength d D) := by
  simpa only [divisorGridRunLength, dif_pos h] using Nat.find_spec h

theorem divisorGridRunLength_pos (d : ℕ) (D : Set ℕ)
    (h : divisorGridBoundedRuns d D) : 0 < divisorGridRunLength d D := by
  obtain ⟨i, hi, hg⟩ := divisorGridRunLength_gap d D h (d+1)
  by_contra hn
  have hi0 : i = 0 := by omega
  exact hg (by simpa [hi0] using divisorGridActive_seed d D)

theorem divisorGridRunLength_le (d : ℕ) (D : Set ℕ)
    (h : divisorGridBoundedRuns d D) (n : ℕ) (hn : divisorGridRunBound d D n) :
    divisorGridRunLength d D ≤ n := by
  simpa only [divisorGridRunLength, dif_pos h] using Nat.find_min' h hn

theorem divisorGridRunLength_attained (d : ℕ) (D : Set ℕ)
    (h : divisorGridBoundedRuns d D) :
    divisorGridHasRun d D (divisorGridRunLength d D) := by
  have hp := divisorGridRunLength_pos d D h
  have hn : ¬ divisorGridRunBound d D (divisorGridRunLength d D - 1) := by
    intro hb
    have := divisorGridRunLength_le d D h _ hb
    omega
  unfold divisorGridRunBound at hn
  push Not at hn
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, fun j hj => ha j (by omega)⟩

theorem divisorGrid_unbounded_runs (d : ℕ) (D : Set ℕ)
    (h : ¬ divisorGridBoundedRuns d D) (n : ℕ) : divisorGridHasRun d D n := by
  have hn : ¬ divisorGridRunBound d D n := fun hn => h ⟨n, hn⟩
  unfold divisorGridRunBound at hn
  push Not at hn
  obtain ⟨a, ha⟩ := hn
  exact ⟨a, fun j hj => ha j (by omega)⟩

/-- A definite run start; zero is used only when the requested run is absent. -/
def divisorGridRunStart (d : ℕ) (D : Set ℕ) (n : ℕ) : ℕ :=
  if h : divisorGridHasRun d D n then Nat.find h else 0

theorem divisorGridRunStart_active (d : ℕ) (D : Set ℕ) (n : ℕ)
    (h : divisorGridHasRun d D n) (j : ℕ) (hj : j < n) :
    divisorGridActive d D (divisorGridRunStart d D n + j) := by
  simpa only [divisorGridRunStart, dif_pos h] using Nat.find_spec h j hj

theorem divisorGrid_univ_active (d k : ℕ) (hk : 1 ≤ k) :
    divisorGridActive d Set.univ k := by
  refine ⟨k-1, Set.mem_insert_of_mem d (Set.mem_univ _), ?_⟩
  have he : k-1+2 = k+1 := by omega
  rw [he]

theorem divisorGrid_univ_unbounded (d : ℕ) :
    ¬ divisorGridBoundedRuns d Set.univ := by
  rintro ⟨n, hn⟩
  obtain ⟨i, _, hi⟩ := hn 1
  exact hi (divisorGrid_univ_active d _ (by omega))

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
