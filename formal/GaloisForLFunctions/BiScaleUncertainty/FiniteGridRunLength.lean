import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.Push

/-!
# Longest consecutive run of a finite divisor family

Index k denotes the positive integer node k+1. The finite family contains the
spacing d+2 and the spacings e+2 for e in D. Its least common multiple supplies
periodic inactive nodes, so its longest active run is finite and attained.
-/

noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SobolevShear
set_option autoImplicit false
attribute [local instance] Classical.propDecidable

def finiteGridActive (d : ℕ) (D : Finset ℕ) (k : ℕ) : Prop :=
  ∃ e ∈ insert d D, e + 2 ∣ k + 1

def finiteGridPeriod (d : ℕ) (D : Finset ℕ) : ℕ :=
  (insert d D).lcm (fun e => e + 2)

theorem finiteGridPeriod_pos (d : ℕ) (D : Finset ℕ) :
    0 < finiteGridPeriod d D := by
  apply Nat.pos_of_ne_zero
  exact Finset.lcm_ne_zero_iff.mpr (by intro e _; omega)

theorem spacing_dvd_finiteGridPeriod (d : ℕ) (D : Finset ℕ) {e : ℕ}
    (he : e ∈ insert d D) : e + 2 ∣ finiteGridPeriod d D :=
  Finset.dvd_lcm he

theorem finiteGridPeriod_ge_two (d : ℕ) (D : Finset ℕ) :
    2 ≤ finiteGridPeriod d D := by
  have h := Nat.le_of_dvd (finiteGridPeriod_pos d D)
    (spacing_dvd_finiteGridPeriod d D (Finset.mem_insert_self d D))
  omega

theorem finiteGridActive_periodic (d : ℕ) (D : Finset ℕ) (k : ℕ) :
    finiteGridActive d D (k + finiteGridPeriod d D) ↔ finiteGridActive d D k := by
  unfold finiteGridActive
  constructor <;> rintro ⟨e, he, hd⟩ <;> refine ⟨e, he, ?_⟩
  · have hp := spacing_dvd_finiteGridPeriod d D he
    exact (Nat.dvd_add_iff_right hp).mpr (by simpa [Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using hd)
  · have hp := spacing_dvd_finiteGridPeriod d D he
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using Nat.dvd_add hd hp

theorem not_finiteGridActive_of_period_dvd (d : ℕ) (D : Finset ℕ) {k : ℕ}
    (hk : finiteGridPeriod d D ∣ k) : ¬ finiteGridActive d D k := by
  rintro ⟨e, he, hd⟩
  have hek : e + 2 ∣ k := (spacing_dvd_finiteGridPeriod d D he).trans hk
  have he1 : e + 2 ∣ 1 := (Nat.dvd_add_iff_right hek).mpr hd
  have := Nat.le_of_dvd (by omega : 0 < 1) he1
  omega

theorem finiteGridActive_first (d : ℕ) (D : Finset ℕ) :
    finiteGridActive d D (d + 1) :=
  ⟨d, Finset.mem_insert_self d D, by simp [Nat.add_assoc]⟩

/-- Every interval of one period contains an inactive positive integer node. -/
theorem finiteGrid_gap_in_period (d : ℕ) (D : Finset ℕ) (k : ℕ) :
    ∃ i < finiteGridPeriod d D, ¬ finiteGridActive d D (k + i) := by
  let L := finiteGridPeriod d D
  have hL : 0 < L := finiteGridPeriod_pos d D
  have hmod := Nat.mod_lt k hL
  by_cases hz : k % L = 0
  · refine ⟨0, hL, ?_⟩
    simpa using not_finiteGridActive_of_period_dvd d D (Nat.dvd_of_mod_eq_zero hz)
  · refine ⟨L - k % L, by omega, ?_⟩
    apply not_finiteGridActive_of_period_dvd d D
    refine ⟨k / L + 1, ?_⟩
    have hdiv := Nat.mod_add_div k L
    dsimp [L] at *
    rw [Nat.mul_add, Nat.mul_one]
    omega

private theorem finiteGrid_runBound_exists (d : ℕ) (D : Finset ℕ) :
    ∃ r : ℕ, ∀ k, ∃ i ≤ r, ¬ finiteGridActive d D (k + i) := by
  refine ⟨finiteGridPeriod d D - 1, fun k => ?_⟩
  obtain ⟨i, hi, hg⟩ := finiteGrid_gap_in_period d D k
  exact ⟨i, by omega, hg⟩

/-- The maximum active run length, defined by its exact exclusion property. -/
def finiteGridRunLength (d : ℕ) (D : Finset ℕ) : ℕ :=
  Nat.find (finiteGrid_runBound_exists d D)

theorem finiteGridRunLength_gap (d : ℕ) (D : Finset ℕ) (k : ℕ) :
    ∃ i ≤ finiteGridRunLength d D, ¬ finiteGridActive d D (k + i) :=
  Nat.find_spec (finiteGrid_runBound_exists d D) k

theorem finiteGridRunLength_pos (d : ℕ) (D : Finset ℕ) :
    0 < finiteGridRunLength d D := by
  by_contra h
  have hz : finiteGridRunLength d D = 0 := by omega
  obtain ⟨i, hi, hg⟩ := finiteGridRunLength_gap d D (d + 1)
  have hi0 : i = 0 := by omega
  simpa [hi0] using hg (by simpa [hi0] using finiteGridActive_first d D)

theorem finiteGridRunLength_lt_period (d : ℕ) (D : Finset ℕ) :
    finiteGridRunLength d D < finiteGridPeriod d D := by
  have hb : finiteGridRunLength d D ≤ finiteGridPeriod d D - 1 := by
    apply Nat.find_min'
    intro k
    obtain ⟨i, hi, hg⟩ := finiteGrid_gap_in_period d D k
    exact ⟨i, by omega, hg⟩
  have := finiteGridPeriod_pos d D
  omega

theorem finiteGridRunLength_attained (d : ℕ) (D : Finset ℕ) :
    ∃ k, ∀ i < finiteGridRunLength d D, finiteGridActive d D (k + i) := by
  have hp := finiteGridRunLength_pos d D
  have h := Nat.find_min (finiteGrid_runBound_exists d D)
    (show finiteGridRunLength d D - 1 < finiteGridRunLength d D by omega)
  push Not at h
  obtain ⟨k, hk⟩ := h
  exact ⟨k, fun i hi => hk i (by omega)⟩

theorem finiteGridActive_add_period_mul (d : ℕ) (D : Finset ℕ) (k j : ℕ) :
    finiteGridActive d D (k + finiteGridPeriod d D * j) ↔ finiteGridActive d D k := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Nat.mul_succ, ← Nat.add_assoc, finiteGridActive_periodic, ih]

/-- A longest run starts inside the first period, allowing a run to cross its end. -/
theorem finiteGridRunLength_attained_in_period (d : ℕ) (D : Finset ℕ) :
    ∃ k < finiteGridPeriod d D,
      ∀ i < finiteGridRunLength d D, finiteGridActive d D (k + i) := by
  obtain ⟨k, hk⟩ := finiteGridRunLength_attained d D
  refine ⟨k % finiteGridPeriod d D, Nat.mod_lt k (finiteGridPeriod_pos d D), ?_⟩
  intro i hi
  have he : k % finiteGridPeriod d D + i + finiteGridPeriod d D *
      (k / finiteGridPeriod d D) = k + i := by
    have := Nat.mod_add_div k (finiteGridPeriod d D)
    omega
  exact (finiteGridActive_add_period_mul d D _ _).mp (by rw [he]; exact hk i hi)

theorem finiteGridRunLength_le_of_gap (d : ℕ) (D : Finset ℕ) (n : ℕ)
    (h : ∀ k, ∃ i ≤ n, ¬ finiteGridActive d D (k + i)) :
    finiteGridRunLength d D ≤ n := Nat.find_min' (finiteGrid_runBound_exists d D) h

/-- Any concrete active run is bounded by the constructed maximum. -/
theorem finiteGrid_run_le (d : ℕ) (D : Finset ℕ) {k n : ℕ}
    (h : ∀ i < n, finiteGridActive d D (k + i)) : n ≤ finiteGridRunLength d D := by
  obtain ⟨i, hi, hg⟩ := finiteGridRunLength_gap d D k
  by_contra hn
  exact hg (h i (by omega))

end GaloisForLFunctions.BiScaleUncertainty.SobolevShear
