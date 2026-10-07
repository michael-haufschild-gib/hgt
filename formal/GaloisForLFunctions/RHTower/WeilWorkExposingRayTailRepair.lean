import GaloisForLFunctions.RHTower.WeilPolarConeExposedDuality

/-!
# Positive-mixture repair of exposing traces

Two-point polar resonators realize the omitted exposing coefficients between any two
cutoffs. Their archimedean energy is bounded by the corresponding difference of box
tails. In particular, the repair cost tends uniformly to zero with the lower cutoff.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real
open Zeta23

namespace RHTower

noncomputable section

/-- The sign of an exposing coefficient, with positive sign at zero. -/
def exposingRepairSign (n : ℕ) : ℝ := if 0 ≤ exposingWeight n then 1 else -1

/-- The nonnegative mixture coefficient which normalizes one resonator's atom. -/
def exposingRepairCoeff (n : ℕ) : ℝ :=
  |exposingWeight n| / (4 * Real.pi * resonatorMass n)

/-- The polar resonator supplying the exposing coefficient at one integer. -/
def exposingRepairTest (n : ℕ) : ℝ → ℂ :=
  twoPointResonator n (exposingRepairSign n)

/-- The integer atoms strictly after the lower cutoff and at most the upper cutoff. -/
def exposingRepairAtoms (N M : ℕ) : Finset ℕ := Finset.Icc (max 2 (N + 1)) M

theorem exposingRepairSign_cases (n : ℕ) :
    exposingRepairSign n = 1 ∨ exposingRepairSign n = -1 := by
  unfold exposingRepairSign
  split_ifs <;> simp

theorem abs_mul_exposingRepairSign (n : ℕ) :
    |exposingWeight n| * exposingRepairSign n = exposingWeight n := by
  unfold exposingRepairSign
  split_ifs with h
  · simp [abs_of_nonneg h]
  · simp [abs_of_neg (lt_of_not_ge h)]

theorem exposingRepairCoeff_nonneg (n : ℕ) : 0 ≤ exposingRepairCoeff n := by
  unfold exposingRepairCoeff
  exact div_nonneg (abs_nonneg _) (by have := resonatorMass_pos n; positivity)

theorem isPolarTest_exposingRepairTest {n : ℕ} (hn : 2 ≤ n) :
    IsPolarTest (atomLevel n) (exposingRepairTest n) :=
  isPolarTest_twoPointResonator hn _

/-- Each normalized positive mixture has exactly one prescribed nonzero atom. -/
theorem exposingRepair_atom {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    2 * Real.pi * (exposingRepairCoeff n * atomCoeff (exposingRepairTest n) m) =
      if m = n then exposingWeight n else 0 := by
  unfold exposingRepairTest exposingRepairCoeff
  rw [atomCoeff_twoPointResonator hn _ hm]
  split_ifs
  · have hmass := (resonatorMass_pos n).ne'
    calc _ = |exposingWeight n| * exposingRepairSign n := by field_simp; ring
      _ = exposingWeight n := abs_mul_exposingRepairSign n
  · ring

/-- The normalization pays at most the exposing box majorant. -/
theorem exposingRepair_energy_le {n : ℕ} (hn : 2 ≤ n) :
    exposingRepairCoeff n * archEnergy (exposingRepairTest n) ≤ exposingMajorant n := by
  have h := mul_le_mul_of_nonneg_left
    (archEnergy_twoPointResonator_le hn (exposingRepairSign_cases n))
    (exposingRepairCoeff_nonneg n)
  refine h.trans_eq ?_
  unfold exposingRepairCoeff exposingMajorant
  rw [if_pos hn]
  have hmass := (resonatorMass_pos n).ne'
  field_simp

/-- All integer coefficients of the finite repair family, including those outside its range. -/
theorem exposingRepair_sum_atoms (N M : ℕ) {m : ℕ} (hm : 2 ≤ m) :
    2 * Real.pi * ∑ n ∈ exposingRepairAtoms N M,
      exposingRepairCoeff n * atomCoeff (exposingRepairTest n) m =
        if N < m ∧ m ≤ M then exposingWeight m else 0 := by
  rw [Finset.mul_sum]
  have hterm : ∀ n ∈ exposingRepairAtoms N M,
      2 * Real.pi * (exposingRepairCoeff n * atomCoeff (exposingRepairTest n) m) =
        if m = n then exposingWeight n else 0 := by
    intro n hn
    exact exposingRepair_atom (le_trans (le_max_left _ _) (Finset.mem_Icc.mp hn).1) hm
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq]
  have hmem : m ∈ exposingRepairAtoms N M ↔ N < m ∧ m ≤ M := by
    simp only [exposingRepairAtoms, Finset.mem_Icc, max_le_iff]
    omega
  simp only [hmem]

/-- The repair cost is bounded by its finite box mass. -/
theorem exposingRepair_sum_energy_le (N M : ℕ) :
    (∑ n ∈ exposingRepairAtoms N M,
      exposingRepairCoeff n * archEnergy (exposingRepairTest n)) ≤
        ∑ n ∈ exposingRepairAtoms N M, exposingMajorant n := by
  exact Finset.sum_le_sum fun n hn =>
    exposingRepair_energy_le (le_trans (le_max_left _ _) (Finset.mem_Icc.mp hn).1)

/-- The finite box mass is dominated uniformly by the full lower-cutoff tail. -/
theorem exposingRepair_mass_le_tail (N M : ℕ) :
    (∑ n ∈ exposingRepairAtoms N M, exposingMajorant n) ≤ exposingTail N := by
  have h := (summable_exposingTail_terms N).sum_le_tsum (exposingRepairAtoms N M)
    (fun n _ => by split_ifs <;> [exact exposingMajorant_nonneg n; exact le_rfl])
  refine le_trans (le_of_eq ?_) h
  refine Finset.sum_congr rfl fun n hn => ?_
  have hnN : N < n := by
    have := (Finset.mem_Icc.mp hn).1
    omega
  rw [if_pos hnN]

/-- The entire finite positive-mixture repair has vanishing upper energy cost. -/
theorem exposingRepair_energy_le_tail (N M : ℕ) :
    (∑ n ∈ exposingRepairAtoms N M,
      exposingRepairCoeff n * archEnergy (exposingRepairTest n)) ≤ exposingTail N :=
  (exposingRepair_sum_energy_le N M).trans (exposingRepair_mass_le_tail N M)

/-- The finite repair budget is exactly the difference of the two box tails. -/
theorem exposingRepair_mass_eq_tail_sub {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ exposingRepairAtoms N M, exposingMajorant n) =
      exposingTail N - exposingTail M := by
  let g : ℕ → ℝ := fun n => if n ∈ exposingRepairAtoms N M then exposingMajorant n else 0
  have hg : Summable g := summable_of_ne_finset_zero (s := exposingRepairAtoms N M)
    (fun n hn => by simp only [g, if_neg hn])
  have hsum : ∑' n, g n = ∑ n ∈ exposingRepairAtoms N M, exposingMajorant n := by
    rw [tsum_eq_sum (s := exposingRepairAtoms N M) (fun n hn => by simp [g, hn])]
    exact Finset.sum_congr rfl fun n hn => by simp [g, hn]
  have hsplit : ∀ n : ℕ, (if N < n then exposingMajorant n else 0) =
      g n + (if M < n then exposingMajorant n else 0) := by
    intro n
    by_cases hn : 2 ≤ n
    · simp only [g, exposingRepairAtoms, Finset.mem_Icc, max_le_iff]
      split_ifs <;> first | omega | ring
    · simp only [g, exposingMajorant, if_neg hn, ite_self, add_zero]
  have h := hg.tsum_add (summable_exposingTail_terms M)
  rw [← tsum_congr hsplit, hsum] at h
  change exposingTail N = _ + exposingTail M at h
  linarith

/-- Appending the repair costs at most the exact decrease of the box tail. -/
theorem exposingRepair_energy_le_tail_sub {N M : ℕ} (hNM : N ≤ M) :
    (∑ n ∈ exposingRepairAtoms N M,
      exposingRepairCoeff n * archEnergy (exposingRepairTest n)) ≤
        exposingTail N - exposingTail M := by
  simpa only [exposingRepair_mass_eq_tail_sub hNM] using exposingRepair_sum_energy_le N M

/-- The actual correction energies have a uniform vanishing upper bound in the upper cutoff. -/
theorem exposingRepair_uniform_vanishing :
    ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ M : ℕ,
      (∑ n ∈ exposingRepairAtoms N M,
        exposingRepairCoeff n * archEnergy (exposingRepairTest n)) < ε := by
  intro ε hε
  have h := tendsto_exposingTail.eventually (gt_mem_nhds hε)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp h
  exact ⟨N₀, fun N hN M => (exposingRepair_energy_le_tail N M).trans_lt (hN₀ N hN)⟩

/-- A cutoff admitted at level `B` admits every repair test at level `B + 1`. -/
theorem exposingRepair_level_le {N M : ℕ} {B : ℝ} (hM : M ≤ ⌊Real.exp (2 * B)⌋₊)
    {n : ℕ} (hn : n ∈ exposingRepairAtoms N M) : atomLevel n ≤ B + 1 :=
  atomLevel_le (le_trans (le_max_left _ _) (Finset.mem_Icc.mp hn).1)
    ((Finset.mem_Icc.mp hn).2.trans hM)

end

end RHTower
