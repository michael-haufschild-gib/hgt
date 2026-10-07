import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# Positive exact repair of integer-null Weil mixtures

The two signs of the isolated pair tests give a positive lift of every finitely
supported logarithmic defect. The lift has an explicit weighted absolute-energy
bound, retaining both pole terms. Adding the lift of the negative defect makes
every integer constraint vanish exactly.
-/

open Finsupp MeasureTheory Zeta23
open scoped ContDiff

noncomputable section

namespace RHTower.WeilWorkPBAP

open WeilOneSided

/-- Full pole-plus-archimedean energy of a finite mixture. -/
def energy : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
  linearCombination ℝ (fun f => weilArchRe (EF.weilTest f.1 f.1))

/-- All integer logarithmic defects of a finite mixture. -/
def defect : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) :=
  linearCombination ℝ logVector

/-- The positive size of the isolated logarithmic atom. -/
def atomWeight (j : LogIndex) : ℝ :=
  2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j

theorem atomWeight_pos (j : LogIndex) : 0 < atomWeight j :=
  pairTest_weight_pos j

/-- The pair test whose atom has the sign of the requested defect. -/
def signedPair (j : LogIndex) (b : ℝ) : WeilTestFn :=
  pairTestFn j (if 0 ≤ b then 1 else -1)

/-- Isolated-atom correction tests are smooth, not merely twice differentiable. -/
theorem contDiff_signedPair (j : LogIndex) (b : ℝ) : ContDiff ℝ ∞ (signedPair j b).1 := by
  exact (contDiff_narrowBumpC j).add
    (contDiff_const.mul ((contDiff_narrowBumpC j).comp (contDiff_id.sub contDiff_const)))

/-- A nonnegative mixture realizing one prescribed signed atom. -/
def atomRepair (j : LogIndex) (b : ℝ) : WeilTestFn →₀ ℝ :=
  Finsupp.single (signedPair j b) (|b| / atomWeight j)

theorem atomRepair_nonneg (j : LogIndex) (b : ℝ) (f : WeilTestFn) :
    0 ≤ atomRepair j b f := by
  classical
  simp only [atomRepair, Finsupp.single_apply]
  split_ifs
  · exact div_nonneg (abs_nonneg b) (atomWeight_pos j).le
  · exact le_rfl

theorem defect_atomRepair (j : LogIndex) (b : ℝ) :
    defect (atomRepair j b) = Finsupp.single j b := by
  classical
  rw [defect, atomRepair, linearCombination_single, signedPair, logVector_pairTestFn,
    Finsupp.smul_single, smul_eq_mul]
  congr 1
  have hw := (atomWeight_pos j).ne'
  change |b| / atomWeight j *
    (2 * (if 0 ≤ b then 1 else -1) * (∫ t, (narrowBump j t) ^ 2) /
      Real.sqrt j) = b
  have hscale (s : ℝ) :
      2 * s * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j = s * atomWeight j := by
    unfold atomWeight
    ring
  rw [hscale]
  by_cases hb : 0 ≤ b
  · rw [if_pos hb, abs_of_nonneg hb]
    field_simp
  · rw [if_neg hb, abs_of_neg (lt_of_not_ge hb)]
    field_simp

/-- Cost per unit logarithmic defect, including both possible signs. -/
def atomCost (j : LogIndex) : ℝ :=
  max |weilArchRe (EF.weilTest (pairTest j 1) (pairTest j 1))|
    |weilArchRe (EF.weilTest (pairTest j (-1)) (pairTest j (-1)))| / atomWeight j

theorem atomCost_nonneg (j : LogIndex) : 0 ≤ atomCost j :=
  div_nonneg ((abs_nonneg _).trans (le_max_left _ _)) (atomWeight_pos j).le

theorem abs_energy_atomRepair_le (j : LogIndex) (b : ℝ) :
    |energy (atomRepair j b)| ≤ |b| * atomCost j := by
  classical
  rw [energy, atomRepair, linearCombination_single, smul_eq_mul, abs_mul,
    abs_of_nonneg (div_nonneg (abs_nonneg b) (atomWeight_pos j).le)]
  have hA : |weilArchRe (EF.weilTest (signedPair j b).1 (signedPair j b).1)| ≤
      max |weilArchRe (EF.weilTest (pairTest j 1) (pairTest j 1))|
        |weilArchRe (EF.weilTest (pairTest j (-1)) (pairTest j (-1)))| := by
    unfold signedPair
    split_ifs
    · exact le_max_left _ _
    · exact le_max_right _ _
  calc
    _ ≤ (|b| / atomWeight j) *
        max |weilArchRe (EF.weilTest (pairTest j 1) (pairTest j 1))|
          |weilArchRe (EF.weilTest (pairTest j (-1)) (pairTest j (-1)))| :=
      mul_le_mul_of_nonneg_left hA (div_nonneg (abs_nonneg b) (atomWeight_pos j).le)
    _ = |b| * atomCost j := by unfold atomCost; ring

/-- A positive finite lift of a finitely supported logarithmic vector. -/
def repair (b : LogIndex →₀ ℝ) : WeilTestFn →₀ ℝ := b.sum atomRepair

/-- Weighted total logarithmic defect controlling the full energy change. -/
def repairBudget (b : LogIndex →₀ ℝ) : ℝ := b.sum fun j t => |t| * atomCost j

theorem repair_nonneg (b : LogIndex →₀ ℝ) (f : WeilTestFn) : 0 ≤ repair b f := by
  classical
  rw [repair, Finsupp.sum_apply]
  exact Finset.sum_nonneg fun j _ => atomRepair_nonneg j (b j) f

theorem defect_repair (b : LogIndex →₀ ℝ) : defect (repair b) = b := by
  rw [repair, map_finsuppSum]
  simp_rw [defect_atomRepair]
  exact Finsupp.sum_single b

theorem abs_energy_repair_le (b : LogIndex →₀ ℝ) :
    |energy (repair b)| ≤ repairBudget b := by
  classical
  rw [repair, map_finsuppSum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum fun j _ => abs_energy_atomRepair_le j (b j))

/-- The repaired mixture; every logarithmic atom cancels exactly. -/
def nullRepair (c : WeilTestFn →₀ ℝ) : WeilTestFn →₀ ℝ := c + repair (-defect c)

theorem defect_nullRepair (c : WeilTestFn →₀ ℝ) : defect (nullRepair c) = 0 := by
  rw [nullRepair, map_add, defect_repair, add_neg_cancel]

theorem nullRepair_nonneg {c : WeilTestFn →₀ ℝ} (hc : ∀ f, 0 ≤ c f) (f : WeilTestFn) :
    0 ≤ nullRepair c f :=
  add_nonneg (hc f) (repair_nonneg _ f)

/-- Exact repair controls the full energy change by the weighted total defect. -/
theorem abs_energy_nullRepair_sub_le (c : WeilTestFn →₀ ℝ) :
    |energy (nullRepair c) - energy c| ≤ repairBudget (-defect c) := by
  rw [nullRepair, map_add, add_sub_cancel_left]
  exact abs_energy_repair_le _

/-- Every integer constraint vanishes, including those beyond any chosen cutoff. -/
theorem logValue_nullRepair (c : WeilTestFn →₀ ℝ) (n : ℕ) (hn : 2 ≤ n) :
    (nullRepair c).sum (fun f t => t * logValue f.1 n) = 0 := by
  have h := congrArg (fun b : LogIndex →₀ ℝ => b ⟨n, hn⟩) (defect_nullRepair c)
  simpa only [defect, linearCombination_logVector_apply, Finsupp.coe_zero, Pi.zero_apply] using h

end RHTower.WeilWorkPBAP
