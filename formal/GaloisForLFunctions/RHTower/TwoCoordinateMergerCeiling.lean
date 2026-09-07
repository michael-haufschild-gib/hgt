import GaloisForLFunctions.RHTower.UniformPrimeSubsetEnergy
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-!
# Sharp energy ceiling for two remaining merger coordinates

The two admissible orders have one distinct intermediate state each. Their
minimax value retains the signed overlap coefficient, and its exact excess
is determined by the symmetric sum and antisymmetric product of four fibres.
-/
noncomputable section
open Finset
namespace RHTower

/-- Minimum peak energy over both complete two-coordinate orders. -/
def twoCoordinateMergePeak (h a b c : ℝ) : ℝ :=
  min (max (max (h^2+a^2+b^2+c^2) ((h+a+b+c)^2)) ((h+a)^2+(b+c)^2))
      (max (max (h^2+a^2+b^2+c^2) ((h+a+b+c)^2)) ((h+b)^2+(a+c)^2))

/-- The antisymmetric product selects the lower-energy first coordinate. -/
theorem twoCoordinateMerge_left_le_right_iff (h a b c : ℝ) :
    (h+a)^2+(b+c)^2 ≤ (h+b)^2+(a+c)^2 ↔ (h-c)*(a-b) ≤ 0 := by
  constructor <;> intro H <;> nlinarith only [H]

/-- Exact minimum next energy, including the nonzero joint-coordinate fibre. -/
theorem min_twoCoordinateMergeEnergy (h a b c : ℝ) :
    min ((h+a)^2+(b+c)^2) ((h+b)^2+(a+c)^2) =
      h^2+a^2+b^2+c^2+(h+c)*(a+b)-|(h-c)*(a-b)| := by
  by_cases hs : 0 ≤ (h-c)*(a-b)
  · rw [abs_of_nonneg hs,min_eq_right (by nlinarith only [hs])]
    ring
  · have hs' : (h-c)*(a-b) ≤ 0 := le_of_not_ge hs
    rw [abs_of_nonpos hs',min_eq_left ((twoCoordinateMerge_left_le_right_iff h a b c).mpr hs')]
    ring

/-- The complete two-coordinate minimax value is the larger endpoint or the unavoidable first-step floor. -/
theorem twoCoordinateMergePeak_eq (h a b c : ℝ) :
    twoCoordinateMergePeak h a b c =
      max (max (h^2+a^2+b^2+c^2) ((h+a+b+c)^2))
        (h^2+a^2+b^2+c^2+(h+c)*(a+b)-|(h-c)*(a-b)|) := by
  have hm (B L R : ℝ) : min (max B L) (max B R)=max B (min L R) := by
    rcases le_total L R with h|h
    · rw [min_eq_left h,min_eq_left (max_le_max_left B h)]
    · rw [min_eq_right h,min_eq_right (max_le_max_left B h)]
  rw [twoCoordinateMergePeak,hm,min_twoCoordinateMergeEnergy]

/-- Exact feasibility of a prescribed two-coordinate ceiling. -/
theorem twoCoordinateMergePeak_le_iff (h a b c B : ℝ) :
    twoCoordinateMergePeak h a b c ≤ B ↔
      h^2+a^2+b^2+c^2 ≤ B ∧ (h+a+b+c)^2 ≤ B ∧
        h^2+a^2+b^2+c^2+(h+c)*(a+b)-|(h-c)*(a-b)| ≤ B := by
  rw [twoCoordinateMergePeak_eq]
  simp only [max_le_iff,and_assoc]

/-- Both first steps increase energy exactly when the symmetric term exceeds the antisymmetric reserve. -/
theorem twoCoordinateMerge_both_increase_iff (h a b c : ℝ) :
    (h^2+a^2+b^2+c^2 < (h+a)^2+(b+c)^2 ∧
      h^2+a^2+b^2+c^2 < (h+b)^2+(a+c)^2) ↔
        |(h-c)*(a-b)| < (h+c)*(a+b) := by
  rw [← lt_min_iff,min_twoCoordinateMergeEnergy]
  constructor <;> intro H <;> linarith only [H]

variable {α ι : Type*} [DecidableEq α]

/-- Removing processed labels from the ambient cube does not change retained source energy. -/
theorem subsetLabelEnergy_remaining (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α) :
    subsetLabelEnergy U I a c P = ∑ R ∈ (U \ P).powerset,(subsetLabelFibre I a c P R)^2 := by
  unfold subsetLabelEnergy
  symm
  apply sum_subset (powerset_mono.mpr sdiff_subset)
  intro R hR hn
  have hz : subsetLabelFibre I a c P R=0 := by
    unfold subsetLabelFibre
    apply sum_eq_zero
    intro i hi
    have hne : a i \ P ≠ R := by
      intro he
      apply hn
      apply mem_powerset.mpr
      intro p hp
      exact mem_sdiff.mpr ⟨mem_powerset.mp hR hp,(mem_sdiff.mp (he.symm ▸ hp)).2⟩
    simp [hne]
  simp [hz]

private theorem sum_singleton_powerset (q : α) (f : Finset α → ℝ) :
    (∑ R ∈ ({q} : Finset α).powerset,f R)=f ∅+f {q} := by
  simpa only [powerset_empty,sum_singleton,insert_empty_eq] using
    sum_powerset_insert (notMem_empty q) f

/-- Two remaining coordinates give exactly four signed fibre squares. -/
theorem subsetLabelEnergy_two_remaining (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α) (p q : α) (hpq : p≠q) (hrem : U \ P={p,q}) :
    subsetLabelEnergy U I a c P = (subsetLabelFibre I a c P ∅)^2+
      (subsetLabelFibre I a c P {p})^2+(subsetLabelFibre I a c P {q})^2+
      (subsetLabelFibre I a c P {p,q})^2 := by
  rw [subsetLabelEnergy_remaining,hrem,sum_powerset_insert (by simpa using hpq)]
  rw [sum_singleton_powerset,sum_singleton_powerset]
  simp only [insert_empty_eq]
  ring

/-- The first of two remaining coordinates merges the two literal row pairs. -/
theorem subsetLabelEnergy_insert_two_remaining (U : Finset α) (I : Finset ι) (a : ι → Finset α)
    (c : ι → ℝ) (P : Finset α) (p q : α) (hpq : p≠q) (hrem : U \ P={p,q}) :
    subsetLabelEnergy U I a c (insert p P) =
      (subsetLabelFibre I a c P ∅+subsetLabelFibre I a c P {p})^2+
      (subsetLabelFibre I a c P {q}+subsetLabelFibre I a c P {p,q})^2 := by
  rw [subsetLabelEnergy_remaining,sdiff_insert,hrem]
  have he : ({p,q} : Finset α).erase p={q} := by ext x; simp [hpq]
  rw [he,sum_singleton_powerset,subsetLabelFibre_insert,subsetLabelFibre_insert]
  simp [hpq]

/-- Completing both remaining coordinates gives the square of their complete signed four-fibre sum. -/
theorem subsetLabelEnergy_insert_insert_two_remaining (U : Finset α) (I : Finset ι)
    (a : ι → Finset α) (c : ι → ℝ) (P : Finset α) (p q : α)
    (hpq : p≠q) (hrem : U \ P={p,q}) :
    subsetLabelEnergy U I a c (insert q (insert p P)) =
      (subsetLabelFibre I a c P ∅+subsetLabelFibre I a c P {p}+
        subsetLabelFibre I a c P {q}+subsetLabelFibre I a c P {p,q})^2 := by
  rw [subsetLabelEnergy_remaining,sdiff_insert,sdiff_insert,hrem]
  have he : (({p,q} : Finset α).erase p).erase q=∅ := by ext x; simp; tauto
  rw [he,powerset_empty,sum_singleton,subsetLabelFibre_insert]
  simp only [notMem_empty,if_false,insert_empty_eq]
  rw [subsetLabelFibre_insert,subsetLabelFibre_insert]
  simp [hpq]
  ring
end RHTower
