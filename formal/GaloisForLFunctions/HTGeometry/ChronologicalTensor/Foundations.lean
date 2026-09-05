import Mathlib.Analysis.Seminorm
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-!
# Capacity seminorms of chronological window polynomials

Finite sums of products of window increments are tested on probes with variation
at most one. The normalization map sends every gap vector into that ball and is
idempotent. The supremum is finite, satisfies the seminorm laws, and vanishes
exactly on observationally zero combinations. Taking interval windows gives the
chronological specialization; no independence of coefficient representatives is
assumed. A single diagram is dominated by its monotone absolute-gap probe.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Finset

def variation {n : ℕ} (g : Fin n → ℝ) : ℝ := ∑ i, |g i|

def normalizeProbe {n : ℕ} (g : Fin n → ℝ) : Fin n → ℝ :=
  fun i => g i / max 1 (variation g)

def windowValue {n : ℕ} (W : Finset (Fin n)) (g : Fin n → ℝ) : ℝ := ∑ i ∈ W, g i

def diagramValue {n r : ℕ} (D : Fin r → Finset (Fin n)) (g : Fin n → ℝ) : ℝ :=
  ∏ j, windowValue (D j) g

def familyValue {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) : ℝ := ∑ j, c j * diagramValue (D j) g

def coefficientBudget {m : ℕ} (c : Fin m → ℝ) : ℝ := ∑ i, |c i|

theorem variation_nonneg {n : ℕ} (g : Fin n → ℝ) : 0 ≤ variation g :=
  sum_nonneg (fun i _ => abs_nonneg (g i))

theorem normalizeProbe_budget {n : ℕ} (g : Fin n → ℝ) : variation (normalizeProbe g) ≤ 1 := by
  have hd : 0 < max 1 (variation g) := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  unfold variation normalizeProbe
  simp only [abs_div, abs_of_pos hd, ← sum_div]
  exact (div_le_one hd).mpr (le_max_right _ _)

theorem windowValue_bound {n : ℕ} (W : Finset (Fin n)) (g : Fin n → ℝ) :
    |windowValue W g| ≤ variation g := by
  exact (abs_sum_le_sum_abs _ _).trans
    (sum_le_sum_of_subset_of_nonneg (subset_univ W) (fun i _ _ => abs_nonneg (g i)))

theorem diagramValue_bound {n r : ℕ} (D : Fin r → Finset (Fin n)) (g : Fin n → ℝ) :
    |diagramValue D g| ≤ variation g ^ r := by
  unfold diagramValue
  rw [Finset.abs_prod]
  have h := prod_le_prod (fun i (_ : i ∈ (univ : Finset (Fin r))) => abs_nonneg (windowValue (D i) g))
    (fun i _ => windowValue_bound (D i) g)
  simpa only [prod_const, card_univ, Fintype.card_fin] using h

theorem familyValue_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    |familyValue D c g| ≤ coefficientBudget c * variation g ^ r := by
  calc
    _ ≤ ∑ i, |c i * diagramValue (D i) g| := abs_sum_le_sum_abs _ _
    _ = ∑ i, |c i| * |diagramValue (D i) g| := by simp only [abs_mul]
    _ ≤ ∑ i, |c i| * variation g ^ r :=
      sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (diagramValue_bound (D i) g) (abs_nonneg (c i)))
    _ = _ := by rw [← sum_mul]; rfl

theorem normalized_familyValue_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    |familyValue D c (normalizeProbe g)| ≤ coefficientBudget c := by
  have h := familyValue_bound D c (normalizeProbe g)
  have hp := pow_le_pow_left₀ (variation_nonneg (normalizeProbe g)) (normalizeProbe_budget g) r
  rw [one_pow] at hp
  have hc : 0 ≤ coefficientBudget c := sum_nonneg (fun i _ => abs_nonneg (c i))
  exact h.trans ((mul_le_mul_of_nonneg_left hp hc).trans_eq (mul_one _))

def familyCapacity {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : ℝ := sSup (Set.range (fun g => |familyValue D c (normalizeProbe g)|))

theorem family_values_bddAbove {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : BddAbove (Set.range (fun g => |familyValue D c (normalizeProbe g)|)) := by
  refine ⟨coefficientBudget c, ?_⟩
  rintro _ ⟨g, rfl⟩
  exact normalized_familyValue_bound D c g

theorem familyCapacity_probe_bound {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) (g : Fin n → ℝ) :
    |familyValue D c (normalizeProbe g)| ≤ familyCapacity D c :=
  le_csSup (family_values_bddAbove D c) (Set.mem_range_self g)

theorem familyCapacity_nonneg {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : 0 ≤ familyCapacity D c :=
  (abs_nonneg _).trans (familyCapacity_probe_bound D c (fun _ => 0))

theorem familyCapacity_le_budget {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) : familyCapacity D c ≤ coefficientBudget c := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g, rfl⟩
  exact normalized_familyValue_bound D c g

theorem familyCapacity_zero {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n)) :
    familyCapacity D 0 = 0 := by
  apply le_antisymm _ (familyCapacity_nonneg D 0)
  simpa [coefficientBudget] using familyCapacity_le_budget D 0

theorem familyValue_add {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c d : Fin m → ℝ) (g : Fin n → ℝ) :
    familyValue D (c+d) g = familyValue D c g + familyValue D d g := by
  simp only [familyValue, Pi.add_apply, add_mul, sum_add_distrib]

theorem familyValue_smul {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (t : ℝ) (c : Fin m → ℝ) (g : Fin n → ℝ) :
    familyValue D (t • c) g = t * familyValue D c g := by
  simp only [familyValue, Pi.smul_apply, smul_eq_mul, mul_assoc, mul_sum]

theorem familyCapacity_add_le {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c d : Fin m → ℝ) : familyCapacity D (c+d) ≤ familyCapacity D c + familyCapacity D d := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g, rfl⟩
  dsimp only
  rw [familyValue_add]
  exact (abs_add_le _ _).trans
    (add_le_add (familyCapacity_probe_bound D c g) (familyCapacity_probe_bound D d g))

theorem familyCapacity_smul_le {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (t : ℝ) (c : Fin m → ℝ) : familyCapacity D (t • c) ≤ ‖t‖ * familyCapacity D c := by
  apply csSup_le (Set.range_nonempty _)
  rintro _ ⟨g, rfl⟩
  dsimp only
  rw [familyValue_smul, abs_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (familyCapacity_probe_bound D c g) (abs_nonneg t)

def chronologicalSeminorm {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n)) :
    Seminorm ℝ (Fin m → ℝ) :=
  Seminorm.ofSMulLE (familyCapacity D) (familyCapacity_zero D)
    (familyCapacity_add_le D) (familyCapacity_smul_le D)

theorem familyCapacity_zero_iff {n r m : ℕ} (D : Fin m → Fin r → Finset (Fin n))
    (c : Fin m → ℝ) :
    familyCapacity D c = 0 ↔ ∀ g, familyValue D c (normalizeProbe g) = 0 := by
  constructor
  · intro h g
    have hp := familyCapacity_probe_bound D c g
    rw [h] at hp
    exact abs_eq_zero.mp (le_antisymm hp (abs_nonneg _))
  · intro h
    apply le_antisymm _ (familyCapacity_nonneg D c)
    apply csSup_le (Set.range_nonempty _)
    rintro _ ⟨g, rfl⟩
    dsimp only
    rw [h, abs_zero]

theorem normalizeProbe_idempotent {n : ℕ} (g : Fin n → ℝ) :
    normalizeProbe (normalizeProbe g) = normalizeProbe g := by
  funext i
  simp only [normalizeProbe, max_eq_left (normalizeProbe_budget g), div_one]

theorem diagramValue_monotone_majorant {n r : ℕ} (D : Fin r → Finset (Fin n))
    (g : Fin n → ℝ) : |diagramValue D g| ≤ diagramValue D (fun i => |g i|) := by
  unfold diagramValue
  rw [Finset.abs_prod]
  exact prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_sum_le_sum_abs _ _)

def intervalSeminorm {n r m : ℕ} (D : Fin m → Fin r → Fin n × Fin n) :
    Seminorm ℝ (Fin m → ℝ) :=
  chronologicalSeminorm (fun j k => Icc (D j k).1 (D j k).2)

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
