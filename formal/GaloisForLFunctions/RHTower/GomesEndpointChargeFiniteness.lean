import GaloisForLFunctions.RHTower.GomesEndpointTensorCharacters

/-!
# Which tensor charges remain finite?

The full integer tensor character lattice exists algebraically. Its finite-measure sector is
an open half-space cut through that lattice. Duality preserves the entire finite sector only
for the trivial generator. Tensor addition preserves it precisely for the trivial generator
or when the surviving sector is an integer cone. These are exact analytic consequences of
applying the charge construction of arXiv:2509.25276v7 section 5.2 to endpoint densities.
-/

noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry
open scoped NNReal ENNReal

namespace RHTower

/-- The integer charges whose scalar tensor densities define finite source measures. -/
def gomesEndpointFiniteCharges (b : ℝ) : Set ℤ := {n | -1 < (n : ℝ) * b}

/-- Membership is precisely integrability of the actual charged density. -/
theorem gomesEndpointFiniteCharges_mem_iff (b : ℝ) (n : ℤ) :
    n ∈ gomesEndpointFiniteCharges b ↔ Integrable (gomesEndpointTensorDensity b n)
      (gomesHausdorffUniformSource : Measure HausdorffSourceSpace) :=
  (gomesEndpointTensorDensity_integrable_iff b n).symm

/-- The neutral charge is always finite. -/
theorem gomesEndpointFiniteCharges_zero (b : ℝ) : 0 ∈ gomesEndpointFiniteCharges b := by
  simp [gomesEndpointFiniteCharges]

/-- Reversing the generator reverses the admissible charge lattice. -/
theorem gomesEndpointFiniteCharges_neg_generator (b : ℝ) (n : ℤ) :
    n ∈ gomesEndpointFiniteCharges (-b) ↔ -n ∈ gomesEndpointFiniteCharges b := by
  simp [gomesEndpointFiniteCharges]

/-- A charge and its dual are both finite exactly inside the unit exponent window. -/
theorem gomesEndpointFiniteCharges_dual_pair (b : ℝ) (n : ℤ) :
    (n ∈ gomesEndpointFiniteCharges b ∧ -n ∈ gomesEndpointFiniteCharges b) ↔
      |(n : ℝ) * b| < 1 := by
  change (-1 < (n : ℝ) * b ∧ -1 < ((-n : ℤ) : ℝ) * b) ↔ _
  rw [Int.cast_neg, neg_mul, abs_lt]
  constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith

/-- At least one member of every dual pair is finite. -/
theorem gomesEndpointFiniteCharges_one_of_dual (b : ℝ) (n : ℤ) :
    n ∈ gomesEndpointFiniteCharges b ∨ -n ∈ gomesEndpointFiniteCharges b := by
  change -1 < (n : ℝ) * b ∨ -1 < ((-n : ℤ) : ℝ) * b
  rw [Int.cast_neg, neg_mul]
  rcases le_total 0 ((n : ℝ) * b) with h | h
  · left; linarith
  · right; linarith

/-- No nontrivial generator keeps every integer tensor charge finite. -/
theorem gomesEndpointFiniteCharges_all_iff (b : ℝ) :
    (∀ n : ℤ, n ∈ gomesEndpointFiniteCharges b) ↔ b = 0 := by
  constructor
  · intro h
    by_contra hb
    rcases lt_or_gt_of_ne hb with hn | hp
    · obtain ⟨n, hgt⟩ := exists_int_gt (-1 / b)
      have hm := mul_lt_mul_of_neg_right hgt hn
      rw [div_mul_cancel₀ _ hb] at hm
      have hf := h n
      change -1 < (n : ℝ) * b at hf
      linarith
    · obtain ⟨n, hlt⟩ := exists_int_lt (-1 / b)
      have hm := mul_lt_mul_of_pos_right hlt hp
      rw [div_mul_cancel₀ _ hb] at hm
      have hf := h n
      change -1 < (n : ℝ) * b at hf
      linarith
  · rintro rfl n
    simp [gomesEndpointFiniteCharges]

/-- Closure of the finite sector under dualization is equivalent to a trivial generator. -/
theorem gomesEndpointFiniteCharges_dual_closed_iff (b : ℝ) :
    (∀ n : ℤ, n ∈ gomesEndpointFiniteCharges b → -n ∈ gomesEndpointFiniteCharges b) ↔ b = 0 := by
  constructor
  · intro h
    apply (gomesEndpointFiniteCharges_all_iff b).mp
    intro n
    rcases gomesEndpointFiniteCharges_one_of_dual b n with hn | hn
    · exact hn
    · simpa only [neg_neg] using h (-n) hn
  · rintro rfl n _
    simp [gomesEndpointFiniteCharges]

/-- At generator size at least one, precisely the nonnegative integer charges survive. -/
theorem gomesEndpointFiniteCharges_positiveCone (b : Set.Ici (1 : ℝ)) (n : ℤ) :
    n ∈ gomesEndpointFiniteCharges b ↔ 0 ≤ n := by
  have hb : (1 : ℝ) ≤ b := b.property
  have hb0 : (0 : ℝ) ≤ b := by linarith
  constructor
  · intro h
    by_contra hn
    have hn1 : n ≤ -1 := Int.le_sub_one_iff.mpr (lt_of_not_ge hn)
    have hnR : (n : ℝ) ≤ -1 := by exact_mod_cast hn1
    have hm := mul_le_mul_of_nonneg_right hnR hb0
    change -1 < (n : ℝ) * b at h
    linarith
  · intro hn
    have hnR : (0 : ℝ) ≤ n := by exact_mod_cast hn
    have hm := mul_nonneg hnR hb0
    change -1 < (n : ℝ) * b
    linarith

/-- The opposite generator gives precisely the nonpositive integer cone. -/
theorem gomesEndpointFiniteCharges_negativeCone (b : Set.Iic (-1 : ℝ)) (n : ℤ) :
    n ∈ gomesEndpointFiniteCharges b ↔ n ≤ 0 := by
  have hb : (b : ℝ) ≤ -1 := b.property
  have h := gomesEndpointFiniteCharges_positiveCone
    (⟨-(b : ℝ), by change (1 : ℝ) ≤ -(b : ℝ); linarith⟩ : Set.Ici (1 : ℝ)) (-n)
  rw [gomesEndpointFiniteCharges_neg_generator, neg_neg] at h
  simpa only [neg_nonneg] using h

/-- Exact tensor-addition closure: only the trivial lattice or a one-sided integer cone survives. -/
theorem gomesEndpointFiniteCharges_add_closed_iff (b : ℝ) :
    (∀ m n : ℤ, m ∈ gomesEndpointFiniteCharges b → n ∈ gomesEndpointFiniteCharges b →
      m + n ∈ gomesEndpointFiniteCharges b) ↔ b = 0 ∨ 1 ≤ |b| := by
  constructor
  · intro h
    by_cases hb : b = 0
    · exact Or.inl hb
    · right
      by_contra hab
      have hab' : |b| < 1 := lt_of_not_ge hab
      have hpair := (gomesEndpointFiniteCharges_dual_pair b 1).mpr (by simpa using hab')
      have hall : ∀ n : ℤ, n ∈ gomesEndpointFiniteCharges b := by
        intro n
        induction n using Int.induction_on with
        | zero => exact gomesEndpointFiniteCharges_zero b
        | succ k hk => exact h (k : ℤ) 1 hk hpair.1
        | pred k hk => simpa only [sub_eq_add_neg] using h (-(k : ℤ)) (-1) hk hpair.2
      exact hb ((gomesEndpointFiniteCharges_all_iff b).mp hall)
  · rintro (rfl | hb) m n hm hn
    · simp [gomesEndpointFiniteCharges]
    · by_cases hb0 : 0 ≤ b
      · rw [abs_of_nonneg hb0] at hb
        have hcone := gomesEndpointFiniteCharges_positiveCone (⟨b, hb⟩ : Set.Ici (1 : ℝ))
        exact (hcone (m + n)).mpr (add_nonneg ((hcone m).mp hm) ((hcone n).mp hn))
      · have hbneg : b ≤ -1 := by rw [abs_of_neg (lt_of_not_ge hb0)] at hb; linarith
        have hcone := gomesEndpointFiniteCharges_negativeCone (⟨b, hbneg⟩ : Set.Iic (-1 : ℝ))
        exact (hcone (m + n)).mpr (add_nonpos ((hcone m).mp hm) ((hcone n).mp hn))

/-- A nontrivial small generator has two finite charges whose tensor product has infinite mass. -/
theorem gomesEndpointFiniteCharges_tensor_failure_iff (b : ℝ) :
    (∃ m n : ℤ, m ∈ gomesEndpointFiniteCharges b ∧ n ∈ gomesEndpointFiniteCharges b ∧
      m + n ∉ gomesEndpointFiniteCharges b) ↔ b ≠ 0 ∧ |b| < 1 := by
  have h := not_congr (gomesEndpointFiniteCharges_add_closed_iff b)
  push Not at h
  exact h

/-- A symmetric charge window remains finite exactly below its endpoint exponent budget. -/
theorem gomesEndpointFiniteCharges_window_iff (b : ℝ) (N : ℕ) :
    (∀ n : ℤ, |n| ≤ (N : ℤ) → n ∈ gomesEndpointFiniteCharges b) ↔
      (N : ℝ) * |b| < 1 := by
  constructor
  · intro h
    have hp := (gomesEndpointFiniteCharges_dual_pair b (N : ℤ)).mp
      ⟨h (N : ℤ) (by simp), h (-(N : ℤ)) (by simp)⟩
    simpa only [Int.cast_natCast, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N)] using hp
  · intro hb n hn
    have hnR : |(n : ℝ)| ≤ (N : ℝ) := by exact_mod_cast hn
    have hm := mul_le_mul_of_nonneg_right hnR (abs_nonneg b)
    have hp : |(n : ℝ) * b| < 1 := by
      rw [abs_mul]
      exact lt_of_le_of_lt hm hb
    exact ((gomesEndpointFiniteCharges_dual_pair b n).mpr hp).1

end RHTower
