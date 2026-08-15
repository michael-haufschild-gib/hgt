import GaloisForLFunctions.RHTower.Matveev.LinearFormBasic

/-!
# The small linear form and its perturbed normalization

Baker's method is run on a relation.  For the *effective* theorem the relation is not exact: one
assumes only that the form is small, and every use of the exact normalization

`log p_pivot = −Σ_{i≠pivot} (bᵢ/b_pivot) log pᵢ`

acquires the explicit error `Λ/b_pivot`.  This file fixes the object carrying that data — a nonzero
integer coefficient vector together with a pivot at which the coefficient is maximal in absolute
value — and proves the perturbed normalization, the elementary consequences of maximality, and the
comparison between the `ℓ¹` and `ℓ^∞` heights.

Choosing the pivot maximal is what makes the normalized coefficients bounded by one, which is the
form the auxiliary construction consumes.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.Matveev

open Finset

variable {d : ℕ}

/-- The `ℓ^∞` height of an integer coefficient vector. -/
def coeffSup (ν : Fin d → ℤ) : ℕ := Finset.univ.sup (fun i => (ν i).natAbs)

theorem coeffSup_le_coeffHeight (ν : Fin d → ℤ) : coeffSup ν ≤ coeffHeight ν := by
  classical
  refine Finset.sup_le fun i _ => ?_
  rw [coeffHeight]
  exact Finset.single_le_sum (f := fun j => (ν j).natAbs) (fun j _ => Nat.zero_le _)
    (Finset.mem_univ i)

theorem coeffHeight_le_card_mul_coeffSup (ν : Fin d → ℤ) :
    coeffHeight ν ≤ d * coeffSup ν := by
  classical
  rw [coeffHeight]
  calc ∑ i, (ν i).natAbs ≤ ∑ _i : Fin d, coeffSup ν :=
        Finset.sum_le_sum fun i _ =>
          Finset.le_sup (f := fun j => (ν j).natAbs) (Finset.mem_univ i)
    _ = d * coeffSup ν := by simp

theorem coeffSup_eq_zero_iff (ν : Fin d → ℤ) : coeffSup ν = 0 ↔ ν = 0 := by
  classical
  constructor
  · intro h
    funext i
    have hi : (ν i).natAbs ≤ coeffSup ν :=
      Finset.le_sup (f := fun j => (ν j).natAbs) (Finset.mem_univ i)
    rw [h] at hi
    show ν i = 0
    omega
  · intro h
    subst h
    simp [coeffSup]

/-- **A maximal pivot exists.**  Every nonzero coefficient vector has an index at which the absolute
value attains the `ℓ^∞` height. -/
theorem exists_max_pivot (ν : Fin d → ℤ) (hν : ν ≠ 0) :
    ∃ k : Fin d, ν k ≠ 0 ∧ ∀ i, (ν i).natAbs ≤ (ν k).natAbs := by
  classical
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
    rcases Nat.eq_zero_or_pos d with hd | hd
    · exfalso
      apply hν
      funext i
      exact absurd i.2 (by omega)
    · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd)
  obtain ⟨k, _, hk⟩ := Finset.exists_max_image Finset.univ (fun i => (ν i).natAbs) hne
  refine ⟨k, ?_, fun i => hk i (Finset.mem_univ i)⟩
  intro hzero
  apply hν
  funext i
  have hi := hk i (Finset.mem_univ i)
  rw [hzero] at hi
  simp only [Int.natAbs_zero, Nat.le_zero] at hi
  show ν i = 0
  omega

/-! ## The small-form object -/

/-- A nonzero integer linear form in prime logarithms, with a distinguished pivot at which the
coefficient is maximal in absolute value. -/
structure SmallForm (d : ℕ) where
  /-- the prime family -/
  p : Fin d → ℕ
  /-- the primes are distinct -/
  p_injective : Function.Injective p
  /-- every entry is prime -/
  p_prime : ∀ i, (p i).Prime
  /-- the integer coefficient vector -/
  b : Fin d → ℤ
  /-- the coefficient vector is nonzero -/
  b_ne_zero : b ≠ 0
  /-- the pivot index -/
  pivot : Fin d
  /-- the pivot coefficient is nonzero -/
  pivot_ne_zero : b pivot ≠ 0
  /-- the pivot coefficient is maximal -/
  pivot_max : ∀ i, (b i).natAbs ≤ (b pivot).natAbs

namespace SmallForm

variable (S : SmallForm d)

/-- The value of the linear form. -/
def value : ℝ := primeLogForm S.p S.b

/-- The normalized coefficients, bounded by one in absolute value. -/
def normCoeff (i : Fin d) : ℝ := (S.b i : ℝ) / (S.b S.pivot : ℝ)

theorem pivot_cast_ne_zero : ((S.b S.pivot : ℤ) : ℝ) ≠ 0 := by
  exact_mod_cast S.pivot_ne_zero

theorem abs_normCoeff_le_one (i : Fin d) : |S.normCoeff i| ≤ 1 := by
  have hpiv : (0 : ℝ) < |((S.b S.pivot : ℤ) : ℝ)| := abs_pos.mpr S.pivot_cast_ne_zero
  rw [normCoeff, abs_div, div_le_one hpiv]
  have hnat : (S.b i).natAbs ≤ (S.b S.pivot).natAbs := S.pivot_max i
  have hint : |S.b i| ≤ |S.b S.pivot| := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast hnat
  calc |((S.b i : ℤ) : ℝ)| = ((|S.b i| : ℤ) : ℝ) := by
        rw [← Int.cast_abs]
    _ ≤ ((|S.b S.pivot| : ℤ) : ℝ) := by exact_mod_cast hint
    _ = |((S.b S.pivot : ℤ) : ℝ)| := by rw [← Int.cast_abs]

theorem normCoeff_pivot : S.normCoeff S.pivot = 1 := by
  rw [normCoeff, div_self S.pivot_cast_ne_zero]

/-- **The perturbed normalization.**  Solving the small form for the pivot logarithm leaves the
exact error `Λ/b_pivot`; with an exactly vanishing form this is the classical normalization. -/
theorem pivot_log_eq :
    Real.log (S.p S.pivot)
      = -∑ i ∈ Finset.univ.erase S.pivot, S.normCoeff i * Real.log (S.p i)
        + S.value / (S.b S.pivot : ℝ) := by
  have hsplit : S.value
      = (S.b S.pivot : ℝ) * Real.log (S.p S.pivot)
        + ∑ i ∈ Finset.univ.erase S.pivot, (S.b i : ℝ) * Real.log (S.p i) := by
    rw [value, primeLogForm, ← Finset.sum_erase_add _ _ (Finset.mem_univ S.pivot)]
    ring
  have hpiv := S.pivot_cast_ne_zero
  have hpull : ∑ i ∈ Finset.univ.erase S.pivot, S.normCoeff i * Real.log (S.p i)
      = (∑ i ∈ Finset.univ.erase S.pivot, (S.b i : ℝ) * Real.log (S.p i))
        / (S.b S.pivot : ℝ) := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by rw [normCoeff]; ring
  rw [hpull]
  field_simp
  linarith [hsplit]

/-- The `ℓ^∞` height of the coefficient vector, which is the pivot's absolute value. -/
theorem coeffSup_eq_pivot : coeffSup S.b = (S.b S.pivot).natAbs := by
  classical
  refine le_antisymm (Finset.sup_le fun i _ => S.pivot_max i) ?_
  exact Finset.le_sup (f := fun j => (S.b j).natAbs) (Finset.mem_univ S.pivot)

/-- The pivot coefficient controls the `ℓ¹` height. -/
theorem coeffHeight_le : coeffHeight S.b ≤ d * (S.b S.pivot).natAbs := by
  rw [← coeffSup_eq_pivot]
  exact coeffHeight_le_card_mul_coeffSup S.b

/-- The form is nonzero. -/
theorem value_ne_zero : S.value ≠ 0 := by
  intro h
  exact S.b_ne_zero ((primeLogForm_eq_zero_iff S.p S.p_injective S.p_prime S.b).mp h)

end SmallForm

end GaloisForLFunctions.RHTower.Matveev
