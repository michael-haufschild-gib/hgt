import GaloisForLFunctions.RHTower.Sieve.ResidueParseval

/-!
# Omitted residue classes force large exponential sums

Parseval over the residues equates `∑_{a<q} |S(a/q)|²` with `q ∑_h A_h²`.  Removing the term `a = 0`,
where `S(0) = |A|`, and bounding `∑_h A_h²` below by Cauchy–Schwarz over the *occupied* classes
gives

`|A|² (q - c) ≤ c ∑_{a ≠ 0} |S(a/q)|²`,   `c = #{h : A meets the class h}`.

So a set that misses many residue classes modulo `q` has large exponential sums at the fractions
with denominator `q`.  This is the lower bound half of Montgomery's sieve; the large sieve of this
folder is the upper bound half, and together they bound `|A|`.

The inequality is stated multiplicatively rather than as `∑_h A_h² ≥ |A|²/c`, so that it remains
true, and vacuous, when `A` is empty.
-/

namespace RHTower.Sieve

open Finset

/-- The residue classes modulo `q` that `A` actually meets. -/
def occupiedClasses (q : ℕ) (A : Finset ℕ) : Finset ℕ :=
  (Finset.range q).filter (fun h => residueCount q A h ≠ 0)

theorem occupiedClasses_subset (q : ℕ) (A : Finset ℕ) :
    occupiedClasses q A ⊆ Finset.range q := Finset.filter_subset _ _

/-- The residue counts sum to the cardinality. -/
theorem sum_residueCount {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    ∑ h ∈ Finset.range q, residueCount q A h = A.card := by
  classical
  have hmaps : Set.MapsTo (fun n => n % q) (A : Set ℕ) (Finset.range q : Set ℕ) := by
    intro n _
    simp only [Finset.coe_range, Set.mem_Iio]
    exact Nat.mod_lt _ hq
  exact (Finset.card_eq_sum_card_fiberwise hmaps).symm

/-- Only the occupied classes contribute. -/
theorem sum_residueCount_occupied {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    ∑ h ∈ occupiedClasses q A, ((residueCount q A h : ℕ) : ℝ) = (A.card : ℝ) := by
  classical
  have hzero : ∀ x ∈ Finset.range q, x ∉ occupiedClasses q A →
      ((residueCount q A x : ℕ) : ℝ) = 0 := by
    intro x hx hnx
    have hz : residueCount q A x = 0 := by
      by_contra hne
      exact hnx (Finset.mem_filter.mpr ⟨hx, hne⟩)
    rw [hz]
    norm_num
  rw [Finset.sum_subset (occupiedClasses_subset q A) hzero, ← Nat.cast_sum,
    sum_residueCount hq A]

/-- **Cauchy–Schwarz over the occupied classes.** -/
theorem sq_card_le_occupied_mul {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    (A.card : ℝ) ^ (2 : ℕ)
      ≤ ((occupiedClasses q A).card : ℝ)
          * ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ (2 : ℕ) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (occupiedClasses q A)
    (fun _ => (1 : ℝ)) (fun h => ((residueCount q A h : ℕ) : ℝ))
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hcs
  rw [sum_residueCount_occupied hq A] at hcs
  refine le_trans hcs ?_
  have hmono : ∑ h ∈ occupiedClasses q A, ((residueCount q A h : ℕ) : ℝ) ^ (2 : ℕ)
      ≤ ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ (2 : ℕ) :=
    Finset.sum_le_sum_of_subset_of_nonneg (occupiedClasses_subset q A)
      (fun i _ _ => by positivity)
  exact mul_le_mul_of_nonneg_left hmono (by positivity)

/-- The exponential sum at the trivial frequency is the cardinality. -/
theorem expSum_zero (q : ℕ) (A : Finset ℕ) :
    ∑ n ∈ A, circleFreq (((n * 0 : ℕ) : ℝ) / (q : ℝ)) = (A.card : ℂ) := by
  have hone : ∀ n : ℕ, circleFreq (((n * 0 : ℕ) : ℝ) / (q : ℝ)) = 1 := by
    intro n
    simp [circleFreq]
  rw [Finset.sum_congr rfl (fun n _ => hone n), Finset.sum_const, nsmul_eq_mul, mul_one]

/-- **Omitted classes force large exponential sums.** -/
theorem occupied_mul_sum_nonzero_ge {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    (A.card : ℝ) ^ (2 : ℕ) * ((q : ℝ) - ((occupiedClasses q A).card : ℝ))
      ≤ ((occupiedClasses q A).card : ℝ)
          * ∑ j ∈ (Finset.univ : Finset (Fin q)).erase ⟨0, hq⟩,
              ‖∑ n ∈ A, circleFreq (((n * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ (2 : ℕ) := by
  classical
  set c : ℝ := ((occupiedClasses q A).card : ℝ) with hc
  set E : ℝ := ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ (2 : ℕ) with hE
  set T : ℝ := ∑ j ∈ (Finset.univ : Finset (Fin q)).erase ⟨0, hq⟩,
      ‖∑ n ∈ A, circleFreq (((n * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ (2 : ℕ) with hT
  have hzero : ‖∑ n ∈ A, circleFreq (((n * ((⟨0, hq⟩ : Fin q) : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ (2 : ℕ)
      = (A.card : ℝ) ^ (2 : ℕ) := by
    have hval : ((⟨0, hq⟩ : Fin q) : ℕ) = 0 := rfl
    rw [hval, expSum_zero]
    simp
  have hsplit := Finset.add_sum_erase (Finset.univ : Finset (Fin q))
    (fun j => ‖∑ n ∈ A, circleFreq (((n * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ (2 : ℕ))
    (Finset.mem_univ (⟨0, hq⟩ : Fin q))
  rw [hzero] at hsplit
  have hfull := sum_full_expSum_sq hq A
  rw [← hE] at hfull
  have heq : (A.card : ℝ) ^ (2 : ℕ) + T = (q : ℝ) * E := by
    rw [hT, hsplit]
    exact hfull
  have hCS : (A.card : ℝ) ^ (2 : ℕ) ≤ c * E := sq_card_le_occupied_mul hq A
  have hqR : (0 : ℝ) ≤ (q : ℝ) := by positivity
  have hmul : c * ((A.card : ℝ) ^ (2 : ℕ) + T) = c * ((q : ℝ) * E) := by rw [heq]
  nlinarith [hCS, hqR, hmul]

end RHTower.Sieve
