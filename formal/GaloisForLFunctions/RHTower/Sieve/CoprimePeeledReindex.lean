import GaloisForLFunctions.RHTower.Sieve.CoprimePrimePeeling

/-!
# Reindexing the peeled part

The part of a coprimality class divisible by a prime `p` is the scaling by `p` of the coprimality
class at height `y/p`.  This is the reindexing half of the prime-peeling recursion.
-/

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **Reindexing the peeled part.** -/
theorem sum_filter_coprime_dvd_reindex {p e y : ℕ} (hp : p.Prime) (hpe : ¬ p ∣ e) (F : ℕ → ℝ) :
    ∑ j ∈ (Finset.Icc 1 y).filter (fun j => Nat.Coprime e j ∧ p ∣ j), F j
      = ∑ j ∈ (Finset.Icc 1 (y / p)).filter (fun j => Nat.Coprime e j), F (p * j) := by
  classical
  have hp0 : 0 < p := hp.pos
  have hep : Nat.Coprime e p := (Nat.coprime_comm.mp (hp.coprime_iff_not_dvd.mpr hpe))
  refine Finset.sum_nbij' (i := fun j => j / p) (j := fun j => p * j) ?_ ?_ ?_ ?_ ?_
  · intro a ha
    obtain ⟨hmem, hce, hdvd⟩ := Finset.mem_filter.mp ha
    obtain ⟨ha1, hay⟩ := Finset.mem_Icc.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_⟩
    · exact (Nat.one_le_div_iff hp0).mpr (Nat.le_of_dvd (by omega) hdvd)
    · exact Nat.div_le_div_right hay
    · exact Nat.Coprime.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd) hce
  · intro b hb
    obtain ⟨hmem, hce⟩ := Finset.mem_filter.mp hb
    obtain ⟨hb1, hby⟩ := Finset.mem_Icc.mp hmem
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
    · calc p * b ≤ p * (y / p) := Nat.mul_le_mul_left p hby
        _ ≤ y := Nat.mul_div_le y p
    · exact Nat.Coprime.mul_right hep hce
    · exact Dvd.intro b rfl
  · intro a ha
    obtain ⟨-, -, hdvd⟩ := Finset.mem_filter.mp ha
    exact Nat.mul_div_cancel' hdvd
  · intro b _
    exact Nat.mul_div_cancel_left b hp0
  · intro a ha
    obtain ⟨-, -, hdvd⟩ := Finset.mem_filter.mp ha
    rw [Nat.mul_div_cancel' hdvd]

end RHTower.Sieve
