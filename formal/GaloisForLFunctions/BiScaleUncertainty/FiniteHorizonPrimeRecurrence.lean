import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import GaloisForLFunctions.BiScaleUncertainty.OddPrimeSieveFamilies
import Mathlib.Data.Nat.Factors

/-!
# Prime-count recurrence for a finite dilation horizon

Reuse the existing odd-prime modes and simultaneous approximation theorem.
Prime factorization transfers their phase control to every integer dilation up to the horizon.
-/

open scoped BigOperators
open Finset

namespace GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
open SieveMoments
noncomputable section
set_option autoImplicit false

private theorem length_add_one_le_prod (l : List ℕ) (hl : ∀ p ∈ l, 2 ≤ p) :
    l.length + 1 ≤ l.prod := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp := hl p (by simp)
    have htail : ∀ p ∈ l, 2 ≤ p := fun p hp => hl p (by simp [hp])
    have h := ih htail
    simp only [List.length_cons, List.prod_cons]
    nlinarith

private theorem product_log_approx (l : List ℕ) (hl : ∀ p ∈ l, 2 ≤ p)
    (q ε : ℝ)
    (h : ∀ p ∈ l, ∃ m : ℤ, |q * Real.log p / Real.log 2 - m| ≤ ε) :
    ∃ m : ℤ, |q * Real.log l.prod / Real.log 2 - m| ≤ (l.length : ℝ) * ε := by
  induction l with
  | nil => exact ⟨0, by simp⟩
  | cons p l ih =>
    have hp := hl p (by simp)
    have htail : ∀ p ∈ l, 2 ≤ p := fun p hp => hl p (by simp [hp])
    obtain ⟨a, ha⟩ := h p (by simp)
    obtain ⟨b, hb⟩ := ih htail (fun p hp => h p (by simp [hp]))
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
    have hl0 : (l.prod : ℝ) ≠ 0 := by
      have hlen := length_add_one_le_prod l htail
      exact_mod_cast (show l.prod ≠ 0 by omega)
    refine ⟨a + b, ?_⟩
    simp only [List.prod_cons, Nat.cast_mul, Real.log_mul hp0 hl0, Int.cast_add,
      List.length_cons, Nat.cast_add, Nat.cast_one]
    calc
      |q * (Real.log p + Real.log (l.prod : ℝ)) / Real.log 2 - ((a : ℝ) + b)| =
          |(q * Real.log p / Real.log 2 - a) +
            (q * Real.log (l.prod : ℝ) / Real.log 2 - b)| := by congr 1; ring
      _ ≤ |q * Real.log p / Real.log 2 - a| +
          |q * Real.log (l.prod : ℝ) / Real.log 2 - b| := abs_add_le _ _
      _ ≤ ε + (l.length : ℝ) * ε := add_le_add ha hb
      _ = ((l.length : ℝ) + 1) * ε := by ring

/-- The existing odd-prime modes control all integer dilations up to the horizon.
The count of independent approximations is the actual prime-mode count. -/
theorem exists_prime_horizon_recurrence (K Q : ℕ) :
    ∃ q : ℕ, 1 ≤ q ∧ q ≤ (Q + 1) ^ (oddPrimeModes (2 * K)).card ∧
      ∀ k : ℕ, 2 ≤ k → k ≤ K → ∃ m : ℤ,
        |(q : ℝ) * Real.log k / Real.log 2 - m| ≤ (K : ℝ) / (Q + 1) := by
  classical
  obtain ⟨q, hq, hbound, happ⟩ := HTGeometry.exists_dirichlet_simultaneous
    (fun p : oddPrimeModes (2 * K) => Real.log (p : ℕ) / Real.log 2) (Q + 1) (by omega)
  refine ⟨q, hq, by simpa using hbound, ?_⟩
  have hlog : Real.log 2 ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  have hQ : (0 : ℝ) < Q + 1 := by positivity
  have hprime : ∀ p : ℕ, Nat.Prime p → p ≤ K →
      ∃ m : ℤ, |(q : ℝ) * Real.log p / Real.log 2 - m| ≤ 1 / (Q + 1) := by
    intro p hp hpK
    by_cases hp2 : p = 2
    · subst p
      refine ⟨(q : ℤ), ?_⟩
      norm_num only [Nat.cast_ofNat]
      have he : (q : ℝ) * Real.log 2 / Real.log 2 - (q : ℤ) = 0 := by
        push_cast
        field_simp
        ring
      rw [he, abs_zero]
      positivity
    · have hmem : p ∈ oddPrimeModes (2 * K) :=
        mem_oddPrimeModes.mpr ⟨hp, hp.odd_of_ne_two hp2, by omega⟩
      obtain ⟨m, hm⟩ := happ ⟨p, hmem⟩
      refine ⟨m, ?_⟩
      simpa only [mul_div_assoc, Nat.cast_add, Nat.cast_one] using hm.le
  intro k hk hkK
  have htwo : ∀ p ∈ k.primeFactorsList, 2 ≤ p :=
    fun p hp => (Nat.prime_of_mem_primeFactorsList hp).two_le
  have hpk : ∀ p ∈ k.primeFactorsList, p ≤ K :=
    fun p hp => (Nat.le_of_mem_primeFactorsList hp).trans hkK
  obtain ⟨m, hm⟩ := product_log_approx k.primeFactorsList htwo (q : ℝ)
    (1 / (Q + 1))
    (fun p hp => hprime p (Nat.prime_of_mem_primeFactorsList hp) (hpk p hp))
  have hprod := Nat.prod_primeFactorsList (show k ≠ 0 by omega)
  rw [hprod] at hm
  refine ⟨m, hm.trans ?_⟩
  have hlength := length_add_one_le_prod k.primeFactorsList htwo
  rw [hprod] at hlength
  have hlen : (k.primeFactorsList.length : ℝ) ≤ K := by exact_mod_cast (by omega : k.primeFactorsList.length ≤ K)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_right hlen (le_of_lt (one_div_pos.mpr hQ))

end
end GaloisForLFunctions.BiScaleUncertainty.FiniteHorizon
