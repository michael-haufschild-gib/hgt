import GaloisForLFunctions.RHTower.Sieve.CoprimeHarmonicBounds

/-!
# The coprime harmonic sum as a Möbius-weighted harmonic sum

Detecting coprimality by `[(e,k)=1] = ∑_{f ∣ (e,k)} μ(f)` and reindexing the multiples of `f`
turns the coprime harmonic sum into a finite Möbius combination of ordinary harmonic sums:

`H_e(z) = ∑_{f ∣ e} (μ(f)/f) · H(⌊z/f⌋)`.

This is the exact identity whose main term supplies the factor `φ(e)/e = ∑_{f ∣ e} μ(f)/f`.
-/

open Finset ArithmeticFunction GaloisForLFunctions.HTGeometry
open scoped ArithmeticFunction.Moebius BigOperators

namespace RHTower.Sieve

/-- **The coprime harmonic sum is a Möbius combination of harmonic sums.** -/
theorem coprimeHarmonic_eq_sum_divisors {e z : ℕ} (he : 0 < e) :
    coprimeHarmonic e z
      = ∑ f ∈ e.divisors, ((μ f : ℤ) : ℝ) / (f : ℝ) *
          ∑ j ∈ Finset.Icc 1 (z / f), 1 / (j : ℝ) := by
  classical
  have hdet : coprimeHarmonic e z
      = ∑ k ∈ Finset.Icc 1 z,
          ∑ f ∈ (Nat.gcd e k).divisors, ((μ f : ℤ) : ℝ) * (1 / (k : ℝ)) := by
    rw [coprimeHarmonic, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_mul, sum_divisors_moebius_real]
    by_cases hc : Nat.gcd e k = 1
    · rw [if_pos hc, if_pos hc]
      ring
    · rw [if_neg hc, if_neg hc]
      ring
  rw [hdet]
  have hmem : ∀ (k f : ℕ),
      k ∈ Finset.Icc 1 z ∧ f ∈ (Nat.gcd e k).divisors
        ↔ k ∈ (Finset.Icc 1 z).filter (fun k => f ∣ k) ∧ f ∈ e.divisors := by
    intro k f
    constructor
    · rintro ⟨hk, hf⟩
      obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
      have hfg : f ∣ Nat.gcd e k := Nat.dvd_of_mem_divisors hf
      have hfe : f ∣ e := dvd_trans hfg (Nat.gcd_dvd_left _ _)
      have hfk : f ∣ k := dvd_trans hfg (Nat.gcd_dvd_right _ _)
      exact ⟨Finset.mem_filter.mpr ⟨hk, hfk⟩, Nat.mem_divisors.mpr ⟨hfe, by omega⟩⟩
    · rintro ⟨hkf, hf⟩
      obtain ⟨hk, hfk⟩ := Finset.mem_filter.mp hkf
      obtain ⟨hk1, hkz⟩ := Finset.mem_Icc.mp hk
      have hfe : f ∣ e := Nat.dvd_of_mem_divisors hf
      refine ⟨hk, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hfe hfk, ?_⟩⟩
      exact Nat.pos_iff_ne_zero.mp (Nat.gcd_pos_of_pos_right e (by omega))
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun f hf => ?_
  have hf0 : 0 < f := Nat.pos_of_mem_divisors hf
  have hfR : (0 : ℝ) < (f : ℝ) := by exact_mod_cast hf0
  rw [sum_filter_dvd_eq_sum_scaled hf0 (fun k => ((μ f : ℤ) : ℝ) * (1 / (k : ℝ)))]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  obtain ⟨hj1, -⟩ := Finset.mem_Icc.mp hj
  have hjR : (0 : ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hcast : (((f * j : ℕ)) : ℝ) = (f : ℝ) * (j : ℝ) := by push_cast; ring
  rw [hcast]
  field_simp

end RHTower.Sieve
