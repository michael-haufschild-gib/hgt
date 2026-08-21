import GaloisForLFunctions.RHTower.Sieve.MatomakiTeravainenCoefficientEnergySchedule

namespace RHTower.Sieve

open Finset

noncomputable section

/-! # Large-amplitude count for literal Type-II factors

This is the source-level `T₁` cardinality input. A bounded raising degree, its coefficient energy,
the exact block cover, and every Huxley schedule condition are discharged internally. -/

/-- A divisor-bounded dyadic factor has the required large-amplitude count at every admissible
fixed threshold. No raised coefficient energy or blockwise density premise remains. -/
theorem exists_matomakiTeravainen_large_amplitude_count_divisor_bounded
    {eps kappa C : ℝ}
    (heps : 0 < eps) (hepss : eps ≤ 1 / 1000) (hkappa : 0 < kappa)
    (hC : 1 ≤ C) (w L : ℕ) :
    ∃ T₀ : ℝ, 1 ≤ T₀ ∧
      ∀ (T : ℝ) (N A ell : ℕ) (rho : ℝ) (a : Fin N → ℂ) (S : Finset ℝ),
      T₀ ≤ T →
      1 ≤ N → N ≤ 2 * A → 1 < (A : ℝ) →
      0 < ell → ell ≤ L →
      T ^ ((9 : ℝ) / 11 - 10 * eps) ≤ ((A ^ ell : ℕ) : ℝ) →
      ((A ^ ell : ℕ) : ℝ) ≤ T ^ (1 - 2 * eps) →
      5 * eps + kappa ≤ rho → rho + kappa ≤ 7 / 32 - 5 * eps →
      (∀ n : Fin N,
        ‖a n‖ ≤ C * ((((n : ℕ) + 1).divisors.card : ℝ) ^ w)) →
      (∀ n : Fin N, a n ≠ 0 →
        A ≤ (n : ℕ) + 1 ∧ (n : ℕ) + 1 ≤ 2 * A) →
      (∀ x ∈ S, ∀ y ∈ S, x ≠ y → 1 ≤ |x - y|) →
      (∀ x ∈ S, ∀ y ∈ S, |x - y| ≤ 2 * T) →
      (∀ t ∈ S, (A : ℝ) ^ (-rho) ≤
        matomakiTeravainenDirichletAmplitude N a t) →
      (S.card : ℝ) ≤ (ell + 1 : ℝ) *
        T ^ (2 * (rho + kappa) - eps ^ 2 / 5) := by
  obtain ⟨Tenergy, hTenergy, henergy⟩ :=
    exists_matomakiTeravainen_coefficient_energy_schedule heps hC w L
  obtain ⟨Tschedule, hTschedule, hschedule⟩ :=
    exists_matomakiTeravainen_raised_huxley_schedule heps hepss hkappa L
  obtain ⟨Tcount, hTcount, hcount⟩ :=
    exists_lemma41_huxley_raised_energy heps hepss
  let T₀ : ℝ := max Tenergy (max Tschedule Tcount)
  refine ⟨T₀, hTenergy.trans (le_max_left _ _), ?_⟩
  intro T N A ell rho a S hT hN hNA hA hell hellL hbaseLo hbaseHi
    hrhoLo hrhoHi hpoint hsupp hsep hspread hlarge
  have hTe : Tenergy ≤ T := le_trans (le_max_left _ _) hT
  have hTs : Tschedule ≤ T :=
    le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hT
  have hTc : Tcount ≤ T :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hT
  obtain ⟨Q, hQ, hQ3, hE⟩ := henergy T N A ell a hTe hN hNA hell hellL
    hA hbaseHi hpoint
  have hscalar := hschedule T A ell rho Q hTs hell hellL hbaseLo hbaseHi
    hrhoLo hrhoHi hQ hQ3
  apply hcount T N A ell rho kappa Q a S hTc hQ hQ3
    (by exact_mod_cast (show 1 ≤ A by omega)) hell (by linarith)
  · intro r
    exact (hscalar r).1
  · intro r
    exact (hscalar r).2.1
  · intro r
    exact (hscalar r).2.2.1
  · intro r
    exact (hscalar r).2.2.2.1
  · intro r
    exact (hscalar r).2.2.2.2.1
  · intro r
    exact (hscalar r).2.2.2.2.2.1
  · intro r
    exact (hscalar r).2.2.2.2.2.2
  · exact hsupp
  · exact hE
  · exact hsep
  · exact hspread
  · intro t ht
    exact raisedDirichletValue_large_of_dirichletAmplitude_large
      (show 1 ≤ A by omega) a (hlarge t ht)

end

end RHTower.Sieve
