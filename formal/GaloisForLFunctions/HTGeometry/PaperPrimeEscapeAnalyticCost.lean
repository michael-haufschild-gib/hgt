import GaloisForLFunctions.HTGeometry.PaperMoebiusPrimePrefixEscape
import GaloisForLFunctions.HTGeometry.PaperPrimeTransportConormal
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!+# Analytic cost of prime escape with the Xi ideal fixed

The same time-one sources that annihilate every finite coefficient prefix preserve
the original Xi ideal and full conormal on Re(s)>0. Their multiplier is 1-p^s;
its norm differs from p^(Re s) by at most one. Consequently the multipliers
diverge at every point of that half-plane as the cutoff escapes.

This supplies the exact missing cost in the finite-energy construction: zero
energy at a moving cutoff does not yield a uniformly controlled transport.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

noncomputable section

/-- The analytic cost of time one is determined to additive error at most one. -/
theorem paperPrimeTransportFactor_time_one_norm_envelope (p : Nat.Primes) (s : ℂ) :
    |‖paperPrimeTransportFactor p 1 s‖ - (p : ℝ) ^ s.re| ≤ 1 := by
  have h := abs_norm_sub_norm_le (1 - ((p : ℕ) : ℂ) ^ s) (-((p : ℕ) : ℂ) ^ s)
  have he : (1 - ((p : ℕ) : ℂ) ^ s) - (-((p : ℕ) : ℂ) ^ s) = 1 := by ring
  rw [he, norm_one, norm_neg, Complex.norm_natCast_cpow_of_pos p.property.pos] at h
  simpa only [paperPrimeTransportFactor_time_one] using h

/-- The primes used to erase successive prefixes escape in the real topology. -/
theorem paperEscapingPrime_tendsto_atTop :
    Tendsto (fun N : ℕ => (paperEscapingPrime N : ℝ)) atTop atTop := by
  apply tendsto_atTop_mono (f := fun N : ℕ => (N : ℝ))
  · intro N
    exact_mod_cast (paperEscapingPrime_gt N).le
  · exact tendsto_natCast_atTop_atTop

/-- At each point of Re(s)>0, the exact divisor-preserving multiplier diverges. -/
theorem paperPrimeEscape_factor_tendsto_atTop (s : {s : ℂ // 0 < s.re}) :
    Tendsto (fun N : ℕ => ‖paperPrimeTransportFactor (paperEscapingPrime N) 1 s‖)
      atTop atTop := by
  have hp := (tendsto_rpow_atTop s.property).comp paperEscapingPrime_tendsto_atTop
  refine tendsto_atTop_atTop.mpr fun B => ?_
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp hp (B + 1)
  refine ⟨N, fun M hM => ?_⟩
  have hpower := hN M hM
  change B + 1 ≤ (paperEscapingPrime M : ℝ) ^ (s : ℂ).re at hpower
  have hnorm := (abs_le.mp
    (paperPrimeTransportFactor_time_one_norm_envelope (paperEscapingPrime M) s)).1
  linarith

/-- No pointwise uniform analytic multiplier bound survives this prefix escape. -/
theorem paperPrimeEscape_no_uniform_factor_bound (s : {s : ℂ // 0 < s.re}) :
    ¬∃ B : ℝ, ∀ N : ℕ, ‖paperPrimeTransportFactor (paperEscapingPrime N) 1 s‖ ≤ B := by
  rintro ⟨B, hB⟩
  obtain ⟨N, hN⟩ := tendsto_atTop_atTop.mp (paperPrimeEscape_factor_tendsto_atTop s) (B + 1)
  have hlower := hN N le_rfl
  have hupper := hB N
  linarith

/-- Arbitrarily large analytic cost coexists with zero finite energy and the exact
original Xi ideal. The full conormal is therefore the original one as well. -/
theorem paperPrimeEscape_fixed_ideal_unbounded_cost (N : ℕ)
    (s : {s : ℂ // 0 < s.re}) (B : ℝ) :
    ∃ p : Nat.Primes,
      (∀ n : Fin (N + 1), paperMoebiusPrimeTransport p 1 n = 0) ∧
      paperMoebiusPrimeTransport p 1 ≠ 0 ∧
      (∀ r : ℝ, paperMoebiusPrimeEnergy p 1 N r = 0) ∧
      paperPrimeTransportXiIdeal p 0 ⟨1, Or.inl rfl⟩ = paperPrimeOriginalXiIdeal 0 ∧
      B < ‖paperPrimeTransportFactor p 1 s‖ := by
  obtain ⟨K, hK⟩ := tendsto_atTop_atTop.mp (paperPrimeEscape_factor_tendsto_atTop s) (B + 1)
  let M := max N K
  refine ⟨paperEscapingPrime M, ?_, paperMoebiusEscapingPrime_ne_zero M,
    ?_, paperPrimeTransportXiIdeal_eq _ _ _, ?_⟩
  · intro n
    exact paperMoebiusPrimeTransport_time_one_below _
      ⟨n, lt_of_le_of_lt (le_trans (Nat.le_of_lt_succ n.isLt) (le_max_left N K))
        (paperEscapingPrime_gt M)⟩
  · intro r
    exact paperMoebiusPrimeTransport_time_one_energy_below _
      ⟨N, lt_of_le_of_lt (le_max_left N K) (paperEscapingPrime_gt M)⟩ r
  · have h := hK M (le_max_right N K)
    linarith

end

end GaloisForLFunctions.HTGeometry
