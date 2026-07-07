/-
# Multiplicative independence of the shifted values {n+α} for transcendental α

`LogIndependence.log_shifts_independent` proves the shifted logarithms `log(n+α)` are ℤ-linearly
independent for transcendental `α`; `ValueOrbit.log_relation_of_mul_relation` turns a multiplicative
relation into a logarithmic one.  Composing them: the shifted values `{n+α}` are multiplicatively
independent — the only relation `∏ (n+α)^{k_n} = 1` is the trivial one.  This is the transcendence
backbone of the Hurwitz value-independence results, and it forces the shifted value orbit onto no
proper relation subtorus.
-/
import GaloisForLFunctions.RHTower.LogIndependence
import GaloisForLFunctions.RHTower.ValueOrbit
import GaloisForLFunctions.RHTower.WeylEquidistribution

open Real Complex Filter Topology
open scoped BigOperators

namespace RHTower

/-- **Multiplicative independence of the shifted values (transcendental shift).**  For transcendental
`α > 0`, the only integer multiplicative relation among the shifted values `{n+α : n ∈ s}` is trivial:
`∏_{n∈s} (n+α)^{k_n} = 1 ⟹ k_n = 0` for all `n`.  Via `log_relation_of_mul_relation` (relation ⟹
log-relation) and `log_shifts_independent` (log-independence for transcendental `α`). -/
theorem shifted_values_mult_independent {α : ℝ} (h0 : 0 < α) (hα : Transcendental ℚ α)
    (s : Finset ℕ) (k : ℕ → ℤ)
    (hrel : ∏ n ∈ s, ((n : ℝ) + α) ^ (k n) = 1) :
    ∀ n ∈ s, k n = 0 :=
  log_shifts_independent h0 hα s k
    (log_relation_of_mul_relation s (fun n => (n : ℝ) + α) k
      (fun n _ => by positivity) hrel)

/-- **The shifted value orbit lies on no proper relation subtorus.**  For transcendental `α > 0`, a
multiplicative relation `∏ (n+α)^{k_n} = 1` — equivalently, the value-orbit character
`t ↦ ∏ (exp(−t·log(n+α)·i))^{k_n}` being identically `1` — occurs only for the trivial exponents
`k_n = 0`.  The joint phase of the shifted Dirichlet monomials `(n+α)^{−it}` is rationally
independent. -/
theorem shifted_value_orbit_relation_trivial {α : ℝ} (h0 : 0 < α) (hα : Transcendental ℚ α)
    (s : Finset ℕ) (k : ℕ → ℤ)
    (hrel : ∏ n ∈ s, ((n : ℝ) + α) ^ (k n) = 1) (t : ℝ) :
    (∀ n ∈ s, k n = 0) ∧
      ∏ n ∈ s, (Complex.exp (-(t : ℂ) * (Real.log ((n : ℝ) + α) : ℂ) * Complex.I)) ^ (k n) = 1 :=
  ⟨shifted_values_mult_independent h0 hα s k hrel,
    orbit_on_relation_subtorus s (fun n => (n : ℝ) + α) k (fun n _ => by positivity) hrel t⟩

/-- **Weyl equidistribution of the shifted Dirichlet monomials (transcendental shift).**  For
transcendental `α > 0` and any *nontrivial* integer exponent vector `k` (some `k_n ≠ 0`), the character
frequency `∑ k_n log(n+α)` is nonzero (shifted log-independence), so its Cesàro time average over
`[0,T]` vanishes as `T → ∞`.  The joint phase of the shifted Dirichlet monomials `(n+α)^{−it}`
equidistributes: no nontrivial character has a nonzero mean. -/
theorem shifted_character_time_average_vanishes {α : ℝ} (h0 : 0 < α) (hα : Transcendental ℚ α)
    (s : Finset ℕ) (k : ℕ → ℤ) (hk : ∃ n ∈ s, k n ≠ 0) :
    Tendsto (fun T : ℝ => (↑T)⁻¹ *
        ∫ t in (0 : ℝ)..T,
          Complex.exp ((∑ n ∈ s, (k n : ℝ) * Real.log ((n : ℝ) + α)) * Complex.I * ↑t))
      atTop (𝓝 0) := by
  refine Weyl.char_time_average_tendsto _ ?_
  intro hzero
  obtain ⟨n, hns, hkn⟩ := hk
  exact hkn (log_shifts_independent h0 hα s k hzero n hns)

end RHTower
