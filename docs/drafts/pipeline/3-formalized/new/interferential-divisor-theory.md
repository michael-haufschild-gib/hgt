# Interferential divisor: location, approximation, impossibility, clocks

- **ID:** interferential-divisor-theory
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — the theory of a new native object
- **Statement:** Split zeros of factored carriers into columnar (a factor vanishes — provably rides that column's vertical progression) and interferential (no factor vanishes). Interferential zeros exist only in the analytic continuation (absolutely convergent products with nonvanishing factors are nonvanishing); they admit no approximation by clockwork zeros of bounded period inventory (the responsible clock escapes); no finite regrouping of columns reaches their habitat (natural boundaries are inherited by finite products off partners' discrete divisors); the vertical stabilizer of a nonzero analytic divisor is cyclic, admits at most one prime clock, and pointwise clockwork does not produce a global clock (two-prime separation via 2^a ≠ 3^b). ζ's strip divisor is 100% interferential.
- **Lean:** `ColumnarInterferential.lean` (`columnar_zero_periodic`, `tprod_one_add_ne_zero`, `no_interferential_zero_in_product_region`), `ClockEscape.lean` (`periodic_zero_limit`, `aperiodic_zero_clock_escape`), `NoCrossColumnHealing.lean` (`column_extends_of_product_extends`, `no_healing`, `no_healing_finset`), `DivisorStabilizer.lean` (`vStab_cyclic_of_analytic`, `twoClock_vStab_trivial`, `vStab_one_prime_clock`, `dzo_vStab_nontrivial`). All axiom-clean. Depletion invariance = in-tree `FiniteEulerInert` (not rebuilt).
- **Dual gate:** PASS as a frame. NOVEL — the columnar/interferential cut and its closure theorems are not literature packagings (product nonvanishing is classical as a lemma; the object-level classification and the clock-escape/no-healing/one-clock rigidity statements are C-PD-native). SIGNIFICANT — bounds C-PD's open content exactly: constraint-only divisor of infinite Euler products; every finite avenue closed by theorem.

## Log
- 2026-07-09 — object named and theory formalized; mechanism conjecture (exact resonance) carded with [KNOWN]-folklore adjacency label on the codim-1 half.

## Verdict correction (2026-07-09, same day)
- **Dual gate: downgraded.** "Interferential" is a negation (no factor vanishes) — it names the
  object by what it is not, and the closure theorems classify what FLOWS do. Retained as the
  flow-side no-go bank. The constraint-side positive structure of this divisor is NOT delivered
  here; naming a complement is not constructing an object.
