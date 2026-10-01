# Linear-programming duality for the Weil cone

- **ID:** MC-186
- **Stage:** 3-formalized (STATUS MUST-624)
- **Type:** THEOREM (Lean)
- **Source:** MC loop cycle 186, after the notch route closed (MUST-622). It generalizes the corpus' prime-blind duality (`exists_weilPositiveUpTo_of_primeBlindPositive`) from feasibility to optimization.
- **Statement:** `sup {L_w(lam) : lam ∈ W_A} ≥ β ⟸ WeilDualBound (A+1) w β`, and `(∃ lam ∈ W_A, L_w(lam) ≥ β) ⇒ WeilDualBound A w β`. Here `WeilDualBound A w β` means that every `w`-matched family of polar tests at levels `≤ A` with multiplier `t` has archimedean energy `≥ tβ`.

## Goal
After cycles 180–185 the uniqueness half (nonnegative cone with vanishing local mass) reduces to one linear inequality at `s = 1`: `T ≥ 0`. Positivity tests give only `T ≤ 0`. This theorem shows where a lower bound must come from: every linear extremal value over the Weil cone equals an archimedean energy minimization over matched families. This is exactly as existence equals prime-blind positivity, which is the case `w = 0`.

## Paper proof
- **Weak duality:** on a `w`-matched family the energy is `Σα A(f_i) − t L_w(lam) ≥ 0`.
- **Strong duality:** the PBAP argument with one extra coordinate for `L_w − β`.
  - Compactness gives a finite set of excluding tests.
  - Hahn–Banach separation gives `α ≥ 0` on the tests and `α₀ ≥ 0` on the constraint.
  - The worst box corner gives `Σα A + 2πΣ(log n + C₀)|C'_n| < α₀β`, where `C'_n = Σα atomCoeff − α₀w(n)/(2π)`.
  - Two-point resonators cancel `C'_n` at most at the corner cost.
  - The resulting family is `w`-matched with multiplier `α₀` and energy `< α₀β`, which contradicts the dual bound.

## Lean
- Module `WeilPositivityLinearDuality`: `linearWeightSum`, `WeilDualBound`, `mul_linearWeightSum_le_of_weilPositiveUpTo`, `exists_weilPositiveUpTo_ge_of_weilDualBound`, `weilDualBound_of_weilPositiveUpTo`.
- Audit:
  - compiles cleanly with `lake env lean`;
  - standard axioms;
  - wired after `WeilPositivityPrimeBlindDuality`;
  - collision scan clean.

## Open / next
- **Pass to all levels.** Combine with `exists_weilPositive_iff_forall_level` (Tychonoff) to get `sup_W L_w = lim_A inf {matched energy}`.
- **Harmonic constant.** Use `w(n) = n^{−½}·1_{n≤N}` (harmonic sums) to express `sup_W c_lam` archimedeanly. `T ≥ 0` then becomes a lower bound on matched archimedean energies, the uniqueness-side twin of prime-blind positivity.

## Log
- 2026-10-01: created and formalized (cycle 186).
- 2026-10-01 (cycle 187): all-levels duality and the single-weight form, formal.
  - `exists_weilPositive_ge_iff_forall_weilDualBound`: (∃ Weil-positive `lam` with `L_w(lam) ≥ β`) ⟺ the dual bound holds at every level seeing `supp w`. Proof: Tychonoff as in `exists_weilPositive_iff_forall_level`; the constraint `L_w ≥ β` involves finitely many coordinates and passes to the limit.
  - `exists_weilPositive_weight_ge_iff`: the range of one weight `lam(n₀)` over the cone is governed by single-atom test families. Their atom coefficients vanish off `n₀`, and their archimedean energy per atom is what matters.
  - Standard axioms; compiles cleanly.
  - **Reading:** uniqueness of the weight `n₀` over `W` (`sup = inf`) is the statement that single-atom families at `n₀` reach energy ratios arbitrarily close to both extremes. This is a Fourier-interpolation property of `{log n}` against the archimedean symbol.
