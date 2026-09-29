# The existence half of Weil positivity is prime-blind archimedean positivity

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityPrimeBlindDuality.lean`

## Statements
- `PrimeBlindPositive A`: for every finite family of polar-constrained `C²` tests `f_i` at levels `≤ A` and weights `α_i ≥ 0` with `Σα_i Re(φ_{f_i}(log n) + φ_{f_i}(−log n)) = 0` for all `n ≥ 2`, the archimedean energy `Σα_i∫|f̂_i|²A(τ/2π)dτ ≥ 0`.
- `primeBlindPositive_of_weilPositiveUpTo`: Weil positivity up to level `A` ⇒ `PrimeBlindPositive A`.
- `exists_weilPositiveUpTo_of_primeBlindPositive`: `PrimeBlindPositive (A+1)` ⇒ some weight system is Weil-positive up to level `A`.
- `exists_weilPositive_iff_primeBlindPositive`: a Weil-positive weight system exists ⟺ `PrimeBlindPositive A` for all `A`.
- Resonator tools:
  - `atomCoeff_twoPointResonator`: the two-point resonator sees exactly the atom `n`.
  - `archEnergy_twoPointResonator_le`: its archimedean energy is `≤ 4π‖g_w‖²(log n + C₀)`.

## Proof
1. Search in the compact box `|lam(n)| ≤ √n(log n + C₀)`. If it is empty, finitely many tests already exclude the box (finite intersection property).
2. Hahn–Banach separation of the compact convex set of energy vectors from the nonnegative orthant gives `α ≥ 0` with negative combined energy on the whole box, in particular at the worst corner.
3. Add one two-point resonator per atom, with sign opposite to the combined atom coefficient and weight `|C_n|/(2‖g_w‖²)`. This cancels all atoms and costs exactly the worst-corner term. The result is a prime-blind family with negative archimedean energy.

## Context
- This is the Minkowski split (L68) made primes-free: existence is a positivity statement about the archimedean symbol and `{log n}`.
- Localization with a margin is excluded under uniqueness (loop L79). Existence must be exact.
