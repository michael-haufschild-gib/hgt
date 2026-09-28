# Weil positivity pins the residue (regular uniqueness with both poles)

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityResidueRigidity.lean`

## Statements
- `pairing_one`: `2πΣ_{n≥2} n^{−½}φ(log n) = 4π Re(ĥ(i/2) conj ĥ(−i/2)) + ∫|ĥ|²P_1`.
- `vonMangoldt_add_residue_eq_zero`: partial sums `κ(n−1) + E(n)`, `Σ|E|/(n√n) < ∞` ⇒ `w = 0`.
- `vonMangoldt_add_twoPole_eq_zero`: partial sums `κ₁(n−1) + κ₂(√n−1) + E(n)` ⇒ `w = 0`.
- `vonMangoldt_add_even_weilPositive_eq_zero`: `Λ + c·1_{2|n}` ⇒ `c = 0`.

## Proof
1. Euler–Maclaurin in `u = log x` with density `e^u`. The telescoped main term `∫_0^∞ e^{u/2}φ` splits into a polar evaluation (`2cosh`) and an `e^{−u/2}` tail. The tail is handled by Fubini on `(0,∞)`.
2. Polar atoms are invisible to polar-constrained concentration, so `P ≤ 0`. The bump (`+`) and the odd probe (`−`) force the polar atom to vanish.
3. With both atoms: the zero-mean odd and even probes fix the polar atom; L76 then handles the atom at 0.

## Context
This closes the regular part of the uniqueness half (L61–L78). The remaining perturbations are singular at zeros.
