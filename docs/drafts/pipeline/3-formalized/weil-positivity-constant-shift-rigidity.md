# Weil positivity pins the constant shift of the von Mangoldt weights

**Status:** formalized (Lean, unconditional, standard axioms).
**Module:** `formal/GaloisForLFunctions/RHTower/WeilPositivityConstantShiftRigidity.lean`

## Statement
Call real weights `lam` *Weil-positive* if the finite-atom Weil symbol of `ζ` with weights `lam` has nonnegative energy on every polar-constrained `C²` test at every level.

1. `polar_mertens_constant_nonpos_of_weilAtomSymbol_nonneg`: if `Σ_{2≤n≤x}(lam(n)−Λ(n))n^{−½} = 2κ√x + A log x + B + o(1)` and `lam` is Weil-positive, then `B ≤ 0`.
2. `vonMangoldt_sub_const_not_weilPositive`: `Λ − c` is not Weil-positive for any `c > 0`.
3. `eq_zero_of_vonMangoldt_add_const_weilPositive`: `Λ + c` Weil-positive ⇒ `c = 0`.

## Proof
- Tests: the spread radical tests `f_{log S, S}` from `WeilPositivityMertensConstantObstruction`. Their zero side is `O(S^{10}e^{−S})` unconditionally, their mass is `≥ cS`, and their transform vanishes at `0` and `±i/2`.
- Abel summation (`integral_weilAtomSymbol_eq_mertens`) splits the energy into three parts:
  - the constant `−4πB‖f‖²`;
  - the √t-slope integral `2κ∫(φ∘log)'√t = −2κφ(0) − κ∫₀^L φe^{u/2}`;
  - a remainder.
- The polar constraint gives `∫₀^L φ(u) cosh(u/2) du = 0`, so the slope term is `κ(∫φe^{−u/2} − 2φ(0)) = O(|κ| sup|φ'|)`.
- `ζ(½) ≤ −1` via the decreasing defect `Σ_{n≤N} n^{−½} − 2√N`, using AM–GM `2√n√(n+1) ≤ 2n+1`.

## Novelty and significance
- New relative to the corpus: it extends `mertens_constant_nonpos_of_weilAtomSymbol_nonneg` (log slope only) to deviations with a pole at `s = 1`. It also closes the downward direction that L61's density ceiling cannot see.
- No literature treats the set of prime weights compatible with Weil positivity.
- The result is a sharpness law: `Λ` is two-sided extreme along constants, unconditionally.
