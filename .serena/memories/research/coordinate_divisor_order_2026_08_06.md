# Orders along the coordinate divisors (2026-08-06)

Card: `stable-coframe-log-calabi-yau-rigidity` (stage 2).  Module **27**.
Continues [[research/tame_monomial_eigenvolume_toric_model_2026_08_06]].

## `CoordinateDivisorOrder.lean`

Over a field `k`, with `σ` a Fintype:

- `isPrime_span_X`, `height_span_X` — `span {X i}` is a height-one prime.
- `coordDivisor i : PrimeDivisor (MvPolynomial σ k)` (**must be `noncomputable`**).
- `irreducible_algebraMap_X` — `X i` is a **uniformizer** of `Localization.AtPrime (span {X i})`.
- `orderAt_coordDivisor_X_self` = 1, `orderAt_coordDivisor_X_of_ne` = 0.
- `orderAt_prod`, `orderAt_pow` — additivity of `orderAt` (general, reusable).
- **`orderAt_coordDivisor_prod_X` = 1** — the logarithmic volume form has a simple pole along each
  coordinate divisor, so `c = −1` there.
- **`orderAt_coordDivisor_det_jacobian` = `e i − 1`** — this is the horizon theorem's `hjac`
  hypothesis, discharged in the toric model.

## mathlib assets used

`MvPolynomial.X_prime` (in `Mathlib/Algebra/MvPolynomial/Division.lean` — **needs an explicit
import**, it is not transitively available),
`Ideal.height_span_singleton_eq_one_of_mem_nonZeroDivisors`,
`IsDiscreteValuationRing.irreducible_iff_uniformizer`,
`IsLocalization.AtPrime.map_eq_maximalIdeal`,
`IsDiscreteValuationRing.addVal_uniformizer`.

## Lean traps

- Rewriting `(coordDivisor i).1 = span {X i}` inside `Localization.AtPrime (coordDivisor i).1`
  gives **"motive is not type correct"** (the `IsPrime` instance depends on it).  Fix: never `rw`
  the subtype projection; use `show Ideal.map … (Ideal.span {X i}) = _` and let defeq do it.
- To prove `X i ∤ X j` for `i ≠ j`, apply `map_dvd` under
  `eval (fun l => if l = i then 0 else 1)` and land in `(0 : k) ∣ 1`.  Cheap and avoids monomial
  combinatorics.

## Remaining for Theorem A

1. Different exponent `e − 1` for a **general** tame extension (the toric/Eisenstein cases are done).
2. Sheaf of differentials on a scheme.
3. Step 4's `e > 1`: `N¹` + int-amplification.
4. Corollary B: MMP.
