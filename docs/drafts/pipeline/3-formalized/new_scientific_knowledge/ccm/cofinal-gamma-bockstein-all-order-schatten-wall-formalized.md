# Cofinal Gamma Bockstein all-order Schatten wall — formalized

- **ID:** `cofinal-gamma-bockstein-all-order-schatten-wall-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `cofinal-gamma-bockstein-all-order-schatten-wall.md`
- **Type:** FORMALIZATION CERTIFICATE

## Lean modules

```text
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGradedVariableIdealFixedXiComparison.lean
formal/GaloisForLFunctions/RHTower/PrimeFirstTraceGammaCofinalNormalizerFrontier.lean
formal/GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean
```

The activation-Fisher twist and the two-sided density bounds
`primeActivationOccupancyFisherTwist_bounds` come from the first module; the last module carries
the whole card.

## Formal theorem chain

```text
1  primeGammaCofinalBocksteinMagnitude              |Delta_t(p)|
2  primeGammaCofinalBocksteinSchattenMass           |Delta_t(p)|^q
3  primeGammaCofinalBocksteinMagnitude_eq           reflection reduces the grade to |t|
4  primeGammaCofinalBocksteinMagnitude_factor       |Delta_t(p)| = F_|t|(p) (1 - p^(-2|t|))
5  primeGammaCofinalBocksteinMagnitude_bounds       (1/4)(1-2^(-2|t|)) p^(|t|-1) ≤ · ≤ p^(|t|-1)
6  summable_primeGammaCofinalBocksteinSchattenMass_iff            statement (1), for every q > 0
7  all_order_summable_primeGammaCofinalBocksteinSchattenMass_iff  statement (2)
```

Step 6 is proved in both directions against `Nat.Primes.summable_rpow`, the prime-power
convergence criterion, using step 5 as a two-sided comparison; the lower constant is positive
exactly because `t ≠ 0`.  Step 7 instantiates step 6 at the boundary order `q = (1 - |t|)^(-1)`
when `|t| < 1` and at `q = 2` when `|t| ≥ 1`, which are the two regimes named in the paper proof.

## Verification

```text
lake env lean GaloisForLFunctions/RHTower/PrimeGammaCofinalBocksteinSchattenWall.lean  -- clean
lake build GaloisForLFunctions.RHTower                                                 -- success
```

`#print axioms` on all 5 named declarations of the module reports exactly
`[propext, Classical.choice, Quot.sound]`.  No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe`
declaration occurs.  The module is imported by `GaloisForLFunctions.RHTower`.
