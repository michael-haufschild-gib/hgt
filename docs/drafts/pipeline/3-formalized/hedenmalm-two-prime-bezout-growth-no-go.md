# Hedenmalm two-prime Bézout growth no-go

- **Stage:** `3-formalized`
- **Status:** `[LEAN-PROVED NO-GO + INTERFACE] [NOT RH]`
- **Target:** mass-shifted spectral trace §9.3

## Conjecture and failure

Newest Hedenmalm corpus proves that centered prime-2 and prime-3 window transforms generate the Xi
ideal in the algebra of entire functions. A tempting conjecture is that its Bézout identity reduces
the fixed-mass source estimate to two bounded prime channels.

This fails at the exact missing topology. For `n=2,3`, the centered multiplier `a_n(t)` tends to
zero on the real axis as `t -> +infinity`. Therefore no uniformly bounded coefficient pair
`b_2,b_3` can satisfy

```text
b_2(t) a_2(t) + b_3(t) a_3(t) = 1
```

for every real `t`. Lean proves this directly: if `‖b_j(t)‖<=C`, choose a late `t` where both
`‖a_j(t)‖<1/(4(C+1))`; triangle inequality makes the left side have norm below `1/2`.

## Scientific consequence

The two-prime ideal theorem is algebraic conormal generation, not bounded multiplier synthesis.
Any use in §9.3 must supply a renormalized coefficient topology allowing necessary growth while
still controlling the exact Abel boundary flux. Ordinary bounded Bézout inversion is impossible,
independently of RH. This agrees with the stronger Kronecker recurrence obstruction after common
first-order decay is removed.

## Lean realization

`formal/GaloisForLFunctions/RHTower/Hedenmalm/HedenmalmTwoPrimeBezoutGrowthNoGo.lean`

Principal theorem: `no_uniformly_bounded_real_two_prime_bezout`.
