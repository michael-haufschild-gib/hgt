# Fixed prime-2--prime-3 seam rigidity

- **ID:** `xi-prime-two-three-seam-rigidity`
- **Stage:** 3-formalized
- **Type:** THEOREM / `[TOP-DOWN SOURCE SIMPLIFICATION]`
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT AN RH PROOF]`

## Target

For the canonical orbitwise prime seam charge

```text
C_p(rho) = log(p) * (p^(-conj rho) - p^(-(1-rho))),
```

the first two prime values satisfy, at every complex point off the critical line,

```text
||C_2(rho)|| < ||C_3(rho)||.
```

Hence each of the following conditions on every actual Xi divisor fibre is equivalent to RH:

```text
C_2(rho) = C_3(rho),
||C_2(rho)|| = ||C_3(rho)||,
the fixed ![2,3] orientation Gram is compact,
the fixed ![2,3] compressed Euler sources commute modulo compact operators.
```

The scalar norm equality is the weakest of these interfaces.  It asks for equality of only two
diagonal source energies, not equality of complex phases.

## Positive defect

Define

```text
Delta_23(rho) = ||C_3(rho)||^2 - ||C_2(rho)||^2.
```

Lean proves unconditionally

```text
0 <= Delta_23(rho),
Delta_23(rho) = 0  iff  Re(rho) = 1/2.
```

This is a positive reformulation of the old common-charge obstruction.  A source construction no
longer has to make every prime charge coherent and then control their cofinal common value.  It is
enough to produce one exact diagonal-energy equality for the fixed primes `2` and `3`.

## Mechanism

The exact per-prime hyperbolic formula gives

```text
||C_p(rho)||^2
  = 4 * (log(p)^2 / p)
      * sinh((Re(rho)-1/2) * log(p))^2.
```

For a nonzero horizontal displacement, both factors increase strictly from `p=2` to `p=3`:

```text
log(2)^2 / 2 < log(3)^2 / 3,
sinh(x log(2))^2 < sinh(x log(3))^2.
```

The coefficient comparison is certified from mathlib's rigorous logarithm bounds.  No numerical
oracle, critical-strip hypothesis, Xi zero location, limiting measure, or cofinal prime argument is
used.

## Top-down chains

```text
fixed 2--3 diagonal seam-energy equality on Xi fibres
  -> Delta_23 vanishes on every Xi fibre
  -> every Xi divisor point has real part 1/2
  -> RH.
```

```text
fixed ![2,3] Euler orientation Gram compact on Xi fibres
  -> finite quadratic Calkin faithfulness
  -> C_2 = C_3
  -> RH.
```

```text
fixed ![2,3] compressed seam-weighted and universal Euler sources
commute modulo compact operators on Xi fibres
  -> the fixed orientation Gram is compact
  -> C_2 = C_3
  -> RH.
```

## Lean declarations

File:
`formal/GaloisForLFunctions/RHTower/XiPrimeTwoThreeSeamRigidity.lean`

- `log_two_sq_div_two_lt_log_three_sq_div_three`
- `sinh_sq_mul_log_two_lt_three`
- `norm_sq_orbitwiseNatPrimeSeamCharge_two`
- `norm_sq_orbitwiseNatPrimeSeamCharge_three`
- `norm_orbitwiseNatPrimeSeamCharge_two_lt_three_of_re_ne_half`
- `re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_eq_three`
- `orbitwisePrimeTwoThreeSeamNormGap`
- `orbitwisePrimeTwoThreeSeamNormGap_nonneg`
- `orbitwisePrimeTwoThreeSeamNormGap_eq_zero_iff`
- `re_eq_half_of_orbitwiseNatPrimeSeamCharge_two_three_norm_eq`
- `xiPrimeTwoThreeSeamChargesEqual_iff_riemannHypothesis`
- `xiPrimeTwoThreeSeamNormsEqual_iff_riemannHypothesis`
- `xiPrimeTwoThreeEulerOrientationGramCompact_iff_riemannHypothesis`
- `xiPrimeTwoThreeEulerCompressionEssentiallyCommuting_iff_riemannHypothesis`

## Gates

- [x] exact two-prime value comparison proved
- [x] positive scalar defect and zero set formalized
- [x] Xi divisor and RH capstones formalized
- [x] fixed-packet orientation-Gram interface formalized
- [x] fixed-packet compressed-source interface formalized
- [x] RHTower umbrella and generated index wiring
- [ ] source-side proof of the fixed `2`--`3` diagonal-energy equality
- [ ] RH
