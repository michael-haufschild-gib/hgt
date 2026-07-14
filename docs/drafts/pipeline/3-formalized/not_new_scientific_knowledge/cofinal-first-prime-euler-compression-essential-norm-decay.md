# Cofinal charge-scale Euler commutator decay suffices for RH

- **ID:** `cofinal-first-prime-euler-compression-essential-norm-decay`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[TOP-DOWN GAP SIMPLIFICATION]`, `[QUANTITATIVE VALUE INTERFACE]`
- **Scientific status:** `[PROVED] [BRIDGE] [NOT AN RH PROOF]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/XiPrimeSeamCofinalAnchoredEssentialNormDecay.lean`
- **Parent:** `cofinal-first-prime-euler-compression-essential-commutation.md`
- **Statement:** On each Xi divisor fibre it is enough that the charge-scale essential norm of
  the anchored two-prime compressed Euler commutator become arbitrarily small along arbitrarily
  large partner primes.

## Quantitative coefficient recovery

Fix a positive Sonin aperture `a`, an open-strip point `rho`, and a prime `q>2`. Write

```text
u_2 = orbitwiseNatPrimeSeamCharge 2 rho,
u_q = orbitwiseNatPrimeSeamCharge q rho,
C_q = firstPrimeAnchoredEulerCompressionCommutator a rho q.
```

The finite prime shell theorem, positive-Euler rescaling, and unitary invariance of Calkin
distance give the unconditional estimate

```text
|u_2-u_q| / sqrt(2q) <= essentialNorm(C_q),               (1)
```

or equivalently

```text
|u_2-u_q| <= sqrt(2q) essentialNorm(C_q).                 (2)
```

Lean proves `(1)` for every finite injective prime packet as

```text
norm_orientationDifference_div_sqrt_le_essentialNorm
```

and proves the anchored form `(2)` as

```text
norm_primeSeamDifference_le_scaledEssentialNorm_anchoredCommutator.
```

This is stronger than the prior compact/noncompact dichotomy: it recovers the actual orientation
coefficient quantitatively from distance to the compact operators.

The estimate also has a positive off-line converse. If `Re rho != 1/2`, then for every sufficiently
large prime `q`,

```text
|u_2|/2 < sqrt(2q) essentialNorm(C_q).                    (2a)
```

This is formalized as

```text
eventually_half_norm_firstPrimeSeamCharge_lt_scaledEssentialNorm_of_re_ne_half.
```

Thus automatic `1/sqrt(2q)` attenuation of the positive-Euler corners cannot fake the required
decay: an off-line horizontal orientation leaves a uniform positive charge-scale Calkin floor.

## Absolute-convergence value relation

For `0 < Re rho < 1`, the exact rational-Hurwitz fibre formula converts `(2)` into

```text
|rationalHurwitzFiberReflectionSeam 2 rho
  - rationalHurwitzFiberReflectionSeam q rho|
    <= sqrt(2q) essentialNorm(C_q).                        (3)
```

All Hurwitz values in `(3)` are evaluated after finite rational distribution and reflection have
moved them into the half-plane of absolute convergence. Lean proves `(3)` as

```text
norm_rationalHurwitzFiberReflectionSeamDifference_le_scaledEssentialNorm.
```

Thus an approximate Calkin relation supplies an approximate finite value relation; exact
compactness is not required.

## Cofinal collapse

Define

```text
XiCofinalFirstPrimeEulerCompressionEssentialNormDecay a
```

to mean that for every Xi divisor point `rho`, every `epsilon>0`, and every threshold `N`, there
is a prime `q>max(N,2)` such that

```text
sqrt(2q) essentialNorm(C_q) < epsilon.                    (4)
```

The open-strip prime-seam formula independently gives `u_q -> 0` as `q -> infinity`. Given a
nonzero `u_2`, choose `epsilon=|u_2|/2`, use `(4)` and `(2)` to make `u_q` simultaneously within
`|u_2|/2` of both `u_2` and zero, and contradict the triangle inequality. Hence `u_2=0` on every
Xi divisor fibre, and the first-prime seam criterion closes RH.

Lean proves

```text
XiCofinalFirstPrimeEulerCompressionEssentialNormDecay a
  <-> RiemannHypothesis                                     (5)
```

for every `a>0`. It also proves directly that cofinally many exactly compact anchored
commutators imply `(4)`. Thus each required compactness event is relaxed to a quantitative
approximation event. Globally on the actual Xi divisor both conditions are equivalent to RH, so
no claim of logical strictness is made for the resulting global propositions.

## Subsequent norm-equivalence verdict

The initially exposed target was

```text
[TARGET] For every actual Xi divisor rho and every epsilon>0,
         find arbitrarily large primes q for which
         sqrt(2q) essentialNorm(C_q) < epsilon.            (6)
```

The successor theorem
`XiPrimeSeamAnchoredCommutatorNormComparison.lean` now proves the two-sided estimate

```text
|u_2-u_q| <= sqrt(2q) essentialNorm(C_q) <= 2 |u_2-u_q|.  (7)
```

Thus `(6)` is uniformly equivalent to cofinal vanishing of the raw value defect `|u_2-u_q|`.
Because `u_q -> 0` is already unconditional in the open strip, `(6)` contains precisely the
missing assertion `u_2=0`.  It is therefore retained as a faithful quantitative RH coordinate,
not as an independently simpler source problem.  The factor `sqrt(2q)` is forced by the literal
positive-Euler normalization; dropping it would only measure the automatic
`1/sqrt(2q)` attenuation of a fixed nonzero orientation coefficient.

The literature supplies nearby operator geometry but not new information beyond `(7)`.
Connes--Consani's finite
prime--archimedean products are quasi-inner and define semilocal Sonin kernels, while Burnol's
Sonine spaces carry complete/minimal systems of zeta-zero evaluators. Neither source proves a
source-side vanishing theorem for the anchored value defect. Any useful continuation must add a
new source relation coupling the finite values; estimating the same two-corner commutator cannot
do so by itself.

## Gates

- [x] prove the exact positive-Euler rescaling of an off-diagonal orientation coefficient
- [x] lift the finite shell lower bound to essential norm on the concrete source line
- [x] prove the anchored `sqrt(2q)` commutator estimate
- [x] prove the positive eventual off-line charge-scale Calkin floor
- [x] prove the absolutely convergent rational-Hurwitz value form
- [x] prove cofinal charge-scale essential-norm decay kills the first-prime seam
- [x] prove the global cofinal decay condition iff RH
- [x] prove exact cofinal compactness implies cofinal charge-scale decay
- [x] import the module through the `RHTower` umbrella
- [x] classify `(6)` as uniformly equivalent to the raw seam value defect
- [ ] introduce an independent source relation that forces that value defect to vanish
