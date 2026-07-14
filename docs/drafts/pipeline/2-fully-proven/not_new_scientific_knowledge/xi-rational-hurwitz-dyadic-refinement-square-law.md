# Xi rational-Hurwitz dyadic refinement square law

- **ID:** `xi-rational-hurwitz-dyadic-refinement-square-law`
- **Stage:** 2-fully-proven
- **Type:** finite value relation / top-down RH bridge
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** paper theorem; the ingredients are formalized, but this composition is not

## Normalized finite-fibre energy

For an integer `n > 1` and `rho in C`, put

```text
C_n(rho) = log(n) * (n^(-conj(rho)) - n^(-(1-rho)))
H_n(rho) = n * ||C_n(rho)||^2 / (4*log(n)^2).
```

The existing finite rational-Hurwitz fibre response satisfies

```text
rationalHurwitzFiberResponse n s = n^s
```

when `0 < Re(s)`.  Hence, throughout the open critical strip, `C_n(rho)` is exactly
`rationalHurwitzFiberReflectionSeam n rho`: it is a finite packet of absolutely convergent
Hurwitz-zeta values at rational arguments, divided by an absolutely convergent nonzero zeta
value.

Writing

```text
x = Re(rho) - 1/2,
```

one has the exact height-free identity

```text
H_n(rho) = sinh(x*log(n))^2.                               (1)
```

## Proof of the normalized identity

Write `rho = sigma + I*t`.  The two reflected powers have the common phase
`exp(I*t*log(n))`, so

```text
n^(-conj(rho)) - n^(-(1-rho))
  = exp(I*t*log(n)) * n^(-1/2)
      * (exp(-x*log(n)) - exp(x*log(n))).
```

Taking squared norms gives

```text
||n^(-conj(rho)) - n^(-(1-rho))||^2
  = 4*n^(-1)*sinh(x*log(n))^2.
```

Multiplication by `n/4` proves `(1)` after cancelling the nonzero `log(n)^2`.

## Arbitrary two-scale rigidity

For integer moduli `1 < m < n`, equation `(1)` gives

```text
H_m(rho) <= H_n(rho),                                     (2)
H_m(rho) = H_n(rho)  iff  Re(rho)=1/2.                    (3)
```

Indeed, if `x != 0`, then

```text
0 < |x|*log(m) < |x|*log(n),
```

and `u |-> sinh(u)^2` is strictly increasing on the positive half-line.  If `x=0`, both energies
vanish.  Thus any two distinct finite rational-Hurwitz moduli may replace the special raw
prime-`2`--prime-`3` comparison already formalized in the corpus, after the canonical amplitude
normalization.

## Dyadic refinement square

The square refinement has substantially more structure.  From `(1)` and

```text
sinh(2u)^2 = 4*sinh(u)^2*(1+sinh(u)^2)
```

one obtains, for every `n > 1`,

```text
H_(n^2)(rho) = 4*H_n(rho)*(1+H_n(rho)),                   (4)
H_(n^2)(rho) - 4*H_n(rho) = 4*H_n(rho)^2 >= 0.            (5)
```

Consequently,

```text
H_(n^2)(rho) = 4*H_n(rho)
  iff H_n(rho)=0
  iff C_n(rho)=0
  iff Re(rho)=1/2.                                        (6)
```

This is a positive reformulation of common-charge vanishing.  The horizontal orientation is the
nonlinear positive-square remainder in the otherwise linear refinement from modulus `n` to
modulus `n^2`.

The underlying finite values also factor before taking norms.  If

```text
A = rationalHurwitzFiberResponse n (conj(rho)),
B = rationalHurwitzFiberResponse n (1-rho),
```

then the distribution law gives

```text
rationalHurwitzFiberResponse (n^2) s =
  rationalHurwitzFiberResponse n s ^ 2,

C_(n^2)(rho) = 2*C_n(rho)*(A^(-1)+B^(-1)).                (7)
```

The positive square in `(5)` is therefore an exact finite-value refinement defect, not a limit,
zero-selected construction, or divisor reconstruction.

## Xi capstone

For a fixed integer `n > 1`, define the finite-fibre linear refinement condition

```text
forall rho in XiDivisorSupport,
  H_(n^2)(rho) = 4*H_n(rho).                              (8)
```

Then `(6)` proves

```text
(8)
  -> every Xi divisor point has real part 1/2
  -> RH.                                                   (9)
```

Conversely RH makes every `H_n(rho)` zero, so `(8)` is exact.  At `n=2`, the chain splices
directly into the already formalized common first-prime seam:

```text
linear modulus-2-to-4 Hurwitz refinement on every Xi fibre
  -> H_2(rho)=0
  -> orbitwiseFirstPrimeSeamCharge(rho)=0
  -> xiHurwitzOrientationEnergy=0
  -> RH.                                                   (10)
```

## What changed in the proof obligation

The old interface asks the modulus-two reflected packet to vanish.  The new interface permits a
comparison of two nonzero finite packets and asks that the exact modulus-four refinement retain
only its linear part.  The discarded nonlinear remainder is already proved to be a positive
square and is faithful to horizontal orientation.

This does not prove the linear refinement `(8)`.  An admissible provider must derive it from a
source constraint on the finite rational-Hurwitz packets without assuming reflected-value
equality, critical-line zero locations, source-core positivity, or an RH-equivalent limiting
measure.  The most concrete remaining question is whether an existing finite coefficient, Ward,
or graded-trace identity annihilates the nonlinear remainder in `(7)`.

## Formalization target

1. Define `normalizedRationalHurwitzReflectionEnergy n rho`.
2. Prove `(1)` by reusing `orbitwiseNatPrimeSeamCharge_weighted_norm_sq_eq_sinh` and
   `rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge`.
3. Prove arbitrary two-scale monotonicity `(2)`--`(3)`.
4. Prove the dyadic refinement identities `(4)`--`(7)`.
5. Package the Xi condition `(8)` and the chain `(10)`.
6. Import the module from `RHTower.lean` after targeted verification is permitted.

## Gates

- [x] exact normalized finite-fibre energy proved on paper
- [x] arbitrary two-scale rigidity proved on paper
- [x] dyadic refinement positive-square law proved on paper
- [x] common-charge and RH chains identified
- [x] circularity boundary stated
- [ ] Lean formalization
- [ ] independent source proof of the linear refinement
- [ ] RH

## Literature calibration

The finite rational-fibre input is the classical Hurwitz-zeta multiplication formula; see NIST
DLMF [25.11.15](https://dlmf.nist.gov/25.11.E15), which traces the identity to the defining
Dirichlet series and standard references including Apostol.  The hyperbolic duplication and strict
monotonicity used after that formula are elementary.  No scientific novelty is claimed for the
abstract identity.  Its project contribution is the exact splice to the already formalized
Xi--Hurwitz common-charge and orientation-energy chain, and the isolation of the nonlinear
refinement remainder as the source defect that a future constraint must annihilate.
