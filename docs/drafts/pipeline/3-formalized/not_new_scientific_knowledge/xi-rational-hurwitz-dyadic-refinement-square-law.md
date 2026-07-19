# Xi rational-Hurwitz dyadic refinement square law

- **ID:** `xi-rational-hurwitz-dyadic-refinement-square-law`
- **Stage:** 3-formalized
- **Type:** finite value relation / top-down RH bridge
- **Status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Lean status:** formalized in
  `formal/GaloisForLFunctions/RHTower/XiRationalHurwitzDyadicRefinement.lean`

## Normalized finite-fibre energy

For an integer `n` and `rho in C`, put

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

At the degenerate scales `n=0,1`, both sides of `(1)` are zero under the existing Lean
definitions.  The closed formula is therefore total in `n`; the hypothesis `n>1` is needed only
when its zero set or equality at distinct scales is used to recover `x=0`.

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

Before restricting to powers, the finite response has a multiplicative law.  For natural
integers `m,n` and `Re(s)>0`,

```text
rationalHurwitzFiberResponse (m*n) s =
  rationalHurwitzFiberResponse m s * rationalHurwitzFiberResponse n s.   (M1)
```

Remove the logarithmic prefactor from the reflected seam and write

```text
D_n(rho) = A_n(rho)^(-1) - B_n(rho)^(-1),
A_n(rho) = rationalHurwitzFiberResponse n (conj(rho)),
B_n(rho) = rationalHurwitzFiberResponse n (1-rho).
```

Then `(M1)` and `xy-uv=(x-u)y+u(y-v)` give the crossed-cocycle law

```text
D_(m*n)(rho) =
  D_m(rho) * A_n(rho)^(-1) + B_m(rho)^(-1) * D_n(rho).   (M2)
```

Thus the reflected finite-value defect is a derivation twisted by the two response characters.
Iterating `(M2)` at a fixed modulus gives the all-power geometric factor below.  This is an
elementary multiplicative-character identity, so no standalone scientific novelty is claimed;
its project value is that it replaces isolated modulus comparisons by one exact semigroup law.

There is a second, power-direction value law.  With

```text
U=A_n(rho)^(-1),  V=B_n(rho)^(-1),
D_k(rho)=D_(n^k)(rho),
```

the response power law gives

```text
D_k(rho) = U^k-V^k,                                      (M3)
D_(k+2)(rho) = (U+V)*D_(k+1)(rho)-U*V*D_k(rho).          (M4)
```

Thus the complete reduced reflection-value ray is the two-root Lucas/sine recurrence with trace
`U+V` and determinant `U*V`.  The `HTGeometry.unitarySineRecurrence` law is exactly the special
case `U*V=1`; `(M4)` records the determinant weight required by the rational-Hurwitz response.
The full seam is recovered by `C_(n^k)=k*log(n)*D_k`, so this recurrence and the geometric
factorization `(7a)` are two exact presentations of the same value hierarchy.

More generally, for every natural `k`, the finite response has the exact power law

```text
rationalHurwitzFiberResponse (n^k) s =
  rationalHurwitzFiberResponse n s ^ k,                  (4a)
H_(n^k)(rho) = sinh(k*x*log(n))^2.                       (4b)
```

Indeed, the first identity is the Hurwitz multiplication response `n^s` together with
`(n^k)^s = (n^s)^k` on the positive real ray; the second follows from `(1)` and
`log(n^k) = k log(n)`.  Thus all integral power refinements are controlled by the single
horizontal coordinate `x`.

The entire power ray also obeys one second-order polynomial law.  Put `E_k=H_(n^k)(rho)`.  Then,
for every natural `k`,

```text
E_(k+2) + E_k = 2*(1+2*E_1)*E_(k+1) + 2*E_1.             (4c)
```

To prove `(4c)`, set `u=x*log(n)` and `a=(k+1)u`.  The addition and subtraction formulas give

```text
sinh(a+u)^2 + sinh(a-u)^2
  = 2*sinh(a)^2*cosh(u)^2 + 2*cosh(a)^2*sinh(u)^2.
```

Substituting `cosh(v)^2=1+sinh(v)^2` twice gives `(4c)`.  This recurrence is total at `n=0,1`
and `k=0`; no positivity or nondegeneracy hypothesis is used.  It subsumes the dyadic square law,
which is its `k=0` case because `E_0=0`.

There is also an exact cross-folder closure with the denominator-free inverse-pair recurrence
`unitaryCosineRecurrence` already formalized in `HTGeometry.TwoProjectionQuantumWalk`.  If
`C_0(X)=2`, `C_1(X)=X`, and `C_(k+2)(X)=X*C_(k+1)(X)-C_k(X)`, then

```text
C_k(2+4*H_n(rho)) = 2+4*H_(n^k)(rho).                   (4d)
```

For `k=0`, both sides are `2`; for `k=1`, the statement is tautological.  The two-step induction
follows by inserting `(4c)` into the defining recurrence for `C`.  Equivalently,
`2+4*sinh(k*u)^2=2*cosh(2*k*u)` is the symmetric power signal of the positive reciprocal pair
`exp(2*u), exp(-2*u)`.  Thus the abstract HTGeometry Laurent-phase hierarchy and the concrete
rational-Hurwitz power hierarchy are the same polynomial law after the affine energy coordinate
`X=2+4*H_n`.

## All-power linearization defect

The dyadic positive square is the first member of a uniform inequality.  For every natural `k`,

```text
H_(n^k)(rho) >= k^2 * H_n(rho).                          (4e)
```

Indeed, for `u>=0`, induction with the hyperbolic addition formula and `cosh(u)>=1` gives

```text
k*sinh(u) <= sinh(k*u).
```

Replacing `u` by `|x*log(n)|` and squaring proves `(4e)`.  If `u>0` and `k>1`, the inequality is
strict: in the last addition step, `sinh((k-1)u)>0` and `cosh(u)>1`.  Consequently, for `n>1` and
`k>1`,

```text
H_(n^k)(rho) = k^2 * H_n(rho)
  iff Re(rho)=1/2.                                       (4f)
```

Both restrictions in `(4f)` are sharp.  At `n=0,1`, every normalized energy is zero; at `k=0,1`,
the linearized power law is tautological.  The inequality `(4e)` itself is total and uses neither
restriction.

The same lower bound gives a source-friendly one-ray criterion.  Define

```text
PowerEnergyBounded(n,rho) := exists B, forall k, H_(n^k)(rho) <= B.
```

For every `n>1`,

```text
PowerEnergyBounded(n,rho)  iff  Re(rho)=1/2.              (4g)
```

The reverse implication is immediate because every energy is zero on the critical line.  For the
forward implication, if `H_n(rho)>0`, choose a natural `k` so large that
`B<k^2*H_n(rho)`; this is possible by the Archimedean property.  Equation `(4e)` then contradicts
the asserted upper bound.  Thus a future unitary, trace, or source estimate need only bound one
complete finite-value power ray; it need not prove exact linear refinement.

The square refinement has substantially more structure.  From `(4b)` at `k=2` and

```text
sinh(2u)^2 = 4*sinh(u)^2*(1+sinh(u)^2)
```

one obtains, for every natural `n`,

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

The equations `(4)`--`(5)` are total.  The condition `n>1` enters only in `(6)`: for `n=0,1`,
the normalized energy vanishes for every `rho`, so linear refinement cannot detect the critical
line.

The underlying finite values also factor before taking norms.  If

```text
A = rationalHurwitzFiberResponse n (conj(rho)),
B = rationalHurwitzFiberResponse n (1-rho),
```

then the distribution law gives the complete power-refinement factorization

```text
C_(n^k)(rho) = k*C_n(rho) *
  sum_(j=0)^(k-1) A^(-j) B^(-(k-1-j)).                  (7a)
```

This is the ordinary difference-of-powers factorization applied to the inverse responses.
At `k=2` it specializes to

```text
rationalHurwitzFiberResponse (n^2) s =
  rationalHurwitzFiberResponse n s ^ 2,

C_(n^2)(rho) = 2*C_n(rho)*(A^(-1)+B^(-1)).                (7)
```

The positive square in `(5)` is therefore an exact finite-value refinement defect, not a limit,
zero-selected construction, or divisor reconstruction.

## Xi capstone

For fixed integers `n>1` and `k>1`, define the all-power finite-fibre linear refinement condition

```text
forall rho in XiDivisorSupport,
  H_(n^k)(rho) = k^2*H_n(rho).                            (8a)
```

Equation `(4f)` makes `(8a)` equivalent to RH.  The dyadic condition is its specialization at
`k=2`: define

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

Likewise, requiring `PowerEnergyBounded(n,rho)` for every `rho` in `XiDivisorSupport` is equivalent
to RH for each fixed `n>1`.  This bounded-ray Prop is therefore exactly interchangeable with
`(8a)`, `(8)`, arbitrary two-scale equality, and orientation-energy vanishing.

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

## Formalized surface

The module defines `normalizedScaleSeamEnergy`,
`normalizedRationalHurwitzReflectionEnergy`, and
`rationalHurwitzFiberInversePowerFactor`.  Its principal declarations are:

- `normalizedScaleSeamEnergy_eq_sinh` and
  `normalizedRationalHurwitzReflectionEnergy_eq_sinh` for `(1)`;
- `normalizedScaleSeamEnergy_lineReflect`, `_conj`, and `_one_sub` for the full reflection orbit;
- `normalizedRationalHurwitzReflectionEnergy_mono` and
  `normalizedRationalHurwitzReflectionEnergy_eq_iff_re_eq_half` for `(2)`--`(3)`;
- `XiRationalHurwitzTwoScaleEnergyEqual` and
  `xiRationalHurwitzTwoScaleEnergyEqual_iff_riemannHypothesis` for the arbitrary-modulus global
  Prop interface;
- `rationalHurwitzFiberResponse_pow`, `rationalHurwitzFiberReflectionSeam_pow`, and
  `normalizedRationalHurwitzReflectionEnergy_pow_eq_sinh` for `(4a)`--`(7a)`;
- `normalizedScaleSeamEnergy_power_recurrence` and its rational-Hurwitz counterpart for the
  all-power polynomial law `(4c)`;
- `unitaryCosineRecurrence_normalizedScaleSeamEnergy` and its rational-Hurwitz counterpart for the
  HTGeometry--RHTower bridge `(4d)`;
- `normalizedScaleSeamEnergy_pow_linear_le`, `_pow_eq_linear_iff`, and their rational-Hurwitz
  forms for `(4e)`--`(4f)`;
- `ScaleSeamPowerEnergyBounded`, `RationalHurwitzPowerEnergyBounded`, and their critical-line
  equivalences for `(4g)`;
- `rationalHurwitzFiberResponse_mul` and
  `rationalHurwitzFiberReducedReflectionSeam_mul` for the multiplicative response and crossed
  cocycle `(M1)`--`(M2)`;
- `rationalHurwitzFiberReducedReflectionSeam_pow` and `_power_recurrence` for the determinant-
  weighted value recurrence `(M3)`--`(M4)`;
- `normalizedScaleSeamEnergy_sq_sub_linear` and its rational-Hurwitz counterpart for `(4)`--`(7)`;
- `xiRationalHurwitzDyadicLinearRefinement_iff_riemannHypothesis` and
  `xiRationalHurwitzDyadicLinearRefinement_two_iff_orientationEnergy_eq_zero` for `(8)`--`(10)`.
- `xiRationalHurwitzPowerLinearRefinement_iff_riemannHypothesis` for the all-power global
  interface `(8a)`.
- `xiRationalHurwitzPowerEnergyBounded_iff_riemannHypothesis` for the bounded one-ray global
  interface.
- `xiRationalHurwitzPowerLinearRefinement_iff_dyadic`, `_iff_twoScaleEnergyEqual`, and
  `_iff_orientationEnergy_eq_zero` discharge the downstream Prop conversions directly.

Targeted module build and the representative `#print axioms` audit pass.  The new declarations
depend only on `[propext, Classical.choice, Quot.sound]`; the scoped proof-debt scan is empty.

## Provider audit

The adjacent finite Ward and graded layers do not currently discharge `(8)`:

- `finiteRankCutoffWardTrace_eq_adjointCurvature_values` is a general packet-evaluation law, but
  its coefficient packet is free data; it does not identify that packet with the rational-Hurwitz
  refinement factor or force the positive remainder to vanish.
- `exists_finiteSoninSemilocalRelativeTrace_ne_vonMangoldt` proves that the canonical finite Sonin
  pairing disagrees with the finite von-Mangoldt source on some compact-support prime-power test.
  Thus the most literal physical Ward provider is already ruled out.
- `no_sigma_graded_refinement` proves that every finite prime atlas has order zero at a strip zero
  while the Xi order is nonzero.  A finite prime grading therefore cannot supply divisor
  multiplicity data that would annihilate the remainder.
- `unitaryCosineRecurrence_soninPrimeDilationSignal` gives the same abstract recurrence for the
  Sonin prime-power dilation tower, and `norm_dilationSum_le_two` bounds every symmetric unitary
  dilation observable by two.  The corpus contains no arithmetic state, intertwiner, or value map
  identifying that bounded operator recurrence with
  `unitaryCosineRecurrence_normalizedRationalHurwitzReflectionEnergy`.  Supplying such an
  identification would already imply the bounded-ray criterion and hence RH, so it cannot be
  inserted as a harmless bridge hypothesis.

The live source obligation is consequently narrower: construct a completed prime--Gamma or Weil
source identity which is not the finite Sonin pairing and which kills the explicit square
`4 * H_n(rho)^2`, or prove a genuine arithmetic bound on one complete finite-value power ray.
Repackaging finite Ward cyclicity, finite prime grading, or the abstract boundedness of the Sonin
unitary recurrence cannot do this without the missing arithmetic intertwiner.

## Gates

- [x] exact normalized finite-fibre energy proved on paper
- [x] arbitrary two-scale rigidity proved on paper
- [x] dyadic refinement positive-square law proved on paper
- [x] all-power response, normalized-energy, and finite-seam refinement laws proved on paper
- [x] all-power second-order polynomial energy recurrence proved on paper
- [x] HTGeometry inverse-pair recurrence splice proved on paper
- [x] all-power nonnegative linearization defect and sharp equality case proved on paper
- [x] bounded one-ray criterion and global RH interface proved on paper
- [x] multiplicative response and reduced-seam crossed-cocycle laws proved on paper
- [x] reduced reflection-value power recurrence proved on paper
- [x] common-charge and RH chains identified
- [x] circularity boundary stated
- [x] Lean formalization
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
