# Gamma-sewn Xi-shift tangent innovation law

- **ID:** `gamma-sewn-xi-shift-tangent-innovation`
- **Stage:** `3-formalized/needs-audit`
- **Type:** `[PAPER-PROVED] [LEAN-PROVED] [NOT RH]`
- **Scientific status:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [NOVELTY UNVERIFIED]`
- **Sources:** `GammaSewnSynchronizedEulerFisherBarycenter.lean`,
  `XiShiftPrimeExposure.lean`, `XiShiftAllValuationLayerBarrier.lean`, and
  `XiPhysicalEndpointLocalStiffness.lean`
- **Open consumer:** the centered height-synthesis response identification in CEERT-4H.

## Exact claim

Fix a prime `p`, an aperture `x>0`, and write

```text
q=p^(-x),        r=q^2,
d_e=(1-r)r^e,
b=r^2/(1+r^2).
```

Let `E` have the geometric law `P(E=e)=d_e`, let `B` be an independent Bernoulli variable with
`P(B=1)=b`, and put

```text
N=E+B,       Y=2 log(p) N.
```

Then the following statements hold.

1. `d` and the joint law of `(E,B)` have total mass one.
2. The centered literal Euler--sewing clock is

   ```text
   Y-E[Y]
    =4(EulerHalfHeight_p(E)-M_(2x)(p))
      +2 log(p)(B-b).                                      (TI1)
   ```

3. Its variance is exactly the full Gamma aperture Fisher curvature:

   ```text
   Var(Y)
    =16 V_(2x)(p)+4 log(p)^2 b(1-b)
    =G_x(p).                                               (TI2)
   ```

4. The probability generating function of `N` is

   ```text
   Phi_(x,p)(z)
    =(1-r)(1+r^2 z)/[(1+r^2)(1-rz)].                       (TI3)
   ```

   Hence its rooted response has the exact tangent factor

   ```text
   Phi_(x,p)(z)-1
    =r(1+r)(z-1)/[(1+r^2)(1-rz)].                         (TI4)
   ```

   In particular the zero-frequency mode is removed before any norm or boundary limit is taken.

5. At physical aperture `x=1`, the depth marginal is not an auxiliary law.  For every valuation
   depth `e`, the coefficient exposed by the completed `+2` Xi shift is its CDF:

   ```text
   filteredVonMangoldtCoeff(p^(e+1))
    =log(p) sum_(j=0)^e d_j
    =log(p)(1-p^(-2(e+1))).                               (TI5)
   ```

   Consequently its valuation forward difference is the normalized all-depth innovation:

   ```text
   A_0=log(p)d_0,
   A_(e+1)-A_e=log(p)d_(e+1),                             (TI6)
   ```

   where `A_e=filteredVonMangoldtCoeff(p^(e+1))`.

6. Define the physical height lift

   ```text
   h_p(e)=(1-p^-2)(e+1)/p.                               (TI7)
   ```

   It is a normalized multiple of the literal Euler half-height, and its all-depth expectation
   reconstructs the physical ordinary-prime endpoint amplitude:

   ```text
   sum_e d_e h_p(e)=p^-1.                                (TI8)
   ```

7. The father/tangent split has exact squared mass

   ```text
   sum_e d_e(h_p(e)-p^-1)^2=p^-4<1.                     (TI9)
   ```

   Hence the apparent `p^-2 -> p^-1` resolution gap is confined to the constant mean removed by
   tangent renormalization.  The centered all-depth height carrier already has norm `p^-2`.

8. If `I_(p,e)` is the actual Xi-shift innovation from `(TI6)`, rooted at `I_(p,0)=A_0`, then

   ```text
   sum_e I_(p,e) h_p(e)=log(p)/p.                       (TI10)
   ```

   Thus the physical endpoint coefficient is obtained by an explicit strict, height-localized,
   infinite synthesis of the actual hypertranscendental Xi-shift source.

## Dependency-closed paper proof

The geometric mass sums to one.  The sewing probabilities are `1/(1+r^2)` and
`r^2/(1+r^2)`, so their sum is one and independence gives the joint normalization.

The literal Euler half-height is `(e+1)log(p)/2`; subtracting its geometric mean removes the
constant `+1`, which proves `(TI1)`.  Independence kills the mixed centered term.  The depth
variance is `16 V_(2x)(p)`, while the sewing variance is
`4 log(p)^2 b(1-b)=4 log(p)^2 q^4/(1+q^4)^2`.  The already proved full-aperture identity then gives
`(TI2)`.

The two probability generating functions are `(1-r)/(1-rz)` and
`(1+r^2 z)/(1+r^2)`.  Their product is `(TI3)`.  Subtracting one and clearing the nonzero
denominator gives `(TI4)`.

At `x=1`, `r=p^-2` and

```text
sum_(j=0)^e (1-r)r^j=1-r^(e+1).
```

The von Mangoldt value at `p^(e+1)` is `log(p)`, so the definition of the filtered shift
coefficient gives `(TI5)`.  Subtraction at adjacent depths gives `(TI6)`.

For `(TI7)`--`(TI9)`, the geometric identities

```text
E[E+1]=1/(1-r),       Var(E)=r/(1-r)^2
```

give

```text
E[h_p(E)]=(1-r)/p * 1/(1-r)=1/p,
Var(h_p(E))=((1-r)/p)^2 r/(1-r)^2=r/p^2=p^-4.
```

Since `I_(p,e)=log(p)d_e`, multiplying `(TI8)` by `log(p)` proves `(TI10)`.  Lean derives the
moment statements from the previously formalized infinite Euler-height barycenter and variance;
it does not install the displayed closed forms as definitions.

No sign, convergence, RH, zero-location, or target-response hypothesis occurs in the proof.

## Anti-theatre and novelty audit

- Geometric prime valuations in the zeta distribution, Bernoulli convolution, variance addition,
  probability generating functions, and finite geometric sums are established parent theory.
- The candidate new content is the **forced conjunction**: the exact Gamma multiplier supplies the
  Bernoulli parameter `r^2/(1+r^2)`; its convolution with the doubled-aperture valuation law has
  variance equal to the already constructed Gamma Fisher curvature; the same law has the rooted
  tangent factor `(TI4)`; and at aperture one its depth innovation is exactly the forward
  valuation difference of the hypertranscendental completed Xi-shift source `(TI5)`--`(TI6)`.
- The sharper candidate new content is the father/tangent resolution law `(TI7)`--`(TI10)`: one
  source-forced physical-height synthesis recovers the `p^-1` endpoint mean, while its orthogonal
  centered mass is exactly `p^-4` and therefore stays at the Xi-shift aperture scale.  This is an
  explicit source map, not an RH-equivalent operator-norm premise.
- Exact corpus and external formula searches found no collision for this conjunction.  This is
  search noncollision, not a priority claim.
- The theorem does not identify the finite tangent source response with the completed target
  kernel `K_tan`, prove its cofinal bound, or prove RH.

## Representation consequence, falsified conjecture, and replacement

The boundary masses `F_H=-F/2` and `F_S=3F/2` are Laurent finite parts of the two marginals of one
positive variance `(TI2)`.  They are not two physical Hilbert vectors to be transported and normed
separately.  Such a separation recreates an artificial negative direction.  The legal object is
the centered joint clock at positive aperture; its rooted response already removes the constant
mode by `(TI4)`, before the boundary limit.

**CEERT-4T is falsified in its raw coefficientwise form.**  The physical endpoint spectrum has a
`p^-1` father mode, whereas the Xi-shift innovations start at the doubled-aperture `p^-2` scale.
An equality before centering therefore asks the source to perform the already forbidden exact
resolution lift.  The positive survivor is `(TI7)`--`(TI10)`: synthesize first, split the exact
mean from the centered height carrier, and send only the latter to the tangent response.

**CEERT-4H (height-synthesized tangent refinement).**  Apply the explicit all-depth synthesis
`h_p(e)` to the actual Xi-shift innovations inside each positive-aperture joint depth--sewing law.
The rooted mean coordinate `log(p)/p` is retained and maps to the already proved positive local
stiffness.  The centered height coordinate, whose exact norm is `p^-2`, enters the two-boundary
four-rate Cauchy exterior before Gram compression.  Its connected second compound—not either
signed Laurent marginal separately—is conjectured to intertwine with the completed tangent
response.  The Gamma sewing bit remains joined until response correlation, and the boundary is
taken only afterward.

The first falsifier is now structural: if the finite four-rate second compound of the centered
height lifts cannot reproduce the target three-node tangent response minor while the rooted means
reproduce the local-stiffness marginal, CEERT-4H is retired.  A coefficientwise raw-kernel equality,
a selected depth, or a post-hoc subtraction of `K(0)` does not count.

## Gates

- [x] exact internal frontier and prior no-gos audited
- [x] generic zeta-distribution and convolution parent theory demoted
- [x] dependency-closed paper proof of `(TI1)`--`(TI10)`
- [x] permanent Lean proof
- [x] axiom audit (`propext`, `Classical.choice`, `Quot.sound` only)
- [x] raw coefficientwise CEERT-4T falsified; height-synthesis survivor extracted
- [ ] finite four-rate centered-lift/tangent-minor identification
- [ ] cofinal tangent-response bound / RH
