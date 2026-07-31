# CCM first-clock tail lower-bound completeness

- **ID:** `ccm-first-clock-tail-lower-bound-completeness`
- **Stage:** `1-in-progress`
- **Type:** THEOREM / source-side RH completeness
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN PENDING]`
- **Parent:** `ccm-first-clock-landau-completeness-law.md`
- **Exact source:**
  `B₁(L)=ccmPublishedSourceSineCoefficient(L/2,2*pi/L)`

## Exact theorem

Define

```text
CCMFirstClockPublishedSourceEventuallyBoundedBelow : Prop :=
  exists C A : R,
    0 <= C and pi/2 <= A and
    for every L>=A, -C <= B₁(L).
```

Then

```text
CCMFirstClockPublishedSourceEventuallyBoundedBelow
  <-> RiemannHypothesis.                                      (TLB)
```

Equivalently, if RH is false, the literal first published CCM clock is unbounded below on every
tail.  This is strictly weaker input than pointwise first-clock nonnegativity and does not add a
zero-side hypothesis.

## Internal frontier

The corpus already proves, unconditionally,

```text
B₁(L) = (2/L) Re Q(L),                                      (D)
Q(L) = ccmFirstClockXiRationalDivisor(L),
B₁(L)>=0 for every L>=pi/2  <-> RH,                          (FC)
```

and supplies:

1. exponential integrability of `Q` for every abscissa above `1/2`;
2. a normal analytic continuation of its Laplace transform through every positive-axis disk
   `closedBall(r,r/2)`;
3. continuous Landau transfer for a nonnegative density;
4. the first-clock Volterra reflection from all positive moments of `Q` to all positive moments
   of the complete Xi screw;
5. `CCMFirstClockXiAllExponentialMoments -> RH`.

No existing theorem or card proves `(TLB)`.  Existing first-clock completeness consumes the
stronger pointwise sign in order to make `Q` itself a positive Landau density.

## Paper proof

The reverse implication is immediate from `(FC)`: under RH, `B₁(L)>=0` for every physical
aperture, so take `C=0` and `A=pi/2`.

Assume the left side.  Increase `A` if necessary and put `d=C/2`.  From `(D)`, for every `L>=A`,

```text
Re Q(L) = (L/2) B₁(L) >= -d L.                              (1)
```

On the fixed physical tail `I=(pi/2,infinity)`, define the compact correction

```text
H(L) = max(-(Re Q(L)+dL),0)   if L<=A,
       0                       if A<L,
R(L) = Re Q(L)+dL+H(L).                                      (2)
```

Equation `(1)` and the definition of `H` give `R(L)>=0` on `I`.  The function `H` is supported in
`(pi/2,A]`.  It is integrable there because

```text
0 <= H(L) <= |Re Q(L)|+dL,
```

`Q` is locally integrable (use its unconditional exponentially weighted integrability at any
abscissa above `1/2`), and `L` is integrable on a compact interval.  Consequently

```text
H*(s)=integral_I exp(-sL) H(L) dL                            (3)
```

is entire.  Also

```text
P_d(s)=d integral_I exp(-sL)L dL
      =d exp(-a s)(a/s+1/s^2),  a=pi/2,                     (4)
```

is analytic on `Re s>0`.

Let `Q*(s)` denote the corpus continuation of the physical-tail Laplace transform of `Q`, and put

```text
R*(s)=Q*(s)+P_d(s)+H*(s).                                   (5)
```

It is analytic in every positive-axis disk `closedBall(r,R0)` with `R0<r/2`.  For `Re s>1/2`,
absolute convergence and `(2)` show that `(5)` is the ordinary Laplace transform of `R`.

For `b>0`, write `M_b` for the assertion that `Q` has every exponential moment with abscissa
strictly above `b` on `I`.  Corrections `dL` and `H` have every positive exponential moment, so

```text
M_b for Q  <->  M_b for R.                                  (6)
```

Unconditional source estimates give `M_(1/2)`.

We prove the halving step `M_b -> M_(b/2)` for `0<b<=1/2`.  Under `M_b`, the ordinary Laplace
transform of `R` is analytic on `Re s>b`.  On the narrow connected strip

```text
S_b={s : b<Re s and |Im s|<b/4},                            (7)
```

both this transform and `R*` are analytic and agree on the nonempty open part `Re s>1/2`.
The identity theorem therefore identifies them on all of `S_b`.

Fix `a>b/2`, and set

```text
r=a+b/2,  rho=b/2.                                          (8)
```

Center the positive measure

```text
dmu_r(L)=1_I(L) exp(-rL)R(L)dL.                             (9)
```

Its complex MGF near zero is `R*(r-z)` by `(7)`.  Choose `R0` with
`rho<R0<r/2`.  The positive-axis disk continuation of `(5)` makes `z |-> R*(r-z)` analytic on
`closedBall(0,R0)`.  Continuous Landau transfer applied to `(9)` gives

```text
integral_I exp(rho L) exp(-rL) R(L)dL < infinity,
```

which is exactly the `a`-moment of `R`.  By `(6)`, the `a`-moment of `Q` exists.  Since `a>b/2`
was arbitrary, `M_(b/2)` follows.

Iterating at `b_n=2^(-(n+1))` and using `b_n -> 0` proves every positive exponential moment of
`Q`, i.e.

```text
CCMFirstClockXiAllExponentialMoments.                       (10)
```

The existing first-clock moment-completeness theorem sends `(10)` to RH.  This proves `(TLB)`.

Every correction used above is source-independent, compact or affine, and analytic on the open
right half-plane.  No correction is fitted to a zero and none can cancel a positive-real Xi
Laplace singularity.

## Hostile audit

1. **Could a large negative `C` fake the premise?** No.  The definition requires `C>=0`, and any
   ordinary tail lower bound can be enlarged to such a constant.
2. **Does multiplication by `L/2` lose boundedness?** It changes a constant floor for `B₁` into
   the exact affine floor `(1)` for `Q`; the affine Laplace correction `(4)` is analytic for every
   positive abscissa.
3. **Can the compact bad head create a Landau boundary?** No.  Its Laplace transform `(3)` is
   entire.
4. **Is positivity assumed after analytic continuation?** No.  Positivity is used only for the
   real measure `(9)`.  Analytic continuation is inherited from the already proved literal
   first-clock continuation plus `(3)--(4)`.
5. **Does the argument assume a rightmost off-line zero?** No.  It uses the corpus
   all-positive-moments-to-RH theorem, whose proof is branch-free and does not select an extremal
   zero.
6. **Is `(TLB)` merely `(FC)` with a renamed sign?** No.  `B₁` may have arbitrary finite and
   tailwise sign changes under the premise.  Only exclusion of unbounded negative excursions is
   required.

Verdict: `SURVIVES PRELIMINARY ATTACK`; paper proof is dependency-closed.

## External frontier and priority

- Groskin's July 2026 finite Guinand--Weil paper supplies the finite source dictionary and
  archimedean tail order but contains no first-clock, Landau, eventual-sign, or tail-lower-bound
  theorem.
- Classical Landau oscillation theorems supply the parent analytic mechanism: a one-signed
  inverse Mellin/Laplace carrier forces a real boundary singularity.  They do not state the
  literal CCM first-clock criterion `(TLB)`.
- Searches for the normalized CCM first clock together with bounded-below/eventual-Landau
  criteria found no exact or equivalent published statement.

The parent mechanism is classical, so novelty cannot rest on Landau transfer itself.  Potential
new content is the exact weakening of one literal published CCM clock from positivity to absence
of unbounded negative tail excursions, with the affine/compact correction proved harmless through
the complete Xi-screw endpoint.  Keep `[NOVELTY UNVERIFIED]` until exact Lean proof and independent
priority review.

## Lean target

```text
formal/GaloisForLFunctions/RHTower/CCMFirstClockTailLowerBoundCompleteness.lean
```

Required capstones:

```text
ccmFirstClockPublishedSourceEventuallyBoundedBelow_iff_rh
not_ccmFirstClockPublishedSourceEventuallyBoundedBelow_of_not_rh
```

