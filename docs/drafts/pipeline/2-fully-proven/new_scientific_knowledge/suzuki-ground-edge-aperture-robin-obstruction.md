# Suzuki ground-edge small-aperture exclusion and Robin compression

- **ID:** `suzuki-ground-edge-aperture-robin-obstruction`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / FRONTIER RELOCATION / NEW CONJECTURE
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parent:** `../../1-in-progress/suzuki-negative-stieltjes-central-flux-colligation.md`
- **Source:** Suzuki's exact screw profile and restricted-Weil convolution operator

## Frontier before this theorem

The representation-free asymmetric selector reduces Suzuki's necessary central Herglotz sign to
one ground-edge quotient.  For aperture `a`, a simple even ground mode `phi_a`, and

```text
c_Xi=Re(XiC''(0)/XiC(0))<0,
```

resolvent pole dominance gives

```text
r_a=<phi_a,g(a-x)>/<phi_a,1>.                            (1)
```

The unresolved source target was `r_a<c_Xi`.  Suzuki proves a positive simple even ground only for
sufficiently small aperture, so that chamber was the only published range where `(1)` was a
literal positive weighted average.  The following theorem shows that chamber has the wrong sign.

## Theorem A: small-aperture ground-edge exclusion `[PROVED]`

Let `g:R->R` be continuous at zero with `g(0)=0`, and let `c<0`.  There is `a_0>0` such that, for
every `0<a<=a_0`,

```text
g(a-x)>c/2>c             for every x in [-a,a].         (2)
```

Consequently every nonzero nonnegative integrable weight `phi` on `[-a,a]` satisfies

```text
<phi,g(a-x)>/<phi,1> > c.                               (3)
```

Taking `c=c_Xi` proves that no sufficiently small positive ground state can satisfy the central
selector `(1)`.  This strengthens the earlier dyadic far-negative obstruction: failure now holds
at the opposite ground edge as well.

### Proof

Continuity at zero and `c/2<0=g(0)` give `delta>0` such that

```text
|t|<delta -> g(t)>c/2.                                  (4)
```

Choose `a_0=delta/4`.  If `x in [-a,a]` and `a<=a_0`, then

```text
0<=a-x<=2a<=delta/2<delta,
```

which proves `(2)`.  Multiplying by `phi>=0`, integrating, and using `<phi,1>>0` gives

```text
<phi,g(a-x)> >= (c/2)<phi,1> > c<phi,1>.
```

Division by the positive mass proves `(3)`.

## Sharp positive-weight feasibility boundary

For an even nonnegative weight, symmetry sharpens the pointwise obstruction.  Put

```text
s_a(x)=[g(a-x)+g(a+x)]/2,               0<=x<=a.        (5)
```

Then

```text
<phi,g(a-x)>/<phi,1>
 = integral_0^a phi(x)s_a(x)dx / integral_0^a phi(x)dx. (6)
```

Therefore a necessary condition for a positive-even selector is

```text
min_(0<=x<=a) s_a(x)<c_Xi.                              (7)
```

It is also the exact profile-only feasibility condition: if `(7)` holds, continuity permits a
positive even test weight concentrated near a strict sublevel point whose average is below
`c_Xi`.  What remains nontrivial is whether the actual restricted-Weil ground mode puts enough
mass there.

For the probability weight induced by a positive ground, define

```text
D_a=integral (c_Xi-g(a-x))_+ dmu_a,
E_a=integral (g(a-x)-c_Xi)_+ dmu_a.                     (8)
```

The exact classification is

```text
r_a<c_Xi  iff  D_a>E_a.                                 (9)
```

Thus existence of one sublevel point is necessary but not sufficient for the actual ground; the
source theorem is the strict deficit-mass dominance `(9)`.

## Theorem B: even ground average is a Robin boundary ratio `[PROVED]`

Positivity preservation cannot be extended to the required aperture range: the corpus already
proves that the exact restricted-Weil form has forbidden positive cross-couplings beyond an
explicit finite threshold.  The viable formulation must therefore allow a signed even mode.

Let `phi` be an even real eigenmode of Suzuki's convolution operator on `(-a,a)`:

```text
(A_a phi)(x)=integral_(-a)^a -g''(x-y)phi(y)dy=lambda phi(x). (10)
```

Define screw convolution

```text
U(x)=integral_(-a)^a g(x-y)phi(y)dy.                    (11)
```

Under the operator-domain trace regularity supplied by `(10)`, `U` is even and

```text
-U''=lambda phi.                                        (12)
```

Integrating `(12)` and using `U'(-a)=-U'(a)` gives exact flux law

```text
-2U'(a)=lambda M,       M=integral_(-a)^a phi.          (13)
```

Also `U(a)=<phi,g(a-x)>`.  Hence, when `lambda M!=0`,

```text
r_a=U(a)/M=-lambda U(a)/(2U'(a)).                       (14)
```

After orienting the eigenmode so `M>0`, threshold crossing is exactly

```text
-lambda U(a)/(2U'(a))<c_Xi
  iff U(a)<c_Xi M.                                      (15)
```

Equation `(14)` compresses the full ground integral to one boundary Robin datum.  It also removes
the unnecessary positivity hypothesis from the selector.  If `M=0`, denominator's ground pole
cancels and next noncancelled even mode must replace ground mode; this is a falsifier, not a
technical exception.

## New conjecture: `SUZUKI-ROBIN-CROSSING`

`[CONJECTURE]` There exists a non-small aperture `a`, a simple even lowest eigenmode `phi_a` with
`lambda_a!=0` and oriented mass `M_a>0`, such that screw convolution `U_a` satisfies

```text
U_a(a)<c_Xi M_a.                                        (16)
```

Equivalently, its ground-edge Robin ratio in `(14)` is below `c_Xi`.  This conjecture is
source-pure: it involves only Suzuki's explicit prime--Gamma `g`, its restricted convolution
operator, and one boundary trace.  It contains no Xi-zero location or RH premise.

### Scientific-method attack plan

1. Locate first aperture where symmetric profile sublevel condition `(7)` becomes true by exact
   prime--Gamma inequalities, not decimal evaluation.
2. Continue lowest even eigenline through that aperture using parity-separated min--max or square
   Evans determinant; positivity-improving theory is forbidden there.
3. Differentiate or compare boundary Robin datum `(14)` along aperture spectral flow.
4. Prove strict deficit dominance `(9)`, equivalently boundary inequality `(16)`.
5. Use existing asymmetric selector to obtain central-valid shift pairs.
6. Prove full normalized jump Pick kernel; central sign alone is only necessary.

### Hostile falsifiers

- `min s_a>=c_Xi` for every aperture with a simple even lowest mode kills positive-weight form.
- `M_a=0` cancels ground pole and forces mode-switching analysis.
- an odd or multiple lowest eigenspace invalidates one-mode pole dominance.
- Robin ratio may cross centrally while full two-variable jump kernel remains indefinite.
- any use of positivity-preserving semigroup past known kernel threshold is invalid.
- any identification of `(16)` from Xi divisor data is circular.

## Actual remaining RH frontier

```text
prove SUZUKI-ROBIN-CROSSING from prime--Gamma restricted operator
 -> fixed/escaping asymmetric pair satisfies central residue sign
 -> prove full normalized source jump is Pick
 -> Euler-defect pole tomography excludes every nonreal Xi zero
 -> RH.                                                   (17)
```

This theorem does not prove RH.  It removes the only published positive-ground chamber from
consideration and replaces a bulk weighted-average problem by an exact signed boundary spectral
crossing.

## Novelty audit

Suzuki's 2023 paper defines continuous `g`, proves `g(0)=0`, and gives screw-function RH
equivalences.  Suzuki's 2026 paper constructs `A_a`, proves small-aperture positive simple-even
ground, and formulates cofinal spectral limits.  Search of those primary sources found no
ground-edge Xi-curvature exclusion, symmetric-profile feasibility law `(7)`, deficit law `(9)`,
or Robin compression `(14)`.  Priority remains unverified beyond those sources.

## Formal status

Exact topology and algebra are formalized unconditionally in
`formal/GaloisForLFunctions/RHTower/SuzukiGroundEdgeApertureObstruction.lean`.  Concrete Suzuki
convolution, eigenfunction trace regularity, and integral instantiation remain absent from Lean.
