# Route U antipodal prime--Gamma polarization

- **ID:** `route-u-antipodal-prime-gamma-polarization`
- **Stage:** 3-formalized
- **Type:** CONJECTURE ATTACK + SOURCE CLASSIFICATION
- **Source:** `rh-current-frontier-map.md`; successor to
  `route-u-prime-gamma-nyquist-flux`
- **Claim:** The Route-U Nyquist complement is the antipodal image of the full hard-edge packet,
  hence physical inversion under the Cayley chart.  Common-filter polarization classifies every
  negative full source capital into a negative even diagonal, a negative odd diagonal, or a
  strictly negative even--odd cross capital; in the third branch a literal pointwise completed
  prime--Gamma cross inversion exists.

## Status labels

`[FORMALIZED] [HOSTILE AUDIT PASSED] [NOVELTY UNVERIFIED]`

## Exact frontier

`[CORPUS]` `XiShiftedHardEdgePrimeGammaNyquistFlux.lean` proves that the common-filter difference
of actual even and odd source capitals is the complete weighted Nyquist current and tends to zero.
The inherited interpretation called the remaining obstruction “diagonal”.

`[CORPUS]` `XiShiftedHardEdgePrimeGammaSourceDisintegration.lean` proves that every negative
filtered capital contains a literal pointwise completed Gamma--polar--von-Mangoldt inversion.

`[CORPUS]` `XiShiftedHardEdgeCofinalLinearFiniteHankelDimension.lean` proves that false RH gives one
fixed polynomial--Gaussian carrier whose finite packet is negative at every sufficiently large
integral hard-edge mass.

`[LITERATURE]` Classical paraunitary/polyphase theory identifies even--odd splitting with mirror
channels, but only for positive Hilbert energy; see Soman--Vaidyanathan--Nguyen,
<https://authors.library.caltech.edu/records/2pty3-6ge64>.  Burnol's invariant explicit-formula
analysis identifies multiplicative inversion and the conductor operator as local explicit-formula
primitives, <https://arxiv.org/abs/math/0101068>.  Connes--Consani identify Fourier/inversion and
Sonin compression as the archimedean positivity mechanism, but explicitly leave the semilocal
prime-bearing positivity problem open, <https://arxiv.org/abs/2006.13771> and
<https://arxiv.org/abs/1910.14368>.  No located source states the finite hard-edge
Gamma--polar--von-Mangoldt channel trichotomy below.

## Conjecture--failure--pivot loop

### U-DIAG -- equalized diagonals close the negative packet

Conjecture: once the common-filter Nyquist flux makes the even and odd diagonal capitals
asymptotically equal, a source-specific lower bound for those diagonals excludes negative full
capital.

**Verdict:** `[FALSIFIED]`.  Let a symmetric quadratic form on `R^2` have matrix

```text
[[1,-2],[-2,1]].
```

For `E=(1,0)` and `O=(0,1)`, both channel diagonals equal `1`, hence their difference is zero, but
the full vector `E+O` has quadratic value `-2`.  The negative capital sits entirely in the
even--odd cross term.  Equal nonnegative diagonals therefore do not orient the full packet.

**Exact why:** the Nyquist current is `Q(E)-Q(O)`, whereas

```text
Q(E+O)=Q(E)+Q(O)+2 B(E,O).
```

It controls the wrong matrix entry for the inherited conclusion.

### U-INDEPENDENT-DETAIL -- treat the complement as fresh detail energy

Stronger conjecture: the complementary packet `E-O` supplies an independent positive detail
diagonal which, together with the vanishing current, controls `Q(E+O)`.

**Verdict:** `[FALSIFIED]`.  If the full finite Chebyshev packet is `P`, parity gives exactly

```text
E=(P+P^-)/2,    O=(P-P^-)/2,    E-O=P^-,
P^-(x)=P(-x).
```

For the hard-edge coordinate

```text
x_a(z)=(a^2-z^2)/(a^2+z^2),
```

one has

```text
x_a(a^2/z)=-x_a(z).
```

Thus the complement is the original packet under physical inversion `z -> a^2/z`, not an
independent resource.  The degree-free Cauchy density obeys the exact Jacobian covariance

```text
x^2 D_a[P^-](x)=a^2 D_a[P](a^2/x)   (a != 0, x != 0),
D_a[P](x)=a^2/(a^2+x^2) P(x_a(x))^2.
```

**Exact why:** diagonal comparison hides one involutive orbit.  Its source defect is modular, not
an additional positive channel.

### U-POLAR -- common-filter labelled anomaly trichotomy

Replacement conjecture: perform full common-filter polarization and classify the source anomaly
before attempting a sign.

**Verdict:** `[FORMALIZED]` in
`XiShiftedHardEdgePrimeGammaAntipodalPolarization.lean`.

## Exact theorem

Fix `y>0`, common degree `d`, and coefficient vectors `c,e : Fin(d+1)->R`.  Write

```text
q(c)=xiShiftedReciprocalHankelQuadratic y c,
b(c,e)=sum_i sum_j c_i e_j Re M_y(i+j),
K=pi (2d)! > 0,
C(c)=K q(c),
X(c,e)=K b(c,e).
```

Here `C` is exactly the filtered completed prime--Gamma capital at common degree `d`; `X` is its
polarized cross capital.  Then

```text
C(c+e)=C(c)+C(e)+2 X(c,e),                         (AP.1)
C(c-e)=C(c)+C(e)-2 X(c,e),                         (AP.2)
C(c)-C(e)=X(c+e,c-e),                              (AP.3)
2(C(c)+C(e))=C(c+e)+C(c-e),                        (AP.4)
4 X(c,e)=C(c+e)-C(c-e).                            (AP.5)
```

Consequently

```text
C(c+e)<0
  -> C(c)<0 or C(e)<0 or X(c,e)<0.                 (AP.6)
```

If both diagonals are nonnegative, the cross anomaly is quantitatively strict:

```text
2 X(c,e) < -(C(c)+C(e)) <= 0.                      (AP.7)
```

Define the literal cross balance and its filtered kernel by

```text
B_x(t)=(B_(c+e)(t)-B_(c-e)(t))/4,
K_x(t)=t^(2d) exp(-yt) B_x(t)    for t>0,
```

where `B_v(t)` is the existing completed Gamma--polar--von-Mangoldt balance.  Then

```text
integral_(0,infinity) K_x(t) dt = X(c,e).           (AP.8)
```

Therefore

```text
X(c,e)<0 -> exists t>0, B_x(t)<0.                  (AP.9)
```

For the actual Route-U even and odd packet polynomials, take `d` to be the existing common lift
degree and `c,e` their zero-padded reciprocal-lift coefficient vectors.  Their sum represents the
full fine packet; their difference represents the complementary alias/antipodal packet.  Hence
every negative full finite packet has the labelled, nonexclusive alternative (AP.6), and every branch
contains a literal pointwise diagonal or cross completed-source inversion.  Under false RH the
same alternative occurs at every sufficiently large integral hard-edge mass for one fixed carrier.

## Dependency-closed paper proof

The moment kernel depends only on `i+j`, so `b` is symmetric bilinear and `q(c)=b(c,c)`.  Expanding
`b(c+e,c+e)` and `b(c-e,c-e)` proves (AP.1)--(AP.2); subtraction, addition, and the expansion
`b(c+e,c-e)=b(c,c)-b(e,e)` prove (AP.3)--(AP.5).  Multiplication by the positive common factor `K`
preserves every identity and strict sign.

If all three terms on the right side of (AP.1) were nonnegative, `C(c+e)` would be nonnegative;
this proves (AP.6).  Under nonnegative diagonals, rearranging (AP.1) with `C(c+e)<0` gives (AP.7).

The existing source disintegration identifies each diagonal capital with the integral of its
filtered kernel.  Both kernels are integrable because `y>0`.  Linearity of the integral therefore
gives (AP.8).  If every literal cross balance were nonnegative, the positive factor
`t^(2d) exp(-yt)` would make the cross kernel nonnegative almost everywhere, contradicting the
negative integral.  This proves (AP.9).

For each actual cofinal explicit packet `P_k`, define its exact antipodal eigencoordinates
`E_k=(P_k+P_k^-)/2` and `O_k=(P_k-P_k^-)/2`.  Then `E_k+O_k=P_k` and
`E_k-O_k=P_k^-`.  The common vectors recover the reciprocal lifts of `E_k` and `O_k`.
Linearity of polynomial reciprocal pullback and `ofFn` makes `c+e` recover the full source
polynomial and `c-e` the complement.  Both the original coefficient vector and the common padded
full vector evaluate to the same shifted reciprocal trace Hankel scalar.  The fixed-carrier
false-RH phase makes this quadratic negative at every sufficiently large integral mass, so
(AP.6)--(AP.9) apply cofinally.  QED.

## Hostile significance audit

Generic polarization is `[REDISCOVERED]`; Cayley/Cauchy inversion is a `[BRIDGE]`.  Scientific
delta is their exact source-faithful Route-U consequence: the inherited diagonal diagnosis is
wrong.  Vanishing Nyquist current controls `X(full,antipode)=C(even)-C(odd)`.  Negative full capital
depends instead on `X(even,odd)`.  No diagonal lower bound, even strict positivity of both
diagonals, can close the packet without controlling this different cross source.

The result does not prove RH.  It retires the diagonal-only Nyquist successor and replaces it with
one exact source alternative.  In the nonnegative-diagonal branch, next open core is a labelled
prime--Gamma bound on the literal cross balance (AP.9), using its hard-edge inversion geometry.
If either diagonal branch occurs cofinally, the existing degree-free Cauchy source inversion must
be attacked there instead.

## Higher universal principle

Multiresolution parity is modular conjugation.  Reconstruction and detail are eigencoordinates of
one inversion orbit; diagonal equality measures orthogonality of the orbit pair, while instability
lives in the covariance between eigencoordinates.  Earlier “diagonal obstruction” was a shadow of
confusing these two polarizations.

## Lean target

New module:
`formal/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaAntipodalPolarization.lean`.

Required closed surface:

- symmetric shifted reciprocal Hankel bilinear and identities (AP.1)--(AP.5);
- literal filtered cross source identity (AP.8) and inversion witness (AP.9);
- negative full-capital channel trichotomy and strict cross branch (AP.6)--(AP.7);
- actual common-degree even/odd specialization;
- antipodal Chebyshev and hard-edge Cauchy inversion laws;
- fixed-carrier cofinal false-RH polarization phase and exact equivalence.

## Lean audit

`lake env lean` passes on scratch and checked-in source.  Exact module `.olean` built directly at
`formal/.lake/build/lib/lean/GaloisForLFunctions/RHTower/XiShiftedHardEdgePrimeGammaAntipodalPolarization.olean`
(882368 bytes); no umbrella or project build was run.  The module is imported by
`formal/GaloisForLFunctions/RHTower.lean`.

`#print axioms` for the cross-capital identity, trichotomy, pointwise cross witness, Cauchy
inversion, actual packet identification, cofinal false-RH equivalence, and premise-free dichotomy
reports only `propext`, `Classical.choice`, and `Quot.sound`.  Targeted forbidden-token and
`git diff --check` audits pass.

## Gates

- [x] Internal corpus audit
- [x] External parent-theory audit
- [x] `U-DIAG` falsified with exact countermodel
- [x] `U-INDEPENDENT-DETAIL` falsified by antipodal/inversion identity
- [x] `U-POLAR` dependency-closed paper proof
- [x] Hostile paper-proof audit
- [x] Stage 2 promotion
- [x] Exact Lean formalization and axiom audit
