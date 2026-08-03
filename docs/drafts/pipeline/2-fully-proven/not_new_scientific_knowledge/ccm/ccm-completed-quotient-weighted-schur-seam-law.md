# The completed causal quotient must remain contractive across one exponential-weight seam

- **ID:** `ccm-completed-quotient-weighted-schur-seam-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE WEIGHTED-CONTRACTION NORMAL FORM / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:** Hardy multiplier theory, the zero strip for `xi`, Suzuki's shifted inner quotient,
  `euler-hardy-leakage-offline-zero-rank.md`, and
  `ccm-causal-pick-affine-conjugacy-law.md`
- **Statement:** For every positive horizontal shift, the completed causal quotient is
  unconditionally a Schur multiplier on the ordinary causal Hardy space, and remains contractive
  under every exponential conjugation of width at most `omega`. The shifted-Xi Pick positivity
  needed by CCM is exactly contractivity of that same causal convolution at width
  `1/2+omega`. Hence the missing width is exactly one half at every prelimit. Off-line zeros are
  precisely the anti-causal leakage channels obstructing the target weighted contraction.

## 1. The completed causal quotient is unconditionally Schur

Fix `omega>0` and put

```text
Phi_omega(z)=xi(1+z)/xi(1+2omega+z),       Re z>0.          (1)
```

Then

```text
Phi_omega belongs to H-infinity(Re z>0),
||Phi_omega||_infinity<=1.                                  (2)
```

In fact the inequality is strict at every point of the open half-plane.

### Proof

Let

```text
X(w)=xi(1/2+w).                                             (3)
```

The function `X` is even, entire of order one, and all its zeros `lambda` satisfy

```text
|Re lambda|<1/2.                                           (4)
```

Pairing the centered Hadamard divisor under `lambda -> -lambda` gives, locally uniformly away
from the zeros,

```text
X'(w)/X(w)
 =m/w+sum_(lambda mod +-) (1/(w-lambda)+1/(w+lambda)),      (5)
```

with the zero multiplicity `m` omitted when it vanishes. The symmetric series is locally
absolutely convergent because its terms are `O_w(|lambda|^(-2))` and the order-one divisor has
`sum |lambda|^(-2)<infinity`.

If `Re w>1/2`, both `w-lambda` and `w+lambda` have positive real part. Hence every reciprocal in
`(5)` has positive real part, as does `m/w`. Therefore

```text
Re X'(w)/X(w)>0,       Re w>1/2.                            (6)
```

For `Re z>0`, the horizontal segment from `w=1/2+z` to `w+2omega` lies entirely in this half-plane.
Consequently

```text
log|Phi_omega(z)|
 =-integral_0^(2omega)
    Re X'(1/2+z+t)/X(1/2+z+t) dt
 <0.                                                        (7)
```

The denominator in `(1)` has no zero there. Thus `Phi_omega` is analytic and bounded by one on
the right half-plane, proving `(2)`. `QED`

This contraction uses only the classical zero strip `0<Re rho<1`; it contains no RH input.

## 2. Causal convolution

Let `H2_+` be the right-half-plane Hardy space. By `(2)`, multiplication by `Phi_omega` defines a
contraction

```text
C_omega=M_(Phi_omega):H2_+ -> H2_+,
||C_omega||<=1.                                            (8)
```

Under the Paley--Wiener identification with `L2(R_+)`, this is a causal convolution operator. It
is the completed version of the signed Möbius causal transfer: the exact archimedean-polar scalar
conjugacy and counterterm relating the two are proved in
`ccm-causal-pick-affine-conjugacy-law.md`.

Thus “construct a causal contraction” is not an open CCM task. The completed source already
supplies one.

## 3. Exponential conjugation is the shifted-Xi boundary

For `a>=0`, let `E_a` denote multiplication by `exp(a t)` on its natural dense domain in
`L2(R_+)`. Define the natural graph operator

```text
C_(omega,a)=E_a C_omega E_(-a)                             (9)
```

on those vectors for which the right side belongs to `L2`. Whenever the graph expression is
defined, its Laplace multiplier is

```text
Phi_(omega,a)(z)=Phi_omega(z-a).                            (10)
```

Indeed exponential conjugation multiplies the causal convolution kernel by `exp(a t)`, which
translates its Laplace symbol left by `a`. No density or boundedness of this graph is asserted at
this stage; those are precisely the continuation questions measured below.

### Unconditional safe weighted width

The zero strip transports the contraction through the full range

```text
0<=a<=omega.                                               (10a)
```

More precisely,

```text
Phi_omega(z-a) belongs to H-infinity(Re z>0),
||Phi_omega(.-a)||_infinity<=1,       0<=a<=omega.          (10b)
```

To prove this, put

```text
c=1+omega-a>=1.
```

On the boundary `z=it`, the two xi arguments are `c-omega+it` and `c+omega+it`. In the centered
variable `w=s-1/2`, their midpoint has real part

```text
d=c-1/2>=1/2.                                              (10c)
```

Use the even Hadamard product of `X(w)=xi(1/2+w)`. For every centered zero `lambda`, both
`lambda` and `-lambda` have real part strictly below `1/2`. For either member `mu` of this pair,

```text
|d+omega+it-mu|^2-|d-omega+it-mu|^2
 =4omega(d-Re mu)>0.                                      (10d)
```

Thus every paired canonical-product factor has no larger modulus at `c-omega+it` than at
`c+omega+it`. Passing through the locally uniform symmetric product gives

```text
|xi(c-omega+it)|<=|xi(c+omega+it)|.                        (10e)
```

The denominator is zero-free in the right half-plane. The quotient is of bounded type with zero
relative mean type, so the Smirnov maximum principle upgrades `(10e)` to `(10b)`. Equivalently,

```text
E_a C_omega E_(-a)
```

closes to a contraction for every `0<=a<=omega`.

This is the full width supplied by the factorwise comparison using only the classical strip
`0<Re rho<1`: at `a=omega` the two boundary lines are symmetric about `Re s=1`. Moving the center
left of one is no longer justified by that strip comparison and requires an additional source
estimate.

Choose the distinguished exponent

```text
a_omega=1/2+omega.                                         (11)
```

Then

```text
Phi_(omega,a_omega)(z)
 =xi(1/2-omega+z)/xi(1/2+omega+z).                         (12)
```

After the rotation `z=-iw`, `(12)` is Suzuki's quotient

```text
Theta_omega(w)
 =xi(1/2-omega-iw)/xi(1/2+omega-iw).                       (13)
```

Therefore exponential conjugation by exactly `a_omega` is not an analogy for contour transfer; it
is the contour transfer.

## 4. Exact weighted-contraction criterion

For every nonexceptional `omega>0`, the following are equivalent:

```text
(i)  xi has no zero rho with Re rho>1/2+omega;

(ii) Phi_(omega,a_omega) is a Schur multiplier of H2_+;

(iii) C_(omega,a_omega) is densely defined and closes to an everywhere-defined contraction on
      L2(R_+);

(iv) the kernel
     K_omega(z,v)
      =(1-Phi_omega(z)conjugate(Phi_omega(v)))
       /(1+2omega+z+conjugate(v))                          (14)
     is positive on every finite subset of Re z>0.
```

At an exceptional shift, cancel the common numerator-denominator divisor before applying the
statement.

### Proof

The equivalence `(i)<->(ii)` is the shifted Hermite--Biehler/Suzuki criterion applied to `(12)`.
The equivalence `(ii)<->(iii)` is the Paley--Wiener multiplier theorem and `(10)`.

For `(ii)<->(iv)`, set

```text
u=z+a_omega,       q=v+a_omega.                            (15)
```

The ordinary Schur kernel of `Phi_(omega,a_omega)` is

```text
(1-Phi_(omega,a_omega)(u)
     conjugate(Phi_(omega,a_omega)(q)))
 /(u+conjugate(q)).                                        (16)
```

Substitution of `(10)`--`(11)` turns `(16)` exactly into `(14)`. Positivity on `Re z>0`, rather
than the whole natural half-plane `Re z>-a_omega`, is sufficient by locality of negative squares
or analytic uniqueness of Schur kernels. This proves all equivalences. `QED`

For all `omega>0`, the negative index of `(14)` is

```text
ind_-(K_omega)
 =sum_(xi(rho)=0, Re rho>1/2+omega) multiplicity(rho),     (17)
```

with infinity allowed. Thus failure of the weighted contraction is not a featureless norm defect:
its anti-causal leakage multiplicity is exactly the off-line divisor count beyond that horizontal
layer.

## 5. The canonical charged graph already exists

After common-divisor cancellation, write the target shifted quotient in coprime inner form

```text
Phi_(omega,a_omega)=A_omega/B_omega.                       (18)
```

Here the denominator Blaschke product `B_omega` has one zero, with multiplicity, for every zero of
`xi` in `Re rho>1/2+omega`. Define the meromorphic multiplier graph

```text
G_omega
 ={(B_omega g,A_omega g):g in H2_+}
 subset H2_+ direct_sum H2_+.                              (19)
```

Then `G_omega` is the graph of multiplication by `Phi_(omega,a_omega)` on its maximal analytic
Hardy domain, and

```text
Dom(G_omega)=B_omega H2_+,
||A_omega g||_2=||B_omega g||_2=||g||_2.                  (20)
```

Thus the canonical Xi-pointed graph is closed and isometric unconditionally. Its domain defect is

```text
K_(B_omega)=H2_+ minus B_omega H2_+,

dim K_(B_omega)
 =sum_(Re rho>1/2+omega)multiplicity(rho),                 (21)
```

including infinite dimension.

### Proof

The coprime inner quotient is the standard bounded-type factorization of the unimodular shifted-Xi
boundary function. If `f=B_omega g`, then

```text
Phi_(omega,a_omega)f=A_omega g in H2_+.
```

Conversely, if `f` and `Phi_(omega,a_omega)f` both belong to `H2_+`, coprimeness forces the inner
factor `B_omega` to divide `f`. Hence the maximal domain is exactly `B_omega H2_+`. Inner
multiplication is isometric, proving `(20)` and closedness. The model-space dimension formula and
the denominator-zero correspondence give `(21)`. `QED`

This changes the open problem. Constructing a closed nonexpansive charged graph is not itself an RH
step; `(19)` already does so. The RH-bearing property is **full domain**:

```text
Dom(G_omega)=H2_+
 iff B_omega=1
 iff no zero lies in Re rho>1/2+omega.                     (22)
```

Every off-line zero is a missing input channel, not a failure of isometry on the pole-cancelling
domain. A successful source proof must show that the model-space defect `(21)` vanishes. Merely
renorming `B_omega H2_+`, proving graph closedness, or proving nonexpansivity there cannot do so.

`[PROVED COFINAL TRANSPORT]` These missing Hardy inputs are exactly the cofinal finite-aperture
Morse charge. The global screw kernel has one negative square per right-half zero, and bounded-
interval exhaustion gives

```text
sup_(a>0)kappa(a)
 =sum_(Re rho>1/2)multiplicity(rho)
 =sup_(omega>0)dim K(B_omega).
```

Thus every finite model-space defect packet becomes an actual negative restricted-Weil subspace at
some finite aperture. See `ccm-aperture-morse-hardymodel-index-exhaustion-law.md`.

The graph is nevertheless the correct orbit-sensitive carrier. Multiplying Xi by a symmetric
orbit polynomial changes `B_omega` and hence changes the domain defect, even when the ordinary
Euler-side Schur multiplier is unchanged. This is the exact marking absent from a divisor-blind
bounded construction.

## 6. Cofinal form of RH

The following are equivalent:

```text
(i) RH;

(ii) for every nonexceptional omega>0,
     E_(1/2+omega) C_omega E_(-(1/2+omega))
     closes to a contraction;

(iii) the same holds for one sequence of nonexceptional shifts
      omega_j downarrow 0.                                 (23)
```

The implication `(i)->(ii)` is Section 4. The implication `(ii)->(iii)` is immediate. If RH is
false and `rho` has displacement `delta=Re rho-1/2>0`, then every sufficiently small
nonexceptional `omega<delta` gives a nonzero negative index in `(17)`, contradicting `(iii)`.

Hence the positive CCM obligation is

```text
unconditional causal contraction C_omega
  + closed exponential-domain transport through a_omega=1/2+omega
  + preservation of every residue channel
  -> weighted contraction
  -> RH.                                                    (24)
```

As `omega` decreases to zero,

```text
a_omega ->1/2.                                             (25)
```

This is the operator form of the invariant half-unit seam found in the weighted Möbius moment
tower. The source must pay for that seam by exponential-domain control; ordinary unweighted
Hardy contractivity is already free.

The safe-width theorem makes the deficit exact at every positive shift:

```text
target width - unconditional safe width
 =(1/2+omega)-omega
 =1/2.                                                      (25a)
```

Thus the half-unit is not an artifact of taking `omega` to zero. It is already the fixed missing
operator weight at each prelimit.

## 7. What a proof must positively construct

Equation `(24)` rules out no architecture by itself. It specifies its carrier:

1. the completed causal convolution `C_omega`, not only the reciprocal-zeta factor;
2. the canonical inner denominator `B_omega` recovered from the Euler--Gamma continuation;
3. the model-space defect `K_(B_omega)` with its explicit Cauchy residue coordinates;
4. a source inequality forcing `K_(B_omega)=0`, equivalently full domain of `(19)`;
5. compatibility as `omega` decreases cofinally to zero.

The rational-orbit insertion law shows that items 3--4 must be pointed by the exact Xi divisor.
A bounded construction depending only on the Euler-side multiplier cannot distinguish the added
residue block.

The scalar periodic-pencil principalization theorem does not replace this graph. At fixed `omega`,
`C_omega` is one scalar one-clock multiplier. Any nonpure relation geometry must live in the
cofinal weighted-domain/residue incidence, a non-DA-flat internal cocycle, or a genuinely
infinite-dimensional action.

## 8. The Poisson half-weight is an exact range-defect problem

Put

```text
s=1/2+omega+z.                                             (26)
```

Choose an integer `m` large enough and define the pole-cleared normalized Muntz multiplier

```text
d_(omega,m)(z)=s(s-1)zeta(s)/(1+z)^m,                     (27)
```

where the value at `s=1` is removable. Standard polynomial vertical-strip bounds for zeta,
together with `zeta(s)->1` as `Re s->infinity`, show that `m` can be chosen so that

```text
d_(omega,m) belongs to H-infinity(Re z>0).                (27a)
```

The factors `s(s-1)` clear the zeta pole and the completed polar points; `(1+z)^m` is zero-free in
the right half-plane. Hence `d_(omega,m)` has exactly the same right-half-plane zero divisor as
`xi(1/2+omega+z)`. This is the Hardy-normalized form of Connes's Mellin summation multiplier: zeta
is the arithmetic Poisson--Muntz factor, while the omitted Gamma factor and the polynomial
normalization are zero-free there and do not alter the Blaschke divisor.

The inner factor of `d_(omega,m)` is exactly `B_omega` from `(18)`. Therefore

```text
closure(Ran M_(d_(omega,m)))=B_omega H2_+,

ker(M_(d_(omega,m))^*)=K_(B_omega).                       (28)
```

### Proof

Write the bounded analytic inner--outer factorization

```text
d_(omega,m)=B_omega O_(omega,m).                          (29)
```

There is no singular inner factor: the normalized function extends meromorphically across the
boundary, has no boundary singular measure, and has zero mean type. The zeros of `B_omega` are
exactly the points

```text
b_rho=rho-(1/2+omega),       Re rho>1/2+omega,             (30)
```

with multiplicity. Multiplication by the outer bounded function `O_(omega,m)` has dense range in
`H2_+`, while multiplication by the inner function `B_omega` is an isometry with closed range.
This proves the first equality in `(28)`. Taking orthogonal complements proves the second.

Pointwise, every simple off-line zero gives the adjoint null vector

```text
M_(d_(omega,m))^* k_(b_rho)
 =conjugate(d_(omega,m)(b_rho))k_(b_rho)=0,               (31)
```

where `k_b(z)=1/(z+conjugate(b))` is the right-half-plane Cauchy kernel. A zero of multiplicity `r`
gives the first `r` Cauchy derivative jets. Their closed span is the model space in `(28)`. `QED`

Consequently the global Poisson formula does not, by itself, cross the missing half-unit. It gives
the zeta multiplier and its reflection intertwining, but the exact target it leaves is

```text
closure(Ran M_(d_(omega,m)))=H2_+.                        (32)
```

By `(28)`, this density statement is equivalent to `K_(B_omega)=0`, hence to the shifted zero-free
half-plane. The positive Poisson/CCM obligation is therefore not another support identity:

```text
completed Poisson--Muntz source
  + half-weight graph control
  -> dense completed multiplier range
  -> no Cauchy-jet defect channels.                        (33)
```

The safe weighted range `a<=omega` has trivial inner defect because its denominator lies strictly
to the right of `Re s=1`. Transport through the remaining one half is exactly the possible birth
of the adjoint null space `(28)`.

This is the completed Hardy-space form of the Nyman--Beurling range criterion. It retires “Poisson
summation supplies the half-weight automatically” as an independent proof step while retaining its
positive content: a successful construction must prove the source-selected dense-range theorem
`(32)`.

## 9. July 2026 literature boundary

The current primary-source boundary agrees with the model-space diagnosis.

- Connes--Consani--Moscovici, *Zeta Spectral Triples*, arXiv:2511.22755, proves the finite
  self-adjoint/real-zero construction and states that rigorous convergence of its spectra or
  normalized determinants to the zeta zeros/`Xi` is the missing RH step. It does not prove full
  domain of the shifted quotient graph.
- Suzuki, *Weil's quadratic form via the screw function*, arXiv:2606.09096, constructs the exact
  localized screw operators without RH, but its global spectral limit is conjectural; the paper
  explicitly leaves the required arithmetic control of the prime contribution beyond its fixed-
  aperture arguments.
- Groskin, *A finite Guinand--Weil dictionary and archimedean tail order for the truncated Weil
  quadratic form*, arXiv:2607.02828, proves that every finite Galerkin value is an exact induced
  Weil zero sum and that the omitted archimedean tail is a positive Cauchy--Stieltjes increment.
  These results calibrate finite signs but do not prove cofinal Weil positivity or eliminate the
  denominator model spaces `(21)`.

Thus no located 2025--July 2026 CCM result supplies the source estimate required in `(22)`. The
operator normal form above is consistent with, but does not improve, the published RH endpoint.

## 10. Scientific classification and Lean decision

The proof combines standard Hadamard monotonicity outside the zero strip, Hardy multiplier theory,
exponential conjugation, and the classical shifted-inner criterion. It is a route normal form, not
new scientific knowledge.

The formal tree lacks xi's analytic Hadamard product, Hardy multipliers, unbounded exponential
conjugation, and generalized negative-square kernels. Formalizing a symbolic shift identity would
not certify `(17)` or `(23)`. No Lean file is added.

## Gates

- [x] unconditional completed causal Schur contraction proved
- [x] exponential conjugation computed exactly
- [x] unconditional safe weighted width `0<=a<=omega` proved from the zero strip
- [x] distinguished exponent `1/2+omega` identified
- [x] invariant prelimit missing width proved to be exactly `1/2`
- [x] weighted contractivity proved equivalent to the shifted zero-free half-plane
- [x] leakage index attached to every failed weighted layer
- [x] canonical closed isometric charged graph constructed
- [x] its domain defect identified with the complete off-line divisor model space
- [x] cofinal model-space defect identified with the restricted-Weil aperture Morse charge
- [x] graph closedness and nonexpansivity retired as independent RH steps
- [x] completed Poisson--Muntz range closure identified with `B_omega H2_+`
- [x] off-line zeros identified as adjoint Cauchy-jet null channels
- [x] Poisson half-weight reduced to the exact dense-range obligation
- [x] cofinal weighted-contraction criterion proved equivalent to RH
- [x] positive closed-graph carrier specified
- [ ] prove from the Euler--Gamma source that every denominator model space vanishes
- [ ] RH
