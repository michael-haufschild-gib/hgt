# EDQ: Estermann inverse-frequency transfer

Status: attempted estimate remains open. No new RH bound or Lean theorem.
The full signed source, logarithmic normalization and infinite frequency tail
are retained below. EDQ is not retired by this failed direct transfer.

## Exact target and paper reduction

Let `N>=1`; all unlabelled summation indices are positive integers, and
`tau` denotes the divisor-counting function. Write `b_h = bdGen(1/h)` and
`Q_N = ||sum_(1<=h<=N) mu(h)*b_h||^2`. This is source energy, not the
target-subtracted approximation error. Put

`M_N=sum mu(h)`, `H_N=sum mu(h)/h`, `J_N=sum mu(h)*log(h)/h`,

with all three sums over `1<=h<=N`. The desired EDQ conclusion requires
cofinal subpower control of the complete source, not merely of one transformed
frequency range.

The full Gram identity in [the covariance attack](edq-full-covariance-core-attack.md)
uses the Vasyunin function. Its relation to the sine Estermann function is

`V(a/b) = -(2*b/pi^2)*D_sin(1,a/b)` for coprime positive `a,b`.

Here `D_sin(1,x)` is the convergent rational sine-divisor series
`sum_(n>=1) tau(n)*sin(2*pi*n*x)/n`. The inverse in
`V(a/b)=-c_0(inverse(a)/b)` is undone by the functional equation relating
`c_0` to `D_sin(1,.)`. See Bettin's
[equation (1.3), Proposition 1 and Remark 2](https://arxiv.org/pdf/1411.2293),
and Bettin--Conrey's
[Vasyunin definition and formula (13)](https://msp.org/ant/2013/7-1/ant-v7-n1-p08-p.pdf).

Substitution into the complete normalized Gram gives the paper identity

```
Q_N = (M_N-H_N)*J_N
    + (2/pi)*sum_(h,k<=N) mu(h)*mu(k)/h
        * (D_sin(1,h/k)-D_sin(1,1/k)).
```

Proof: the two logarithmic Gram terms combine to `(M_N-H_N)*J_N`.
The two `V(1/h),V(1/k)` terms combine to
`-(2/pi)*H_N*sum_(k<=N) mu(k)*D_sin(1,1/k)`.
For the remaining terms put `g=gcd(h,k)`, `a=h/g`, `b=k/g`.
Symmetry makes their contributions equal, and `g*b=k` cancels the
denominator in the directed term. This gives the displayed identity without
dropping a gcd class, normalization term or part of the physical Gram.

## Conjecture, failed transfer, and retained cutoff

Candidate: apply a bilinear or trilinear Kloosterman-fraction estimate directly
to this signed Gram, preserving the original Möbius weights.

[Wright, August 2026, Theorem 2.1](https://arxiv.org/html/2608.27732v1)
improves a trilinear estimate when the two modulus-variable supports occupy
subdyadic intervals or consecutive elements of congruence classes. Its phase
is `e(theta*n*inverse(h)/k)`, with nonzero integer `theta`. Its additional
support-size hypotheses must also be supplied. The earlier
[Dong--Robles--Zeindler Theorems 1.4--1.6](https://arxiv.org/html/2601.00292v1)
likewise estimate inverse-fraction phases; only their `b=1` case was considered
for this transfer.

The displayed EDQ identity instead contains `e(n*h/k)`. Keeping the original
coefficients does not resolve this phase mismatch. Transferring a tail through
the Estermann functional equation still leaves the direct-frequency portion.
No complete bound for that portion, the associated correction, or the
coefficient-dependent transformed weights was established. In particular,
no claimed saving for an isolated inverse-frequency sum is a bound for `Q_N`.

A second attempt applies Möbius inversion before estimating. Define

`T_N(l)=sum_(d|l, d<=N) mu(d)*tau(l/d)`.

For every finite integer `L>=1`, exact regrouping gives

```
sum_(h<=N) mu(h)/h
  * sum_(n<=floor(L/h)) tau(n)*sin(2*pi*n*h/k)/n
 = sum_(l<=L) T_N(l)*sin(2*pi*l/k)/l.
```

For fixed `N,k`, taking `L` to infinity recovers the Estermann terms.
Because the Dirichlet convolution `mu*tau` is the constant-one function,
`T_N(l)=1` when `1<=l<=N`. When `N<l<=2*N+1`, every
proper divisor of `l` is at most `N`, so `T_N(l)=1-mu(l)`. This is an
exact surviving cutoff, not an error replaced by its absolute value.
The [sharp sign boundary](../3-formalized/edq-divisor-frequency-sign-boundary.md)
is now formalized: all coefficients through `2*N+1` are nonnegative, but
`T_N(2*N+2)=-1` at cofinally many cutoffs. This is a coefficient theorem;
the analytic physical-Gram representation remains paper-only.

Consequently the same source energy has the paper representation

```
Q_N = (M_N-H_N)*J_N
    + (2/pi)*lim_(L->infinity) sum_(l<=L)
        (T_N(l)-H_N*tau(l))/l
        * sum_(k<=N) mu(k)*sin(2*pi*l/k).
```

The limit is justified by the preceding finite regrouping and the finite
number of convergent rational Estermann series. No infinite double sum is
asserted absolutely convergent. The signed frequency tail and harmonic
correction remain uncontrolled; this rearrangement supplies no power saving.

## Compensated mean and the remaining divisor error

Another exact paper rearrangement removes the apparent separate Mertens
normalization term. Put `U_N(l)=T_N(l)-H_N*tau(l)+J_N`. The ordered sine
series `sum_(l>=1) sin(2*pi*l/k)/l` equals `pi*(1/2-1/k)` for `k>=2`,
and is zero for `k=1`. This follows by integrating the geometric series
inside the unit disk and taking the radial limit; Dirichlet convergence
identifies that limit with the ordered partial sums. Hence

```
Q_N = J_N*(H_N-1)
    + (2/pi)*lim_(L->infinity) sum_(l<=L) U_N(l)/l
        * sum_(k<=N) mu(k)*sin(2*pi*l/k).
```

The `k=1` exception is included; omitting it changes the anchor term.
For integer `L>=N`, define `D(x)=sum_(l<=x) tau(l)` and
`Delta_c(x)=D(x)-x*log(x)-c*x`, where `c` is any fixed real constant.
Finite hyperbola regrouping and logarithm subtraction give exactly

```
sum_(l<=L) U_N(l)
 = sum_(h<=N) mu(h)*Delta_c(L/h) - H_N*Delta_c(L).
```

Thus the normalization is absorbed without discarding a term, but the
remaining source is a signed Möbius combination of divisor errors. A separate
square-root envelope for each divisor error loses the Möbius cancellation
and yields only a `sqrt(N*L)` scale (and the harmonic contribution).
No subpower estimate for the complete sine pairing was obtained. These
mean-subtraction identities are not asserted as new Lean results.

For `N<=L<=2*N+1`, the proved coefficient classification gives the sharper
paper diagnostic

```
sum_(l<=L) U_N(l) = (1+J_N)*L - H_N*D(L) - (M_L-M_N).
```

Thus the first band retains the actual Mertens increment. The corpus theorem
`Sieve.tendsto_mertensSup_sqrt_div` bounds `M_sup(3*sqrt(x))/sqrt(x)` by a
quantity tending to zero; changing variable to the cutoff gives `o(Y)`,
not a square-root Mertens estimate. It cannot close this diagnostic.

The attempted odd-kernel cancellation also leaves the required part intact:
with `A(h,k)=D_sin(1,h/k)/h`, swapping the finite `h,k` sums removes the
antisymmetric part of `A`, whereas the source retains its symmetric part.
`HTGeometry.double_voronoi_resonant_cancellation` proves an odd-kernel
identity with symmetric weights; no identification of the retained EDQ
kernel with that odd kernel is established. Broad arXiv searches on
martingale and decoupling also recovered the already audited shell
decoupling and Hodge two-field mechanisms; no new analytic transfer resulted.

Selecting cutoffs cannot avoid negative coefficients. The Lean theorem
`coeff_prime_band` proves `T_N(4*p)=-1` throughout `p<=N<2*p` for every odd
prime `p`. More generally `coeff_four_mul_band` proves the exact plateau
`T_N(4*m)=1-2*mu(2*m)`. Any squarefree divisor of `4*m` divides `2*m`, so
no nonzero Möbius term enters strictly between `m` and `2*m`. The analytic
large-argument Bertrand theorem supplies, at every `N>=1024`, a negative
coefficient in `[2*N+2,4*N]`. This closes the cofinal coefficient-positivity
shortcut in
[the coverage leaf](../../../../formal/GaloisForLFunctions/RHTower/EulerDeletionDivisorFrequencyCoverage.lean).
It supplies no source-energy bound.

The associated corpus search used six cached deep/method requests: signed
divisor-error compensation, the single word `Mertens`, dyadic dilation
cancellation, Voronoi/divisor oscillation, resonant antisymmetry, and prime
interval/squarefree support. Candidate statements, source methods and their
obligations were inspected alongside proof ideas and ingredient sets.
Results remained partial with pending/source-only compiler metadata. In
particular, `CorrelationExponentBridge.divisor_threshold` is an algebraic
exponent calculation, not a bound for the divisor error. Relevant names
used in the new leaf were checked against the current Lean toolchain.

## Corpus and formal status

Four cached deep searches covered reciprocity/bilinear cancellation,
first-crossing involutions, the single word `Kloosterman`, and functional
equation/frequency remainders. Results were partial; compiler applicability
was mostly `source_only`. Candidate statements, method assumptions and
obligations were inspected. The Kloosterman ingredient set supplied symmetry
and phase negation, not the missing signed cross-modulus estimate.

The already available `KloostermanPhysicalResidueModulusBilinear` preserves
ordinary coefficient sequences, but its fixed-modulus norm estimate does not
prove the required bound above. The full analytic identities in this card
remain paper deductions. The finite sign classification has its separate
targeted Lean verification linked above. No computations or axiom checks ran.
