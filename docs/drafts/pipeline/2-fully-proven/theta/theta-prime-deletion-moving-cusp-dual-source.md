# Moving-cusp reflection turns Euler deletion into a signed-totient source

- **ID:** `theta-prime-deletion-moving-cusp-dual-source`
- **Stage:** 2-fully-proven (paper)
- **Type:** exact source duality, cofinal local limit, and graded boundary profile
- **Routes:** STC, CSB, U, BPC, K-RVM, MPLF, RHist; Euler-deletion interface
- **Status:** `[PROVED HERE ON PAPER] [FINITE REFLECTION AND TOTIENT INVERSE IN LEAN] [NOT AN RH PROOF]`
- **Dependencies:** [finite prime deletion](../../3-formalized/theta/theta-prime-deletion-spectral-escape.md), [terminal weighted admission](../../3-formalized/theta/theta-prime-deletion-graded-terminal-admission.md), literal theta first-atom asymptotic.

## Exact finite identity

Let `k` be the even completed-theta source, `S` a finite set of primes,
`P=∏_(p∈S)p`, and `k_S=∏_(p∈S)(1-p^(-1/2)T_(log p))k`.
For `u∈ℝ`, define the moving-frame source

```text
R_S(u) = μ(P)√P k_S(−log P−u).
```

Reflection about the **moving** cusp gives the exact identities

```text
R_S(u) = ∑_(e|P) μ(e)√e k(u+log e)
       = ∏_(p∈S)(1−√p T_(log p))k(u).                 (1)
```

Indeed, expand `k_S` over divisors `d|P`, use evenness to replace
`k(−log(P/d)−u)` by `k(u+log(P/d))`, and substitute `e=P/d`.
Squarefreeness gives `μ(P)μ(P/e)=μ(e)`; the coefficient becomes
`√e`. The abstract finite-list reflection identity, without arithmetic
specialization, is formalized in
`ThetaFiniteEulerMovingCuspDuality.lean`.

The Mellin transform of (1), with `F(w)=∫e^(wu)k(u)du=Xi_C(iw)`, is

```text
∫ e^(wu) R_S(u)du
  = F(w)∏_(p∈S)(1−p^(1/2−w))
  = μ(P)P^(1/2−w) F(−w)∏_(p∈S)(1−p^(−1/2+w)).       (2)
```

The second equality follows directly from the definition and evenness
`F(−w)=F(w)`. All transforms in (2) are entire for finite `S`.

## Cofinal dual source

As finite prime sets increase through all primes, the normalized
moving-frame sources converge locally uniformly to

```text
R_∞(u) = ∑_(e squarefree ≥1) μ(e)√e k(u+log e).       (3)
```

The series is absolutely and locally uniformly convergent: for large
`e`, its summand is bounded by a polynomial in `e` times
`exp(−c e²)` on every compact `u`-interval, by the first theta atom.
The convergence remains valid after any fixed number of derivatives.
Thus the full finite Euler polynomial, not only its terminal word,
survives at the cofinal moving cusp. Equivalently,
`√P k_S(−log P−u)−μ(P)R_∞(u)→0` locally uniformly.

Writing the completed source as
`k(u)=∑_(n≥1)n^(−1/2)h(u+log n)` and rearranging its absolutely
convergent atom expansion yields a second exact description:

```text
R_∞(u) = ∑_(m≥1) A(m)m^(−1/2)h(u+log m),
A(m) = ∑_(e|m) μ(e)e = ∏_(p|m)(1−p).              (4)
```

The moving cusp therefore replaces the unit arithmetic coefficients
of `k` by a signed-totient coefficient. Its prime factors are the
`blockDeletionCoefficient` already formalized in
`CoprimeBlockCarryTransgression.lean`; (1) connects that arithmetic
carrier to the literal theta source through moving-cusp reflection.
Let `φ` be Euler's totient. The two arithmetic streams are exact
Dirichlet-convolution inverses:

```text
(A * φ)(m) = [m=1],
h(u) = ∑_(n≥1) φ(n)/√n · R_∞(u+log n).              (4a)
```

Indeed, the Dirichlet series of `A` and `φ` are respectively
`ζ(s)/ζ(s−1)` and `ζ(s−1)/ζ(s)` for `Re s>2`.
Alternatively, check the prime-power coefficients and use
multiplicativity. Substituting (4) and collecting the coefficient of
`h(u+log m)` proves the second identity. The sum and its rearrangement
are absolutely convergent for each fixed `u`, since `R_∞` has a
Gaussian positive tail while `φ(n)/√n` grows at most polynomially.
Thus a **positive** arithmetic dilation operator reconstructs the
original seed from the signed moving-cusp source. This operator is
pointwise defined; no bounded Hilbert-space inverse is asserted.
The exact arithmetic inverse and its identification with Euler's
totient are formalized in
`ThetaMovingCuspSignedTotientInverse.lean`; the infinite source
reconstruction remains paper-proved.

The reconstruction has a stronger **finite-stage** form. Put
`T_φ f(u)=∑_(n≥1)φ(n)n^(−1/2)f(u+log n)` and let `P=∏_(p∈S)p`.
Then, without taking a limit,

```text
A_S(m) = ∏_(p∈S, p|m)(1−p),
R_S(u) = ∑_(m≥1) A_S(m)m^(−1/2)h(u+log m),
T_φ R_S(u) = ∑_((m,P)=1) √m · h(u+log m).         (4b)
```

To see the coefficient mechanism, first `T_φ k` has coefficient
`∑_(d|m)φ(d)=m` on the atom `m^(−1/2)h(u+log m)`, hence
`T_φ k=∑_m√m h(u+log m)`. The finite dual factor
`1−√p T_(log p)` deletes precisely the atoms with `p|m`, because
their shifted coefficient is `√p√(m/p)=√m`. These factors commute
with `T_φ`, proving (4b). The right side converges locally uniformly
to `h` as `S` increases through all primes. Thus moving-cusp
reflection and totient reconstruction reverse the atom weight
`m^(−1/2)` into `m^(1/2)` while preserving the **same coprime
prime sieve**. The complementary prime set is the exact finite
boundary datum; its removal recovers the seed.

In the initial half-plane
`Re w>3/2`, absolute convergence permits Mellin interchange and the
ordinary Euler product:

```text
∫ e^(wu)R_∞(u)du = F(w)/ζ(w−1/2).                (5)
```

Equation (5) identifies the spectral content of the dual source; it
does not assert a zero-free continuation of the quotient. The original
Xi divisor remains in its numerator, while the shifted reciprocal
zeta factor introduces a new singular boundary problem.

The reconstruction in (4a) has Mellin multiplier
`ζ(w−1/2)/ζ(w+1/2)` in its initial convergence half-plane.
For any nontrivial zeta zero `ρ` of multiplicity `m`, set
`w_−=ρ−1/2` and `w_+=ρ+1/2`. Meromorphic continuation gives an
exact **one-unit spectral shear**: the dual transform (5) has a zero
of order `m` at `w_−` and a pole of order `m` at `w_+`; the positive
totient reconstruction multiplier has the opposite pole and zero.
There is no accidental cancellation because `ζ(ρ−1)≠0` in
`−1<Re(ρ−1)<0`, and `ξ(ρ+1)≠0` for `Re(ρ+1)>1`.
Their product is the zero-free seed transform
`ℒ_wh=(w−1/2)G(w)` in the open Xi strip. Thus the positive
pointwise inverse cannot be continued as a bounded holomorphic
spectral transfer through an Xi zero: its pole is exactly what
erases that zero in the seed. The same zero reappears one unit to
the right as a dual-source resonance. This pairing preserves the
horizontal displacement of any hypothetical off-line zero; it is
not a critical-line orientation law.
At the real convergence wall `w=3/2`, the roles reverse again:
`1/ζ(w−1/2)` has a simple zero, while the positive totient
multiplier has a simple pole. Their cancellation is exact but
cannot transport positivity analytically across that wall.

There is also an unconditional **sign-change theorem**. The first
theta atom in (3) dominates every `e>1` term as `u→+∞`, so
`R_∞(u)/k(u)→1` and `R_∞(u)>0` on a far positive ray. Suppose instead
that `R_∞≥0` everywhere. For each real `σ>3/2`, (5) and absolute
Mellin convergence give

```text
∫ e^(σu)R_∞(u)du = F(σ)/ζ(σ−1/2) > 0.
```

As `σ↓3/2`, the right side tends to zero because `F` is continuous
and finite there and `ζ(s)→+∞` as `s↓1`. Fatou's lemma for the
nonnegative integrands would imply
`∫e^(3u/2)R_∞(u)du=0`, contradicting strict positivity on the
positive ray. Hence `R_∞` is negative on some open interval and
positive on a positive ray. No zero-location input or prime-number
theorem is needed for this sign obstruction.

Identity (4a) gives a second, source-specific proof of the sign
obstruction: `φ(n)≥0`, whereas the explicit theta seed `h(u)` is
negative on a far negative ray. If `R_∞` were nonnegative everywhere,
its positive totient reconstruction could not equal `h` there.

In fact **both signs occur arbitrarily far into the negative cusp**.
Set `g(t)=R_∞(−t)` for `t≥0`. Suppose `g` eventually had one sign;
discard a finite head and reverse sign if needed, leaving a
nonnegative Laplace carrier. Its convergence abscissa satisfies
`c≤3/2`; the pole below also shows that `c` is finite.
The Mellin quotient (5) has a genuine pole at
`w₀=ρ+1/2` for any corpus-certified nontrivial zeta zero `ρ`:
`ζ(w₀−1/2)=0`, while `F(w₀)=ξ(ρ+1)≠0`.
The finite head has entire transform, so `c≥Re w₀>1/2`.
Yet `F(w)/ζ(w−1/2)` is holomorphic at every **real**
`w∈(1/2,3/2]`: zeta has no real zero on `(0,1)`, and its pole at
one becomes a zero of the reciprocal. The head correction is entire.
Thus the tail transform is holomorphic at its real abscissa `c`,
contrary to Landau's abscissa singularity theorem (formalized in
`LandauSingularAtAbscissa.lean`). Hence `g` is neither eventually
nonnegative nor eventually nonpositive. Continuity gives infinitely
many sign changes tending to the negative cusp. This is stronger
than the one-sign obstruction and does not assume RH.

## Why the terminal Hilbert scale is the moving scale

Fix `0<c<2` and take the sharp admissible grade `q_P=c/P²` from the
terminal admission theorem. On each fixed moving coordinate `u`, the
literal theta first atom gives

```text
k(−log P−u)^(−q_P) → exp(cπ exp(2u)).             (6)
```

Consequently the **pointwise** normalized weighted energy density
of the moving-frame source converges to
`|R_∞(u)|² exp(cπ exp(2u))`. The positive-`u` tail of this limiting
density is integrable exactly when `c<2`: from (3),
`R_∞(u)/k(u)→1` as `u→+∞`, and
`k(u)~4π²exp(9u/2−πexp(2u))`. At `c=2` its residual exponential
factor grows as `exp(9u)`.

The opposite tail has an unconditional **non-`L²` obstruction**:

```text
R_∞ ∉ L²((−∞,0)),
lim_(S cofinal) P ‖k_S‖²_(H_(c/P²)) = +∞
    for every fixed 0<c<2.                         (7)
```

For the first assertion, suppose `R_∞∈L²((−∞,0))`. Its positive tail
has Gaussian decay, so Cauchy–Schwarz makes its Mellin transform
holomorphic on `Re w>0`. On `Re w>3/2` it equals (5). By analytic
continuation, the product identity
`ζ(w−1/2) ℒ_wR_∞=F(w)` holds meromorphically throughout `Re w>0`.
The corpus theorem `exists_riemannZeta_zero_mem_openStrip` supplies
`ρ` with `0<Re ρ<1` and `ζ(ρ)=0`. At `w=ρ+1/2`, the left side has
zero coefficient, while `F(w)=Xi_C(iw)=ξ(ρ+1)≠0`, since
`Re(ρ+1)>1`. This is impossible. Equivalently, (5) has a genuine
pole inside the putative Mellin holomorphy half-plane.

For the second assertion, change variables in the exact finite norm:

```text
P ‖k_S‖²_(H_(c/P²))
  = ∫_ℝ |R_S(u)|² k(−log P−u)^(−c/P²)du.
```

Equations (3) and (6) give pointwise convergence of its nonnegative
integrand to `|R_∞(u)|²exp(cπexp(2u))`, whose integral diverges by
the first assertion. Fatou's lemma gives (7). Each individual norm is
finite by the terminal admission theorem; the divergence is solely a
cofinal transport obstruction. Thus this natural Hilbert boundary
cannot carry the dual source with bounded normalized energy. A
distributional or more singular carrier remains possible.

## Failed producer and surviving question

The conjecture that fixed-stage terminal-word dominance persists
uniformly as `P→∞` fails: equation (1) retains every squarefree word
at `−log P−u`. The stronger conjecture that the cofinal dual source
is a positive boundary producer is false by the sign-change theorem.
Its signed operator (1) and shifted quotient (5) also do not by
themselves supply a reflected spectral orientation.
This does not retire the route. It exposes a precise candidate
signed boundary object and rules out its most direct positive-Hilbert
transport. A viable source-specific cross-grade or phase law must
compare the two coprime atom weights `m^(−1/2)` and `m^(1/2)`
through their one-unit spectral shear, survive the negative-`u`
tail in a more singular topology, and control the original Xi
numerator. Real-ray positivity of the totient coefficients holds
only on the initial absolute-convergence side of the pole at
`w=3/2`; it does not supply such continuation. The already known
[finite-prime causal port](finite-prime-moving-cusp-causal-criterion.md)
is a directed positive-ray atom split at a different moving scale;
it is not the unsplit, reflected source (1). No computation or RH
premise enters these identities. External literature novelty has not
been established.
