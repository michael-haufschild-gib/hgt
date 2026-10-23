# Centered shifted-Möbius distribution at the prime-pair root

- **ID:** twin-prime-centered-root-distribution
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** [twin-prime programme](twin-prime-unconditional-programme-2026-10-23.md)
- **Statement:** The centered discrepancy below has arbitrary logarithmic
  savings when summed over odd squarefree moduli up to `X^(51/100)`.

## Exact candidate

Write `θ_P(n)=log n` for primes and zero otherwise. Define

`B(t)=Σ_{n≤t} θ_P(n) μ(n+2)`,

`F_q(t)=Σ_{n≤t, n≡-2 (mod q)} θ_P(n) μ(n+2) - B(t)/φ(q)`,

`D(X)=Σ_{q≤X^(51/100), q odd and squarefree} sup_{0≤t≤X} |F_q(t)|`.

Conjecture: for every `A>0`, there are `C_A,X_A>0` such that
`D(X)≤C_A X/(log X)^A` for `X≥X_A`.

**Verdict: BRIDGE.** This is a restricted shifted-Möbius distribution
problem, not new terminology for a proven estimate. It might fail even
if twin primes are infinite. No novelty claim or conditional Lean
declaration is made. The residue class and moving endpoint are retained.

## Parent theorem and endpoint audit

[Murty–Vatwani (2017), Theorem 1.1](https://mrammurty-ai.github.io/TwinPrimes-Parity.pdf)
assumes ordinary prime distribution to `X^θ(log X)^C` and centered
shifted-Möbius distribution to `X^(1-θ)`. It states a positive twin-prime
lower bound. Taking `θ=49/100` places the ordinary input within
Bombieri–Vinogradov. Their signed input takes a maximum over all reduced
residues; the switched tail uses only `-2`. Theorem statement and §§4–5
were read from extracted PDF text.

The factor `μ(e)` also removes nonsquarefree moduli. Keeping them would
add avoidable demands: for example, the root class modulo `9` has
`μ(n+2)=0`, so `F_9(t)=-B(t)/6`. An all-modulus bound with arbitrary
logarithmic savings would already force the same savings for `B`.
The present candidate removes that unnecessary requirement.

The first switched-sum display in §4 omits `n>ey-2` after interchanging
the divisor sums. Preserve it. For the long-divisor term the exact form is

`Σ_{e<(X+2)/y, e odd} μ(e) Σ_{ey-2<n≤X, n≡-2 (mod e)}
 θ_P(n) μ(n+2) log(e/(n+2))`.

Thus the full prefix cannot replace the moving interval. This is a proof
audit issue, not a refutation of the theorem's conclusion. The endpoint
problem is also recorded in the public solveathome research; it is not a
new discovery claimed here.

## Reconstruction to check before formalization

Take `y=ceil((X+2)/X^(51/100))`. Every tail modulus is then within the
candidate range. Partial summation on its actual interval bounds the
summed centered error by `O(log X · D(X))`.

After centering, exchange finite sums. The coefficient of
`θ_P(n)μ(n+2)` is

`Σ_{e<(n+2)/y, e odd} μ(e)/φ(e) · log(e/(n+2))`.

For `n>X^(3/4)`, the upper limit exceeds a fixed positive power of `X`.
The usual reciprocal-totient Möbius estimates make this coefficient tend
uniformly to `-S(2)`: the logarithmic sum tends to `-S(2)`, while the
unweighted sum times `log(n+2)` tends to zero. The small prefix has size
`o(X)` using its `O(log²X)` coefficient bound. Together with the short
divisor main term, the proposed conclusion is

`Σ_{n≤X} θ_P(n)θ_P(n+2)=S(2)(X-B(X))+o(X)`.

The standard squarefree-shift density bounds `|B(X)|` by
`(A_2+o(1))X`, where `A_2<1`, giving a positive reserve. All analytic
inputs and their Lean dependencies still require a complete audit; this
card is not a dependency-closed proof of infinitude.

## Attack on the October 2026 operator transfer

The modulus-one term `F_1` is identically zero. Unrestricted cancellation
of `B(X)` therefore supplies no estimate for `D(X)` by itself.

The marked determinant expansion in
[Lü–Wang–Wu, §4.1](https://arxiv.org/html/2610.20242v1)
has `mn+2=ah` and `rs+2=bh`. At the root residue, and for labels coprime
to `q`, the extra conditions reduce to `q|h`. They do not force `a=b`.
In contrast, at a residue `r` with `gcd(r+2,q)=1`, the common cofactor
forces `a≡b (mod q)`, hence equality when both labels lie in an interval
of length less than `q`. These are distinct geometric cases.

In the determinant coordinates `P=(Dbm,s)`, `Q=(Dar,n)`, the condition
`mn≡-2 (mod q)` couples the two vertices. It is not an orthogonal
projection at each endpoint, so restricting an existing operator-norm
bound does not justify the transfer.

Expanding this condition in multiplicative characters separates `m,n`,
but adds conductors up to `X^(51/100)` and requires cancellation across
characters and moduli. Bounding every character separately loses the
needed modulus density. The source's character–Mellin estimate covers
only polylogarithmic conductors.

**[OPEN CORE]** Bound this root-restricted mixed operator moment while
retaining its modulus density, and remove the auxiliary marks with the
required quantitative error. Neither step has been proved.

## Exact character reduction

For odd `q`, put

`B_χ(t)=Σ_{n≤t} θ_P(n) μ(n+2) χ(n)`,

`E_q(t)=Σ_{p≤t, p|q, p prime} log p · μ(p+2)`.

Character orthogonality, including the zero values on nonunits, gives

`F_q(t)=[Σ_{χ≠χ₀ (mod q)} conjugate(χ(-2)) B_χ(t) - E_q(t)]/φ(q)`.

Indeed, the principal-character sum is `B(t)-E_q(t)`. Also
`|E_q(t)|≤Σ_{p|q}log p≤log q`, uniformly in `t`. Thus replacing `D(X)`
by the corresponding sum of absolute nonprincipal-character combinations
changes it by at most `Σ_{q≤X^(51/100)} log q/φ(q)=O(log²X)`.
The modulus-one sum is empty. This exact reduction does not take absolute
values separately in the character sum.

For a squarefree modulus and the root relation `mn+2=qh`, the coefficient
is exactly `μ(q)μ(h)` when `(q,h)=1` and zero otherwise. Retaining this
cofactor form exposes a four-variable determinant relation; it does not
make the coefficient separable in `m,n`.

## Exact dual form of the unresolved estimate

The supremum in each `F_q` may be taken over integer endpoints. Since
there are finitely many moduli and endpoints, `D(X)` is the maximum,
over choices `ε_q∈{-1,1}` and `0≤t_q≤floor X`, of

`Σ_q ε_q μ(q) Σ_{4≤qh≤t_q+2, (q,h)=1} μ(h) θ_P(qh-2)
 - Σ_q ε_q B(t_q)/φ(q)`.

Both outer sums use precisely the odd squarefree moduli in `D(X)`.
This follows from the root substitution `n+2=qh`, with the zero Möbius
value when the factors are not coprime. In particular, replacing the
root term by an arbitrary unstructured sequence discards usable
multiplicativity in the long cofactor `h`.

On a dyadic prime interval of size `X`, a modulus of size `X^(51/100)`
has cofactor size `X^(49/100)`. A divisor decomposition of the prime
weight produces the literal relation `qh-mn=2`. Its arithmetic weights,
coprimality restriction, and centered term must be retained together.
No estimate for this signed determinant sum has been obtained here.

## Cofactor Gram calculation

Fix a finite set `Q` of odd squarefree moduli and one integer endpoint
`0≤t_q≤X` for each modulus. Put

`I_q(h)=1_{4≤qh≤t_q+2} 1_{gcd(q,h)=1}`,

`A_q=Σ_h μ(h) θ_P(qh-2) I_q(h)`,

`b_q=μ(q)B(t_q)/φ(q)`.

Then `F_q(t_q)=μ(q)(A_q-b_q)`. In the dual expression, multiplication
of each arbitrary sign by `μ(q)∈{-1,1}` is a bijection on the choices of
signs. Thus multiplicativity in the *outer modulus sign* supplies no
extra cancellation for this absolute-value target. The cofactor sign
`μ(h)` still matters. The centered term changes with the same sign;
it cannot be dropped in making this observation.

The exact quadratic expression is

`Σ_{q∈Q}|F_q(t_q)|² = Σ_{h,k} μ(h)μ(k)G(h,k)
 - 2Σ_{q∈Q} b_q A_q + Σ_{q∈Q}b_q²`,

where

`G(h,k)=Σ_{q∈Q} θ_P(qh-2)θ_P(qk-2) I_q(h)I_q(k)`.

This retains the actual endpoints and all coprimality restrictions.
Its diagonal is exactly

`Σ_{p≤X, p prime} (log p)² μ²(p+2)
 #{q∈Q : q|(p+2), p≤t_q}`.

Indeed, for squarefree `q`, the diagonal factor
`μ²(h)1_{gcd(q,h)=1}` equals `μ²(qh)`. The divisor bound and Chebyshev's
estimate bound this diagonal by `O_ε(X^(1+ε)log X)`. For a dyadic block
of `O(Q)` moduli with `Q≤X^(51/100)`, its contribution to the
Cauchy–Schwarz bound for the first moment is therefore smaller than
`X` by a fixed power, after choosing a sufficiently small fixed `ε`.
The problem is the *centered off-diagonal combination*, not this
diagonal estimate. Bounding the cross term and `Σ b_q²` separately
loses the centering; at `q=1` their cancellation is exact.

For fixed `h≠k`, the off-diagonal kernel counts the two prime linear
forms `qh-2` and `qk-2`, with the signed coefficient `μ(h)μ(k)` outside.
An upper-bound sieve followed by absolute values discards that
coefficient. Neither a prime-pair asymptotic for every `(h,k)` nor the
required signed average has been established here. An adequate
mean-square estimate, uniform in the individual endpoints, would be a
new analytic input; the displayed expansion is not such an estimate.

## Shared factors in a marked determinant expansion

Let `a` be a squarefree selected divisor from a marked expansion and
let `q` be one of the squarefree root moduli. Write

`j=gcd(a,q)`, `r=q/j`, `ell=lcm(a,q)=ar`.

The simultaneous conditions `a|(mn+2)` and `q|(mn+2)` are precisely
`mn+2=ell k`. Their Möbius coefficient is
`μ(ell)μ(k)1_{gcd(ell,k)=1}`. This formula includes labels sharing
primes with `q`; replacing `ell` by `aq` would omit those terms.
If a weight contains `ρ^ω(mn+2)`, it becomes
`ρ^ω(ell)ρ^ω(k)` on that coprime support. Endpoint `t_q` remains
attached to the original modulus, even when several `(a,q)` give the
same `ell`.

After squaring in a common cofactor, two labels `ell_1,ell_2` satisfy
`ell_2(mn+2)=ell_1(rs+2)`. Set `g=gcd(ell_1,ell_2)` and
`u=ell_1/g`, `v=ell_2/g`. The determinant equation is

`v mn-u rs=2(u-v)`.

It only forces a common integer
`s_0=(mn+2)/u=(rs+2)/v`; the original common cofactor additionally
requires `g|s_0`. Thus the determinant equation alone is insufficient
on shared-factor strata. The equal-label stratum includes distinct
marked-divisor/modulus representations of the same label. No estimate
allowing these strata to be deleted has been proved.

## Kloosterman interface audit

The fresh corpus query for the determinant mechanism surfaced
`RHTower.Sieve.kloostermanHybridBilinear_eq_inverseResidueCorrelation`
and `kloostermanSharedHybridModulusBilinear_eq_inverseResidueCorrelation`
in `RHTower/Sieve/KloostermanSharedHybridCollapse.lean`. Their source
statements were checked. Completing both Fourier legs returns exactly
the inverse-residue correlation, scaled by the square of the modulus.
This is a warning against treating an exact Fourier rewrite as an
additional cancellation estimate. The inspected fixed-modulus bound
`norm_kloostermanBilinear_le` gives the baseline `q‖a‖₂‖b‖₂`.

[Blomer–Pascadi, Theorems 1.1 and 5.5](https://arxiv.org/html/2607.24311v1)
bound Kloosterman bilinear forms whose frequency coefficients lie in
specified intervals, with a coprimality restriction. Their square-root
frequency range has a power saving. Our complete Fourier coefficients
have not been confined to those ranges: interval support of the
original Möbius coefficients does not imply interval support of their
Fourier transforms. A point mass already has nonzero Fourier transform
at every frequency. The required localization and its error are open.

[Duke–Friedlander–Iwaniec, Theorems 1–3](https://www.math.ucla.edu/~wdduke/preprints/bilinear.pdf)
instead bound separated two-variable Kloosterman fractions, with fixed
phase numerator. The Gram expression above has not been transformed
into that form with controlled norms, endpoints and shared factors.
Their separate determinant paper was retrieved, but text extraction
returned no text; no claim based on its theorem statements is made.

These checks do not refute the centered-distribution conjecture. They
identify unfilled hypotheses in proposed applications of existing
estimates. No analytic frontier has moved, and no new Lean declaration
has been added for these routine finite reductions.

## Next research action

The [mark-preserving root-average deduction](../2-fully-proven/twin-prime-mark-preserving-root-average.md)
establishes a more specific transfer on paper: for moduli coprime to all marking
primes, the root restriction becomes divisibility in the common
cofactor. A positive-energy argument then averages the moduli without
a square-root loss in their number. Its paper proof includes the
weighted energy, Type I estimates, and a checked application of the
cited signed source energy. Its analytic dependencies are not yet
formalized in Lean.

For the unmarked target, attack the centered off-diagonal combination
above. Keep `μ(h)μ(k)`, individual endpoints and the `g|s_0`
shared-factor condition. The marked candidate cannot remove these
requirements from the full problem. Any Fourier estimate must include
every frequency range and the norms of its actual coefficients. It
must also handle small moduli without replacing qualitative
`B(X)=o(X)` by an unproved arbitrary-logarithmic rate. Do not add the
missing estimate to Lean.
