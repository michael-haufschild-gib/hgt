# Hyperbolic-gap flat completion of the Gamma prime pair

- **ID:** `stc-hyperbolic-gap-flat-completion`
- **Stage:** 3-formalized
- **Type:** exact source reinterpretation and uniqueness theorem
- **Routes:** STC, Gamma-six/Sonin source lift
- **Status:** `[PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`

## Source and proposed reinterpretation

At common valuation depth `e`, put `n=e+1`, `x=log p`, `y=log q`, and let `B_p,B_q` be the positive literal Gamma amplitudes in `DeningerGammaAllPrimeStokesPairBridge.lean`. Its reflection-odd exterior satisfies, for `p<q`,

```text
S_pq,e(g)/(B_p B_q)
  = n(y-x)/2 · sinh[g(x+y)/2].                         (1)
```

The physical log-height gap `y-x` is the only obstruction to making this normalized pair a difference of one-prime potentials. Let `S(t)=sinh(t)/t`, with `S(0)=1`, and multiply (1) by the positive **gap factor** `S(g(y-x)/2)`. The hyperbolic difference formula yields the division-free identity

```text
g S(g(y-x)/2) S_pq,e(g)/(B_p B_q)
  = n/2 [cosh(gy)-cosh(gx)].                           (2)
```

Thus the corrected pair is an exact coboundary of the source-defined one-prime potential `V_g(p)=cosh(g log p)` at **every** real grade, including `g=0` in the division-free form. The correction is positive and tends to one for a shrinking prime log gap. It is pair-dependent, so it is compatible with the earlier proof that one-prime diagonal rescaling cannot calibrate every source pair.

## Rigidity of the gap factor

Fix `g≠0`. Suppose a continuous function `F:[0,∞)→ℝ` with `F(0)=1` has the property that, for every `0<x<y`,

```text
(y-x) F(y-x) sinh[g(x+y)/2] = Φ(y)-Φ(x)               (3)
```

for some one-prime potential `Φ:(0,∞)→ℝ`. Then necessarily

```text
F(d)=S(gd/2)  for every d≥0,
Φ(x)=cosh(gx)/g + constant.                              (4)
```

Indeed the difference quotient of (3) as `y↓x` gives `Φ'(x)=sinh(gx)`; continuity of `F` at zero is all that is needed. Integration gives the displayed potential. The identity

```text
cosh(gy)-cosh(gx)
  = 2 sinh[g(x+y)/2] sinh[g(y-x)/2]
```

and nonvanishing of the sum-phase sine on `0<x<y`, `g≠0`, then force (4). This is the unique continuous gap-only normalization equal to one at coincidence that makes the literal normalized Gamma pair exactly flat for all positive real log coordinates. The following theorem recovers uniqueness from actual prime labels alone.

### Prime-only rigidity (stronger form)

The same uniqueness holds if (3) is required **only at ordered prime logarithms**, with an arbitrary potential defined on the primes. Precisely, let `g≠0`, let `F:[0,∞)→ℝ` be continuous with `F(0)=1`, and suppose

```text
(log q-log p) F(log q-log p)
  sinh[g(log p+log q)/2] = Φ(q)-Φ(p)                 (4a)
```

for every pair of primes `p<q`. Then `F(d)=S(gd/2)` for **every real** `d≥0`. The conclusion needs no continuity or growth assumption on the prime potential `Φ`.

Put `a=|g|>0` and `A(d)=d F(d) exp(ad/2)`. For any fixed `d,e>0`, the corpus's PNT consequence `prime_between` supplies cofinal prime triples `p<q<r` with `q/p→exp(d)` and `r/q→exp(e)`: choose `p→∞`, then primes in multiplicative windows of relative width tending to zero around `exp(d)p` and `exp(d+e)p`. The potential in (4a) cancels around each triangle. Dividing that identity by `p^a`, using the exponential form of `sinh`, and passing to the limit through continuity of `F` gives

```text
A(d+e)=A(d)+exp(ad) A(e).                          (4b)
```

For negative `g`, the common minus sign of the three `sinh` terms cancels, so (4b) is unchanged. Interchanging `d,e` in (4b) gives

```text
A(d)/(exp(ad)-1)=A(e)/(exp(ae)-1)                 (4c)
```

for all `d,e>0`. The common ratio is `1/a`, because `A(d)/d→F(0)=1` and `(exp(ad)-1)/d→a` as `d↓0`. Thus `A(d)=(exp(ad)-1)/a` and

```text
F(d)=[exp(ad)-1]/[ad exp(ad/2)]
    =sinh(ad/2)/(ad/2)=S(gd/2).
```

PNT is used only to realize arbitrary limiting prime-log gaps. The flat completion is forced by the actual all-prime triangle law, without extending that law to fictitious real prime labels.

## Relation to the canonical Xi seam

Let `ρ=1/2+g+iτ` with real `g,τ`. The corpus defines

```text
u_p(ρ)=orbitwiseNatPrimeSeamCharge p ρ
      =(log p)[p^(-conj ρ)-p^(-(1-ρ))].
```

Direct exponent algebra and differentiation of `V_g` give the exact identity

```text
u_p(ρ) = -2 p^(-1/2+iτ) ∂_g V_g(p).                  (5)
```

So the canonical **complex** seam is the grade derivative of the flat Gamma potential, followed primewise by the critical half-density and vertical phase. The grade derivative and phase twist must act on each one-prime section **before** taking the exterior difference; applying a common scalar to an already-formed pair does not implement (5).

Equation (5) suggests a concrete source-to-Sonin task: construct one source-defined operator family carrying `V_g(p)` with a controlled grade derivative and a coefficient-faithful critical phase twist, then prove the resulting all-prime exterior has sub-root Calkin growth on Xi-divisor fibres. Equations (2) and (5) give the exact algebraic target. They do not construct that operator family or establish the needed Calkin bound. The pairwise analytic Stokes scalar `c_pq(g)` has nonzero cofinal triangle holonomy by the [all-grade theorem](stc-cofinal-triangle-holonomy-all-grades.md), so it cannot simply replace the flat source pair in this construction.

## Operator-domain and positivity tests

The correction in (2) is positive **entrywise**, but is not positive as a two-prime Schur kernel. For `g≠0` and distinct log coordinates `x,y`, put `s=S(g(y-x)/2)>1`. The two-point matrix with diagonal `1` and off-diagonal `s` has quadratic values `2(1-s)<0` on `(1,-1)` and `2(1+s)>0` on `(1,1)`. The inequality `S(t)>1` for every `t≠0` follows from `sinh(t)>t` for `t>0` and evenness. Thus the **unique** gap-only flat correction cannot be implemented by a positivity-preserving Schur multiplier even on two primes. [HyperbolicGapFlatCompletion.lean](../../../../formal/GaloisForLFunctions/HTGeometry/HyperbolicGapFlatCompletion.lean) proves the strict factor inequality and both quadratic signs without assumptions beyond `t≠0`.

The [full-packet signature theorem](stc-hyperbolic-gap-krein-signature.md) strengthens this two-point failure: every `N`-prime gap-sinc matrix is nonsingular with `ceil(N/2)` positive and `floor(N/2)` negative directions. The source correction therefore has an infinite-index indefinite geometry in any completion retaining all finite prime packets.

The [exterior spectral reader theorem](stc-flat-gap-exterior-spectral-reader.md) identifies the corresponding topological obstruction. Reflection makes the gap kernel a positive Hilbert Gram with spectral band `[-|g|/2,|g|/2]`, but the canonical seam is derivative evaluation at `±|g|` and is nonclosable in that norm. Prime-log uniqueness further rules out bounded recovery from **any** finite compact spectral band, even one enlarged to contain those evaluation points.

There is also a sharp scalar prime-Hilbert boundary. Use the actual depth-zero primitive amplitude `b_u(p)=xiGammaEulerPrimitiveBoundaryAmplitude u (p,0)` and define, for `g≠0`,

```text
F_{u,g}(p,q)=b_u(p)b_u(q)
               [cosh(g log q)-cosh(g log p)].             (6)
```

The matrix (6) defines a bounded operator on ordinary `ℓ²(primes)` **if and only if** `u>2|g|`; there it has rank at most two and is compact. Indeed it is the wedge of `b_u` and `b_u cosh(g log p)`. The source amplitude law gives `b_u(p)^2=(log p)^2 p^(-1-u)` and `b_u(p)p^a=b_{u-2a}(p)` for `a=|g|`. Since `cosh(g log p)≤p^a` and the corpus proves `b_v∈ℓ²` exactly for `v>0`, both wedge vectors are Hilbert when `u>2a`. Conversely, fixing any prime `q` and taking `p` large gives

```text
|F_{u,g}(p,q)| ≥ [b_u(q)/4] b_{u-2a}(p),
```

because `cosh(a log p)≥2 cosh(a log q)` eventually and `cosh(a log p)≥p^a/2`. At `u≤2a`, this column is not square-summable, so no bounded operator has these matrix entries. At `g=0` the matrix vanishes, explaining the qualification. This is the exact domain price of the **flat** completion; the prior [Gamma-prime Hilbert chamber](stc-gamma-prime-hilbert-chamber.md) treated the uncorrected two-channel kernel and the analytic Stokes gauge instead.

The critical half-density does not solve the Calkin problem by itself. At physical `u=0` and every `|g|<1/2`, both prime vectors

```text
a_p = b_0(p)/sqrt(p),
d_p = a_p (log p) sinh(g log p)
```

belong to `ℓ²(primes)`: their squared tails are bounded by constants times `(log p)^2/p²` and `(log p)^4/p^(2-2|g|)`, respectively. Thus the critically weighted source wedge and its grade derivative are finite-rank, hence trace-class, in this scalar prime Hilbert model throughout the entire Xi strip. Vertical factors `p^(iτ)` are unitary diagonal and do not change that conclusion. Any **bounded, compactness-preserving** transport from this particular model to the Sonin carrier therefore cannot produce the nonzero off-neutral Calkin class already proved for the canonical seam. A successful source lift has to use a different operator representation or a mathematically controlled singular decompactification; this statement does not rule out either.

## Audit

- Literal source pair and its amplitude/height formulas: `DeningerGammaAllPrimeStokesPairBridge.lean` and `CCMFirstClockPrimitivePromotedExteriorSource.lean`.
- Positive hyperbolic-sinc source function: `RouteRDeningerBVGreenPositiveUnitComparison.lean`.
- Canonical complex seam: `XiPrimeSeamCoherenceCollapse.lean`.
- [HyperbolicGapFlatCompletion.lean](../../../../formal/GaloisForLFunctions/HTGeometry/HyperbolicGapFlatCompletion.lean) formalizes the real hyperbolic difference identity, exact triangle flatness, grade derivative, two-prime Schur indefiniteness, and uniqueness of the normalized exponential cocycle (4b); the module passed `lake env lean` and is wired into the HTGeometry umbrella without building that umbrella. Importing the full source bridge in scratch was blocked by the missing `PrimeDepthBVWoldSourceDaggerAtlasTransition.olean`. The prime-ratio transfer to (4b), source specialization, complex charge identity, and prime-Hilbert domain classification remain paper-only.
- Deep corpus and targeted source searches found the relevant ingredients, but no statement of (2)–(5) together. External priority is not claimed.

## Log

- 2026-09-27: (1)–(6), continuous and prime-only rigidity, complex seam identity, domain classification and critical half-density wedge formalized unconditionally (`HyperbolicGapFlatCompletion.lean`, `STCHyperbolicGapFlatCompletionSource.lean`, shared `LpTwoMatrixOperators.lean`); certificate `stc-hyperbolic-gap-flat-completion-formalized.md`; moved to stage 3.
