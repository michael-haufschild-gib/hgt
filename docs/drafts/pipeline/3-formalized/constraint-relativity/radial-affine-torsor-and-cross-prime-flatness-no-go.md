# Radial affine torsor and cross-prime flatness no-go

- **ID:** `radial-affine-torsor-and-cross-prime-flatness-no-go`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO / POSITIVE SURVIVOR (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [NEW RH-ROUTE LEVERAGE]`
  `[NO RH CLAIM] [FORMALIZED IN LEAN]`
- **Role:** proves cross-grade trivial stabilizers and all cross-prime consistency/curvature data
  determine radial orbit but cannot select absolute critical origin.
- **Novelty:** elementary affine gauge theory. New corpus leverage is exact classification of
  missing datum as absolute radial calibration rather than more relative prime compatibility.

## Theorem 1: two-grade relations are one radial torsor

Let `g,h>0`, `g!=h`, and choose nonzero vectors in distinct graded components. For

\[
 L_\lambda=\mathbb C(x_g+\lambda x_h),
 \qquad \lambda>0,
 \tag{1}
\]

radial character action `Gamma_c(x_q)=q^c x_q` obeys

\[
 \Gamma_cL_\lambda=L_{\lambda(h/g)^c}.
 \tag{2}
\]

Action is free and transitive on family `{L_lambda:lambda>0}`.

### Proof

After scaling by `g^(-c)`, image of generator is

\[
 x_g+\lambda(h/g)^cx_h,
\]

which proves `(2)`. Map `c mapsto (h/g)^c` is isomorphism from additive `R` to positive
multiplicative reals because `h/g!=1`. Hence action is free and transitive. QED.

Thus every member has trivial stabilizer, but no radial-equivariant datum chooses a member.

## Theorem 2: complete cross-prime orbit invariant

Let `P` be set of at least two primes and let radial slope profile be arbitrary function

\[
 b=(b_p)_{p\in P}\in\mathbb R^P.
\]

Radial gauge group acts by

\[
 (c\cdot b)_p=b_p+c\log p.
 \tag{3}
\]

Define normalized differences

\[
 \kappa_{pq}(b)
 =\frac{b_p}{\log p}-\frac{b_q}{\log q}.
 \tag{4}
\]

Then all `kappa_pq` are gauge invariant and complete: profiles `b,b'` lie in same radial orbit if
and only if

\[
 \kappa_{pq}(b)=\kappa_{pq}(b')
 \quad\text{for all }p,q.
 \tag{5}
\]

### Proof

Under `(3)`, each normalized coordinate `b_p/log p` increases by same `c`; differences are
unchanged. Conversely fix base prime `p_0`. If `(5)` holds, then

\[
 \frac{b'_p-b_p}{\log p}
 =\frac{b'_{p_0}-b_{p_0}}{\log p_0}
 =:c
\]

for every `p`; hence `b'=c dot b` by `(3)`. QED.

Thus cross-prime “curvature” `kappa` classifies orbit, not point within orbit.

## Corollary 3: flatness never selects critical slope

Profile is cross-prime flat,

\[
 \kappa_{pq}(b)=0
 \quad\text{for all }p,q,
 \tag{6}
\]

if and only if there exists `a in R` with

\[
 b_p=a\log p
 \quad\text{for every }p.
 \tag{7}
\]

Flat locus is one full radial orbit, not point. For Riemann physical profile

\[
 b_p(\rho)=(2\Re\rho-1)\log p,
 \tag{8}
\]

all cross-prime curvatures vanish identically for every `rho`, on line or off line.

### Proof

If `(6)` holds, normalized coordinates are common constant `a`; this is `(7)`. Converse is
immediate. Substitute `(8)` into `(4)`. QED.

Therefore prime consistency, commensurability, common-slope law, vanishing pairwise curvature,
and any function of complete orbit invariant cannot prove RH. They verify physical profile belongs
to radial character orbit already known.

## Theorem 4: finite algebraic radial invariants are constant

For finite prime set `F`, put

\[
 X_F=(\mathbb C^\times)^F,
 \qquad
 \gamma(t)=(p^t)_{p\in F}.
 \tag{9}
\]

The subgroup `gamma(R)` is Zariski dense in `X_F`. Consequently every rational function on `X_F`
invariant under radial flow is constant.

### Proof

For Laurent polynomial

\[
 P(z)=\sum_{m\in M}a_mz^m,
\]

restriction is exponential polynomial

\[
 P(\gamma(t))
 =\sum_{m\in M}a_m
   \exp\!\left(t\sum_{p\in F}m_p\log p\right).
 \tag{10}
\]

Distinct exponent vectors give distinct real exponents: equality would imply
`product_p p^(m_p-n_p)=1`, hence `m=n` by unique factorization. Distinct exponentials are linearly
independent; derivatives at zero give Vandermonde matrix. Therefore no nonzero Laurent polynomial
vanishes on `gamma(R)`, proving Zariski density.

If rational function is invariant under `gamma(R)`, its algebraic stabilizer contains Zariski
dense subgroup and hence whole torus. Translation action of torus on itself is transitive, so
function is constant. QED.

Thus finite algebraic cross-grade geometry cannot even form nonconstant radial invariant. The
logarithmic curvature `(4)` exists only after choosing analytic branches, and still classifies
orbit rather than origin.

## Theorem 5: trace-one tensor does not frame individual legs

Let `L_+,L_-` be one-dimensional complex spaces and

\[
 0\ne\omega\in L_+\otimes L_-.
 \tag{11}
\]

Factorizations `omega=x tensor y` form `C^times`-torsor

\[
 (x,y)\longmapsto(rx,r^{-1}y).
\]

This fixes tensor, trace normalization, and reciprocal pairing, but moves transverse line

\[
 \mathbb C(x+y)
 \longmapsto
 \mathbb C(x+r^{-2}y).
 \tag{12}
\]

No transverse line in `L_+ direct-sum L_-` is natural from `(L_+,L_-,omega)` alone.

### Proof

If `x tensor y=x' tensor y'` are nonzero pure factorizations of same tensor between lines, unique
`r!=0` satisfies `x'=rx`; tensor equality forces `y'=r^(-1)y`. This proves torsor. Scaling image
generator by `r^(-1)` gives `(12)`. A natural transverse line would be fixed by all torsor
automorphisms, impossible because coefficient ratio ranges over `C^times`. QED.

Applied to trace-one prime/inverse-prime tensor: product normalization does not determine
same-fibre individual-leg frame. Literal Gaussian, relation-kernel calibrator, or equally strong
source datum must do that work.

## Positive survivor: absolute calibration is affine, not curvature datum

To select critical line one needs affine section/origin

\[
 \mathfrak o:
 \mathbb R^P/\mathbb R(\log p)_p
 \longrightarrow\mathbb R^P
 \tag{13}
\]

or equivalent weight-one cocycle comparing profile to source-normal zero. Such section cannot be
constructed from differences `(4)` alone. It must arise from non-translation-invariant source
datum: absolute prime--infinity normalization, fixed analytic dagger, or source anomaly.

For physical flat orbit, asserting calibrated coordinate `a=0` without independently produced
origin is exactly desired conclusion. Hence “more primes” and “flat connection” are theatre unless
calibration provenance is proved.

## Relation to source symmetry

Initial execution built from radial-equivariant data inherits radial action. Theorem 2 identifies
why: all relative prime data descend to orbit quotient. A unique selector must therefore include
source symmetry anomaly or nonunique phase selection beyond orbit invariants.

## Hostile audit

1. This theorem does not construct absolute origin and does not prove RH.
2. It closes multi-prime consistency, pairwise curvature, and trivial-stabilizer arguments as
   selectors.
3. Functional equation already centers coordinate at `1/2`, but it does not prove divisor profile
   equals origin; reflection sends `a` to `-a` and permits nonzero pairs.
4. A canonical source-normal measure or positive folium could supply origin only after literal Xi
   landing is proved; that landing remains RH-bearing.

## Lean-return note

No Lean work authorized. If later requested, affine orbit classification is elementary finite-set
linear algebra; formalize for finite prime packets before any cofinal version.

## Log

- 2026-08-08 — hostile generalized-prime/cross-grade countermodel attack; proof promoted.

## Formalized companion

`radial-affine-torsor-and-cross-prime-flatness-no-go-formalized.md` (same directory).
