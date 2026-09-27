# Sharp Hilbert chamber of the literal two-channel Gamma kernel

- **ID:** `stc-gamma-prime-hilbert-chamber`
- **Stage:** 3-formalized
- **Type:** exact operator-domain classification and scoped STC obstruction
- **Routes:** STC, RHist, Gamma/Sonin
- **Status:** `[PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]`

## Source and question

On the depth-zero prime face let

```text
b_u(p) = xiGammaEulerPrimitiveBoundaryAmplitude u (p,0) > 0,
Q_{u,g}(p,q) = b_u(p)b_u(q) sinh[g(log p+log q)/2].
```

The exact source-amplitude law in
`CCMFirstClockPrimitivePromotedExteriorSource.lean` gives

```text
b_u(p)^2 = (log p)^2 p^(-1-u),
b_u(p) p^(a/2) = b_{u-a}(p).                         (1)
```

At `u=0`, `Q` is the two-channel kernel of the literal equal-depth
reflection-odd Gamma exterior proved in
`DeningerGammaAllPrimeStokesPairBridge.lean`. For `u≠0` this is its
natural extension using the literal displaced source amplitudes; no
source-to-Sonin identification is asserted for that extension. We
classify whether this specific kernel, at any displacement and nonzero
common local grade, defines a bounded operator on the unweighted prime
Hilbert space.

## Theorem: compact interior, inadmissible boundary

For real `u,g` with `g≠0`, the following are equivalent:

1. `u>|g|`.
2. Both source channels `p ↦ b_{u-g}(p)` and `p ↦ b_{u+g}(p)` lie in
   `ℓ²({primes})`.
3. Every fixed-prime column of `Q_{u,g}` lies in `ℓ²({primes})`.
4. The matrix `Q_{u,g}` defines a bounded operator on `ℓ²({primes})`.

Whenever these conditions hold, the operator has rank at most two and
is compact. When `u≤|g|`, **no bounded operator** has this matrix:
every fixed-prime column fails to lie in `ℓ²`. At `g=0`, `Q_{u,0}=0`
for every `u`, so the nonzero-grade qualification is essential.

### Proof

The hyperbolic formula and (1) give the exact, source-selected
two-channel decomposition

```text
Q_{u,g}(p,q)
  = [b_{u-g}(p)b_{u-g}(q)-b_{u+g}(p)b_{u+g}(q)]/2.     (2)
```

The existing sharp primitive-source theorem
`summable_sq_xiGammaEulerPrimitiveBoundaryAmplitude_iff` proves
`∑_p b_v(p)^2<∞` exactly when `v>0`: its necessity proof uses this
depth-zero face, and its sufficiency covers all prime depths. Thus
both vectors in (2) are Hilbert exactly when `u>|g|`. In that chamber,
(2) is a difference of two bounded rank-one operators, hence compact.

For necessity set `a=|g|>0`. Up to an overall sign, (2) becomes

```text
Q_{u,g}(p,q)
  = b_{u-a}(p)b_{u-a}(q) [1-(pq)^(-a)]/2.             (3)
```

For each fixed prime `q` and all primes `p≥2`, the bracket is at
least `1-(2q)^(-a)>0`. Therefore the square of this column dominates
a positive constant times `b_{u-a}(p)^2`. If `u≤a`, the sharp source
threshold makes that series diverge. A bounded operator would send
the standard basis vector at `q` to this column in `ℓ²`, impossible.
This proves all implications and the sharp boundary without any
asymptotic prime-gap argument.

## Theorem: scalar boundary renormalization has only the zero strong limit

Fix `g≠0`, put `a=|g|`, and approach the chamber wall with
`u=a+v`, `v↓0`. Write `x_v=b_v`, `y_v=b_{v+2a}`, and let
`P_z(w)=⟨z,w⟩z` on the real prime Hilbert space. Equation (2) reads

```text
Q_{a+v,g} = sign(g) [P_{x_v}-P_{y_v}]/2.             (4)
```

The norm of `x_v` tends to infinity. Indeed `b_v(p)^2` increases
pointwise to `b_0(p)^2` as `v↓0`, and the latter prime sum diverges by
the sharp source theorem. Meanwhile `‖y_v‖≤‖b_{2a}‖<∞`. Hence

```text
2‖Q_{a+v,g}‖/‖x_v‖² → 1.                         (5)
```

Set `e_v=x_v/‖x_v‖`. Every fixed prime coordinate of `e_v` tends to
zero, while `‖e_v‖=1`; density of finite-support vectors implies
`e_v ⇀ 0`. Therefore `P_{e_v}→0` in the **strong** operator topology,
although each projection has norm one. From (4),

```text
2Q_{a+v,g}/‖x_v‖² → 0 strongly,
‖2Q_{a+v,g}/‖x_v‖²‖ → 1.                         (6)
```

More generally, if any scalar family `c_v Q_{a+v,g}` has a bounded
strong-operator limit as `v↓0`, that limit is zero. The uniform
boundedness principle and (5) force `|c_v|‖x_v‖²=O(1)`, hence
`c_v→0`. The first term of `c_v Q` is a bounded scalar multiple of
`P_{e_v}` and tends strongly to zero; the second tends to zero in
operator norm because `‖y_v‖` is bounded. Without a compensating
scalar, the norms in (5) diverge, so `Q` itself has no bounded strong
limit.

This excludes scalar singular rescaling of this exact source-amplitude
extension as a way to obtain a nonzero bounded Sonin seam. It does not
exclude prime-dependent renormalization, nonlocal mixing, a different
carrier, or a singular physical reader; those require source-derived
definitions and fresh domain proofs.

## Theorem: the analytic Stokes gauge has a second, sharper wall

Let `c_pq(g)=routeRCrossPrimeStokesOddCurvature p q g` be the existing
analytic pair scalar and put

```text
C_{u,g}(p,q)=b_u(p)b_u(q)c_pq(g)=-2 Q_{u,g}(p,q)G_pq(g),
G_pq(g)=R_pq(g)+R_pq(g)^(-1)>0.
```

For `g≠0`, the **source-weighted analytic curvature** defines a
bounded operator on prime `ℓ²` exactly when `u>2|g|`. In that chamber
it has rank at most four and is compact. At `u≤2|g|`, every
fixed-prime column is non-square-summable, so no bounded operator
has these entries.

To prove this, set `a=|g|`, `s_p=sinh(a log(p)/2)>0`, and
`d_p=cosh(a log(p)/2)`. The corpus's exact Stokes ratio simplifies to
`R_pq=s_q/s_p`. Its four-channel identity expresses `c_pq`, up to
the sign of `g`, as `-2` times

```text
s_p d_p + s_q d_q + s_p²(d_q/s_q) + (d_p/s_p)s_q².  (7)
```

For primes `p≥2`, `s_p d_p` and `s_p²` are bounded above by a
constant times `p^a`, while `d_p/s_p` is uniformly bounded. By
(1), every one-prime vector in the four rank-one terms of
`C_{u,g}` is in `ℓ²` when `u>2a`. Conversely, for fixed `q`, the
positive expression (7) contains `(d_q/s_q)s_p²`. Since

```text
s_p ≥ [1-2^(-a)]p^(a/2)/2,
```

that column's absolute value dominates a positive constant times
`b_u(p)p^a=b_{u-2a}(p)`. The sharp source threshold proves its
non-summability when `u≤2a`.

The **ordered** kernel obtained by changing the sign below the
prime-order diagonal and setting the diagonal to zero has the same
threshold. In the admitted chamber, its entrywise absolute values
are bounded by those of the rank-four kernel, which is
Hilbert--Schmidt; hence the ordered kernel is Hilbert--Schmidt and
compact, although its finite prime packets can have unbounded
rank. Outside the chamber, deleting one diagonal entry from each
column cannot repair non-summability. This reconciles the prior
`stc-ordered-curvature-unbounded-rank.md` theorem with the absence
of a nonzero Calkin class: **growing finite rank is not enough when
the entire all-prime matrix remains Hilbert--Schmidt.**

In particular, bounded left/right transport from this admitted
prime operator into a Sonin carrier still gives a compact operator,
because compact operators form a two-sided ideal. A nonzero
essential-spectrum seam cannot emerge from this source matrix by
bounded transport alone. A proposed transfer must identify the
specific singular boundary operation or a different infinite source
whose domain includes the physical Xi reader.

## Consequence for the proposed Calkin seam

The literal depth-zero `Q_{0,g}` lies outside the bounded-operator
algebra for every `g≠0`; every admitted `Q_{u,g}` is compact and has
zero Calkin class. Consequently this **raw two-channel Gamma kernel**
cannot itself be the nonzero essential-spectrum reporter required by
the STC Sonin endpoint. The same source exterior additionally carries
the height difference `h_p-h_q`. In the admitted chamber its matrix is
still finite rank and compact: choose `0<ε<u-|g|` and use
`(log p)^2≤C_ε p^ε` to put the height-weighted channels in `ℓ²`;
expanding `(h_p-h_q)Q_{u,g}` then gives at most four rank-one terms.
This is a classification of the raw prime kernel, not a no-go theorem
for a different, nonlocal Sonin construction.

The earlier prime-height commutator ghost is a general bounded-operator
obstruction. The present theorem makes its scope precise for the
actual source: in the ordinary prime `ℓ²` representation, the raw
critical kernel is not even in that commutator's bounded domain, and
the displaced kernel is compact. An RH-producing step would have to
derive a new source-faithful boundary operation, with a specified
domain and physical Xi reader, that survives the singular limit.
The existing primitive-source-to-Xi pairing in
`EulerPrimitiveJointDepthHilbertSource.lean` is proved for `u>0` and
reads the continued source at `s=1+u`; it supplies no such boundary
operator or zero-forced Hilbert admission.

## Audit

- Exact amplitudes and literal exterior: the two Lean source modules
  cited above.
- Sharp full-source Hilbert threshold:
  `EulerPrimitiveJointDepthHilbertSource.lean`, including its
  depth-zero necessity proof.
- Equations (1)--(7), both sharp column thresholds, both operator
  classifications, and the scalar-limit obstruction are
  dependency-closed paper proofs.
  Their specific Lean formalization is pending. No theorem about RH,
  source-to-Sonin identification, or Calkin sub-root growth is claimed.

## Log

- 2026-09-27: chamber equivalences, compact rank-two interior, column obstruction, scalar wall renormalization (strong limits, uniform boundedness), analytic Stokes wall `u > 2|g|` with rank four, ordered Hilbert--Schmidt kernel, unbounded packet rank and the height-weighted exterior formalized unconditionally (`STCGammaPrimeHilbertChamber.lean`, `STCGammaPrimeWallScaling.lean`); certificate `stc-gamma-prime-hilbert-chamber-formalized.md`; moved to stage 3.
