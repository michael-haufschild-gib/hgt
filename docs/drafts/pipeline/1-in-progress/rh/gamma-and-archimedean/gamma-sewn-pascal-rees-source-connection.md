# Gamma-sewn Pascal--Rees source connection

- **ID:** `gamma-sewn-pascal-rees-source-connection`
- **Stage:** 1-in-progress
- **Type:** PAPER THEOREMS + CONJECTURE
- **Scientific status:** `[CORPUS-NEW COMPOSITION] [EXTERNAL PRIORITY UNVERIFIED] [NOT RH YET]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusReesMappingCone.lean`
- **Source inputs:**
  `GammaSewnMobiusValuationContraction.lean`,
  `XiShiftPrimeHypertranscendence.lean`,
  `InverseTiltedPrimeGammaCentralSource.lean`,
  `BakerWeldIndependence.lean`, and the causal--lcm/FCRJ chain in
  `critical-multiplicative-compensated-cancellation-rh.md`.

## Anti-theatre verdict

The local ingredients are classical: binomial thinning, geometric probability generating
functions, diagonal Dirichlet shifts, twisted derivations, Laplace--Carleson analysis, Douglas
factorization, Hankel difference-of-squares factorizations, and Potapov/Julia signature
conversion.  None of those is new and none proves RH.

The source-specific composition below was not found in the corpus or in exact primary-literature
searches.  The scientific delta is the simultaneous identification of:

1. the true-aperture valuation feature as a geometric law transported by a canonical Pascal
   connection;
2. the infinitesimal connection rate as the exact inverse of its aperture normalization;
3. the causal `log p` label as the finite part of the same connection;
4. the filtered von Mangoldt stream as a forced two-endpoint Rees mapping cone; and
5. the inverse-tilted finite source as necessarily non-scalar before any Hilbert norm.

Search noncollision is not a priority claim.  The RH-bearing contraction remains conjectural.

## Exact local Pascal connection `[PAPER-PROVED]`

For `0<x<y`, a prime `p`, and

```text
q_x=p^(-x),  q_y=p^(-y),
a_(x,y,p)=q_y(1-q_x)/(q_x(1-q_y)),
phi_a(z)=1-a+a*z,
g_x(z)=(1-q_x)/(1-q_x*z),
```

one has

```text
0<a_(x,y,p)<1,
a_(x,y,p)*a_(y,z,p)=a_(x,z,p),
g_x(phi_a(z))=g_y(z).                                  (P1)
```

Thus binomial thinning of the valuation count transports the geometric aperture law exactly.
Pullback by `phi_a` preserves multiplication and acts on the local Möbius/Koszul factor by

```text
P_a((1-z)f)=a(1-z)P_a(f).                              (P2)
```

The local operation therefore respects Euler multiplication and every Koszul grade.  It is not a
finite reporter and it does not erase the all-order prime-log Rees rank.

For the existing Gamma-sewn multiplier `C_(x,p)`, the scaled connection

```text
T_(x,y,p)=(C_(y,p)/C_(x,p))*P_(a_(x,y,p))              (P3)
```

maps the Gamma-sewn geometric ray at `x` exactly to the ray at `y` and composes on every aperture
triple.  The Gamma scalar is projective: it commutes with every physical height projection, so it
does not alter the support-boundary curvature created by compressing the Pascal connection.

## Exact generator and source recovery `[PAPER-PROVED]`

The infinitesimal death rate of `(P1)` is

```text
lambda_(x,p)=log(p)/(1-p^(-x)).                         (P4)
```

For every valuation depth `e`, this rate cancels the geometric normalization exactly:

```text
lambda_(x,p)*(1-p^(-x))*p^(-x*e)
  =log(p)*p^(-x*e).                                    (P5)
```

Consequently the generator applied before Gram formation turns a normalized true-aperture ray
into its full logarithmic prime-power ray.  On the existing fixed-critical Möbius feature,

```text
lambda_(x,p)*B_x(p,e)
 =C_(x,p)/(p+1)*log(p)*p^(-x*e).                       (P6)
```

At unit aperture this is a uniformly invertible damping of
`Lambda(p^(e+1))/p^(e+1)`; no `sqrt p` coordinate recovery occurs.

The projective finite part of the same generator is the causal label:

```text
2*(lambda_(x,p)-1/x) -> log(p)       as x->0+.         (P7)
```

For a squarefree support `l`, summing `(P7)` over its occupied prime coordinates gives `log l`.
If `P_H` projects onto multiplicative height at most `H`, the compressed pure-death generator has
the exact boundary law

```text
[P_H,L_x]e_T
 =sum_(p in T, height(T\{p})<=H<height(T))
    lambda_(x,p)e_(T\{p}).                             (P8)
```

Applied to the signed Koszul vector, `(P8)` is the first-crossing boundary with its Möbius signs
already joined.  After `(P7)`, its edge weight is exactly `log p`; successive future dressing adds
these weights to `log l`.  This identifies the previously external causal/lcm logarithmic label as
the finite-part curvature of the same true-aperture connection that carries the Hilbert source.

The two-prime tests are exact.  If `p<=H<q`, the compressed curvature of
`(1-e_p)(1-e_q)` is `-lambda_(x,q)(1-e_p)`; if `p,q<=H<pq`, it is
`lambda_(x,q)e_p+lambda_(x,p)e_q`.  No scalar prime vector remains.

## One-edge scalar source production is false `[PAPER-PROVED NO-GO]`

The diagonal Dirichlet aperture transport

```text
(U_h f)(p,e)=p^(-h(e+1))*f(p,e)
```

is a compact injective fusion character with `||U_h||=2^(-h)`, `||I-U_h||=1`, and a twisted
Leibniz aperture difference.  On the Gamma-sewn source its one-edge coefficient is one geometric
valuation character.  Any scalar postcomposition therefore has ratio `p^(-y)<1` between the
`p^2` and `p` depths.  The actual filtered von Mangoldt factor has ratio

```text
(1-p^(-4))/(1-p^(-2))=1+p^(-2)>1.                     (N1)
```

So no scalar one-edge functional can produce even the first two valuation coefficients.  Making
the whole source horizontal is worse: twisted Leibniz then kills the algebra generated by every
singleton source.  Both scalar-edge variants are retired.

A separate two-prime test kills a prime-blind scalar Stokes weight for the inverse-tilted dyadic
source.  At apertures `0,1`, depth zero,

```text
d_p=B_1(p,0)=(p-1)/(p*(8*(p^4+1))^(1/4)).              (N2)
```

Matching the exact `n=2,3` inverse-tilted coefficients with one scalar would give a nontrivial
algebraic linear relation between `log 2` and `log 3`, contradicting the existing formalized
two-prime Baker theorem.  Hence no prime-blind scalar edge can be the coefficient converter.

## Critical half-aperture Jacobi--Gamma survivor `[LEAN-PROVED]`

**Status update, 2026-07-20.**  The preceding scalar no-go does not force coefficient recovery to
be cross-prime.  It leaves a source operation on valuation depth, and that operation closes
exactly at the critical half-aperture.

Apply the Pascal death rate and inverse Gamma sewing before Gram formation:

```text
F_x(p,e)=lambda_(x,p) C_(x,p)^(-1) B_x(p,e)
          =log(p)/(p+1) p^(-x e).                      (J1)
```

Let `q=p^(-1/2)`.  At `x=1/2`, every interior central prime-power coefficient is the two-neighbour
Jacobi incidence

```text
F_(1/2)(p,e-1)+F_(1/2)(p,e+1)
  =log(p) p^(-(e+1)/2),                e>=1.            (J2)
```

The unilateral depth-zero defect is not an unbounded `sqrt(p)` scalar repair.  The missing virtual
predecessor is the actual Gamma vacuum coordinate `H_0(p)=q(1-p^(-1))`, with bounded rational
gauge

```text
G(p)=p^2/(p^2-1),       1<=G(p)<=4/3,                  (J3)

F_(1/2)(p,1)+G(p) log(p) H_0(p)=log(p)q.               (J4)
```

Equations `(J2)` and `(J4)` give the complete stream
`log(p) p^(-(e+1)/2)`, and Lean identifies it exactly with the existing semilocal Sonin prime-flux
coefficient.  More strongly, the half-aperture is rigid: for `x>0`, the first self-reproduction
equation

```text
F_x(p,0)+F_x(p,2)=log(p) p^(-2x)                       (J5)
```

holds iff `x=1/2`.  Thus `1/2` is forced by the fixed Möbius denominator `p+1` and symmetric
valuation adjacency.

The coefficient in `(J2)` is classical: it is the prime-power weight in the centered explicit
formula.  The corpus-new theorem is the source factorization `(J1)`--`(J5)`, not the coefficient.
It replaces the previous claim that coefficient conversion itself had to mix primes.  Cross-prime
mixing remains only in the literal moving-window incidence below.

Permanent Lean:
`formal/GaloisForLFunctions/RHTower/CriticalHalfApertureJacobiGammaRecovery.lean`.
The direct file check and exact module build pass; the principal theorem axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## Forced positive survivor: two-endpoint Rees mapping cone `[PAPER-PROVED]`

Let

```text
a_p=1/(p+1),
R_(k,p)=a_p*(log p)^(k+1),
eta_(k,p)=p^(-2)*(log p)^(k+1)
            /(C_(2,p)*(1-p^(-2))^(k+1)).               (R1)
```

Using the all-order depth-difference law of the Gamma-sewn source gives, exactly,

```text
R_(k,p)-eta_(k,p)*(-1)^k*Delta_e^k B_2(p,e)
 =a_p*(log p)^(k+1)*(1-p^(-2*(e+1))).                  (R2)
```

For `k=0`, `(R2)` is the fixed-critical Möbius-damped filtered von Mangoldt stream.  For every
fixed depth, its first `N` grades on `N` distinct primes are a log-Vandermonde times the nonzero
diagonal

```text
a_p*log(p)*(1-p^(-2*(e+1))).                           (R3)
```

Thus the filtered source requires two endpoint characters—zero-aperture Rees residue and the
renormalized aperture-two tail—and retains unbounded exact prime rank.  Removing `a_p` inside the
Hilbert carrier would multiply by `p+1` and recreate the exact resolution deficit; `(R2)` keeps the
prime damping until the completed response stage.

## Source-derived infinite analysis contraction `[PAPER-PROVED]`

Put `L_p=log p`, `I_(p,e)=[eL_p,(e+1)L_p]`, and define

```text
(A_x f)(p,e)=x*C_(x,p)/(p+1)*integral_(I_(p,e)) f(h) dh,
kappa_x=x^2*sum_p C_(x,p)^2*L_p/(p+1)^2.               (A1)
```

Cellwise Cauchy--Schwarz and the partition of the half-line by `I_(p,e)` for fixed `p` give

```text
||A_x f||^2<=kappa_x||f||^2.                           (A2)
```

Therefore

```text
S_(x,y)(f,g)=(A_y f-A_x g)/sqrt(kappa_x+kappa_y)       (A3)
```

is an explicit infinite contraction that combines aperture signs before the Gram.  It has
infinite rank.  For the source Laplace vector `ell_x(h)=exp(-xh)`,

```text
A_x ell_x(p,e)=B_x(p,e).                               (A4)
```

This is the missing literal Laplace-leg to Gamma-sewn Rees intertwiner.  It avoids graph
saturation because it is a specified bounded infinite analysis map, and it avoids a fixed
resolution because every logarithmic valuation cell is retained.

## Forced cross-prime moving-window incidence

The recovered central prime-power coefficient is diagonal in prime/valuation coordinates by
`(J2)`--`(J4)`.  The inverse-tilted moving window itself is still cross-prime.  With
`m=p^(e+1)`, define

```text
W(n;(p,e))=(m/n)*1_(n/2<m<=n),
v_(p,e)=log(p)/sqrt(m).                                 (W1)
```

Then

```text
T_-(n)=sum_(p,e) W(n;(p,e))*v_(p,e).                   (W2)
```

The first nontrivial block is `[[1,0],[2/3,1]]`, which is precisely why a scalar aperture edge
cannot work.  Including the polar term, the literal signed coefficient row is

```text
[alpha*sqrt(n), -2W],   alpha=(4-sqrt(2))/3.            (W3)
```

The prime and polar columns in `(W3)` must be joined before taking any norm.

## Superseded candidate: logarithmic-cell cross-prime Julia colligation

**Status update, 2026-07-19.**  This is no longer the selected conjecture.  It left the
cross-prime coefficient converter as a generic Julia/Potapov existence problem.  The
Gamma-sewn synchronized-lcm construction in
`gamma-sewn-synchronized-lcm-contraction.md` supplies a sharper source-fixed object and a bounded
Rees-boundary recovery to the literal physical density.  The material below is retained only as
the predecessor and as a falsifier for any attempted colligation.

Conjugate the signed row `(W3)` by the Gamma-sewn logarithmic-cell analysis `(A1)` and retain the
two-endpoint Rees cone `(R2)` in every grade.

**Conjecture.**  The resulting finite height truncations admit a source-prescribed cofinal
Potapov/Julia rotation whose ordinary part is contractive, whose coefficient row is literally
`(W3)`, and whose projective Pascal curvature is `(P8)`.  The rotations are compatible in prime
cutoff, valuation depth, physical height, and Rees grade.  Their locally uniform source responses
converge to `continuedPrimeArchSourceRelativeTrace` at every regular upper-half-strip point.

This is not a generic “there exists a colligation” interface.  The conjectured object is fixed by
the explicit matrices `(A1)`, `(R2)`, and `(W3)`; its first symbolic falsifier is the `n=2,3`
coefficient row, and its second is the two-prime physical-curvature law after future dressing.
If either coefficient changes, the conjecture is false.

If the compatible contraction and convergence hold, the existing finite-KMS passive-response
capstone proves RH.  The missing theorem is the cross-prime polar cancellation before the norm,
not another positivity assumption and not another equivalent RH criterion.

## Novelty boundary

- Independent geometric prime valuations and ordinary thinning are known probability theory.
- Dirichlet shifts and twisted derivations are known.
- Laplace--Carleson embeddings, Douglas factorization, Hankel `L* Sigma L` factorization, and
  Potapov/Julia conversion are known operator theory.
- No exact corpus or primary-literature match was found for `(P4)`--`(P8)`, `(R2)`, or the
  arithmetic composition `W o A_x` with the Gamma-sewn Rees system.

The local parent theories are not counted as discoveries.  The new scientific claim is the exact
source composition and the forced shape of the still-open cross-prime colligation.

## Gates

- [x] Source object explicit and coefficientwise falsifiable.
- [x] Scalar one-edge route killed on `p,p^2` and on the inverse-tilted `n=2,3` packet.
- [x] Strongest two-endpoint and cross-prime survivors extracted.
- [x] Paper proofs complete for `(P1)`--`(P8)`, `(N1)`, `(R2)`, and `(A1)`--`(A4)`.
- [x] Lean formalization and narrow direct-file audit of the Jacobi--Gamma coefficient core.
- [ ] Lean formalization and narrow audit of `(P1)`--`(P8)`, `(R2)`, and `(A1)`--`(A4)`.
- [ ] Construct the literal finite Julia rotation for `(W3) o (A1)`.
- [ ] Prove compatibility and cofinal source-value convergence.

## Log

- 2026-07-19 — created after anti-theatre corpus and primary-literature audit; scalar edge killed,
  two-endpoint Rees cone and logarithmic-cell cross-prime target selected.
- 2026-07-20 — corrected the scalar no-go: critical valuation adjacency plus the Gamma vacuum
  recovers the complete central coefficient stream prime-locally; formalized the exact recovery,
  bounded gauge, Sonin identification, and half-aperture rigidity.

## Safe-half-plane Jacobi and dyadic source section `[LEAN-PROVED UPDATE, 2026-07-20]`

The isolated critical Jacobi recovery extends uniquely through the closed safe half-plane.  Put

```text
d_x(p)=p^(1/2-x),     b_x(p)=d_x(p)^2=p^(1-2x).
```

The asymmetric boundary/interior operator

```text
J_x(f,g)(p,0)=f(p,1)+d_x(p)G(p)g(p),
J_x(f,g)(p,e+1)=b_x(p)f(p,e)+f(p,e+2)
```

recovers `log(p)p^(-x(e+1))` exactly for every `x>=1/2`.  For `x>1/2` both multipliers are strict
nonzero contractions, every finite prime/valuation rank survives, and the recovered complete
stream is square-summable.  The converse is sharp: square summability holds iff `x>1/2`.  At the
boundary the operator reduces literally to the previous critical symmetric recovery.

The safe aperture increments expose the actual HT source on the prime layer:

```text
v_x(p)-v_(x+a)(p)=p^(-x) xiTransverseShiftArithmetic(a,p).
```

Thus the family cannot be replaced by a scalar aperture reporter; its integral increments retain
the existing cofinite-deletion robust Xi-shift differential rank over the genuine coordinate
field.

Applying the literal inverse-tilted dyadic incidence gives

```text
T_x(n)=sum_(n/2<k<=n) Lambda(k)k^(-x)(k/n),
P_x(n)=((1-2^(x-2))/(2-x))n^(1-x),
R_x(n)=2(P_x(n)-T_x(n)).
```

At `x=1/2`, `T_x` is exactly `inverseTiltedDyadicWeightedPrimeWindow` and
`2P_x=(4-sqrt(2))/3*sqrt(n)`.  Hence this is the fixed safe deformation of the literal critical
prime--polar row, not a free colligation.

Permanent Lean:

- `formal/GaloisForLFunctions/RHTower/XiSafeHalfPlaneJacobiGammaRecovery.lean`
- `formal/GaloisForLFunctions/RHTower/XiSafeHalfPlaneDyadicWindow.lean`

Direct checks and exact module builds pass for both files.  The selected research
conjecture is now the explicit source-section inequality

```text
sum_n |R_x(n)|^2/n <= 4*sum_(p,e)|log(p)p^(-x(e+1))|^2,   1/2<x<=1.
```

It is forbidden to extend this inequality to ambient `ell^2`: the literal critical window kernel
is unbounded there.  The conjecture must be proved, refuted, or sharpened using joined polar
cancellation and the nonlinear HT source relation above.
