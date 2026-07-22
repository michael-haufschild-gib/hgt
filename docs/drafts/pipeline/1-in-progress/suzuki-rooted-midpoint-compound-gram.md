# Suzuki rooted midpoint compound Gram

- **ID:** `suzuki-rooted-midpoint-compound-gram`
- **Stage:** 1-in-progress
- **Type:** RH-SUFFICIENT SOURCE CONJECTURE
- **Status:** `[OPEN CORE CORRECTED] [SOURCE-PURE] [NO RH PREMISE]`
- **Parent:** `suzuki-jump-kernel-loewner-growth.md`
- **Algebraic precursor:**
  `../2-fully-proven/new_scientific_knowledge/suzuki-global-local-compound-bezoutian-weld.md`

## Actual corpus frontier

The canonical full-jump carrier is already fixed.  For local marked pair `(Q,P)` and global
completed-Xi pair `(S,T)=(XiC',z^2 XiC)`, put

```text
N=Q*T-S*P,   D=P*T.
```

Its Hermitian Bezoutian is exactly

```text
[N,D]=T(z)conj(T(w))[Q,P]-P(z)conj(P(w))[S,T].
```

What corpus cannot prove is positivity of this source-specialized compound Bezoutian.  Generic
boundary-triple, Pluecker, balanced-Cauchy, and local resolvent arguments do not solve it.

Hostile source audit has killed one proposed limit order.  Raw Bianchi mass

```text
b_x(p)=Lambda(p)/p*exp(-x log p)
```

matches Suzuki critical source only at `x=-1/2`, where it is `Lambda(p)/sqrt(p)` and not summable.
Existing uniquely renormalized Gamma-conormal boundary coordinate is exactly its square root.
Therefore standalone critical raw Bianchi leg has no cofinal Hilbert realization.  Any constant
residual multiple is square-summable iff coefficient is exactly zero.

## New midpoint prediction

Write two shifts as

```text
alpha=m-d,   beta=m+d,   p=alpha*beta=m^2-d^2,
B0=X+c,      U=B0-m*x,   V=Y-m*y,   F=B0*y-x*Y.
```

Exact marked pair should obey

```text
Q=U*V-d^2*x*y+m*F,
P=V^2-d^2*y^2,
N=V*(U*T-S*V)+d^2*y*(S*y-x*T)+m*F*T.                 (1)
```

The symmetric coefficient form of `Q` is

```text
S((r,s),(R,S))=r*R-m*(r*S+s*R)+p*s*S,
S((r,s),(r,s))=(r-m*s)^2-d^2*s^2.                   (2)
```

Therefore exact minimal rooted diagonal completion is `d^2`: adding `kappa*s^2` is nonnegative
for every `(r,s)` iff `kappa>=d^2`, and equality collapses `(2)` to one square.  Alternating part
is forced flux `m*(r*S-s*R)`.

For dyadic pair `alpha=-2L`, `beta=-L`, this predicts

```text
m=-3L/2,   d=L/2,   p=2L^2,
minimal missing rooted mass=d^2=L^2/4,
completed rooted coefficient=p+d^2=m^2=9L^2/4.       (3)
```

## Exact critical aperture subchannel inside `SUZUKI-MARKED-WEIL-ROBIN-CD`

The provisional leakage coordinate `L_M` is now rejected: canonical affine two-boundary residual
is exact but its critical mass still dominates `1/(6400000*p)`.  Corpus supplies a different
power-scale object.  Pair uniquely renormalized critical Gamma boundary with cubically normalized
true-aperture innovation *before squaring*.  For prime `p` and valuation depth `e`, Lean proves

```text
T_e(h,a,t;p)=conj(G_(-1/2,t)(p,e))*I_(h,a)(p,e),
T_(e+1)=rho(h,a,t;p)*T_e,
rho=exp(-(log p)/4)*exp(i*t*log p/2)*r^2,
r=exp(-(h*a/2)log p),
|rho|<1.                                               (4)
```

Hence actual source current is no longer unspecified:

```text
C_(h,a,t)(p)=sum_(e>=0) T_e
             =T_0/(1-rho).                            (5)
```

Prime completion of `(5)` is absolutely convergent on paper because transverse factor
`q/(1+q)=1/(p+1)` changes critical scale to `sqrt(log p)/p^(5/4)`.  Its Lean completion is next
analytic gate.

This subchannel cannot be polarized atomwise: delayed-hinge theorem gives explicit negative Pick
nodes for every nonzero prime atom.  It must enter stronger collective identity already proved in
corpus:

```text
z^2 R_g[v](z)
 = exp(i*a*z)(i*z*U(a)-U'(a)) + E_(-g'')[v](z).        (6)
```

Here complete prime--Gamma--polar source is assembled in signed Weil distribution `-g''`, and
midpoint `d^2` shift is localized to Robin boundary current.  Actual conjecture remains
`SUZUKI-MARKED-WEIL-ROBIN-CD`: affine-sew marked Robin currents, polarize completed causal Weil
exterior, and prove resulting compound Bezoutian is positive Green Gram.  New theorem `(4)--(5)`
fixes critical Gamma/aperture component of Robin channel and removes former existential `L_M`; it
does not replace completed Weil exterior by positive prime atoms.

One negative principal minor after full marked Robin/Weil assembly falsifies conjecture.  Success
factors canonical compound Bezoutian, giving jump Pick positivity and RH through existing
pole-tomography connector.

## Why rooting is forced

All corpus balance mechanisms annihilate entire canonical packet `(+1/2,-1/2)`, including cofinal
limit.  A Gram built only after this compression is zero there.  Marked secant retains arbitrary
rank-one affine intercept.  Therefore direct balanced two-boundary producer cannot equal full
compound source.  Raw rooted Bianchi coordinate must remain at finite aperture until debt `d^2`
and completed counterterm are combined.  It may not be completed as standalone Hilbert vector.
Only cancelled residual may be squared and passed cofinally.

## Falsifiers

- One source expansion where Gamma/aperture part of Robin current differs from exact quarter-shift
  current `(4)--(5)`.
- Failure of absolute prime completion of `(5)` despite paper majorant.
- One finite node packet with negative determinant after exact archimedean remainder is included.
- Any derivation using only balanced two-boundary vectors: these are identically zero at source
  packet and cannot carry marked affine intercept.
- Any extra fitted coefficient, Xi-zero location, Herglotz premise, or quotient nonvanishing
  assumption.
- A mixed block not equal to common-prime Julia/Bianchi cross term already fixed by corpus.
- Any proof taking standalone `B_M` cofinally before cancellation: formally ruled out.

## Scientific method

1. Prove `(1)--(3)` and sharp completion theorem unconditionally.
2. Formalize those exact identities and connect them to compound Bezoutian theorem.
3. Complete absolute prime summability of exact current `(5)` in Lean.
4. Insert exact current into marked Robin term of collective identity `(6)` before characteristic
   division.
5. Match finite compound kernel against marked Robin plus completed causal Weil exterior and
   hostile-test all two-by-two principal minors
   symbolically; no numerical computation.
6. Prove convergence of completed block only.  Existing raw-source convergence theorem at `x>0`
   cannot be invoked at critical `x=-1/2`; quarter-shift current must supply cofinal topology.
7. Apply compound positivity and RH connector.

## Log

- 2026-07-22 — conjectured after compound Bezoutian and Volterra marked tensor were compared in
  midpoint/halfgap coordinates.  Exact predicted debt is quadratic half-gap `d^2`, not unspecified
  completion.  Two-boundary collapse forces rooted source architecture.
- 2026-07-22 — algebraic predictions `(1)--(3)`, sharp completion iff, compound three-channel
  split, product-resolvent midpoint forcing, and physical `-d^2*phaseNeumann(v)` source identity
  proved on paper and in Lean.  Open work is now only atom-by-atom prime--Gamma/Xi identity `(4)`.
- 2026-07-22 — **producer falsified and replaced.**  Raw critical rooted Bianchi mass diverges.
  Stronger delayed-hinge audit proves every far prime power `log n>=2a` is absent from local
  Volterra triangle but remains as global jump atom `-i Lambda(n)/sqrt(n) exp(iz log n)/z^2`.
  Its Pick diagonal is positive on imaginary axis and strictly negative at phase-aligned node
  `2pi/log n+i*pi/log n`; nonzero compound denominator preserves sign.  Therefore proposed
  atom-by-atom/direct-sum Gram `(4)` is impossible.  Exact `d^2` debt survives.  Correct open core
  is `SUZUKI-CAUSAL-APERTURE-ENTRY-COMPOUND-WELD`: assemble finite-delay boundary tails, complete
  far-prime tail, and exact polar--Gamma source inside compound kernel before positivity or
  cofinal limit.  Paper/Lean theorem:
  `../2-fully-proven/new_scientific_knowledge/suzuki-causal-hinge-boundary-tail-green-law.md`.
- 2026-07-22 — hostile audit disproved unrenormalized cofinal order: exact critical raw mass is
  `Lambda(p)/sqrt(p)`, dominates `log(2)/p`, and diverges.  Lean connector lands no-go directly on
  existing uniquely renormalized Gamma-conormal coordinate.  Stronger scalar-rigidity theorem says
  constant residual is square-summable iff it vanishes.  Replaced original conjecture by finite
  cancel-before-limit identity `(5)`; actual open core is exact Volterra leakage/Gamma-polar
  residual, not generic positivity.
- 2026-07-22 — collective channel identified exactly.  Causal Weil--Robin Green law proves
  `z^2*R_g=exp(iaz)(izU(a)-U'(a))+E_(-g'')`.  Compound denominator converts screw exterior into
  one Robin boundary current plus causal exterior of already-completed Weil distribution.
  Delayed hinge recovers boundary--tail theorem; direct form-shift delta vanishes outside compact
  source, placing exact `d^2` Neumann debt in Robin current rather than raw Bianchi bulk.  Correct
  open core is `SUZUKI-MARKED-WEIL-ROBIN-CD`: factor marked sewing of these exact two channels,
  without splitting prime atoms or replacing signed Weil exterior by positive part.  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-causal-weil-robin-green-identity.md`.
- 2026-07-22 — formal audit completed: direct source check and targeted SOTA build `9448/9448`
  pass; all new declarations use only standard Lean axioms.  This closes source-coordinate
  uncertainty but not sign: sole frontier remains positive Green-Gram realization of marked
  Robin current plus completed signed Weil exterior.
- 2026-07-22 — canonical affine two-boundary Cauchy repair falsified: exact residual-weighted
  critical mass dominates `1/(6400000*p)` and is nonsummable.  Positive survivor found in existing
  finite Gamma--Euler aperture current.  At critical displacement, actual valuation atoms have
  exact contractive quarter-shift ratio `(4)` and per-prime resolvent `(5)` in Lean.  This fixes
  Gamma/aperture subchannel topology as distributional boundary pairing, while leaving actual RH
  frontier unchanged: marked Robin current plus completed signed Weil exterior must jointly admit
  positive Green-Gram realization.
- 2026-07-22 — affine cancellation escape closed.  For every common normalized channel,
  `S_gamma(m W_alpha,m W_beta)=m(beta-alpha)W_alpha W_beta`, independently of target shift.  A far
  prime-power exterior is such a channel, so the complete far von-Mangoldt tail survives affine
  sewing as an exact characteristic factor.  Common-factor Bezoutian is only congruence, hence the
  phase-aligned negative delayed-hinge diagonal survives whenever the sewn characteristic is
  nonzero.  Two shifts neither cancel nor dilute far atoms.  Correct open core is now
  `SUZUKI-CAUSAL-ENTRY-SCHUR-WARD`: prove one complete mixed Robin + near-entry + universal-far +
  polar--Gamma compound kernel is a positive source Gram, paying exact `d^2` and holonomy Schur
  debt.  Any diagonal/direct-sum prime construction is formally impossible.  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-affine-sewn-weil-robin-far-tail-factorization.md`.
- 2026-07-22 — exact Gram equality requirement weakened.  Corpus fixed-width rectangular screw
  curvature proves RH from mere eventual lower boundedness on `a=log(n)/2`.  Therefore for any
  nonnegative explicit source energy `E_L(n)`, it is enough to lower-bound Ward defect
  `Delta_L=Q_L-E_L`; exact `Q_L=E_L` is unnecessary.  Conversely false RH forces `Delta_L` below
  every real level cofinally for every such energy.  Correct open core is now
  `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`: build actual mixed affine-sewn Weil--Robin
  rectangular source vector and prove its defect uniformly lower bounded.  Trace-class or
  finite-rank error helps only after its values on this orbit are uniformly lower bounded.
  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-rectangular-ward-defect-semiboundedness.md`.
- 2026-07-22 — discrete near-entry placeholder resolved to exact boundary reporter.  For the
  denominator-matched hinge channel, moving-boundary endpoint terms cancel in the first two delay
  derivatives.  Near and far channels match at `ell=2a` through order two; first defect is
  `z^2*exp(I*a*z)*v(-a)`.  Affine sewing yields one marked barycentric endpoint trace, and even a
  common normalized trace survives.  Instantaneous positive entry updates are impossible.
  Current open core remains `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`, but discrete near-entry
  input is no longer free: couple this forced third-jet trace to critical quarter-shift Gamma
  current, triple-integrate from each wall, and prove only uniform lower semiboundedness.
  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-causal-entry-third-jet-boundary-law.md`.
- 2026-07-22 — phase/type and triple-integration ambiguity closed.  The complete near/far gap
  satisfies exact all-depth transport `(d/dell-I*z)gap''=z^2*exp(I*a*z)*endpointTrace`.  At
  prime-power entry wall `a=log(p^(e+1))/2`, its phase is exactly conjugated critical Gamma phase.
  Existing quarter-shift atom factors as one real endpoint amplitude times this wall phase, hence
  its canonical `t^2` multiple is the actual third-jet entry forcing; all valuation depths sum to
  existing contractive resolvent.  Off `t=0`, forcing determines endpoint trace uniquely.  Open
  core remains `SUZUKI-RECTANGULAR-WARD-DEFECT-SEMIBOUNDED`, now reduced to proving concrete
  restricted-Weil deficiency endpoint trace realizes calibrated amplitude after fixed affine
  normalization, or proving residual rectangular form uniformly lower semibounded.  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-critical-entry-wall-quarter-shift-green-law.md`.
- 2026-07-22 — **source-type correction and symmetric-square weld.**  S57 observed amplitude
  depends injectively on independently chosen positive observer aperture at depth zero, so cannot
  be universal restricted-Weil deficiency endpoint trace.  Removing observer innovation exposes
  bare Gamma wall field `omega_e=b_e*exp(I*t*log(p^(e+1))/2)` with exact source identities
  `b_e^2=Lambda(p^(e+1))/sqrt(p^(e+1))`, far-hinge numerator `omega_e^2`, bare entry third jet
  `t^2*omega_e`, and observed jet `t^2*omega_e*I_e`.  Universal far tail is therefore quadratic
  degree of same linear entry field, not independent channel.  Correct open core is
  `SUZUKI-WALL-SYMMETRIC-SQUARE-WARD`: prove actual normalized deficiency wall trace equals `b_e`,
  or prove observer-paired residual form uniformly lower bounded; then establish assembled
  rectangular Ward-defect lower bound.  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-square-root-weld.md`.
- 2026-07-22 — **second source-type correction: resolvent dressing is mandatory.**  Bare `b_e` is
  restricted-Weil input coordinate, not endpoint response.  At one spectral level `s`, shifted
  response is `D_lambda=(s-lambda)^(-1)omega_e`.  Exact two-shift residual is
  `D_0-D_aff=K_(alpha,beta)(s)omega_e`; self-pairing closes as
  `omega_e(D_0-D_aff)=K_(alpha,beta)(s)omega_e^2`, i.e. scalar Krein defect times exact far-hinge
  numerator.  For negative shifts and zero height this is strictly negative on negative spectral
  modes and positive on positive modes.  Correct open core is
  `SUZUKI-RESOLVENT-DRESSED-WALL-WARD`: construct actual spectral measure/boundary observation and
  prove marked Robin/polar--Gamma/holonomy compensation pays exact negative-mode debt with
  uniformly lower-bounded rectangular residual.  Paper/Lean:
  `../2-fully-proven/new_scientific_knowledge/suzuki-critical-wall-field-resolvent-dressing-law.md`.
