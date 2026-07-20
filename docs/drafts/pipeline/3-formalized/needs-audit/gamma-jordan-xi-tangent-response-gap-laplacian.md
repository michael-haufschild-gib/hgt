# Gamma-Jordan / Xi-tangent response-gap Laplacian

- **ID:** GJXTRGL
- **Stage:** 3-formalized/needs-audit
- **Type:** `[FORMALIZED CANDIDATE NEW SCIENTIFIC KNOWLEDGE] [RH OPEN]`
- **Source:** `GammaSewnFourRateSynchronizedEulerFisher.lean` +
  `SoninSemilocalGammaMeasureCharacteristic.lean` +
  `GammaSewnXiShiftTangentHilbertKernel.lean`
- **Statement:** The variance-biased Gamma response and the actual all-depth Xi-shift tangent
  response have a strictly positive off-diagonal gap on inverse-prime Fisher coordinates; that
  gap is a source-defined graph-Laplacian weight and therefore produces strict finite slope
  dispersion.

## Goal

Construct the missing source-derived response-correlation object demanded by CEERT-4H2 without
closing the hypertranscendental source graph and without applying an unbounded endpoint resolution.
The result must preserve the already proved `-1/2,+3/2` Jordan join and act on the actual
all-depth Xi-shift tangent vectors, rather than on an auxiliary target-selected Hilbert family.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem package in
  `GammaJordanXiTangentResponseGap.lean`, `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Exact objects

Let

```text
phi(t) = sech(t)^(1/2),
J(t)   = (3/2) phi(t)^5 - (1/2) phi(t).
```

The corpus already realizes `phi` as the characteristic function of the normalized
archimedean Gamma measure `mu_Gamma`.  The proposed joined response is not a new free kernel:

```text
J(t) = -2 phi''(t)
     = 2 integral s^2 exp(i t s) d mu_Gamma(s).                 (G1)
```

Thus `J` is the characteristic function of the probability measure
`2 s^2 mu_Gamma(ds)`.  At `t=0`, its two displayed terms are exactly the source coefficients
`+3/2` and `-1/2`, and `J(0)=1`.

For primes `p,q`, put

```text
a = p^(-1),  b = q^(-1),
k(p,q) = sqrt((1-a^2)(1-b^2)) / (1-ab).
```

If `s_p=artanh(a)`, then `k(p,q)=sech(s_p-s_q)=phi(s_p-s_q)^2`.  The normalized all-depth
Xi-shift tangent kernel already constructed in Lean is

```text
T(p,q) = k(p,q) (2 k(p,q)^2 - 1)
       = -(d^2/dd^2) sech(d) | d=s_p-s_q.                      (G2)
```

Define the prime-local joined Gamma response and its tangent gap by

```text
J_pq = sqrt(k(p,q)) (3 k(p,q)^2 - 1) / 2,
W(p,q) = J_pq - T(p,q).                                       (G3)
```

## Paper proof

### 1. The signed Jordan join is one positive correlation

Since `phi=sech^(1/2)`, direct differentiation gives

```text
phi'  = -(1/2) tanh(t) phi,
phi'' = (1/4) phi - (3/4) phi^5.
```

This proves the first equality in `(G1)`.  Differentiation under the already normalized Gamma
Fourier integral gives the second equality.  Also

```text
2 integral s^2 d mu_Gamma(s) = J(0) = 1,
```

so `2s^2 mu_Gamma` is a probability measure.  Hence `J` is positive definite even though its
closed form is a signed two-term decomposition.  This is the response-level reason that the
source's separate height and sewing Laurent pieces must not be normed separately.

### 2. The actual Xi-shift tangent is the derivative of the same Gamma geometry

For `a=tanh(s)` define the unit depth state

```text
g_s(e)=sqrt(1-a^2) a^e.
```

Its overlap is

```text
<g_s,g_t>
 = sqrt((1-a^2)(1-b^2))/(1-ab)
 = sech(s-t).
```

Differentiating in Fisher coordinates gives

```text
partial_s g_s(e)
 = sqrt(1-a^2) a^(e-1) ((1-a^2)e-a^2),
```

which is exactly the corpus's forced `p^2` normalization of the Xi-shift tangent feature.
Therefore

```text
<partial_s g_s,partial_t g_t>
 = -sech''(s-t)
 = 2 sech(s-t)^3-sech(s-t),
```

which is `(G2)`.

### 3. Prime height localization forces a strict response surplus

Every prime gives `0<a,b<=1/2`.  Moreover

```text
1-k(p,q)^2 = ((a-b)/(1-ab))^2.
```

If, say, `a>=b>0`, then

```text
2(a-b) < 1-ab
```

because `a(2+b) <= 1+b/2 < 1+2b`; the other order is symmetric.  Consequently

```text
k(p,q)^2 > 3/4.                                             (G4)
```

Write `x=sqrt(k(p,q))`.  Then `x>0`, `x<=1`, `x^4>3/4`, and a direct factorization gives

```text
W(p,q)
 = x/2 (1-x) (4x^4+x^3+x^2+x-1).                          (G5)
```

The last factor is positive because `4x^4>3`.  Also `x=1` exactly when `a=b`, hence exactly when
`p=q`.  Thus

```text
W(p,q)>=0,
W(p,q)=0 iff p=q,
W(p,q)>0 iff p!=q.                                         (G6)
```

The comparison is quantitatively coercive.  The tangent correlation defect factors as

```text
1-T=(1-k)(2k^2+2k+1).
```

Direct factorization of `4W-(1-T)` and `(1-T)-3W` gives, for `p!=q`,

```text
(1/4)(1-T(p,q)) < W(p,q) < (1/3)(1-T(p,q)).               (G7)
```

Lean exposes a genuine asymmetry in this estimate: the lower bound uses the inverse-prime
localization `(G4)`, but the upper bound holds on the entire chamber `0<k<1`.  Prime localization
is needed for coercivity, not for contractivity.

The existing all-depth tangent distance satisfies `d_tan^2=2(1-T)`.  Hence

```text
(1/8)d_tan(p,q)^2 < W(p,q) < (1/6)d_tan(p,q)^2.            (G8)
```

Thus the response surplus is uniformly equivalent to the actual source Hilbert metric; it is not
merely an entrywise positive correction.

For a finite prime packet `S` and a real slope `f`, define

```text
L_W(S,f) = (1/2) sum_(p,q in S) W(p,q)(f(p)-f(q))^2.       (G9)
```

Every summand is nonnegative, so `L_W>=0`.  If `f` is nonconstant on `S`, one ordered pair has
both factors strictly positive, hence `L_W>0`.  This is a connected, source-derived slope
dispersion with the same pairwise-difference form as the Hilbert Gram in the first nonconstant
Xi central minor.

The proof of `(G1)`--`(G9)` is dependency-closed.  The RH-facing identification below is not.

## Anti-theatre correction: the causal operation must have an exact domain

The first wording of the frontier said that a "fixed causal first-crossing dressing" pushes
`L_W` to the target.  That was not yet a mathematical conjecture.  The corpus contains the exact
first-crossing **weights**

```text
w_(p,h)(t)=quadraticCongruenceAliasSurvivalWeight(S_p,t,h),
sum_(t subset S_p) w_(p,h)(t)=1,  w_(p,h)(t)>=0,          (G10)
```

with the first-crossing prime retained as an outer colour, but it does not yet contain the
canonical compressed response `X_(p,h,t)` on which those weights act.  Calling an unspecified
map a push-forward would hide the source-to-target bridge rather than conjecture it.

There is, however, an exact forced shape once `X` is constructed.  Put

```text
m_(p,h)=E_t X_(p,h,t),
v_(p,h)=E_t |X_(p,h,t)-m_(p,h)|^2.
```

Independent causal dressing at primes `p,q` obeys the finite identity

```text
E_(t,u)|X_(p,h,t)-X_(q,h,u)|^2
 =|m_(p,h)-m_(q,h)|^2+v_(p,h)+v_(q,h).                  (G11)
```

Consequently the pre-dressed response-gap energy has the unique decomposition

```text
E_pre
 =L_W(m)+C_W,
C_W=(1/2)sum_(p,q)W(p,q)(v_(p,h)+v_(q,h))>=0.           (G12)
```

This is the correct sign: causal averaging does not preserve the response-gap energy.  Its exact
conditional-variance loss produces one positive local charge channel.  `(G11)`--`(G12)` are the
classical bias--variance identity specialized to the corpus's exact first-crossing probability and
new source weight `W`; they are not claimed as new mathematics.

## Frontier conjecture exposed by the theorem

**Causal alias-variance crossing (CAVC).**  Construct `X_(p,h,t)` from the literal anchored
primitive response `B_(pa,r,h)`, the height synthesis `(E42)`, and the canonical two-boundary
second compound, with no arbitrary response parameter.  For every matched finite source/zero
packet, prove simultaneously

```text
E_pre = xiSquaredEulerFiniteApertureHilbertGram,
C_W   = xiSquaredEulerFiniteApertureBoundaryCharge.     (G13)
```

Then `(G12)` gives

```text
L_W(m)=xiSquaredEulerFiniteApertureCentralMinor,         (G14)
```

which is precisely the missing sign-producing crossing.  The joined Gamma response enters once,
through the probability law defining the response coordinate; its `-1/2,+3/2` closed-form pieces
are never assigned separate norms.

This is bold but falsifiable.  The first test is the smallest two-prime packet with one future
Boolean coordinate.  The literal `X` must make both equalities in `(G13)` hold; an arbitrary
response makes `(G13)` vacuous, while a nonzero `C_W` over a target packet with zero boundary
charge kills the conjecture.  The singleton off-line target is the sharp hostile test: its Hilbert
Gram is zero and its charge is positive, so no nonnegative dressed source Laplacian can represent
it.  Thus `(G13)` is already RH-strength and cannot be justified by generic variance theory.

The third-compound remainder remains separate: `(G14)` targets only the `2 x 2` central Hankel
minor and does not identify `T` with the full three-node determinant.

## Anti-theatre and novelty audit

- Known parent: powers of `sech` as Meixner characteristic functions, their
  Meixner--Pollaczek orthogonal polynomials, differentiation of characteristic functions, and
  graph-Laplacian positivity are classical.  None is claimed as new.
- RH/Meixner parent: Romik's Meixner--Pollaczek expansion of Xi is also established theory and
  does not contain the source response-gap construction.
- Exact searches for the conjunction of the `-1/2,+3/2` Gamma-Jordan law, the completed Xi-shift
  all-depth tangent, inverse-prime Fisher localization, factorization `(G5)`, metric comparison
  `(G8)`, and its RH
  response-correlation role found no collision.  This is search noncollision, not a priority
  claim.
- The candidate new theorem is precisely `(G1)`--`(G9)` as one source-derived object.  Its
  significance is that it replaces the vague instruction “correlation must cancel the Jordan
  mass” by an explicit positive edge kernel whose finite energy already has the required target
  dispersion shape.
- Exact searches for the CAVC conjunction `(G10)`--`(G14)` found only unrelated Meixner
  first-passage/percolation and generic conditional-variance theory.  That is a noncollision
  report, not evidence for truth or priority.  The conjecture is accepted here because its finite
  source formula and first falsifier are explicit, not because search failed.

Primary parent references:

- W. Schoutens and J. L. Teugels, the Meixner process and its characteristic function, 1998--2000
  parent literature.
- D. Romik, *Orthogonal polynomial expansions for the Riemann xi function in the Hermite,
  Meixner--Pollaczek, and continuous Hahn bases*,
  <https://arxiv.org/abs/1902.06330>.

## No-go closure

- **Exact killing mechanism:** The generic headline “the signed Gamma response is a positive
  correlation” reduces to classical variance-biasing of a Meixner characteristic function and is
  not new.
- **Strongest positive survivor:** On the source-forced inverse-prime chamber, comparison with the
  actual Xi-shift tangent leaves the strictly positive off-diagonal gap `(G5)` and strict
  bilipschitz metric `(G8)` and strict Laplacian dispersion `(G9)`.
- **New insight:** Correlation cancellation should be implemented as a source response-gap
  Laplacian before four-rate compression, not as positivity of either Laurent summand and not as a
  free target Gram factorization.
- **Status:** `(G1)`--`(G9)` is paper-proved and formalized.  Direct Lean checking and the exact
  module build pass; the four capstone axiom audits report only `propext`, `Classical.choice`, and
  `Quot.sound`.  CAVC `(G13)` is the named open core; the literal compressed response
  `X_(p,h,t)` is the first missing object.

## Log

- 2026-07-20 — created in `1-in-progress` after corpus audit and hostile Meixner/RH search.
- 2026-07-20 — `(G1)`--`(G9)` formalized and audited; vague causal-push-forward prose replaced by
  the explicit CAVC finite conjecture `(G10)`--`(G14)` and its smallest-packet falsifier.
