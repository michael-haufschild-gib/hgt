# The critical prime-shift form is an exact logarithmic position commutator

- **ID:** `critical-euler-position-commutator-carrier-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** weighted translation operators, the position--translation commutator, and
  Burnol's conductor-operator realization of local explicit-formula terms
- **Statement:** At every finite aperture, the Hermitian von Mangoldt shift operator is exactly the
  commutator of logarithmic position with a skew-adjoint Euler-logarithm operator. The commutator
  coefficients are `1/(k p^k)`, so the missing unsquared logarithmic Euler response is already an
  operator identity on the faithful arithmetic carrier.

## Aperture space

Fix `A>0` and put

```text
H_A=L2([0,A],e^(-x)dx).                                    (1)
```

Let `P_A` denote restriction to `[0,A]`, followed by zero extension in the bilateral weighted
space, and define

```text
T_(A,h)=P_A S_h P_A,
(S_h f)(x)=e^h f(x-h),       0<=h<A.                       (2)
```

Let `X_A` be multiplication by the logarithmic position:

```text
(X_A f)(x)=x f(x).                                         (3)
```

It is bounded and self-adjoint with `||X_A||=A`.

## Exact commutator

`[PROVED]` For every `0<=h<A`,

```text
[X_A,T_(A,h)]=h T_(A,h),                                  (4)
[X_A,T_(A,h)^*]=-h T_(A,h)^*.                             (5)
```

### Proof

The aperture projection commutes with `X_A`. On the support of the shifted vector,

```text
X_A S_h f(x)-S_h X_A f(x)
 =x e^h f(x-h)-e^h(x-h)f(x-h)
 =h e^h f(x-h).                                           (6)
```

Compression gives `(4)`. Taking adjoints in `(4)` and using self-adjointness of `X_A` gives `(5)`.

## Euler logarithm operator

Let

```text
N_A={n>=2:log n<A}.                                       (7)
```

This set is finite. Define the bounded skew-adjoint operator

```text
Z_A
 =sum_(n in N_A) Lambda(n)/(n log n)
    (T_(A,log n)-T_(A,log n)^*).                          (8)
```

Equations `(4)`--`(5)` give the exact identity

```text
[X_A,Z_A]
 =sum_(n in N_A) Lambda(n)/n
    (T_(A,log n)+T_(A,log n)^*).                          (9)
```

The right side is the Hermitian prime contribution in
`critical-euler-weighted-shift-accretivity-law.md`.

For `n=p^k`,

```text
Lambda(n)/(n log n)=1/(k p^k).                            (10)
```

Thus `Z_A` is precisely the finite-aperture Euler logarithm: `(10)` is the coefficient in

```text
-log(1-p^(-1-z))=sum_(k>=1)p^(-k(1+z))/k.                 (11)
```

The orbital length `log(p^k)` is produced by the commutator with `X_A`; it is not inserted as an
external scalar normalization.

## Exact transport to the unweighted logarithmic carrier

Define the unitary

```text
W_A:H_A -> L2([0,A],dx),
(W_A f)(x)=e^(-x/2)f(x).                                  (11a)
```

Let

```text
(V_(A,h)g)(x)=1_(x>=h)g(x-h)                              (11b)
```

be the ordinary truncated translation. Direct substitution gives

```text
W_A T_(A,h) W_A^(-1)=e^(h/2)V_(A,h),                     (11c)
W_A X_A W_A^(-1)=X_A.                                    (11d)
```

Consequently, for `n=p^k`, the corresponding term of the transported Euler logarithm is

```text
1/(k p^(k/2))
  (V_(A,k log p)-V_(A,k log p)^*).                        (11e)
```

This is exactly the coefficient magnitude in the formalized semilocal logarithmic metric
`semilocalPrimeLogMode` and in `soninLogPrimePowerCoefficient`; the Mellin character supplies its
unimodular spectral phase. Thus the weighted Euler-shift carrier, the logarithmic commutator, and
the semilocal Sonin coefficient are the same ambient operator before application of the exact Sonin
projection.

## Exact compression through an orthogonal constraint

The projection transport is algebraic. Let `Q` be any orthogonal projection on a Hilbert space, let
`X^*=X`, and let `Z^*=-Z`, with all products below defined on a common invariant core. Put

```text
X_Q=QXQ,                  Z_Q=QZQ,
L_X=(1-Q)XQ,              L_Z=(1-Q)ZQ.                    (11f)
```

Then

```text
Q[X,Z]Q
 =[X_Q,Z_Q]+L_X^*L_Z+L_Z^*L_X.                           (11g)
```

### Proof

Insert `1=Q+(1-Q)` between `X` and `Z`:

```text
QXZQ-QZXQ
 =QXQZQ-QZQXQ
  +QX(1-Q)ZQ-QZ(1-Q)XQ.                                 (11h)
```

The first line is `[X_Q,Z_Q]`. Self-adjointness of `X` gives
`QX(1-Q)=L_X^*`, while skew-adjointness of `Z` gives `QZ(1-Q)=-L_Z^*`. This proves `(11g)`.

Whenever a trace or relative trace is defined on the right side and annihilates the internal
commutator,

```text
Tr(Q[X,Z]Q)=2 Re Tr(L_X^*L_Z).                            (11i)
```

Thus the orbital-length response after Sonin or aperture compression is not a scalar
normalization. It is the polarized cross-boundary Gram of logarithmic-position leakage and Euler
leakage.

For a renormalized functional, annihilation of the internal commutator is an extra theorem rather
than a formal property. Define its trace-defect cocycle by

```text
Def_tau(A,B)=tau([A,B]).                                      (11j)
```

Applying `tau` to `(11g)` gives the unconditional decomposition, whenever all three terms are in
the stated domain of `tau`,

```text
tau(Q[X,Z]Q)
 =Def_tau(X_Q,Z_Q)+tau(L_X^*L_Z+L_Z^*L_X).                  (11k)
```

Thus every source-compatible renormalized realization has exactly two degree-one channels: the
internal trace anomaly and the polarized leakage cross. A construction may prove that the anomaly
vanishes and retain only the cross, or it must carry both terms. It may not impose cyclicity before
checking the cutoff/renormalization domain, because Connes's semilocal trace formula and Burnol's
conductor formalism use boundary-sensitive traces.

For the exact Sonin projection, `L_Z` is the orientation-sensitive prime-dilation corner and `L_X`
is the conductor/position corner. The existing bounded projection-correction scalarization paired
the Euler cross with a different Hilbert--Schmidt operator and consequently had uniformly bounded
response. Equation `(11i)` identifies the source-compatible replacement.

`[PROVED IN LEAN; COORDINATE CORRECTION]` In the original Sonin coordinate the generator in
`(11i)` is `log|x|`, not ordinary position `x`. The standard two-edge formula for `[x,Q_0]` is
therefore not the orbital-length carrier. Under the exact even logarithmic unitary, dilations become
translations, but the Sonin Fourier constraint becomes the involutive translation-reversing
scattering operator `J_log`, not the ordinary Fourier transform. The corrected theorem is in
`../../3-formalized/not_new_scientific_knowledge/sonin-log-coordinate-mellin-scattering-carrier.md`.

The required position transport is consequently the nonlocal commutator `[M_t,J_log]`, equivalently
`[log|x|,B_a]` before logarithmic transport. This is the Burnol conductor/Mellin-scattering channel;
compactness of the Sonin projection correction does not control it.

The algebraic projection transport is therefore closed. The remaining analytic theorem is to
construct a common Mellin-scattering form graph on which the conductor commutator, Euler leakage
cross, and internal trace-defect cocycle have the genuine semilocal relative trace, and to derive a
uniform finite lower floor for the completed prime--Gamma flux.

## Completed source form

Let `B_A` be the aperture restriction of the archimedean/pole multiplier form in
`critical-euler-weighted-shift-accretivity-law.md`. The Hermitian completed operator on the common
finite-aperture core is

```text
H_A
 =B_A+B_A^*-[X_A,Z_A].                                   (12)
```

Burnol's local conductor operator

```text
log|x|+Fourier^* log|x| Fourier                           (13)
```

is the archimedean analogue: its spectral multiplier is the logarithmic derivative of the local
Gamma factor. Equations `(8)`--`(13)` therefore place the finite primes and the archimedean place in
one degree-one logarithmic operator category.

## Arithmetic carrier

Every coefficient in `(8)` is nonzero. By
`ccm-compressed-prime-shift-arithmetic-complement-law.md`, the operators

```text
{T_(A,log p):p<e^A}                                      (14)
```

are linearly independent. Hence weighting them by `(10)` does not collapse the prime-log carrier.
After quotienting the phase directions `D` supplied by the signed-Gamma completion, `(8)` still
carries

```text
A_N=V_N/(V_N intersection D)                             (15)
```

for every `N<e^A`.

## Positive CCM consequence

The degree-one part of the three-grade carrier is now concrete. A successful construction must
prove the completed commutator domination

```text
B_A+B_A^*>=[X_A,Z_A]                                     (16)
```

as a closed form, or construct an equivalent Gram contraction preserving `(15)`. Equation `(16)`
is exactly finite-aperture Weil nonnegativity, so the commutator identity alone is not an RH proof.
Its value is that the required logarithmic response no longer has to be guessed: the carrier is

```text
log-position X_A
  + skew Euler logarithm Z_A
  + Burnol Gamma conductor
  + the arithmetic quotient A_N.                         (17)
```

The viable mechanism is therefore a source-specific positive-commutator or graph-contraction
theorem for `(12)`. Its degree-one term is the pair

```text
(internal trace-defect cocycle, polarized position/Euler leakage cross). (17a)
```

A bounded projection-correction scalar cannot substitute for this pair; its response has no
orbital-length growth.

## Relation to the three-grade Sonin carrier

In `ccm-sonin-three-grade-relative-carrier-law.md`, grade one was characterized abstractly as the
Hilbert--Schmidt principal/residual cross carrying the unsquared coefficient. Equations `(8)`--`(10)`
give its logarithmic generator before Sonin compression. The remaining compatibility theorem is to
transport this position commutator through the principal--relative Sonin extension while retaining
its closed graph and the aperture Morse index.

## Scientific classification

The position--translation commutator and Euler logarithm expansion are classical. Burnol already
identifies the corresponding conductor operator at every local place. The result is a route bridge,
not new scientific knowledge.

## References

- J.-F. Burnol, *The explicit formula and the conductor operator*, 1999.
- `critical-euler-weighted-shift-accretivity-law.md`.
- `ccm-sonin-three-grade-relative-carrier-law.md`.

## Lean decision

The formal tree contains aperture correlation cutoffs and normalized dilation operators, but not
this weighted half-line shift representation with the bounded log-position commutator. A discrete
wrapper would not certify `(12)`. Formalization is deferred until the commutator is transported to
the actual Sonin/CCM carrier.

## Gates

- [x] bounded finite-aperture position operator fixed
- [x] exact compressed-shift commutator proved
- [x] skew Euler logarithm constructed
- [x] unsquared prime-power coefficients recovered
- [x] exact unitary transport to the semilocal logarithmic coefficient proved
- [x] exact projection-compressed commutator/Gram identity proved
- [x] renormalized trace-defect/leakage decomposition proved
- [x] sharp Sonin position leakage identified as a signed Sobolev edge trace plus first-moment correction
- [x] arithmetic-complement faithfulness retained
- [ ] determine the internal trace-defect cocycle on the genuine semilocal cutoff
- [ ] prove the resulting degree-one pair has the genuine semilocal relative trace
- [ ] complete the prime--Gamma leakage form to a positive square or contraction
- [ ] prove the completed positive-commutator inequality `(16)`
- [ ] preserve the CCM aperture index
- [ ] prove RH
