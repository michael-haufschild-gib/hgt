# Rectangular semilocal finite-part curvature to RH

- **ID:** `rectangular-semilocal-finite-part-curvature-rh`
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / `[RH-SUFFICIENT SOURCE ROUTE]`
- **Scientific status:** `[OPEN] [SURVIVES ONLY IN COHERENT/GROWING-CHANNEL FORM]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:** `../../../reports/rh-proof-shape-1707.md`;
  `../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/connes-semilocal-finite-part-orbital-source-class.md`;
  `../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/sonin-burnol-conductor-cutoff-bounded-graph-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/critical-euler-position-commutator-carrier-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/ccm-sonin-three-grade-relative-carrier-law.md`;
  `../2-fully-proven/not_new_scientific_knowledge/08-sonin-semilocal-copoisson/rectangular-semilocal-observer-tail-separation.md`;
  `../2-fully-proven/needs-audit/semilocal-one-prime-harmonic-moment-defect.md`
- **Statement:** `[CONJECTURE]` Extend the positive semilocal Sonin trace to the sharp rectangular
  autocorrelation and identify its Connes--Sonin comparison defect with the cyclic relative trace of
  the Sonin operator-naturality defect.  After the polar modes are retained inside a coherent or
  growing-channel Gamma--prime covariance, the exact rectangular source is positive
  polar-plus-Sonin bulk minus this comparison defect and a bounded Gamma correction.  A
  source-uniform compensated relative-resolvent trace-norm estimate makes the defect
  square-summable on the arithmetic aperture sequence, and the existing rectangular
  negative-energy theorem then proves RH.  Independent prime innovations coupled to one fixed
  scalar Gamma conductor are formally excluded.

## Exact arithmetic endpoint

Fix `L>0` and put

```text
A_L(n)=rectangularPrimePolarSourceCoefficient(L,log(n)/2).
```

The formal corpus proves

```text
RH
<-> for every epsilon>0,
    LSeries(A_L(n)^-,1+epsilon) converges.                 (1)
```

It also proves

```text
A_L(n)=C_L+2 I_L(n),                                      (2)
```

where `I_L(n)` is the adjacent Haar block of the completed critical-Mellin prime mass.  Therefore
the only new implication needed is a source construction forcing the negative part in `(1)` to
have subcritical Dirichlet energy.

The square-energy gate is sufficient.  If a source identity gives

```text
A_L(n)=B_L(n)+kappa_L(n)+O_L(1),
B_L(n)>=0,                                                (3)
```

and

```text
sum_n (kappa_L(n)^-)^2/n^(1+epsilon)<infinity             (4)
```

for every `epsilon>0`, weighted Cauchy--Schwarz and `(1)` give RH.  Condition `(4)` is the terminal
consumer, not the theorem to assume: it must follow from a source-uniform operator-ideal estimate.

There is an even shorter terminal consumer.  Let `Q_L(n)` be the actual rectangular Xi--Weil
value.  The corpus proves `Q_L(n)=A_L(n)+GammaCorrection_L(n)` and proves directly that weighted
square energy of `Q_L(n)^-` implies RH.  The Connes--Sonin comparison below naturally decomposes
`Q_L`, so the bounded Gamma transfer back to `(1)` is unnecessary in the final proof.

## The rectangular test fixes the finite-place system

Let `g_(L,n)` be the symmetric two-edge log profile with edges of length `L` centered at arithmetic
aperture `log(n)/2`, and let

```text
h_(L,n)=g_(L,n) * reverse(g_(L,n)).                       (5)
```

This is a positive-type autocorrelation.  Its positive-lag support is contained in `[0,log n]`.
Consequently its nonarchimedean Weil value sees exactly the finite prime powers `q<=n`; at fixed
`n` there is no arbitrary all-prime limiting procedure.  The canonical semilocal place set is

```text
S_n={infinity} union {p prime:p<=n}.                      (6)
```

The cofinal problem is therefore a single arithmetic sequence `n->infinity`, not a separately
chosen exhaustion of the primes.

The zero-lag mass is already formalized:

```text
h_(L,n)(0)=rectangularTwoEdgeAutocorrelation(L,log(n)/2,0)=2L  (7)
```

once the edges are disjoint.  Thus the universal divergent term in the semilocal cutoff trace,
`2 h_(L,n)(0) log Lambda=4L log Lambda`, is independent of `n`.  It cannot carry an off-line
power mode and is harmless for the negative-energy endpoint.  The `n`-dependent sign must live in
the renormalized cutoff curvature.

## Required finite-part/positive-trace identity

There are three different parameters and they may not be conflated:

```text
L                 fixed rectangular width,
alpha_n=log(n)/2  translation/aperture of the rectangular test,
lambda            Sonin phase-space cutoff, fixed canonically at lambda=1.  (8)
```

Let `FP_(S_n)` be Connes's canonical semilocal finite part, `Pi_(S_n,lambda)` the exact semilocal
Sonin projection in the `S_n`-dependent Hilbert metric, and `vartheta_(S_n)` the scaling
representation.  For the sharp step profile the first missing analytic theorem is trace-class
extension/approximation.  It must justify

```text
T_(n,lambda)
 :=Tr(vartheta_(S_n)(g_(L,n)) Pi_(S_n,lambda)
       vartheta_(S_n)(g_(L,n))^*)
  =Tr(vartheta_(S_n)(h_(L,n)) Pi_(S_n,lambda))
  >=0.                                                       (9)
```

The archimedean analogue is known for the admissible positive-type test class.  The semilocal
trace-class extension, and passage to the sharp `g_(L,n)` and piecewise-linear `h_(L,n)`, are not
proved in the live corpus or cited literature.  Formula `(9)` must be constructed on the full
principal--relative carrier before scalarization so that the exponent-one Euler shell and its
one-body mass are not discarded.

Once `(9)` exists, define the independently source-side comparison scalar

```text
D_(n,lambda):=T_(n,lambda)+FPbox_(S_n)(h_(L,n)).           (10)
```

Here `FPbox` denotes the sharp rectangular specialization of Connes's pinned finite part.  This
definition uses only that finite part and the Sonin projection, not Xi zeros or
the target value `A_L(n)`.  The required comparison theorem then computes `(10)` from the exact
Sonin projection formula as

```text
D_(n,lambda)
 = Def_tau(Pi X Pi,Pi Z Pi)
   + Re Tr(Gamma_(L,n)^* Delta_n Gamma_(L,n)),             (11)

Delta_n=R_(S_n)(z) J_n-J_n R_infinity(z)
       =-R_(S_n)(z) Omega_n R_infinity(z),                (12)
```

or an equivalent pinned relative-resolvent formula.  Here `Z` is the finite Euler logarithm, `X`
is log position completed by Burnol's Gamma conductor, `Omega_n` is their operator-naturality
defect, and `Def_tau` is the internal cyclic trace-defect cocycle.  The canonical place transition
itself has zero cutoff boundary; only operator nonnaturality in the `S_n`-dependent metric can
contribute `(11)`.  The place map is boundedly invertible rather than unitary, so the orthogonal
Sonin projections do not transport flatly; this metric curvature is the candidate location of
`D_(n,lambda)`.

With the sign convention of the semilocal explicit formula, put

```text
b_L(n)=2*rectangularEvenPolarFeature(L,alpha_n)^2>=0.
```

For the even rectangular autocorrelation the pinned finite part is exactly

```text
FPbox_(S_n)(h_(L,n))
 =2*rectangularPrimeAutocorrelationSum(L,alpha_n)
  -GammaCorrection_L(n).                                  (13)
```

Indeed the finite places contribute twice the positive-lag prime autocorrelation, while the real
place contributes the negative of the Lean Gamma correction.  The exact rectangular source law is

```text
Q_L(n)=A_L(n)+GammaCorrection_L(n)
      =b_L(n)-FPbox_(S_n)(h_(L,n)).                        (14)
```

Use this pinned rectangular finite part in `(10)`.  Substitution yields the decisive non-circular
algebra

```text
Q_L(n)
 =[b_L(n)+T_(n,lambda)]-D_(n,lambda).                    (15)
```

The first bracket is nonnegative.  Hence `Q_L(n)^-<=D_(n,lambda)^+<=|D_(n,lambda)|`.  If desired,
the Gamma-free coefficient also satisfies `(3)` with
`B_L=b_L+T`, `kappa_L=-(D+GammaCorrection)`.

## The actual analytic theorem

Pointwise trace class or a post hoc `L2` assertion is insufficient.  The rectangular observer
itself is uniformly bounded.  In logarithmic coordinates `||g_(L,n)||_1<=2L`, so the integrated
unitary representation satisfies

```text
||vartheta(h_(L,n))||<=4L^2.                              (15a)
```

Trace duality therefore sharpens the required bound to

```text
|D_(n,1)|
 <=4L^2 * ||R_(S_n)(z) Omega_n R_infinity(z)||_1
    + |Def_tau(Pi X Pi,Pi Z Pi)|.                        (16)
```

Thus the observer contributes no aperture growth.  The proof-bearing theorem is a direct source
proof that the compensated trace norm and cyclic anomaly have all-epsilon subpower growth; this
already makes the square of `(16)` summable against every `n^(-1-epsilon)`.  Equation `(15)` then
gives directly

```text
Q_L(n)^-<=D_(n,1)^+<=|D_(n,1)|,                          (17)
```

and the existing Xi square-energy gate proves RH.  The estimate must use rectangular support separation and Gamma--Euler
compensation before taking norms.  Boundedness of the Burnol graph, trace class at each fixed
aperture, compactness modulo the principal shell, or exact stabilization of every fixed
rectangular coefficient does not imply the moving-tail estimate uniformly.

The quadratic principal-subtracted Sonin residual is not the obstruction.  Its all-prime
Hilbert--Schmidt energy and positive trace-class square are already summable.  The only live
analytic channel is the degree-one finite-part class in `(11)`: the exponent-one principal shell,
the internal trace anomaly, and the conductor/Euler leakage must be estimated as one compensated
relative object.

## Two-boundary balance must be global

The existing all-depth von Mangoldt--Gamma Cauchy Gram is positive after projecting away the two
boundary characters `w=+1/2,-1/2`, but it cannot be the bulk in `(8)`.

For a source containing one rate `lambda`, every raw Cauchy vector has the form

```text
A(w)=c(lambda,w) A(1/2),                                  (13)
```

away from its Cauchy pole, while at the pole Lean's totalized division makes it zero.  Hence the
canonical projection away from the two boundary vectors kills the entire one-rate packet.  By
contrast, one prime-power atom contributes a nonzero rectangular tent whenever its logarithmic
rate lies in an active fixed or moving window.  Therefore no source-functorial identity can equate
the rectangular one-body mass with the atomwise balanced Cauchy Gram.

The boundary modes must instead be removed globally, after the unbalanced principal Euler mass and
Gamma/polar channel have been assembled.  Even then, a fixed scalar Gamma coordinate is
insufficient.  `GammaConductorSchurCapacity.lean` proves that independently resolved prime
channels force conductor cost

```text
sum_(p in F) R_p,
R_p>=9/(512p),                                             (13a)
```

which diverges; nonzero diagonal damping does not change the cost.  The same theorem supplies the
positive alternative: with fixed conductor capacity `B`, normalized prime covariance `K`, and
`S_F=sum R_p`, positivity forces off-diagonal coherent energy at least

```text
S_F^2/B-S_F.                                               (13b)
```

The valid operation is therefore a Schur/Feshbach reduction of the full coherent covariance, a
Gauss-paired growing Gamma-channel family, or a principal-relative form before scalarization, not
atomwise orthogonal deletion.  The balanced Cauchy packet may still measure inter-rate curvature
or part of `Delta_n`; it is not `B_L(n)`.

## Likely RH proof

```text
rectangular positive-type test h_(L,n)
  -> exact finite semilocal Connes trace on S_n
  -> closed Euler-position plus Burnol-conductor graph
  -> coherent/growing-channel Gamma--prime Schur reduction
  -> sharp-test semilocal Sonin trace-class extension
  -> positive bulk b_L(n)+T_(n,1)
  -> exact Connes--Sonin comparison curvature D_(n,1)
  -> source-uniform relative-resolvent Schatten estimate
  -> weighted square energy of |D_(n,1)|
  -> weighted square energy of Q_L(n)^-
  -> existing Lean theorem
  -> RH.                                                    (14)
```

This is shorter than the full inverse-tilted Hankel route.  That route must transport inverse
prime-log Cauchy packets into positive prime-log Mellin jets and is blocked by a proved diagonal
transport wall.  The rectangular route asks only for one fixed-width autocorrelation family and
one scalar curvature estimate.

## Kill conditions

- **Kill:** the semilocal Sonin trace in `(9)` fails to retain a singleton prime-power contribution.
- **Killed architecture:** independently resolved prime innovations coupled to one fixed scalar
  Gamma conductor; the accumulated Schur cost diverges like the reciprocal-prime sum.
- **Killed architecture:** independent one-prime positive moment-Gram innovations with summable
  trace-class defects.  The one-prime normalized second moment drops by
  `delta_p=3*sqrt(2)/(2p)+O(p^-2)`, forcing `||R_p||_1>=delta_p` and a divergent prime sum.
- **Kill:** the construction discards the coherent cross-prime covariance or growing Gauss-paired
  Gamma channels forced by those two no-go theorems.
- **Kill:** `(11)` depends on a freely chosen self-adjoint extension or boundary condition rather
  than the semilocal Fourier/Sonin source structure.
- **Kill:** the internal trace-defect cocycle is discarded by formal cyclicity without proving its
  relative-trace domain.
- **Kill:** the relative-resolvent trace contains an uncompensated exponent-one prime-harmonic
  component, so its square energy cannot be cofinally controlled.
- **Kill:** the defect is defined as `FP-positiveBulk` with no independent operator-naturality
  formula.
- **Kill:** the proof of `(15)` uses Xi zeros, target Weil positivity, or an aperture selected after
  observing `A_L(n)`.
- **Kill:** cofinal summability is inferred only from finite-level summability, pointwise
  stabilization, compactness, or positive innovations.  A triangular-array counterexample proves
  that this inference is false.
- **Promote:** prove `(9)`, derive `(10)`--`(12)` from the semilocal trace formula and exact Sonin projection, then
  prove a source-uniform estimate implying `(4)`.

## Immediate research tasks

1. Formalize the singleton-collapse theorem for the atomwise two-boundary Cauchy compression and
   retire its direct rectangular identification.
2. Prove the sharp rectangular approximation/trace-class extension `(9)` and write
   `h_(L,n)` inside Connes's semilocal finite-part normalization.
3. Derive the global coherent/growing-channel Schur formula before applying the Sonin projection;
   preserve the covariance energy forced by `(13b)`.
4. Compute the full curvature `(11)`, retaining both the internal trace anomaly and the polarized
   conductor/Euler leakage.
5. Construct the full compensated defect for the canonical finite place set `S_n` and prove that
   its trace norm plus cyclic anomaly has all-epsilon subpower growth.  The reporter norm is already
   uniformly bounded by `(15a)`; independent one-prime defects cannot be summed.

## Gates

- [x] 0 -> 1: exact RH endpoint, finite rectangular place set, positive trace candidate, defect,
  source estimate, and kill conditions identified
- [x] universal cutoff counterterm shown to be aperture-independent by the formalized zero-lag law
- [x] atomwise balanced Cauchy Gram excluded as the rectangular bulk
- [x] fixed scalar Gamma conductor with independent prime channels excluded
- [x] independent one-prime positive innovations with summable defects excluded
- [x] exact capacity--coherence alternative attached
- [x] rectangular reporter norm proved aperture-uniform on paper
- [x] finite-cutoff coordinate stabilization separated from the moving-tail problem
- [ ] prove the sharp-test semilocal Sonin trace-class extension `(9)`
- [ ] derive the exact comparison identity `(10)` and operator formula `(11)`
- [ ] prove the source-uniform relative-resolvent estimate `(15)`
- [ ] derive the weighted square-energy condition `(4)`
- [ ] formalize the analytic identity and estimate, then invoke `(1)`

## Log

- 2026-07-17 -- Created after the whole-corpus proof-shape audit.  The route was sharpened from an
  unspecified positive Gram plus summable defect to a rectangular Connes finite-part curvature
  theorem.  The audit also killed the direct use of the atomwise two-boundary Cauchy Gram as the
  positive bulk: singleton compression vanishes while the rectangular singleton response does not.
- 2026-07-17 -- A second hostile audit killed independent prime innovations against one fixed
  scalar Gamma conductor by formal harmonic Schur-capacity divergence, and killed channelwise
  moment-Gram innovations by the harmonic one-prime second-moment deficit.  The live route now
  requires coherent/growing Gamma channels.  Exact coordinate stabilization and a uniform
  rectangular trace-duality bound remove observer continuity from the open core; only the
  compensated cofinal trace-norm tail remains.
