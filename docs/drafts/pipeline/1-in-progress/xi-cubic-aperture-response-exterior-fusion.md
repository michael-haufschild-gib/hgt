# Xi cubic aperture--response exterior fusion

- **ID:** `xi-cubic-aperture-response-exterior-fusion`
- **Stage:** 1-in-progress
- **Type:** PAPER THEOREM + CONJECTURE
- **Scientific status:** `[CORPUS-NEW PAPER THEOREM] [CONJECTURE] [EXTERNAL NOVELTY UNVERIFIED]`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/XiApertureCubicExteriorMatching.lean` and
  `formal/GaloisForLFunctions/RHTower/VonMangoldtGammaConormalEulerBoundary.lean` and
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusValuationContraction.lean`
- **Source inputs:**
  `XiMobiusContinuousApertureDyadicProjection.lean`,
  `XiMobiusDyadicCubicReflectionApertureNoGo.lean`,
  `XiAperturePoissonResponseSignature.lean`,
  `GammaClockCoronaConormal.lean`,
  `GammaPeriodicConstraintCorona.lean`, and
  `VonMangoldtGammaJuliaBianchiJointGram.lean`.

## Frontier selected by the corpus audit

The separate physical-cutoff Jordan masses are not invariant.  The joined response cancels that
gauge through detector order two, and the first live obstruction is order three: source-side
cross-orbit dispersion must dominate the exact transverse charge.  The true aperture innovation is
a positive Hilbert Gram, whereas the correctly oriented fine-minus-coarse Poisson response has
inertia `(2+,1-)` on every distinct three-node packet.  A finite Hilbert congruence therefore cannot
be the crossing theorem.

The missing object must be constructed before quadratic Gram compression, must retain the complete
valuation tower, must have a source-defined nonzero annihilator, and must be compatible over the
full valuation-depth by response-resolution diagram.  This card identifies the exact finite
determinant-line normalization that such an object is forced to realize.

## Completed cubic source mass

Put

```text
kappa_M = (1/16) * sum_p xiMobiusPrimeContinuousApertureCubicSlopeTerm(p).
```

Every summand is strictly positive and the series is summable, so `kappa_M>0`.  The existing
primewise cubic coefficient law gives, for `x,y>0`,

```text
xiMobiusContinuousApertureCubicKernel(x,y)
  = kappa_M * x^2*y^2/(x+y).                            (1)
```

Thus the actual all-prime cubic germ is not merely congruent to a Cauchy kernel: its single global
normalization is the source-defined positive mass `kappa_M`.

## `[PAPER-PROVED]` Cubic determinant-line matching law

For three positive nodes `x,y,z`, define

```text
C_kappa(u,v)=kappa*u^2*v^2/(u+v).
```

The Cauchy determinant gives

```text
det_3(C_kappa;x,y,z)
 = kappa^3*x^3*y^3*z^3
     *(x-y)^2*(x-z)^2*(y-z)^2
   /(8*(x+y)^2*(x+z)^2*(y+z)^2).                       (2)
```

For `0<a<b`, let `R_(a,b)` be the existing correctly oriented Poisson refinement kernel

```text
R_(a,b)(u,v)=-(L_b(u-v)-L_a(u-v)),
L_c(d)=c^2/(c^2+d^2).
```

The existing response determinant law and its rational factorization give

```text
-det_3(R_(a,b);x,y,z)
 = 2*(b^2-a^2)^3*(x-y)^2*(x-z)^2*(y-z)^2
   / product_(d in {x-y,x-z,y-z})
       ((a^2+d^2)*(b^2+d^2)).                           (3)
```

Define the source/response exterior gain

```text
G^2(kappa,a,b;x,y,z)
 = 16*(b^2-a^2)^3*(x+y)^2*(x+z)^2*(y+z)^2
   /
   (kappa^3*x^3*y^3*z^3
      * product_(d in {x-y,x-z,y-z})
          ((a^2+d^2)*(b^2+d^2))).                      (4)
```

Then `G^2>0` and

```text
-det_3(R_(a,b);x,y,z)
  = G^2(kappa,a,b;x,y,z) * det_3(C_kappa;x,y,z).        (5)
```

The proof is exact cancellation of the common Vandermonde square in `(2)` and `(3)`.  Formula `(4)`
has no collision denominator, so `(5)` continues through node collisions with both determinants
zero.  This is stronger than a determinant ratio defined only after seeing a nonzero target
packet.

Specializing `kappa=kappa_M` makes `(5)` a comparison between the actual all-prime cubic aperture
germ and the actual finite-resolution response refinement.

## `[PAPER-PROVED]` Localization and normalization laws

The exterior gain is necessarily nonuniform.

1. With `y,z,a,b,kappa` fixed and positive,

   ```text
   G^2(kappa,a,b;x,y,z) asymptotic x^(-3) as x -> 0+.
   ```

   Hence no globally bounded exterior converter exists on the whole positive node chamber.

2. Under fixed-shape high-height dilation `(x,y,z) -> (T*x,T*y,T*z)` with fixed resolutions
   `a,b`,

   ```text
   G^2(kappa,a,b;T*x,T*y,T*z) asymptotic T^(-15).
   ```

   Every compact shape chamber therefore eventually lies in a strict exterior-contraction
   regime.  Height localization is forced by the exact formula; it is not a target-dependent norm
   choice.

3. The raw dyadic innovation is order `h^3` entrywise, hence its three-vector Gram determinant is
   order `h^9` and its exterior volume is order `h^(9/2)`.  A finite nonzero response packet can
   only be compared after feature normalization by `h^(-3/2)`.  A bounded map on the raw
   innovations is impossible.

These laws jointly avoid the two prior mistakes: demanding one global contraction and forming the
positive Gram before completing the valuation-resolution source diagram.

## `[PAPER-PROVED NO-GO + POSITIVE SURVIVOR]` The raw Gamma conormal is the wrong boundary vector

Let `L=log m`.  The factorial Gamma conormal applied at one raw Bianchi coordinate is

```text
sum_(k>=0) L^k/(k+1)! = (exp L-1)/L = (m-1)/log m.       (6)
```

Consequently the raw conormal compression of the source coordinate

```text
b_(x,k)(m)=sqrt((Lambda(m)/m)*exp(-x log m))*(log m)^k
```

is

```text
sqrt((Lambda(m)/m)*exp(-x log m))*(m-1)/log m.           (7)
```

At `x=0` its squared prime coordinate is `(p-1)^2/(p log p)`, so it does not even tend to zero
along the prime carrier.  The canonical factorial conormal is therefore not a bounded boundary
functional on the raw Julia--Bianchi prime Hilbert space.  Inserting it directly into the
signature decomposition is retired.

There is a unique coordinatewise normalization which sends the complete conormal power series to
one:

```text
r(m)=log m/(m-1),
r(m)*sum_(k>=0) (log m)^k/(k+1)! = 1.                   (8)
```

After this forced normalization, `(7)` becomes exactly

```text
E_x(m)=sqrt((Lambda(m)/m)*exp(-x log m)).                (9)
```

At `x=0`, `(9)` is the square-root Euler amplitude already carried by the source-Julia leg.  Thus
the missing negative line is not a second independent Gamma vector.  It must be a boundary use of
the same Euler amplitude in a different exterior/current degree.  This is the coordinate-field
analogue of the HTGeometry lesson that completion changes the admissible functional, not the
underlying coordinate field.

The resulting height-localized infinite boundary vector is explicit.  For `z=t+i*u`, `u>0`, and
the valuation coordinate `q=(p,e)` with `n_q=p^(e+1)`, put

```text
E_z(q)=sqrt(log(p)/n_q) * exp(-(u+i*t)*log(n_q)/2).       (9a)
```

Then

```text
|E_z(q)|^2=log(p)*n_q^(-1-u),
sum_q |E_z(q)|^2=sum_(n>=2) Lambda(n)*n^(-1-u)<infinity. (9b)
```

Thus `E_z` is a genuine valuation-complete Hilbert vector on every open height fibre `u>0`, with
no divisor input.  This statement is correct, but the interpretation of `E_z` as the missing
boundary line is false.

## `[PAPER-PROVED NO-GO + POSITIVE SURVIVOR]` Fixed Hilbert vectors miss the cubic aperture

At one prime the true dyadic innovation feature is

```text
U_(h,a)(p,e)=c_p*(1-r)^2*(r^2)^e,
c_p=1/(p+1),  r=exp(-h*a*log(p)/2).
```

After the forced cubic normalization, every fixed depth coordinate satisfies

```text
h^(-3/2) U_(h,a)(p,e) -> 0,                            (9c)
```

while the squared norm has a nonzero cubic limit.  Its mass therefore escapes to valuation depth
`e` of order `1/h`.  In particular, for the Euler vector `(9a)`, put
`alpha=p^(-(1+u+i*t)/2)`, so `|alpha|<1` for `u>0`.  Exact geometric summation gives

```text
h^(-3/2) <E_z,U_(h,a)>_p
 = h^(-3/2) c_p*sqrt(log p)*alpha*(1-r)^2
     /(1-alpha*r^2)
 -> 0.                                                  (9d)
```

The numerator is order `h^(1/2)` after normalization and the denominator tends to
`1-alpha != 0`.  The same escape mechanism kills every fixed Hilbert vector: the normalized
innovation vectors are bounded and coordinatewise null, hence weakly null.  The former
fixed-`E_z` negative-line conjecture is retired.

The positive survivor is structural.  A nonzero boundary current must move on the microscopic
depth scale `e~1/h`, or live in the finite-blind/projective corona rather than the fixed Hilbert
carrier.  The Euler vector remains the correct renormalized Julia coordinate, but it is not the
cubic boundary detector.

## `[PAPER-PROVED NO-GO + POSITIVE SURVIVOR]` The raw odd Xi kernel does not supply the cubic

Assume only for this diagnostic that an off-line zero has horizontal displacement `delta>0`,
height `gamma`, and multiplicity `m`.  For the raw completed odd kernel `O_u`, put
`A=O_delta(0)<0`, choose `u=delta+epsilon`, and use nodes `0,gamma,c*epsilon`.  Then

```text
epsilon^2 det_3[-O_u(x_i-x_j)]
  -> 4*A*m^2*c^4/(1+c^2)^2 < 0,

epsilon^2 det_2[-O_u(x_i-x_j)] -> -4*m^2,

det_3/det_2 -> (-A)*c^4/(1+c^2)^2 > 0.                 (10)
```

Paper proof: write the symmetric matrix with diagonal `-a` and off-diagonal entries `-b,-r,-d`.
Direct expansion gives

```text
det_3=-a^3-2*b*r*d+a*(b^2+r^2+d^2),
det_2=a^2-b^2.
```

The filled Xi pole germ gives `a->A`, `r->A`, `epsilon*b->-2m`, and
`epsilon*d->-2m/(1+c^2)`.  Multiplying the displayed determinants by `epsilon^2` and passing to
the limit gives `(10)`.  The denominator limit is nonzero, so the Schur quotient limit follows by
division.  No numerical input is used.

The three-node matrix has the desired `(2+,1-)` inertia, but its negative direction is inherited
entirely from the already-negative resonant two-node pole block.  After Schur removal, the genuine
third channel is positive.  Therefore the raw odd kernel cannot be the response amplifier whose
first obstruction occurs at order three.  Its positive survivor is exact: any successful source
completion must remove self-resonant pole mass *before* forming finite response determinants.  A
divisor-selected principal-part subtraction is disallowed; the remover must be produced by the
prime--Gamma source.

## `[PAPER-PROVED]` The Gamma-sewn true-aperture contraction

The corpus already contains both sides of a complementary obstruction:

- the inverse Möbius--Schur valuation dressing grows like `sqrt(p)` and is unbounded;
- the doubled-frequency Gamma characteristic decays like `1/p` at energy level;
- Gamma Schur elimination is not a scalar diagonal completion: the coherent valuation covariance
  makes it exactly one valuation-depth shift and retains every finite prime packet by a weighted
  Vandermonde determinant.

Sew the first two factors before completing over primes.  For aperture `x>=0`, prime `p`, and

```text
q_(x,p)=exp(-x*log p),
R_(x,p)=(1+q_(x,p))/sqrt(q_(x,p)),
```

define the source multiplier

```text
C_(x,p)=1/2 * sqrt(phi_infty(2*x*log p)) * R_(x,p),     (11)
```

where `phi_infty(t)=cosh(t)^(-1/2)` is the existing semilocal Gamma characteristic.  Direct source
algebra gives

```text
C_(x,p)^4 = (1+q_(x,p))^4 / (8*(1+q_(x,p)^4)).         (12)
```

The gap factors exactly as

```text
8*(1+q^4)-(1+q)^4=(1-q)^2*(7*q^2+10*q+7).             (13)
```

Factoring `1-C^4=(1-C)(1+C)(1+C^2)` gives the stronger exact tangency law

```text
1-C_(x,p)=(1-q_(x,p))^2*G_(x,p),                       (13a)

G_(x,p)=
 (7*q^2+10*q+7)/[8*(1+q^4)*(1+C)*(1+C^2)],
G_(0,p)=3/8.                                            (13b)
```

This is the first direct source-side explanation for the order-three obstruction found elsewhere
in the aperture corpus.  The unsown continuous Möbius feature already has one factor `1-q`, so

```text
B_x(p,e)-xiMobiusPrimeSchurContinuousForwardDifference(x,p,e)
 = -G_(x,p) * [p^(-1)/(1+p^(-1))] * (1-p^(-x))^3*p^(-x*e). (13c)
```

Thus Gamma sewing is invisible in the linear aperture tangent and first enters the actual source
at exactly cubic order.  The prior cubic determinant was not an accidental truncation: it is the
first grade at which the archimedean sewing can modify the Möbius valuation ray.  It still cannot
replace the full Rees germ.

Hence `0<C_(x,p)<1` for every `x>0`, while `C_(0,p)=1`.  The contraction is therefore genuinely
height/aperture localized: its gap is strict on every open fibre and closes only at the physical
boundary.  It is also bounded away from zero and tends to `2^(-3/4)` as `p->infinity`; consequently
it is noncompact and loses no prime coordinate.  At `x=1`, `R_(x,p)` is literally the existing
unbounded `xiMobiusPrimeSchurValuationRecovery`.  Formula `(12)` proves that Gamma sewing cancels
that unboundedness without collapsing the source.

The multiplier avoids both previous category errors:

1. **HT graph saturation:** every multiplier is nonzero and uniformly separated from zero, while
   the existing valuation Vandermonde minors remain nonsingular.  The complete prime directions
   survive.
2. **Exact resolution deficit:** it is composed with the coherent valuation covariance for which
   Gamma Schur elimination is the depth shift, not with the impossible independently resolved
   diagonal/scalar-conductor block.

But its uniform lower bound exposes another exact no-go.  In fact `C_(x,p)>1/2`, so for every
nonnegative prime-energy profile `a_p`,

```text
sum_p C_(x,p)^2*a_p < infinity  iff  sum_p a_p < infinity.        (14)
```

Thus the sewn multiplier cannot repair the divergent naive continuous frame that moves the prime
weight itself from `p^(-1)` to `p^(-x)`.  Treating it as a free Hilbertization was false.  The
positive survivor is forced: keep the already source-valid critical Möbius damping `p^(-1)`, move
only the valuation ray by the true aperture, and sew Gamma onto that frame.

Put `q_p=p^(-1)` and `r_(x,p)=p^(-x)`.  The resulting source feature is

```text
B_x(p,e)=C_(x,p) * [q_p/(1+q_p)] * (1-r_(x,p))*r_(x,p)^e.        (15)
```

Its completed cross-prime metric is

```text
K_x(p,r)=C_(x,p)C_(x,r)
  * [q_p/(1+q_p)] [q_r/(1+q_r)]
  * (1-r_(x,p))(1-r_(x,r))/(1-r_(x,p)r_(x,r)).                  (16)
```

Equation `(16)` is a genuine infinite Hilbert object, not only a multiplier: it is exactly the
Gram over all valuation depths, its diagonal is summable over all primes for every `x>0`, and its
first `N` depth coordinates separate every injective `N`-prime packet by a nonzero weighted
Vandermonde determinant.  It therefore retains unbounded finite prime rank while respecting the
existing critical source domain.

The permanent Lean target `GammaSewnMobiusValuationContraction.lean` defines the multiplier,
infinite stream map, feature `(15)`, and kernel `(16)`; it proves the fourth-power and gap laws,
the exact quadratic tangency/cubic source correction `(13a)`--`(13c)`, strict contractivity, the
uniform lower bound and no-free-Hilbertization equivalence `(14)`, the complete Gram identity,
all-prime diagonal summability, finite prime-rank faithfulness, the lossless zero-aperture boundary,
and injectivity.

## `[RETIRED]` Cubic-only and one-negative-line completions

The order-three determinant identity `(5)` remains true but cannot define the all-rank crossing.
There are two independent reasons.

First, the normalized cubic aperture has a universal continuum depth profile.  After the change of
variable `omega=log(p)*s`, all prime dependence in the leading cubic grade factors through one
prime vector and the single scalar `kappa_M`.  The cubic associated grade therefore forgets the
prime-dependent hypertranscendence proved elsewhere in the corpus.  The full aperture germ must be
retained before prime fusion.

Second, the Poisson refinement has a signed spectral shuttle with a nontrivial frequency band, not
a globally one-dimensional negative sector.  The exact shuttle and its unique switch were already
formalized in `XiAperturePoissonValuationClockShuttle.lean`; they are not new.  Promoting the
three-node inertia `(2+,1-)` to a one-negative-line all-rank model was invalid.  Equations `(10a)`--
`(11)` from the previous version of this card are retired.

The positive survivor of the cubic calculation is only this: `(5)` is the first exterior tangent
of the full source colligation and fixes its order-three normalization.  It is not the colligation.

## `[CONJECTURE]` Gamma-sewn Rees--Stokes passive source convergence

The bold frontier conjecture now uses an explicit object rather than an unspecified boundary
vector.

Let `B_x` be the fixed-critical source embedding `(15)` with Gram `(16)`, and let `S` be the
coherent valuation shift already identified with Gamma Schur elimination.  The independent
research logs impose an additional hostile constraint: direct sums of positive finite-aperture
norms retain the persistent singleton/father cost, and a sharp norm-one contraction supplies no
aperture power.  Therefore form the signed Stokes current from aperture differences `B_y-B_x`
before taking any Gram square.  Only after its source coefficients have been identified should one
form finite prime/depth KMS completions, using the fixed Gamma connection, `S`, and transition
frequencies `(e+1)log p`.  No Xi zero, multiplicity, or target eigenvector enters the definition.

**Conjecture (source convergence).** There is a source-prescribed cofinal aperture schedule
`x_N>0`, tending to the lossless boundary slowly enough that the full aperture Rees germ is
retained, together with a canonical inverse-tilted Stokes functional on its aperture edges, for
which the signed current has the exact safe-half-plane prime-power coefficients and the resulting
finite KMS/Wightman completions generated by

```text
(inverse-tilted prime coefficients, Gamma connection,
 signed aperture differences of B_(x_N), S)
```

have passive responses converging pointwise at every regular point of the upper half-strip to
`continuedPrimeArchSourceRelativeTrace`.

This conjecture has four nonoptional strengthening clauses.

1. **Full Rees faithfulness.** Every finite aperture jet order is retained before the prime limit.
   The order-`j` grade carries the new prime-log profile forced by differentiating the exact disk
   nodes; the resulting finite profile matrices must have unbounded exact rank.  Replacing the
   Rees germ by `kappa_M` fails this clause.  The fixed-aperture prime-rank part is already proved
   for `(15)`; the aperture-jet rank is the remaining clause.
2. **Pre-Gram Stokes law.** Aperture signs are combined before positivity.  A direct sum of the
   pointwise kernels `(16)` is explicitly disallowed by the prior aperture-cost no-go.
3. **Corona compatibility.** The cofinal limit is taken in the Gamma finite-blind/projective
   boundary topology, not by pairing with a fixed Hilbert vector.  Its graph annihilator is the
   cyclic Gamma source constraint and its translates, so the construction neither saturates nor
   invents a one-dimensional conormal.
4. **Value identity.** On the safe half-plane the signed current, before KMS squaring, must agree
   coefficientwise with the actual inverse-tilted prime source; after the fixed Gamma correction
   the finite responses must agree with the actual
   inverse-tilted prime--Gamma source up to a remainder proved to vanish locally uniformly.  This
   is the producer needed by `riemannHypothesis_of_finiteKMSWightmanResponse_tendsto`; without this
   exact value convergence the construction is only source geometry.

If proved, structural KMS passivity supplies the anti-Herglotz sign and the existing capstone gives
RH.  This is not another RH-equivalent predicate: all finite objects and their positivity are
source-defined; the open assertion is the local-uniform source-value convergence.

## Cheapest decisive falsifiers

1. **Safe-half-plane coefficient test.** Expand the signed aperture Stokes current built from
   `(15)` where both the inverse-tilted source and the Euler series converge absolutely.  If its
   pre-Gram coefficient at any
   prime power differs from the exact filtered von Mangoldt coefficient after the displayed
   quadrature/Gamma correction, the conjecture is false.  This is the first test; no boundary or
   Xi-zero argument is allowed before it passes.
2. **Rees-rank test.** For the first `N` aperture grades on `N` distinct primes, the source profile
   determinant must be nonzero.  Rank bounded independently of `N` proves cubic-style source
   collapse and retires the route.
3. **Cofinal remainder test.** The safe-half-plane remainder must admit a locally uniform majorant
   compatible with independent prime, depth, and aperture limits.  Convergence only along a fitted
   diagonal schedule without path independence is insufficient.
4. **Domain test.** Every source vector used in the response must remain in the fixed-critical
   Hilbert carrier.  Invoking Gamma sewing to admit the divergent moving-prime frame contradicts
   `(14)` and kills the construction.
5. **Quartet sensitivity.** A centered FE--Schwarz rational-quartet surgery must change the
   boundary response before the value limit.  Invariance means the construction is divisor-blind.

## Anti-theatre and external novelty audit

The exact sewn multiplier and the Rees--passive convergence conjecture were searched by their
source terms and formulas.  Searches found the semilocal `S={p,infinity}` moment/Jacobi and prolate
operator parent programme, but no source containing the Möbius--Schur recovery, the Gamma-sewn
multiplier `(11)`, its fourth-power law `(12)`, or the Rees--passive convergence statement.  This
is a noncollision check, not a priority proof; specialist review is still required.

Reject any future claim that merely reproves the Poisson spectral switch, the Gamma valuation
shift, the Vandermonde finite-prime separation, the inverse-tilted source identity, or generic KMS
passivity.  All are already in the corpus or literature.  The new target is the exact composition
and its source-value limit.

## Gates

- [x] fixed Euler Hilbert boundary retired by valuation-depth weak escape
- [x] one-negative-line all-rank extrapolation retired
- [x] cubic-only source collapse identified; full aperture Rees germ required
- [x] Gamma-sewn multiplier constructed and fourth-power law proved on paper
- [x] exact quadratic multiplier tangency and cubic source-correction law extracted
- [x] no-free-Hilbertization theorem `(14)` extracted from its uniform lower bound
- [x] actual all-prime complete-valuation metric `(16)` constructed on paper
- [x] complete Gram, prime summability, and fixed-aperture all-rank laws formalized in Lean source
- [ ] complete the narrow Lean verification of `GammaSewnMobiusValuationContraction.lean`
- [ ] prove finite Rees-grade prime-profile determinants have unbounded exact rank
- [ ] derive the pre-Gram aperture Stokes coefficient formula from `(15)` and the inverse-tilted
      coefficients
- [ ] construct the finite KMS completion only after the signed coefficient identity is known
- [ ] pass the safe-half-plane coefficient test prime-power by prime-power
- [ ] prove locally uniform, path-independent cofinal response convergence
- [ ] discharge `riemannHypothesis_of_finiteKMSWightmanResponse_tendsto`
- [ ] external specialist novelty audit
