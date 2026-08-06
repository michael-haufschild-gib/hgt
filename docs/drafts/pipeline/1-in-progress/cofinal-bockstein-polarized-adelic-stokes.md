# Cofinal Bockstein polarized adelic Stokes

- **Stage:** 1-in-progress
- **Status:** `[CONJECTURE] [OPEN CORE]`
- **Active claim:** `[CONJECTURE — COEFFICIENT_GENERATED_REES_CORONA_SOURCE_ADMISSION]`
  construct, before divisor specialization, an exact irregular realization of the resolved
  prime/depth source whose one directed Rees microstalk has quotient norm equal to the physical
  fixed-metric Stokes excess; prove the strict source boundary lands in the corona kernel.

## Exact target

For every `n >= 2`, Xi divisor support `rho`, ordinary prime `p`, and Tate stage `m`, prove

```text
ccmMobiusThetaCofinalSourceHomologyLanding n
  (xiSupportMultiplicity rho) m (rho : C)
  (xiSpectralPointSupport rho)
  (ccmRationalAdelicOrdinaryPrimeCycleAtom p) = 0.
```

The existing coefficient reader proves this is equivalent to `Re(rho)=1/2`; global target proves
RH. No RH-equivalent condition may occur as a premise.

## Established frontier

- `[CORPUS]` relative group is one-dimensional and its generator is nonzero.
- `[CORPUS]` physical class reads
  `(deningerHalfDensityMateGain n rho - 1) * firstNonzeroXiJet * primeTrace`.
- `[CORPUS]` first nonzero Xi jet and ordinary-prime trace are nonzero.
- `[CORPUS]` finite and archimedean Haar characters cancel on full rational adelic source,
  producing literal Haar trace `epsilon_1` and reduced cyclic source `ker epsilon_0 intersect ker epsilon_1`.
- `[LOCAL-RESEARCH]` finite interval exactness, ordinary cofinal inclusion, mixed cobar exactness,
  regular Meyer--Poisson boundary membership, and relation-kernel exactification do not annihilate
  the coefficient faithfully.

## First hostile discriminator

Write source-inverse and analytic-adjoint positive characters as

```text
alpha_rho(n) = n^(1/2-Re(rho)),
beta_rho(n)  = n^(Re(rho)-1/2).
```

Adelic product formula gives `alpha_rho(n) * beta_rho(n) = 1` for every spectral parameter.
Physical Bockstein vanishing requires `alpha_rho(n) = beta_rho(n)`. Any proposal deriving only
reciprocity, full-product gain one, or zero after trace-erasing completion is `[FALSIFIED]` as an
RH argument.

## Active conjecture

`[CONJECTURE — POLARIZED_ADELIC_STOKES]` There is a global source-pointed singular comparison,
defined before divisor specialization, from the reduced rational adelic cyclic source to the
Gamma/co-Poisson top-conormal target such that:

1. its two endpoint residues are the source-inverse and analytic-adjoint characters separately;
2. the source Real/cyclic symmetry identifies the two residues without inverting the prime label;
3. the comparison is coefficient-faithful on the ordinary-prime top atom;
4. its Stokes boundary is zero in the retained, non-trace-erasing cofinal quotient.

These four clauses would force `alpha_rho=beta_rho`, hence vanish the explicit class.

## Open core

`[OPEN CORE]` Construct clause (2) from literal arithmetic source data. Existing Real structure
conjugates while rational scaling inversion changes `p` to `p^-1`; that proves reciprocity, not
same-prime equality. A valid proof must supply a non-divisor-fitted polarization which removes this
inversion without assuming unitary modular character.

## Failure log

- Full adelic Haar cancellation: kills total product character only; does not kill physical ratio.
- Direct-limit inclusion: sends every top output to zero one stage later; maximally trace-erasing.
- Regular Meyer boundary: fixed Gaussian source is not in boundary range; membership is equivalent
  to desired scalar vanishing.
- Baumslag exactification: lowers nonzero cup to faithful relation-kernel character; does not
  annihilate it.

## 2026-08-03 hostile closure of the pointwise Fourier--Real conjecture

`[FALSIFIED]` The displayed `POLARIZED_ADELIC_STOKES` conjecture cannot be obtained from the
currently formalized source Real structure and functional-equation Fourier symmetry.  The actual
CCM Real involution is coefficientwise and preserves the rational scaling label.  Fourier/Poisson
reflection is the operation which inverts dilation and exchanges the spectral fibres
`s` and `1-s`.  Its square closes the reflected two-point orbit; it does not identify the two
characters inside one fibre.  Treating that orbit exchange as same-prime pointwise equality would
assume the RH-bearing conclusion.

The finite/cofinal alternatives do not repair this failure.  Ordinary closed completion erases
the retained class, while the explicit cofinal quotient retains a one-dimensional generator whose
physical coefficient is exactly `gain - 1`.  Enlarging the boundary by that generator makes the
quotient vanish for every parameter, not only at Xi zeros.

## Frozen successor: actual-edge relative ideal provenance

Let

```text
d_p = primeFirstTraceEssentialSourceDeviation p,
c_p = d_p(2) = 1/p - p/(farPrime p)^2.
```

The proved bounds `3/(4p) <= c_p <= 1/p` show that `c=(c_p)` is the canonical prime-harmonic
relative edge.  For a real modular displacement `t`, put

```text
c_t(p) = p^t c_p.
```

`[PAPER-PROVED POSITIVE SURVIVOR]` The actual edge has the exact reflected trace-ideal fracture

```text
Summable c_t       <-> t < 0,
Summable c_(-t)    <-> t > 0,
(Summable c_t <-> Summable c_(-t)) <-> t = 0.
```

Moreover `1/p-c_p=p/(farPrime p)^2` is summable, so `[c]=[1/p]` modulo `ell1`, independently of
the far-prime presentation.  This is the actual strict-preclosure edge, not the previously known
raw model `p^(-sigma)`.

`[CONJECTURE -- ORDINARY_PRIME_POLARIZED_IDEAL_PROVENANCE]` Construct before divisor
specialization one completed ordinary-prime source class and one literal Gamma/co-Poisson Fourier
comparison such that, after specialization at every Xi Cartier stalk:

1. the two endpoint images are the actual twists `c_t` and `c_(-t)`, with
   `t=2 Re(rho)-1`;
2. both images retain the same nonzero source ancestry modulo trace class;
3. the comparison preserves trace-class membership because it is induced by one source-defined
   Morita/Fourier correspondence, not by a divisor-fitted identification;
4. multiplicity jets travel in a separate compatible filtration.

Clauses 1--3 plus the exact fracture force `t=0`.  Clause 3 is not supplied by the current CCM
Real structure: Real preserves scaling degree, whereas Fourier supplies reflection by swapping
fibres.  The missing producer is therefore the completed Fourier--Morita action on the retained
relative ideal, together with proof that it transports one ancestral class rather than two
unrelated reflected classes.

### Circularity falsifier

It is invalid to define both endpoint twists from `rho` and then declare them images of one class.
The comparison must be constructed on the literal reduced adelic source, before Xi specialization,
and its ideal preservation must follow from an explicit operator/correspondence theorem.  Without
that construction the conjecture is another exact RH criterion, not a proof.

## Dependency-closed proof of the actual-edge law

Fix an ordinary prime `p`, put `P=p`, and write `R=farPrime(p)`.  The construction gives
`P >= 2` and `R >= P^2`.  Its retained coordinate is

```text
c_p = 1/P - P/R^2.
```

Since `R^2 >= P^4 >= 4P^2`,

```text
0 <= P/R^2 <= 1/(4P),
3/(4P) <= c_p <= 1/P.                                      (E1)
```

Also `R^2 >= P^4` gives

```text
0 <= 1/P-c_p = P/R^2 <= 1/P^3.                             (E2)
```

The prime-cubic majorant is summable, so (E2) proves that the actual edge and prime harmonic edge
define the same class modulo `ell^1`.  In particular, every allowed far-prime presentation has the
same quotient class: changing the auxiliary far-prime witness changes `c` by an `ell^1` sequence.

For `t in R`, set `c_t(p)=P^t c_p`.  All terms are nonnegative.  If `t<0`, (E1) and the real-power
law give

```text
0 <= c_t(p) <= P^t/P = P^(t-1).
```

Here `t-1 < -1`; the prime real-power series is summable.  Hence `c_t` is summable.  Conversely, if
`t>=0`, then `P^t>=1`, so (E1) gives

```text
c_t(p) >= c_p >= (3/4)/P.
```

Euler's prime harmonic divergence excludes summability.  Therefore

```text
Summable(c_t) <-> t<0.                                     (E3)
```

Applying (E3) to `-t` gives `Summable(c_(-t)) <-> t>0`.  The two trace-class truth values agree
exactly at `t=0` (where both fail), and they can never both hold.  No divisor, zero, functional
equation, positivity postulate, or spectral conjecture enters this proof.

## Antagonistic scope audit

- **Proved:** literal strict-preclosure edge carries a presentation-independent nonzero class in
  `ell^2/ell^1`; modular twisting has an exact, reflected trace-ideal phase transition at `t=0`.
- **Not proved:** a Gamma/co-Poisson or CCM correspondence sends one source-defined ancestral class
  to both reflected twists.  Equality of their trace-ideal status is therefore not yet available
  at Xi divisor points.
- **Why this is not decorative:** unlike a scalar RH equivalence, (E1)--(E3) is unconditional and
  identifies the exact ideal-valued invariant which any successful physical comparison must
  preserve.  It simultaneously explains Hilbert--Schmidt survival, trace-class failure, reflected
  one-sidedness, and auxiliary far-prime independence.
- **Kill condition for the successor:** if literal Fourier/Morita comparison swaps unrelated source
  fibres, erases the `ell^2/ell^1` class, or preserves only reciprocal product gain, then it cannot
  supply clause 3 and this successor route remains open rather than proving RH.

## Source provenance found: occupancy Fisher equals the essential edge modulo trace class

The apparent gap between the activation/Möbius/Gamma source and the strict-preclosure edge is not
real.  Put `q_p=1/p` and let

```text
F_p = q_p/(1+q_p)^2
    = (xiMobiusPrimeSchurValuationDamping p)^2.
```

The second equality is the already proved activation-disintegration law: `F_p` is simultaneously
squarefree occupancy Fisher information and the square of the Möbius-to-Gamma damping.  Direct
algebra gives

```text
0 <= 1/p-F_p = (2p+1)/(p(p+1)^2) <= 3/p^2.                 (F1)
```

Together with (E2),

```text
|c_p-F_p| <= |1/p-F_p| + |1/p-c_p| <= 4/p^2.              (F2)
```

For the modular twists `c_t(p)=p^t c_p` and `F_t(p)=p^t F_p`, positivity of real powers and (F2)
give

```text
|c_t(p)-F_t(p)| <= 4 p^(t-2).
```

Hence, whenever `t<1`, the difference `c_t-F_t` is in `ell^1`.  Every Xi divisor lies in the open
critical strip, so its centered rate `t_rho=2 Re(rho)-1` satisfies `|t_rho|<1`.  Consequently both
reflected actual edges have literal source representatives modulo `ell1` in the full prime-sequence
module:

```text
[c_(t_rho)]  = [F_(t_rho)]  modulo ell^1,
[c_(-t_rho)] = [F_(-t_rho)] modulo ell^1.                 (F3)
```

This closes clauses 1 and 2 of `ORDINARY_PRIME_POLARIZED_IDEAL_PROVENANCE`: the two endpoint
classes are no longer unrelated analytic decorations.  They are modular transports of one
ordinary-prime Fisher density already selected by diagonal Wold activation, squarefree occupancy,
Möbius depth differences, and Gamma valuation damping.

It does **not** place both twists in one fixed `ell2/ell1` quotient.  The exact formalized Fisher
threshold is

```text
sum_p F_t(p)^2 < infinity                     <-> t < 1/2,
sum_p F_t(p)^2, sum_p F_(-t)(p)^2 < infinity <-> |t| < 1/2. (F4)
```

Thus the whole Xi critical strip `|t|<1` is too large for one common prime `ell2` carrier.  The
outer half-strips are genuine topology escape, not missing estimates.

### Sharpened sole open producer

The current algebraic CCM Morita representation cannot prove the remaining conservation law.  It
lands entirely in trace-class operators, while (E3) says the retained critical Fisher/essential
class is not trace class.  Its ordinary trace and higher restriction formulas therefore consume
an `ell^1` orbit coefficient before the relative class is formed.  The coefficientwise CCM Real
structure preserves scaling degree; analytic Fourier reflection swaps fibres; neither acts on the
retained `ell^2/ell^1` class.

The exact remaining statement is now:

`[OPEN CORE -- GRADED POLARIZED FISHER-IDEAL CONSERVATION]` Construct, before divisor
specialization, a graded/variable-ideal completion of the literal adelic source whose neutral
fibre contains `[F]`, and a source-inverse/analytic-Fourier correspondence between its reflected
fibres such that at every Xi divisor its endpoint maps are `[F_t]` and `[F_-t]` and the
correspondence preserves membership of `ell^1`.  It may not replace these fibres by one fixed
Hilbert completion: (F4) proves that such a carrier does not exist across the whole strip.  Then
(E3) and (F3) force `t=0`, hence RH.

This is strictly narrower than “construct a source” or “prove positivity.”  Source, arithmetic
atom, Gamma ancestry, non-erasure class, both endpoint representatives, critical-strip
moderateness, and ideal classifier are now explicit.  Missing mathematics is one polarized
conservation theorem on a singular relative ideal.  Defining that conservation by declaring the
two endpoint statuses equal is circular; it must follow from a literal Fourier/cyclic operator or
correspondence on the completed arithmetic source.

## 2026-08-04 fixed-Hilbert Fisher completion falsified

`[FALSIFIED]` The polarized Fisher comparison cannot be defined on one fixed prime `ell2/ell1`
completion over the full Xi critical strip.  The source-selected density has the exact formula

```text
F_t(p) = p^t * p/(p+1)^2,
1/4 * p^(t-1) <= F_t(p) <= p^(t-1).
```

Euler's prime-power criterion gives the sharp laws (F4), formalized in
`PrimeFirstTraceEssentialEdgeReflectedIdealGrade.lean`.  Since Xi supplies only `|t|<1`, not
`|t|<1/2`, some admissible divisor fibres leave every proposed common `ell2` carrier.

**Strongest positive survivor.**  The trace-ideal classifier survives unchanged:
`F_t in ell1 <-> t<0`.  What changes is the representation.  A viable singular Cartier object
must be a graded variable-ideal/off-diagonal correspondence carrying reflected fibres, with
`ell1` as the conserved subobject; it cannot be an ordinary bounded operator, one fixed Hilbert
completion, or a two-sided-singular relation without additional source invariance.  The new
`two-sided-singular-gelfand-defects` manuscript reinforces the last point: abstract countable
noncoercive observers admit large common closed avoidance spaces, so singularity alone supplies no
selection.

## 2026-08-04 strict cyclic-provenance audit

The new source-dagger manuscript and
`MobiusThetaPhysicalParacyclicSourceNullHomology.lean` sharpen the scalar obstruction but do not
yet construct the chain-level source claimed by the phrase “source-null-homology.”  Precisely:

- `CCMRationalAdelicDegreeOneCyclicSource` is the degree-one cyclic-bar tensor object;
- the ordinary-prime object is proved to have product trace one, but is not proved to lie in the
  kernel of the Hochschild degree-one boundary;
- the product reporter is invariant under cyclic rotation, but the same formal module proves it
  does not annihilate all degree-two Hochschild boundaries when the unit trace is nonzero;
- `ccmMobiusThetaCofinalSourceHomologyLanding` is a linear map directly scaled by the Xi jet and
  the product reporter; it is not proved to factor through Hochschild/cyclic homology or to be a
  component of a strict chain map.

Therefore the current one-dimensional Tate cokernel is a correct retained obstruction quotient,
but calling its old product-trace input a cyclic homology class would be theatre.

The missing chain producer is now constructed and formalized in
`CCMRationalAdelicPrimeIsotropyRelativeXiChainMap.lean`.  The prime zero-isotropy relative complex
has unconditional `D_1 D_0=0`; its ordinary-prime class is retained by a Schwartz fixed-vector
theorem; and a strict prime-faithful chain map sends it nontrivially to the resolved actual-Xi
complex, where it is annihilated.  The formal classification also proves that this image is a
target boundary.  Thus strict rational-adelic provenance is closed, but the physical/scalar
cofinal landing is not: the open Bockstein/Route-R theorem must compare this resolved boundary to
the singular coefficient-faithful Cartier quotient without replacing the comparison by the
RH-equivalent statement that the physical coefficient vanishes.

The source class now also has an independent normalized Stokes period in
`CCMRationalAdelicPrimeIsotropyStokesRegulator.lean`.  The bilateral prime orbit sum converges at
both archimedean ends and satisfies `R_p(alpha_p x-x)=epsilon_0(x)` on the actual adelic core.
Hence `I_p(y,z)=z-R_p(y)` kills every relative boundary and descends to `H^1` with
`I_p([eta_p])=1`.  Source Stokes flatness and class retention are therefore closed without using
Xi.  This makes the remaining obstruction sharper: the strict Xi image is nevertheless a target
boundary, so missing Cartier step cannot be an ordinary boundary-preserving cohomology map.  It
must be a source-constructed singular/secondary comparison retaining the chosen Xi primitive and
the graded `ell1` subobject; declaring its physical anomaly zero is still exactly RH.

## 2026-08-04 explicit cofinal Gamma Bockstein

The fixed-ideal obstruction has now been constructed as one literal class.  For centered grade
`t`, define

```text
beta_t=[F_(-t)]-[F_t] in (P -> C)/ell1.
```

`PrimeFirstTraceGammaCofinalNormalizerFrontier.lean` proves unconditionally, for `|t|<1`,

```text
beta_t != 0  <->  t != 0.
```

This class is invisible at every finite stage: a Gamma multiplier supported on a finite prime set
induces the identity modulo `ell1`, so its finite Bockstein is zero.  The full multiplier preserves
the fixed ideal exactly for `t>=0`; its reflection preserves it exactly for `t<=0`; both preserve
it exactly at `t=0`.

The construction is now source-derived on the actual Xi landing.  The two physical images of the
same retained period-one rational-adelic class differ by

```text
(first nonzero Xi jet at rho) * beta_(2 Re(rho)-1).
```

The jet is proved nonzero, so this physical source Bockstein is nonzero exactly off the critical
line.  Its global annihilation is equivalent to RH.  This is new obstruction-level knowledge, not
the missing annihilation theorem.

**Sharpened open producer.** Construct from the literal infinite-prime arithmetic source a
coefficient-faithful singular secondary boundary whose fixed-fibre physical image is exactly this
`beta` class and whose independent Stokes/Cartier law annihilates it.  No finite-prime naturality,
ordinary boundary-preserving comparison, transported variable norm, or fixed-Hilbert completion
can supply the law: the first is quotient-trivial, the strict source image is already a target
boundary, and the latter two preserve the wrong ideals.  The proof must act at the singular
cofinal all-prime boundary and cannot use `beta=0`, equal trace-class status, or critical-line
placement as a premise.

## 2026-08-04 all-order Schatten reformulation

### Killed precursor: one Hilbert--Schmidt two-boundary

`[FALSIFIED]` A divisor-independent pair of global Hilbert--Schmidt source legs whose trace-class
product has prime diagonal `F_(-t)-F_t` cannot exist over the whole spectral strip.  The diagonal
of a trace-class operator is `ell1`, whereas the proved cofinal Bockstein classification gives

```text
[F_(-t)-F_t]=0 in (P -> C)/ell1  <->  t=0.
```

Thus a universal Hilbert--Schmidt factorization would force every strip parameter to have grade
zero.  Restricting the Hilbert--Schmidt hypothesis to actual Xi zeros would merely rename the
desired RH admission theorem.

**Representation lesson.** Route R cannot use one fixed Schatten exponent.  The literal
occupation `det2` kernel is not trace class but belongs naturally to every Schatten class above
order one.  The source completion should retain this entire order scale.

### Sharp Bockstein Schatten wall `[FORMALIZED BRIDGE]`

Put

```text
Delta_t(p)=F_(-t)(p)-F_t(p),
F_t(p)=p^t p/(p+1)^2.
```

For every real `t` and `q>0`,

```text
sum_p |Delta_t(p)|^q < infinity
  <-> t=0 or q*(1-|t|)>1.                         (S1)
```

Consequently, for every real `t`,

```text
Delta_t in intersection_(q>1) ell^q  <-> t=0.    (S2)
```

**Proof.** If `t=0`, `Delta_t=0`.  Suppose `t!=0` and put `u=|t|`.  Up to the sign of `t`,

```text
|Delta_t(p)|
 = F_u(p)-F_(-u)(p)
 = F_u(p)*(1-p^(-2u)).
```

For every ordinary prime `p>=2`,

```text
1-2^(-2u) <= 1-p^(-2u) <= 1,
1/4*p^(u-1) <= F_u(p) <= p^(u-1).
```

The first lower constant is strictly positive because `u>0`.  Hence `|Delta_t(p)|^q` is bounded
above and below by positive constants times `p^(-q*(1-u))`.  Euler's prime-power criterion says
the latter prime series converges exactly when `q*(1-u)>1`, proving `(S1)`.  If `0<u<1`, choose
`q=(1-u)^(-1)>1`, which lies exactly on the divergent threshold.  If `u>=1`, already `q=2`
violates the strict inequality.  This proves the reverse implication in `(S2)` globally.  The
forward implication at `t=0` is immediate.

Lean module `PrimeGammaCofinalBocksteinSchattenWall.lean` proves `(S1)`, both uniform prime-power
bounds, and the unrestricted equivalence `(S2)` with no critical-line or fixed-ideal premise.

This classifier is not the RH producer.  It identifies the weakest all-order regularity that
would force annihilation without assuming fixed `ell1` preservation or one common Hilbert
carrier.

### Frozen conjecture

`[CONJECTURE — UNIVERSAL_1PLUS_SCHATTEN_STOKES_CARTIER_LANDING]`

Let `S_(1+)` be the projective-limit operator ideal

```text
S_(1+) = intersection_(q>1) S_q
```

on the literal prime/depth occupation carrier.  There is a source-normal mixed Stokes/Cartier
two-boundary, constructed before divisor specialization, with all of the following properties:

1. its finite-prime restrictions are the already constructed graded-`det2`/BV source boundaries;
2. these restrictions form one Cauchy object in `S_(1+)`, not merely in every divisor-fitted
   variable ideal;
3. singular Xi principal-Cartier base change is a continuous, coefficient-faithful reporter from
   this same `S_(1+)` object to `intersection_(q>1) ell^q(P)`;
4. on the retained period-one rational-adelic class at `rho`, its reported prime diagonal is

   ```text
   j_rho * Delta_(2 Re(rho)-1),
   ```

   where `j_rho` is the already proved nonzero leading Xi jet;
5. multiplicity jets travel in a separate filtered channel, so no simplicity premise is inserted.

Clauses 2--3 are source-topological statements, not declarations that `Delta_t` is summable.
Clause 4 is the coefficient computation.  They imply `Delta_(2 Re(rho)-1)` lies in every
`ell^q`, `q>1`; `(S2)` then gives `Re(rho)=1/2`.  Equivalently the fixed-quotient class `beta`
vanishes in both Gamma orientations.

### Hostile falsifiers and open core

- Product-topology completion is excluded: finite-support sequences are dense and the quotient
  loses the Bockstein.
- One fixed `S_2` carrier is excluded by the sharp outer-half-strip escape.
- A family of `q`-norms chosen after seeing `rho` is circular.  One projective-limit topology and
  one reporter must exist before Xi specialization.
- Mere membership of the occupation kernel in every `S_q` is insufficient.  The load-bearing
  theorem is continuity of the singular Cartier reporter on the completed mixed boundary.
- Generalized-prime systems must fail Clause 2 or Clause 3; otherwise the conjecture is false.

`[OPEN CORE]` Construct the mixed boundary on the existing nonseparable prime/depth source and
prove Clause 2 directly from its occupation coefficients.  Then construct the Cartier reporter
on the algebraic core and prove one uniform seminorm estimate for every `q>1`.  No Lean work on
this conjecture is licensed until those two paper proofs close.

## 2026-08-04 hostile correction: ambient `S_(1+)` landing is impossible

`[FALSIFIED] [NO-GO]` Clause 3 of
`UNIVERSAL_1PLUS_SCHATTEN_STOKES_CARTIER_LANDING` cannot hold on an ambient strip family.
Indeed, suppose one pre-divisor continuous reporter were defined for every `|t|<1`, took values
in `intersection_(q>1) ell^q(P)`, and reported `Delta_t`.  The sharp wall `(S2)` would then give
`t=0` for every parameter in the strip, a contradiction.  This is independent of the choice of
occupation presentation.

Restricting the reporter to the set of Xi divisor points does not repair the proof: the statement
that its value lies in the all-order ideal at each such point is, by `(S2)`, already the
critical-line assertion.  Passing to the principal Cartier quotient `O/(Xi)` changes the domain
but not this logical burden unless the quotient reporter is constructed as the boundary of an
independent source complex.  Thus the all-order ideal is a sharp **reader**, not the producer.

The positive survivor is `(S1)`--`(S2)`: it gives the complete variable Schatten-order spectrum
of the explicit cofinal Gamma Bockstein and proves that no ambient locally convex operator ideal
can supply the desired boundary law merely by continuity.

## Frozen replacement: corrected determinant-line Stokes monodromy

`[CONJECTURE — SINGULAR_ALL_PRIME_CORRECTED_DET2_CARTIER_MONODROMY]`

Let `U` be the literal two-orientation rational-adelic source double generated by an ordinary
prime cycle and its cyclic rotation.  Its source rotation is

```text
tau(x,y)=(y,x),                 det(tau)=-1.
```

Let `omega_src` be its nonzero top exterior orientation.  The all-prime Calderon--Witt oriented
complex already proves that every prime copy of this orientation represents the same normalized
top source line and that differences of copies are exact oriented boundaries.

At a divisor point `rho`, put

```text
j_rho = XiC^(m_rho)(rho) != 0,
delta_(n,rho)=exp((2 Re(rho)-1) log n),
R_(n,rho)(x,y)=(y,delta_(n,rho)x).
```

The existing physical source landing supplies the nonzero determinant-line value

```text
Omega_rho(omega_src)=j_rho^2 (e_0 wedge e_1).
```

There is a source-pointed singular Cartier connection over the cofinal all-prime boundary with
the following properties.

1. Its algebraic core is defined before an Xi divisor is selected and retains prime, inverse
   prime, depth, divisor, and multiplicity-jet provenance.
2. Its two finite Stokes legs are the already constructed graded-`det2` occupation boundary and
   singular BV first-trace boundary.  Their corrected determinant is the Hilbert--Carleman
   `det2` determinant plus the first-trace Cartier counterterm, not an ordinary trace-class
   determinant.
3. The corrected determinant of every Stokes factor is one.  Equivalently the quadratic regular
   Wold--Gamma cocycle and singular BV first trace form one determinant-line coboundary.
4. The total singular monodromy comparison on the nonzero orientation line is

   ```text
   Omega_rho o (wedge^2 tau)
     = (wedge^2 R_(n,rho)) o Omega_rho
       o (product of corrected Stokes factors).
   ```

5. The product is formed in the source singular completion and is a literal boundary law; no
   fixed-ideal preservation, critical-line placement, `beta=0`, or divisor-fitted norm occurs in
   its construction.

### Exact consequence `[PAPER-PROVED CONDITIONAL CAPSTONE]`

Taking corrected determinants in Clause 4 and using Clauses 2--3 gives

```text
det(tau)=det(R_(n,rho)).
```

The two determinants are `-1` and `-delta_(n,rho)`.  Hence
`delta_(n,rho)=1`.  Since `n>=2` and the exponent is real,

```text
2 Re(rho)-1=0.
```

Thus `Delta_(2 Re(rho)-1)=0` coefficientwise and the explicit source-derived physical Gamma
Bockstein vanishes.  This implication uses neither a fixed summability ideal nor beta
annihilation as a premise.  Multiplicity is harmless because `j_rho^2!=0` for the first nonzero
jet.

### Hostile audit and exact open core

- Defining the Stokes product after choosing `rho` is circular.  It must be the specialization of
  one all-prime source connection.
- Unipotence of abstract Stokes matrices is insufficient.  Clause 2 must identify their
  corrected determinant with the existing explicit `det2`/BV class.
- Reflection-hyperbolic determinant one is not Clause 4: it compares two divisor fibres and holds
  for every rate.  The conjecture transports the one source top orientation into the determinant
  line of one physical Cartier fibre.
- A rank-one landing cannot carry the determinant comparison.  The ordered prime/inverse-prime
  source double and its nonzero wedge must be retained before the cyclic trace.
- Product topology is excluded by maximal verticality; ordinary Hilbert topology is excluded by
  the sharp outer-half-strip escape.  The completion must be singular and source-pointed.

`[OPEN CORE — DET2_BV_STOKES_DETERMINANT_COMPARISON]` Construct the corrected determinant functor
on the algebraic finite-prime/depth Stokes bicomplex, prove compatibility under aperture
enlargement, and identify its cofinal Cartier monodromy with the physical `R_(n,rho)` on the
nonzero leading Xi wedge.  This—not another selector or quotient—is the missing producer.

## 2026-08-04 determinant transgression and Witt-law correction

### Common corrected determinant is not the producer `[FORMALIZED NO-GO]`

For ordinary prime `p`, real grade `t`, and positive Fisher density `d(p)`, define the signed
Bockstein coefficient and two physical rotation determinants by

```text
b_t(p)=F_(-t)(p)-F_t(p),
det R_t(p)=-p^t,
det R_(-t)(p)=-p^(-t).
```

Then

```text
b_t(p)=d(p) (det R_t(p)-det R_(-t)(p)).          (D1)
```

Since `d(p)>0` and `p>1`,

```text
b_t(p)=0
 <-> det R_t(p)=det R_(-t)(p)
 <-> det R_t(p)=det tau=det R_(-t)(p)
 <-> t=0.                                        (D2)
```

If a corrected Stokes determinant `c` is common to both orientations and `c!=0`, cancellation
gives

```text
c det R_t(p)=c det R_(-t)(p) <-> t=0.            (D3)
```

Thus Clause 3 of `SINGULAR_ALL_PRIME_CORRECTED_DET2_CARTIER_MONODROMY`, when interpreted as one
common determinant-one correction, cannot annihilate the explicit Bockstein.  It preserves its
vanishing locus exactly.  Comparing either physical determinant with the cyclic source
determinant is already the neutral-grade assertion.  A valid Stokes producer must be genuinely
orientation-sensitive before Xi specialization; unimodular conservation is insufficient.

Equations `(D1)`--`(D3)` are formalized in
`PrimeGammaCofinalBocksteinDeterminantTransgression.lean`.

### Contribution of the Lorentzian Stokes coarea law

The coefficient-generated Stokes theorem gives, for a realized finite Puiseux spectrum,

```text
Q=P-lambda M^2,    P>0,
ind^-(Q)+null(Q)<=1.
```

Fusion, topology, nonnegative multi-Rees specialization, and positive corona elimination retain
the same unique nonpositive rank port.  This sharply supports Route R's observed one-scalar
frontier, but it does **not** annihilate that scalar.  The paper's corona exact sequence

```text
0 -> X -> X+Y -> Y -> 0
```

identifies the quotient with `Y`; exactness alone does not put a specified landed vector in the
kernel of the quotient map.

The exact Route-R fixed-source excess is already

```text
Delta(a,i,j,c)
 = |(a theta_ij/(lambda_i lambda_j)) c|^2,
```

where `a=2 Re(rho)-1`, `theta_ij` is the resolved BV--Wold connection coefficient, the lambdas
are positive Wold--Gamma clocks, and `c` is the nonzero first Xi jet.  This suggests a precise
Rees coordinate

```text
z_(i,j)=tau_(i,j) nu_(i,j),
tau_(i,j)=a theta_ij/(lambda_i lambda_j),
```

whose directed microstalk norm would be `Delta`.

### Frozen replacement conjecture

`[CONJECTURE — COEFFICIENT_GENERATED_REES_CORONA_SOURCE_ADMISSION]`

There is a pre-divisor irregular realization of the existing resolved rational-adelic
prime/depth complex satisfying all five clauses:

1. finite prime/depth coefficients generate an equivariant Puiseux spectrum and its canonical
   cut/Rees incidence without using an Xi zero;
2. the strict resolved source differential and period-one Stokes regulator are carried by an
   exact functor to the analytic-wall germ and its corona sequence;
3. the unique edge microstalk coordinate specializes on the physical Xi conormal to

   ```text
   ((2 Re(rho)-1) theta_ij/(lambda_i lambda_j)) c_rho;
   ```

4. the source boundary law places that specialized vector in the image of the corona inclusion,
   so its quotient microstalk is zero;
5. the construction extends across Rees parameter zero, where exponential factors collide, and
   retains prime, inverse-prime, depth, divisor, and multiplicity-jet provenance.

Clauses 1--3 identify the quotient norm with `Delta_rho`.  Clause 4 forces that norm to zero.
On the certified nonzero edge and nonzero leading Xi jet, the existing formal classifier then
gives `Re(rho)=1/2`.

### Exact open core and falsifiers

`[OPEN CORE — SOURCE_TO_CORONA_KERNEL_ADMISSION]` Construct Clauses 1--2 on the literal arithmetic
source and prove Clause 4 before selecting a divisor.  This is narrower than a general irregular
Riemann--Hilbert theorem and stronger than the abstract Witt law.

- The Witt index bound only proves uniqueness of a nonpositive channel, not its vanishing.
- Corona exactness identifies a quotient; it does not kill an arbitrary quotient coordinate.
- Puiseux contact orders and microstalk ranks are discrete.  Equality with the analytic norm
  `Delta` requires an additional metric/Rees comparison, not wall counting alone.
- Choosing `tau` after seeing `rho` is circular.  It must specialize from the global source Real
  family carrying both Gamma orientations.
- At `tau=0` the two exponential factors collide; a realization valid only for distinct factors
  cannot prove critical-line admission.
- Any exact functor built from the already curved scalar physical connection simply assumes the
  conclusion.  It must start from the unconditionally flat resolved rank-two source.

### Formal metric identification of the unique physical rank port (4 August 2026)

The coefficient and metric comparisons are now unconditional.  For every real grade `t`, ordinary
prime `p`, and conormal coefficient `c`, let `kappa(t,p)` be the graded Bockstein-to-corona factor.
Lean proves

```text
kappa(t,p) > 0,
B_t(p) = -kappa(t,p) tau_t(p),
B_t(p)^2 |c|^2 = kappa(t,p)^2 Delta(t,(p,0),(p,1),c).
```

Here `B_t(p)` is the signed all-prime Gamma Bockstein/determinant-transgression coefficient and
`tau_t(p)` is the literal adjacent-depth Rees--corona weight.  The last identity is also proved
with `Delta` replaced by the exact `CoronaSchur.coronaCorrection`.  Thus the cofinal determinant
transgression and the Lorentzian Stokes physical rank port are not merely zero-equivalent: their
positive energies agree up to an explicit strictly positive square, with prime/depth provenance
retained.  This closes the metric-port identification part of Clauses 1--3.

Formal anchors:

- `PrimeDepthBVWoldReesCoronaQuotient.lean` constructs resolved and fixed physical lifts and proves
  resolved quotient zero, physical quotient `tau_t(p)c`, and corona energy `Delta`;
- `PrimeGammaBocksteinReesCoronaComparison.lean` proves the positive coorientation and the two
  energy identities above.

Hostile audit of the corrected `det2` square: its positive channel is the hidden compensator energy
`Delta`, not an independently vanishing source energy.  Therefore unconditional corrected
`D1 D0=0` cannot be substituted for physical admission.  Exact remaining producer is unchanged
but now has no coefficient or metric ambiguity: prove from pre-divisor source structure that the
fixed physical lift lies in the harmonic corona graph, equivalently annihilate this one identified
positive rank port.  No RH proof is claimed.

## 2026-08-04 harmonic-corona source-structure audit

### Exact shear classification `[PROVED HERE; BRIDGE]`

Let `V` be a finite-dimensional real inner-product space and let `K : V -> V` be self-adjoint.
On `V x V` put

```text
q_K(x,y) = Kx+y,
h_K(x)   = (x,-Kx),
S_K(x,y) = (x,y+Kx).
```

Then

```text
q_0 S_K = q_K,             S_K h_K = h_0,
pi_1 S_K = pi_1,
Omega(S_K z,S_K w)=Omega(z,w),
Omega((x,y),(x',y'))=<x,y'>-<y,x'>.
```

The last identity uses only self-adjointness of `K`.  Thus `S_K` preserves the coefficient
projection, exact extension, alternating cup/intersection form, determinant orientation, and
the full resolved chain law while carrying the harmonic graph to the fixed zero-hidden section.
Moreover, if `g_0` is the product positive form and `g_K=S_K^*g_0`, then `S_K` is an isometry
from the transported resolved polarization to `g_0` for every `K`.  This is precisely why the
already-constructed varying positive polarization is nonselective.

In contrast,

```text
S_K is an isometry of the same fixed product form g_0  <->  K=0.
```

Indeed, applying fixed-form norm preservation to `(x,0)` gives
`||x||^2+||Kx||^2=||x||^2` for every `x`, hence `K=0`; the converse is immediate.  Equivalently,
`S_K` commutes with the fixed odd Hodge rotation exchanging the two factors exactly when `K=0`.

For Route R, `K=tau_(i,j) id`, so on the certified edge and nonzero Xi conormal this fixed-form
condition is exactly `Delta=0`, harmonic-corona admission, and critical-line placement.

### Killed source enhancements

- `[FALSIFIED]` A second cup or intersection mate by itself forces harmonic admission.  The shear
  is symplectic, so the nondegenerate derived Calderon--Witt cup and its Milnor-incidence Green
  splitting remain unchanged for arbitrary `tau`.
- `[FALSIFIED]` Transported positivity forces the fixed physical section to be harmonic.  Pullback
  metric `g_K` makes the shear unitary for every `tau`; it is not the fixed physical metric.
- `[FALSIFIED]` Ordinary source cyclicity makes the cofinal defect a retained source boundary.
  The explicit cofinal relative class has period one.  Over the complex coefficient field,
  annihilating `(delta-1)` times that class off the unit-monodromy locus annihilates the retained
  generator itself.  The formal minimal stable defect boundary is therefore the whole physical
  two-leg target off line.
- `[FALSIFIED]` Wild/Stokes exactness selects an arbitrary lift.  The corona exact sequence
  determines `ker q_K=im h_K`; it supplies no reason that `h_0(c)` belongs to this kernel.

### Surviving exact producer

`[CONJECTURE — SOURCE_DAGGER_FIXED_POLARIZATION_CARTIER_DESCENT]` Construct before divisor
specialization a morphism from the literal rational-adelic cyclic source, together with its
source Hodge mate, into the coefficient-generated corona extension such that:

1. the period-one ordinary-prime atom lands on the fixed zero-hidden physical section;
2. its source Hodge mate lands on the fixed odd-Hodge mate, not the shear-transported mate;
3. the cyclic equivariance defect is an arithmetic Cartier boundary killed by a source-derived
   period regulator;
4. the atom remains nonzero modulo that boundary in both Gamma orientations;
5. comparison preserves the fixed source polarization and Cartier dagger before any Xi stalk is
   selected; and
6. specialization agrees with the already-constructed resolved chain map and with the exact
   Bockstein-to-corona coefficient/energy comparison.

The shear classification proves that Clauses 1--6 force `K=0`; the nonzero leading Xi jet then
gives RH through the existing formal consumer.  It also proves that replacing Clause 5 by cup,
exactness, a transported metric, or an abstract harmonic metric is insufficient.

`[OPEN CORE — FIXED_POLARIZATION_PRODUCTION]` Derive Clause 5 and the nonerasing boundary in
Clauses 3--4 from the pre-divisor Euler--Gamma--rational-adelic source.  Current source objects do
not imply it: the explicit shear is a countermodel to every presently proved invariant clause.
No unconditional source annihilation theorem or RH proof is claimed.

## 2026-08-04 pre-divisor rational-adelic / reflected-Gaussian Cartier comparison

### New dependency-closed bridge `[PROVED ON PAPER AND IN LEAN]`

Let `H_p^1` be the genuine ordinary-prime zero-isotropy relative cohomology, let
`R_p : H_p^1 -> C` be its bilateral Stokes regulator, and let `eta_p` be its retained class.  The
existing source theorem gives `R_p(eta_p)=1`.  Let `h_G` be the fixed reflected Meyer Gaussian
horizon, constructed before divisor restriction by the two exterior absolute-Euler Cauchy lines.
Its Xi restriction is square summable and nowhere zero, is invariant under functional-equation
reflection, and intertwines line conjugation with coefficient conjugation.  The singular
Gamma-residue normalizer carries the forced Cartier residue exactly to `h_G`.

Define

```text
C_p(x) = R_p(x) h_G,
J_p(x) = -G C_p(x),
```

where `G` is the already constructed completed source Green linear isometry.  Then:

1. `C_p(eta_p)=h_G`, and this is exactly the source-graded singular Cartier residue;
2. `C_p(x)=0 <-> R_p(x)=0`, because every coordinate of `h_G` is nonzero;
3. both upper and lower absolute-Euler Gamma Cauchy legs of `eta_p` are nonzero for every real
   boundary parameter: the Gaussian exponential and the regular-point Cauchy denominator never
   vanish;
4. the two-sided Gamma boundary integral is exactly `C_p(eta_p)`;
5. `J_p(eta_p)` is the unique completed Green primitive and is the integral of the oriented
   two-sided Gamma boundary;
6. the fixed completed-Xi Hilbert polarization is preserved exactly:

```text
<J_p(x), J_p(y)> = <C_p(x), C_p(y)>;
```

7. the atom is retained under both functional-equation reflection and Hermitian line
   conjugation.

This bridge is source-first in the relevant sense: the coefficient is supplied by the independent
rational-adelic period and the vector is reconstructed from pre-divisor Euler--Gamma Cauchy data;
no divisor-indexed interpolation or pulled-back source norm is introduced.

Formal module:
`GaloisForLFunctions/RHTower/CCMRationalAdelicReflectedGaussianCartierComparison.lean`.

### Exact surviving obstruction `[OPEN CORE NARROWED]`

This theorem closes the missing provenance link and the two-orientation non-erasure part, but it
does **not** identify the completed-Xi Hodge isometry with Route R's fixed same-fibre product metric.
After applying the actual Green covariance fracture, the retained atom becomes

```text
D_G(C_p(eta_p)) = reflectedGaussianHorizonGreenProvenance,
```

and Lean proves unconditionally

```text
D_G(C_p(eta_p)) = 0 <-> RiemannHypothesis.
```

Thus the Cauchy/Cartier comparison cannot itself be cited as source annihilation.  Clauses 3--4 of
the surviving producer now have an explicit source realization, and a fixed completed-Hilbert
polarization is preserved.  Remaining hard theorem is stricter: prove that this independent source
polarization specializes to the **same fixed physical corona polarization** and fixed zero-hidden
lift, rather than to the completed Green/Hodge mate.  The shear countermodel still blocks replacing
that specialization law by transported positivity or abstract isometry.

## 2026-08-04 completed-Xi fixed-corona polarization normal form

### Frozen statement `[BRIDGE — PROVED ON PAPER]`

Fix a multiplicity-exact Xi copy `q`.  Write

```text
E_q(c) = lp.single(2,q,c) in XiDivisorL2,
R(c)   = (Re c, Im c),
w_q    = i sign(Im(q.1)).
```

The canonical completed-Xi basis is orthonormal, while the source Hodge multiplier satisfies
`|w_q|=1` and `w_q^2=-1`.  On the two-channel coefficient plane define

```text
U_q(z_0,z_1) = (R(z_0), R(-w_q z_1)),
J_q(z_0,z_1) = (w_q z_1, w_q z_0).
```

Put the fixed completed-Xi real polarization on the source plane and the fixed Route-R product
polarization on the target:

```text
g_Xi(z,u) = Re <E_q(z_0),E_q(u_0)> + Re <E_q(z_1),E_q(u_1)>,
g_cor((x,y),(x',y')) = x dot x' + y dot y'.
```

Then, without any critical-line or fixed-ideal premise,

```text
g_cor(U_q z,U_q u) = g_Xi(z,u),
U_q(c,0)           = (R(c),0),
U_q(J_q(c,0))      = (0,R(c)),
U_q J_q            = J_0 U_q,
J_q^2              = -1,
```

where `J_0(x,y)=(-y,x)` is the fixed odd-Hodge rotation of the corona product.  The first equality
uses the literal completed-Xi norm, not a transported or divisor-fitted metric: orthonormality gives
`<E_q(c),E_q(d)>=conj(c)d`, and realification gives
`R(c) dot R(d)=Re(conj(c)d)`.  Multiplication by `-w_q` preserves this form because `|w_q|=1`.

The hidden trivialization is canonical.  If a real-linear `T : C -> R^2` satisfies
`T(w_q c)=R(c)` for every `c`, then `w_q^{-1}=-w_q`, hence necessarily

```text
T(z)=R(-w_q z).
```

Thus no arbitrary gauge or pulled-back metric has been selected.

### Coefficient-faithful Route-R specialization

For ordinary prime `p`, support point `rho`, and rational-adelic relative class `x`, take the first
multiplicity copy `q_rho` and the already constructed coefficient

```text
c_(p,rho,x) = R_p(x) * XiC^(m_rho)(xiSpectralPointSupport rho).
```

The completed vector `E_(q_rho)(c_(p,rho,x))` has exactly this coefficient and no other divisor
coordinate.  Therefore `U_(q_rho)(c_(p,rho,x),0)` is definitionally the Route-R fixed same-fibre
physical lift.  On the period-one retained class its coefficient is the actual nonzero leading Xi
jet.  This closes the amplitude issue left by the reflected-Gaussian global vector: the canonical
completed basis has unit norm, so no Gaussian/jet radial renormalization is used.

For any real Route-R shear coefficient `K`, define the completed resolved coefficient pair

```text
G_(q,K)(c) = (c,-K w_q c).
```

Then

```text
U_q(G_(q,K)(c)) = (R(c),-K R(c)),
```

which is exactly the harmonic corona graph for coupling `K id` and hidden metric `id`.  This formula
holds both on and off the critical line.  It identifies the resolved shear as the coefficient of
the unique completed-Xi Hodge-mate direction; it does not erase that coefficient.

### Dependency-closed proof

All identities reduce to four existing unconditional inputs: the orthonormal `lp.single` basis of
`XiDivisorL2`, the coefficient law for `lp.single`, `deningerFreqSign_sq`, and `Complex.I_sq`.
Indeed `w_q^2=-1`; hence `(-w_q)(w_q c)=c`.  Expanding real and imaginary parts proves both the
realification dot-product law and invariance under multiplication by `-w_q`.  The zero-hidden,
odd-Hodge, and graph identities then follow by substitution.  Finally, substituting `z=w_q c` in
the defining property of any competing hidden trivialization proves uniqueness.

### Hostile audit and exact surviving frontier

`[FALSIFIED AS AN RH PRODUCER]` Fixed-polarization identification alone forces `K=0`.  The displayed
normal form exists for every real `K`; off-line shear is carried to the explicit Hodge-mate
coefficient `-K`, while both fixed polarizations remain unchanged.

`[POSITIVE SURVIVOR]` Completed-Xi and Route-R fixed same-fibre polarizations now have a canonical,
coefficient-faithful common normal form, and the actual physical leading-jet lift is provably the
zero-hidden section.  Remaining RH-strength statement is no longer a metric, coefficient, or gauge
comparison: derive from source structure that the Hodge-mate coefficient in the actual resolved
atom is zero, equivalently that the zero-hidden physical atom itself belongs to the harmonic graph.
No such annihilation, and therefore no RH proof, is claimed here.

Formal status: `[FORMALISED IN LEAN]` in
`GaloisForLFunctions/RHTower/CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean`.
The module proves the fixed-polarization isometry, comparison injectivity, actual completed Hodge
action on the coordinate line, unique hidden untwisting, zero-hidden physical landing, exact
resolved-graph landing, retained leading-jet nonerasure, and the rational-adelic atom
specializations.  Direct Lean check and targeted module build pass.  The axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.

## 2026-08-04 selector-shape no-gos: invariant lines and comparison gauge

### Killed selector shapes `[FORMALIZED NO-GO]`

The demanded producer — a source-defined fixed positive same-fibre dagger/Cartier line,
constructed before inspecting `rho`, preserved by actual Route-R transport,
coefficient-faithful on the leading Xi jet, and identifying resolved with zero-hidden
lifts — is over-determined, and each admissible weakening of its clauses is now classified
unconditionally in Lean, with no RH-flavoured premise anywhere.

1. **Invariant-line rigidity.** The resolved shear `S_K` is unipotent.  A vector `v` with
   `v_0 != 0` spans an `S_K`-invariant line exactly when `K = 0`
   (`completedXiSameFiberResolvedShear_eigenvector_iff`): from `S_K v = lam v`,
   faithfulness forces `lam = 1`, and unipotence then forces `K w_q v_0 = 0` with
   `|w_q| = 1`.  Hence transport preservation plus coefficient-faithfulness — clauses
   (1)+(2) alone, with no positivity, dagger, metric, or lift-identification clause — are
   already equivalent to the missing annihilation:

   ```text
   CCMRationalAdelicPrimeXiInvariantFaithfulLine p rho
     <-> K_(p,rho) = 0  <->  Re(rho) = 1/2
   ```

   (`ccmRationalAdelicPrimeXiInvariantFaithfulLine_iff_hodgeMateCoefficient_eq_zero`,
   `..._iff_re_eq_half`).  Clause 5 of `SOURCE_DAGGER_FIXED_POLARIZATION_CARTIER_DESCENT`
   therefore cannot be weakened to any line-invariance statement: a valid producer must
   construct the fixed polarization law itself, not a preserved line, eigen-direction, or
   dagger axis.

2. **Comparison-gauge ceiling.** For every function `Phi` from the coefficient plane to the
   corona plane preserving the two fixed polarizations — no linearity, continuity, or
   naturality assumed — the resolved-over-physical energy excess transports unchanged:

   ```text
   g_cor(Phi(G_K c), Phi(G_K c)) - g_cor(Phi(c,0), Phi(c,0)) = K^2 |c|^2
   ```

   (`completedXiFixedCorona_comparison_energyGap`), so at nonzero shear and nonzero
   coefficient the two landings stay separated under every such comparison
   (`completedXiFixedCorona_comparison_separates`,
   `ccmRationalAdelicPrimeXi_offLine_no_comparison_identifies`).  Re-choosing the
   comparison map is not a possible discharge mechanism; the earlier transported-metric
   kill is the linear special case of this ceiling.

### Route-test verdict for the fixed-corona layer

The layer consumes exactly two divisor-sensitive inputs: nonvanishing of the
multiplicity-leading Xi jet and strict positivity of the prime/depth clocks and adjacent
connection.  Both hold verbatim for any entire order-one function with functional-equation
divisor symmetry and a hypothetical off-line zero, and every layer statement is natural in
the centered rate `t = 2 Re(rho) - 1`, holding for all real `K`.  No argument factoring
through this interface can prove `K_(p,rho) = 0`; a proof must consume input that breaks
rate-naturality (global positivity of Weil type on the full test algebra, bilinear
short-interval control, or an independent singular all-prime boundary law).  The open core
`FIXED_POLARIZATION_PRODUCTION` is unchanged and is the entire remaining content of this
layer; it is now exactly isolated, with line-invariance and comparison-gauge weakenings
both closed.

Formal status: appended to
`GaloisForLFunctions/RHTower/CCMRationalAdelicCompletedXiFixedCoronaPolarization.lean`.
Direct check, targeted build, and axiom audit (only `propext`, `Classical.choice`,
`Quot.sound`) pass.

## 2026-08-05 cross-corpus transfer: twisted-cyclic modular-dimension transmutation

### Internal analogue audit

The closest positive model is not a Hilbert-space or determinant construction.  The
HT source-face corpus treats a retained Bockstein as the connecting image of a primitive
lost under strict completion, and the irrational-triptic source-effectivity theorem shows
what a successful producer must add: one pointed source cochain must construct the analytic,
Hermitian, integral, and spectral realizations together, followed by a genuinely conservative
comparison.  Applied to Route R, this changes the requested theorem from an unspecified
``boundary killing beta`` to preservation of one pre-existing source modular class under a
strict connecting comparison.

The relevant scalar laws already exist on the two sides.  On a prime Wold ray the source
first-trace/twisted-cyclic law has ratio

```text
source modular ratio = p^(-1).
```

The gauge-averaged positive marginal of the centered Xi character has ratio

```text
Xi conormal ratio = p^(-2 Re(rho)).
```

Consequently a nonzero specialization of the *same* twisted-cyclic class gives

```text
p^(-1) = p^(-2 Re(rho))
  -> Re(rho) = 1/2
  -> ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0.
```

The last implication is already formalized by the Route-R adjacent-depth classifier.  The
existing Bockstein-to-corona comparison then identifies this modular mismatch with the unique
positive Hodge-mate/corona port.  Thus modular-dimension preservation would annihilate the
named central Bockstein on the retained atom without postulating `beta = 0`, a fixed-ideal
normalizer, or critical-line placement.

### Killed transfers

1. A `C*`/GNS completion alone is blind: the cofinal Gamma diagonal is compact throughout the
   strip, while its trace-class wall occurs only at neutral grade.
2. The unitization unit or an augmented-simplex extra degeneracy supplies an algebraic primitive,
   but it forgets the full Euler cube and only proves that the class is a boundary in an enlarged
   absolute complex.  It does not make the fixed physical coefficient zero.
3. A free oriented interval/Koszul carrier makes an endpoint difference a formal boundary, but
   without a conservative reporter it merely relocates the nonzero class.  The modular action
   on every interval layer is load-bearing.
4. The existing CCM Real structure fixes the unit and is cyclically natural, but Real invariance
   of the resolved graph holds for arbitrary Hodge-mate coefficient.  It does not imply the fixed
   odd-Hodge commutation needed for `K = 0`.
5. A bare Calderon resolvent has zero duality--adjunction seam but is rational and divisor-blind.
   The primitive must be Euler-decorated and must retain the all-prime cube, Gamma/Poisson face,
   and multiplicity data before completion.

### Surviving producer

`[CONJECTURE — ROUTE_R_TWISTED_CYCLIC_CONNECTING_CONSERVATIVITY]`

Construct, before divisor specialization, one strict dagger-stable source/ambient/corona exact
sequence from the literal rational-adelic prime-isotropy complex and the Euler-decorated
Calderon/Wold--Toeplitz primitive, together with a morphism to the completed-Xi fixed-corona
comparison, such that:

1. the retained ordinary-prime class is the connecting image of the Euler-decorated primitive,
   with prime, inverse-prime, depth, and full Euler-cube provenance;
2. the source twisted-cyclic ratio is the literal `p^(-1)` first-trace/BV ratio and is preserved
   by dagger and by the connecting morphism;
3. reduced Xi specialization is strict and nonzero on every retained principal-conormal line;
4. its positive gauge-averaged restriction is the centered-character marginal with ratio
   `p^(-2 Re(rho))`;
5. ramified multiplicity jets descend through a separate compatible channel, so conservativity
   on the reduced line does not incorrectly force simplicity; and
6. the fixed completed-Xi/corona comparison carries the resulting modular defect to the explicit
   Hodge-mate coefficient `K`, not merely to a zero-equivalent scalar reporter.

Clauses 1--2 make the source value independent of `rho`; Clauses 3--4 prevent zero-fibre fitting
or erasure; Clause 5 avoids the known Jordan obstruction; Clause 6 connects the source theorem
to the exact Route-R endpoint.  Their conjunction gives the unconditional source-dagger/norm
identity and hence `K = 0`.

This is not yet a proof.  The corpus closes the abstract connecting-map naturality, local
Calderon dagger equality, source modular-ratio calculation, positive marginal calculation,
algebraic Xi principal-parts carrier, Route-R coefficient/energy comparison, and final rigidity
consumer.  Missing scientific content is the zeta-specific strict all-prime comparison in
Clauses 1--4.  Any construction that starts after Xi fibre decomposition, transports a fitted
metric, or merely declares the physical class null-homologous fails the anti-theatre gate.

## 2026-08-05 cross-corpus audit: singular completion migration, not missing finite homology

### Conjecture loop and collisions

The proposed finite extension of the BV relation to a Hochschild/Tate chain map is not the live
frontier. `LowDegreeHochschildFaceFlatness.lean` already supplies the one- and two-face
Hochschild primitives, while `TateKummerWoldGammaIntervalCharacter.lean` supplies the oriented
interval/Koszul carrier, prime-square boundary, and Wold character. The ordinary-integer source
also already has the exact Toeplitz primitive

```text
B_n = [S_n^*, Q S_n] = b(S_n^* tensor Q S_n).
```

Three attempted cofinal extensions fail for exact reasons.

1. The Wold thermofield standard-form vector is strict under prime enlargement, but for the
   diagonal multiplication algebra it is central and the algebra is commutative. Therefore
   `HH_0(A,M)=M/[A,M]=M`; the retained central vector is not made null-homologous. Passing to the
   noncommutative Toeplitz algebra recovers the genuine modular twist and the displayed primitive,
   but that primitive is already corpus-known.
2. Bilateralization makes the shift unitary and removes the ambient Toeplitz index only by
   enlarging the carrier. The corpus's exact bilateral Mellin formula still contains `XiC`, and
   the Wold decomposition stores the nonrecurrent compressed state in the complementary channel.
   Thus unitary dilation is conservative, not selective.
3. The source-pure selector and the Calderon--Witt Green retractions split resolved or incidence
   spaces. They do not split the fixed physical quotient `S/I`, `I=ell1(P)`. Off neutral grade
   one of `F_t,F_(-t)` is literally in `I`, so no retraction defined after this quotient can retain
   both orientations without already implying the conclusion.

### Closest successful corpus mechanism

The closest positive analogue is the Shilov boundary-migration/Roos exact sequence. There a class
born only after cofinal completion is represented as degree-one migration cohomology; an explicit
coherent lifting theorem, not finite-stage exactness, proves derived acyclicity. The
Gamma-head/Hardy-tail moving-horizon complex supplies the complementary local model:

```text
d(head, tail)/dL = (endpoint, -endpoint),
sumTrace(endpoint, -endpoint) = 0,
Green(endpoint, -endpoint) = endpoint.
```

Route R has precisely the same local boundary, but its two physical legs are evaluated by
different modular functionals. Their mismatch is the explicit cofinal class `beta_t`, hence the
Hodge-mate coefficient `K`. The ordinary `C*` Shilov theorem cannot be imported: the relevant
Gamma diagonal is compact throughout the strip and the distinction occurs only at the fixed
Schatten-one/`ell1` wall.

This identifies the correct new object as a **singular trace-ideal boundary-migration complex**,
not another finite Hochschild complex and not an ordinary inverse limit. The qualification is
essential: finite-coordinate trace ideals inverse-limit to the whole product, whereas `ell1`
means uniform boundedness of partial absolute sums. The source topology must therefore retain
bounded sections, not merely compatible sections.

`[CONJECTURE — ROUTE_R_SINGULAR_TRACE_IDEAL_MIGRATION_ACYCLICITY]`

Construct from the pre-divisor Euler--Gamma--rational-adelic source a bounded-section coefficient
system over the ordinary-prime exhaustion with:

1. bounded global ideal exactly the fixed physical first-trace ideal `I=ell1(P)`;
2. local degree-one primitive the literal `S_p^* tensor Q S_p`, coupled to the full
   interval/Koszul and Boolean/Tate faces without scalar diagonal renormalization;
3. two Gamma orientation restrictions equal to the already-constructed classes
   `[F_(-t)]` and `[F_t]` in `S/I`;
4. Gamma-head/Hardy-tail moving-horizon differential supplying one source-defined contracting
   cochain on the bounded-section migration complex;
5. a nondivisive polarized Cartier identity, before selecting a zero,

   ```text
   beta(z,w) = d H(z,w) + XiC(z) R(z,w) + XiC(w) S(z,w),
   ```

   with `H,R,S` bounded in the source-selected singular bornology and retaining every prime,
   depth, divisor-multiplicity, and both-Gamma-orientation label; and
6. coefficient-faithful comparison of the specialized migration class with the fixed same-fibre
   corona Hodge-mate coefficient `K`.

At an actual divisor point put `(z,w)=(rho,conj rho)`. Both Xi terms vanish by the real entire
structure, so `beta_(t_rho)` is a literal source boundary. Clause 6 then gives `K=0`, and the
existing Lean endpoint gives `Re rho=1/2`.

### Anti-theatre falsifiers

1. `H` is defined by dividing `beta` by `XiC`, by a leading jet, or by `2 Re(rho)-1`.
2. Boundedness is checked only at each finite prime cutoff; the required assertion is one uniform
   bounded-section estimate in the fixed trace-ideal bornology.
3. The coefficient system is a transported weighted `ell1_t` ideal rather than fixed `ell1`.
4. The construction is an ordinary `C*` completion, a virtual diagonal, a bilateral unitary
   dilation, or a diagonal thermofield state; all four erase the load-bearing trace wall.
5. The Cartier identity holds only after substituting a divisor point or only in scalar residue.
6. Prime/depth coefficients or the multiplicity-leading conormal are fused before the migration
   class is compared to the physical corona port.

This is a genuine reinterpretation of the open theorem. It does not prove the conjecture. It
removes four already-solved or impossible subproblems and specifies the missing producer as a
uniform singular-completion homotopy with an explicit nondivisive Xi remainder.

## 2026-08-05 — Exact tail–Roos model of the fixed first-trace corona

### Setup

Fix the increasing enumeration of ordinary primes
\(p_0,p_1,\ldots\). For \(n\ge 0\), put
\[
  A_n:=\mathbb C^{\{k:k\ge n\}},
  \qquad
  J_n:=\ell^1(\{k:k\ge n\}).
\]
Let \(\iota_n:A_{n+1}\to A_n\) insert a zero in coordinate \(n\).
It restricts to \(J_{n+1}\to J_n\). Write \(e_n\in J_n\) for the
head-coordinate atom.

### [PAPER-PROVED] `ROUTE_R_FIXED_TRACE_TAIL_ROOS_DIAGONAL_CLASSIFICATION`

For every sequence \(a=(a_k)_{k\ge0}\in\mathbb C^{\mathbb N}\):

1. The induced map
   \[
      A_{n+1}/J_{n+1}\longrightarrow A_n/J_n
   \]
   is an isomorphism. Surjectivity holds because any \(x\in A_n\) differs
   from \(\iota_n(x|_{k\ge n+1})\) by the one-coordinate vector
   \(x_ne_n\in J_n\); injectivity follows because deletion of the head
   coordinate sends an \(\ell^1\) sequence to an \(\ell^1\) sequence.

2. The tail representatives \(a^{(n)}=(a_k)_{k\ge n}\) define a compatible
   family in the quotient tower. Their representative mismatch is the
   diagonal Roos cochain
   \[
      c_n:=\iota_na^{(n+1)}-a^{(n)}=-a_ne_n\in J_n.
   \]

3. If a family \(h_n\in J_n\) trivializes this mismatch,
   \[
      h_n-\iota_nh_{n+1}=c_n=-a_ne_n
      \qquad(n\ge0),                                      \tag{TR}
   \]
   then it is forced coordinate by coordinate that
   \[
      h_n=-a^{(n)}.
   \]
   Indeed, the head coordinate of `(TR)` is \((h_n)_n=-a_n\), while every
   coordinate \(k>n\) gives \((h_n)_k=(h_{n+1})_k\). Iteration fixes all
   coordinates of every \(h_n\). Conversely these forced tails satisfy
   `(TR)` whenever \(a\in\ell^1\).

4. Consequently the diagonal physical Roos class is null-homologous exactly
   when
   \[
      a\in\ell^1(\mathbb N).
   \]
   This is the fixed-ideal criterion, not merely a sufficient condition.

Applying the classification to the Route-R Fisher defect
\[
  a=\beta_t,
  \qquad
  \beta_t(p)=F_{-t}(p)-F_t(p),
\]
and using the already formalized first-trace estimate gives, for \(|t|<1\),
\[
  [c(\beta_t)]=0
  \iff \beta_t\in\ell^1
  \iff t=0.
\]
At \(t=2\Re\rho-1\), this is exactly the critical-line condition. The
formalized summable-difference theorems
`xi_actualEdge_forward_sub_activationFisher_summable` and
`xi_actualEdge_reflected_sub_activationFisher_summable` transport the same
classification to the actual essential edge in both Gamma orientations.

### Scope and hostile audit

This theorem classifies the diagonal class supplied by a global coefficient
sequence. It does **not** identify the entire derived limit
\(\varprojlim^1J_n\) with \(\mathbb C^{\mathbb N}/\ell^1\): arbitrary
families in \(\prod_nJ_n\) need not be diagonalizable by a global sequence.
No such stronger assertion is used.

The classification rules out three false closures:

- finite-stage exactness cannot kill the compatible diagonal class;
- a reflection coequalizer can call \(\beta_t\) a boundary while failing to
  supply the forced \(\ell^1\) primitive;
- a global Real/quaternionic involution pairs distinct divisor fibres, whereas
  `(TR)` is a fixed same-fibre equation. Identifying those fibres is already
  the critical-line condition.

Thus there is no freedom to choose a more convenient physical homotopy. Any
coefficient-faithful source proof must construct the literal tail primitive
\(-\beta_t^{(n)}\) inside \(J_n\).

### [CONJECTURE — `ROUTE_R_SOURCE_TAIL_ROOS_PRIMITIVE`]

There is a pre-divisor Euler–Gamma–rational-adelic source family \(H_n(z,w)\),
with values in the fixed tail trace ideals \(J_n\), and source-exact/Xi-remainder
terms whose specialization at \((z,w)=(\rho,\bar\rho)\) gives
\[
  H_n(\rho,\bar\rho)-\iota_nH_{n+1}(\rho,\bar\rho)
  =-\beta_{2\Re\rho-1}(p_n)e_n.                         \tag{SR}
\]
The construction must be coefficient-faithful, preserve the fixed physical
polarization, work in both Gamma orientations, and use no division by Xi,
critical-line placement, fixed-ideal preservation assumption, or prior
vanishing of \(\beta\).

By the classification, `(SR)` immediately forces
\(\beta_{2\Re\rho-1}\in\ell^1\), hence \(2\Re\rho-1=0\). Conversely, any
claimed source Stokes/Cartier annihilator which does not produce `(SR)` in the
fixed ideals has changed the problem rather than solved it. This is the
smallest exact source theorem still missing from Route R.

## 2026-08-05 — Cross-corpus synthesis: safe-cone primitive and trace-wall removability

The closest existing organs are not another divisor detector. They are:

1. `TateClockUnilateralShiftDefect.lean`, which gives the exact
   boundary-plus-zero-prepended-tail recursion;
2. `EulerPrimitiveCommonTestLabeledOccupationSource.lean`, which constructs
   genuine pre-divisor, prime-power-labelled \(\ell^1\) head/tail packets in
   the Euler convergence chamber;
3. the Gamma--Meixner convolution-root scale, which supplies canonical
   positive damping \(p^{-\varepsilon}\) down to arbitrarily small positive
   aperture;
4. `PrimeDepthBVWoldBarrelledSourceSelector.lean`, which turns pointwise
   boundedness on an independently completed barrelled source into the
   depth-uniform estimate that kills the centered rate.

These four organs combine into an exact normal form for the desired producer.

### [PAPER-PROVED] `ROUTE_R_EULER_SAFE_CONE_TAIL_PRIMITIVE`

For \(|t|<1\) and \(\varepsilon\ge0\), define
\[
 \beta_{t,\varepsilon}(p)
 :=p^{-\varepsilon}\bigl(F_{-t}(p)-F_t(p)\bigr)
 =F_{-t-\varepsilon}(p)-F_{t-\varepsilon}(p).
\]
Then
\[
 \beta_{t,\varepsilon}\in\ell^1
 \quad\Longleftrightarrow\quad
 t=0\ \text{ or }\ \varepsilon>|t|.                    \tag{SC1}
\]

Proof. If \(t=0\), the sequence is zero. If \(t>0\), then
\(F_{t-\varepsilon}\ge F_{-t-\varepsilon}\) pointwise and
\[
 F_{t-\varepsilon}-F_{-t-\varepsilon}
 =F_{t-\varepsilon}(1-p^{-2t})
 \ge (1-2^{-2t})F_{t-\varepsilon}.
\]
The already-proved Fisher threshold
\(F_u\in\ell^1\Longleftrightarrow u<0\) therefore gives summability exactly
when \(t-\varepsilon<0\). The case \(t<0\) follows by reflection. This proves
`(SC1)`, including the harmonic boundary \(\varepsilon=|t|\).

For every point of the safe cone \(\varepsilon>|t|\), put
\[
 H_{n,t,\varepsilon}:=-\bigl(\beta_{t,\varepsilon}(p_k)\bigr)_{k\ge n}
 \in J_n.
\]
Then
\[
 H_{n,t,\varepsilon}-\iota_nH_{n+1,t,\varepsilon}
 =-\beta_{t,\varepsilon}(p_n)e_n.                       \tag{SC2}
\]
The tail--Roos classification proves that `(SC2)` has no other
\(J_n\)-valued solution. Hence the pre-divisor Euler object already supplies
the required primitive throughout its honest convergence chamber. The hard
operation is continuation of this exact, uniquely forced primitive through
the trace wall to \(\varepsilon=0\).

### Same wall in the Gamma--Meixner corpus

The Gamma--Meixner root weight satisfies
\[
 w_\varepsilon(p)asymp p^{-\varepsilon},
\]
and the proved prime-seam aperture law has the identical threshold
\[
 E_\varepsilon(\rho)<\infty
 \quad\Longleftrightarrow\quad
 2\Re\rho-1=0\ \text{ or }\ \varepsilon>|2\Re\rho-1|.
\]
This is not a numerical coincidence. The Route-R base coefficient is exactly
the square of the Möbius--Gamma damping, while the Meixner family is the
canonical convolution-root scale of the same archimedean cyclic measure.
Thus Route R fixed-\(\ell^1\) annihilation and all-root Gamma deconvolution are
two ideal grades of one trace-wall continuation problem.

### What the existing regulator does and does not control

The period-one rational-adelic Stokes regulator is a separate local-prime
linear functional. It proves that the retained class is not an ordinary
relative boundary. It does not bound
\(\sum_p|\beta_{t,\varepsilon}(p)|\), so it cannot justify passage through
the trace wall. Likewise, the completed divisor Hilbert Green primitive is
an \(\ell^2\) primitive after divisor completion; it does not supply the
fixed prime-indexed \(\ell^1\) tails forced by `(SC2)`.

### [CONJECTURE — `ROUTE_R_SOURCE_TRACE_WALL_REMOVABILITY`]

Construct, before divisor selection, an independently topologized
Euler--Gamma--rational-adelic barrelled source \(E_{\rm src}\) with:

1. a coefficient-faithful map from its safe-cone Euler packets to the exact
   tails \(H_{n,t,\varepsilon}\);
2. continuous Gamma-root deconvolution readouts whose pointwise orbits are
   bounded on every element of \(E_{\rm src}\);
3. an off-diagonal Cartier identity, with nondivisive Xi remainder, which at
   a Xi divisor identifies the zero-aperture specialization with the same
   fixed-tail Roos equation `(SR)` in both Gamma orientations.

Barrelled Banach--Steinhaus then converts clause 2 into a uniform
deconvolution estimate. Clauses 1 and 3 identify its limit with the unique
tail primitive. Therefore \(\beta_{2\Re\rho-1}\in\ell^1\), the Hodge-mate
coefficient \(K\) vanishes, and the existing Lean endpoint proves RH.

This formulation removes two false freedoms: the primitive cannot be chosen
after continuation, and the completion cannot be defined as “vectors with
bounded deconvolution orbit.” The only new scientific content required is
source-derived pointwise boundedness plus the coefficient-faithful
zero-aperture Cartier landing.

## 2026-08-05 cross-corpus comparison: one central class, not two gaps

The closest independently developed object is the trace-one ordinary-prime
class in `MobiusThetaPhysicalParacyclicSourceNullHomology`. Its cofinal Tate
relative coordinate is

\[
  (p^{t}-1)\,\XiC^{(r)}(w_\rho),
  \qquad t=2\Re\rho-1,
\]

whereas the fixed-trace class uses

\[
  \beta_t(p)=F_{-t}(p)-F_t(p),
  \qquad F_t(p)=p^t\frac{p}{(p+1)^2}.
\]

These are not merely equivalent zero tests. Direct factorization gives the
pre-divisor, same-prime, nondivisive identity

\[
 \boxed{
  \beta_t(p)=
  -\frac{p}{(p+1)^2}(1+p^{-t})(p^t-1).
 }
 \tag{CB1}
\]

The transfer factor is strictly negative and never zero. Thus the singular
all-prime Gamma Bockstein and the rational-adelic paracyclic central
Bockstein are two coefficient models of one class. This is formalized in
`RHTower/RouteRFixedTraceTailRoos.lean` by:

- `routeRPrimeGammaBockstein_eq_centralGainDefect`;
- `routeRPrimeGammaCentralTransferFactor_ne_zero`;
- `deningerHalfDensityMateGain_prime_eq_rpow`;
- `routeRPrimeGammaBockstein_eq_deningerCentralDefect`;
- `routeRPrimeGammaXiDiagonalTailRoosClass_eq_zero_iff_sourceNullHomologous`.

The same module now also formalizes the sharp damped trace wall

\[
 \sum_p p^{-\varepsilon}|\beta_t(p)|<\infty
 \quad\Longleftrightarrow\quad
 t=0\ \text{or}\ |t|<\varepsilon,
 \tag{CB2}
\]

and constructs the literal fixed-ideal tail primitive throughout the safe
cone, with its exact Roos boundary.

### Conjecture loop audit

1. **Ordinary Connes `bB+Bb` contraction — failed.** The source degree-one
   product trace does not annihilate ordinary degree-two Hochschild
   boundaries; this failure is already proved in
   `MobiusThetaPhysicalParacyclicSourceNullHomology`. Hence the Cartan identity
   alone cannot kill the retained trace-one atom.
2. **Finite Arakelov product formula — exact but insufficient.**
   `DeningerRealKummerArakelovBoundary` makes finite prime data exact only
   after adjoining the negative logarithmic archimedean coordinate. Extending
   this boundary to `(CB1)` requires exactly the missing zero-aperture
   all-prime trace; off centre that trace crosses the divergence wall `(CB2)`.
3. **Reflected source entropy positivity — failed.** The corpus quantity is
   identically `1 - 2 re(s)`, a signed log-character, not a nonnegative
   relative entropy. Reflection oddness therefore supplies no positivity
   contradiction.
4. **Real/quaternionic corona — two-fibre only.** Its antiunitary structure
   exchanges reflected divisor fibres. It does not furnish the fixed
   same-fibre isometry required to annihilate `K`; imposing that identification
   is precisely the missing selection law.

Consequently `(CB1)` removes the possibility that tail--Roos annihilation and
paracyclic source-null-homology are independent obligations. A successful
producer must extend one and the same central class through the all-prime
trace wall while preserving the period-one prime detector. The remaining
source theorem is now a singular Arakelov/Cartier extension theorem, not a new
boundary, carrier, or comparison theorem.

## Discriminator upgraded to a theorem (2026-08-05)

The "first hostile discriminator" above is now an unconditional Lean theorem, not a judgement call.

`[CORPUS]` `GaloisForLFunctions.RHTower.phaseDefect_eq_iff_exists_character` — for phases normalised
at the unit, two local phases have the same coboundary defect exactly when they differ by a group
character. The reciprocity layer is precisely the phase layer modulo characters.

`[CORPUS]` `GaloisForLFunctions.RHTower.no_phaseDefect_criterion_detects_criticalLine_adelicScaling`
— on the actual scaling group `CCMRationalAdelicScaling`, no predicate on coboundary-defect data is
equivalent to `Re rho = 1/2`. The source-inverse endpoint residue is the character
`q |-> (1/2 - Re rho) * log |q|` and `adelicXiSourceInverseCharacter_eq_one_iff` identifies its
triviality with the critical line.

Consequence for this card: `alpha_rho * beta_rho = 1` is defect-level data
(`adelicXiSourceInverse_mul_adelicXiAnalyticAdjoint`), so the `[FALSIFIED]` verdict on
reciprocity-only proposals is now forced rather than observed. Any admissible
`POLARIZED_ADELIC_STOKES` comparison must be shown to transport the *phase*, i.e. to separate the
two endpoint residues before their product is taken; a construction whose only invariant is the
Stokes boundary defect cannot land the critical line, whatever its degree.

Card: `docs/drafts/pipeline/3-formalized/adelic-phase-defect-character-blindness-law.md`.

## 2026-08-06 — `SingularStokesFlat` producer audit after prime-log transport

The formal endpoint is now exact.  For every Xi support point `rho`, the
prime-log transported cap port is

\[
 P_p(\rho)
 =a_\rho(1-p^{-1})(2-p^{-1})c_\rho,
 \qquad
 a_\rho=2\operatorname{Re}\rho-1,
 \qquad c_\rho\ne0,
\]

and hence \(P_p(\rho)\to2a_\rho c_\rho\).  Therefore

\[
 \operatorname{SingularStokesFlat}(\rho)
 \Longleftrightarrow a_\rho=0.
 \tag{SSF}
\]

This is formalized in
`RHTower/RouteRPrimeLogEssentialCapSingularStokesLaw.lean`, including the
global equivalence of `(SSF)` with RH.  The following source-first producers
were hostile-tested against the literal pre-divisor objects.

1. **Reflected entropy positivity — falsified.**  The corpus quantity called
   `riemannReflectedSourceEntropy` is exactly \(1-2\operatorname{Re}s\).  It
   is an oriented log-ratio, is reflection-odd, and is negative on the
   right-half divisor.  It is not a nonnegative relative entropy.
2. **Rational Cartier orbit rigidity — consumer only.**  The canonical
   pre-divisor rational potential is constant and has source gain \(1\).
   Its defect from physical gain \(p^{a_\rho}\) is exactly the central
   Bockstein coordinate.  Identifying those gains is the already-formalized
   rational Cartier landing, equivalent to `(SSF)`.
3. **Weak-\(L^1\)/singular-trace commutator — domain failure.**  The exact
   damped wall is
   \[
     \sum_p p^{-\varepsilon}|\beta_t(p)|<\infty
     \Longleftrightarrow t=0\ \text{or}\ |t|<\varepsilon.
   \]
   At zero aperture, membership in the required trace domain already forces
   \(t=0\).  A bounded-commutator or Dixmier-trace presentation would assume
   the conclusion through ideal membership.
4. **Cyclic dagger plus Gamma reversal — falsified by the retained atom.**
   Genuine cyclic reversal sends the corrected multiplier class to a
   distinct class and flips its nonzero Kummer period.  This sign cancels the
   Gamma-reflection sign, so dagger-transported naturality holds for every
   horizontal grade and annihilates nothing.
5. **All-prime Kakutani/GNS sector rigidity — missing bounded intertwiner.**
   Source and physical valuation sectors are mutually singular off neutral
   grade, but the infinite-rank comparison currently transports only
   multiplication, trace, derivation, and the nonzero prime atoms.  It does
   not intertwine the product valuation representations.  The canonical
   source Hilbert marking is Fisher-damped, while exact recovery of the
   undamped Gamma valuation frame grows at least as \(\sqrt p\) and is
   formally unbounded.
6. **Fixed Hilbert Stokes reporter — exact but unavailable.**  If the
   transported prime-log derivation were self-adjoint on one fixed positive
   target, its normalized distinct-prime eigenvectors would be orthonormal.
   Any one bounded Stokes reporter would then have coefficients tending to
   zero by Bessel, and the exact port limit would prove `(SSF)`.  Existing
   source topologies do not give this reporter: the algebraic LF topology
   allows arbitrary coefficient families, trace-norm continuity allows
   bounded constant coefficients, and the completed-Xi Hilbert comparison
   forgets the prime-log eigenspaces.  Bounded reporter assembly is another
   form of zero-aperture trace-wall removability, not a consequence of
   primewise continuity.

### Exact open source equation

No independent obstruction remains between the paracyclic and fixed-trace
models: `(CB1)` identifies them coefficientwise.  The only unresolved
source step is to construct, before divisor selection and in both fixed
Gamma orientations, a source-derived family in the literal fixed tail
ideals satisfying

\[
 H_n(\rho)-\iota_nH_{n+1}(\rho)
 =-\beta_{2\operatorname{Re}\rho-1}(p_n)e_n.
 \tag{SSR}
\]

The tail--Roos classification makes `(SSR)` equivalent to
\(\beta_{2\operatorname{Re}\rho-1}\in\ell^1\), hence to `(SSF)`.  Safe-cone
families exist uniquely for every damping
\(\varepsilon>|2\operatorname{Re}\rho-1|\); missing scientific content is
their coefficient-faithful continuation to \(\varepsilon=0\).  Current
pre-divisor source structure supplies neither pointwise-bounded Gamma-root
deconvolution nor a fixed-ideal zero-aperture landing.  Consequently no
unconditional Lean proof of `SingularStokesFlat` can be added without first
proving this analytic extension theorem.

## 2026-08-06 — First-wall oriented harmonic quantization

`[LEAN-PROVED]` Forbidden continuation interval is no longer minimal producer
burden. Put

\[
 W_t(p)=p^{-|t|}\beta_t(p),\qquad h(p)=p^{-1}.
\]

New module
`RHTower/RouteRCriticalWallOrientedHarmonicQuantization.lean` proves

\[
 [W_t]=
 \begin{cases}
   +[h],&t<0,\\
   0,&t=0,\\
   -[h],&t>0,
 \end{cases}
 \qquad [h]\ne0
 \tag{QW}
\]

inside actual fixed summable tail--Roos corona. Proof is coefficient-faithful
and pre-divisor: occupancy Fisher differs from `1/p` by an `ell^1` sequence,
while remaining critical-wall correction has order `p^(-1-2|t|)` and is
summable for every `t != 0`.

### Mathematical delta

Every off-centre aperture no longer presents a separate continuation problem.
At its first trace wall, complete continuum collapses to one universal nonzero
prime-harmonic rank port with orientation sign. Route R therefore does not
need source continuation from `epsilon>|t|` through entire forbidden interval
to `epsilon=0`. A strictly smaller producer suffices:

`[OPEN CORE — ROUTE_R_FIRST_WALL_SOURCE_RESIDUE_VANISHING]` Prove from
pre-divisor fixed-source-orientation Stokes/Cartier law that Xi-specialized
critical-wall tail class has zero harmonic residue.

By `(QW)`, zero residue forces oriented rank to be zero, hence `t=0`. Existing
fixed-tail/Xi comparison then annihilates Hodge-mate coefficient and closes RH
endpoint. Remaining unproved content is this source-derived residue law, not
an `ell^1` deconvolution across a positive-width aperture region.

## 2026-08-06 — Cofinal restarted-sieve realization of harmonic residue

`[LEAN-PROVED] [BRIDGE] [NOVELTY UNVERIFIED]` The phrase “harmonic residue”
now has an explicit, source-native meaning. For any prime enumeration `e`,
restart the Euler sieve after prefix `N` and put

\[
 D_{N,n}=\prod_{k<n}\left(1-\frac1{e(N+k)}\right),\qquad
 S_N(a)=\sum_{n\ge0}D_{N,n}a(e(N+n)).
\]

New module
`RHTower/RouteRCofinalSieveHarmonicResidue.lean` proves:

1. restarted loss weights `D_{N,n}/e(N+n)` are positive and sum to one;
2. `S_N(b) -> 0` for every summable prime field `b`;
3. if `a(p)=c/p+b(p)` with `b in ell^1`, then `S_N(a) -> c`, and `c` is
   unique;
4. for actual first-wall Gamma field `W_t`, the limits are `-1` for `t>0`,
   `0` for `t=0`, and `+1` for `t<0`, for every enumeration.

The first two conjectures were falsified before formalization: an unshifted
sieve reporter has nonzero `ell^1` bias, and global-tail normalization hides
the source law behind division by vanishing density. Literal tail restart
removes both defects.

### Frontier reduction

`[OPEN CORE — ROUTE_R_COFINAL_SIEVE_STOKES_ZERO_LIMIT]` Derive, from the
pre-divisor fixed-source-orientation Stokes/Cartier producer, the concrete law

\[
 S_N(W_{t_\rho})\longrightarrow0
\]

for every Xi support point `rho`. Formal theorem
`routeRPrimeGammaXiCriticalWallReporter_zeroLimit_iff_re_eq_half` proves this
zero limit is equivalent to `Re rho = 1/2`, but does not assume or assert the
limit. Thus quotient ambiguity is gone: remaining RH-bearing content is one
explicit cofinal source limit, not an undefined residue, tail-Roos equality,
or continuation through a forbidden aperture interval.

## 2026-08-06 — Sub-quantum gap replaces exact annihilation

`[LEAN-PROVED]` The first-wall residue is a coordinate, not a device output. New module
`RHTower/RouteRHarmonicQuantumGapCriterion` rests on `HTGeometry/CofinalUnitProfileResidue`, which
isolates the three properties a reader actually needs:

1. pointwise weights in `[0,1]`;
2. unit reference mass `sum_p mu_N(p)/p = 1`;
3. supports eventually avoiding every finite set.

Any such family reads the residue: `A_N(a) -> c` whenever `a - c/p` is summable. The Euler sieve is
one instance; the family is nonempty for every positive divergent weight on a countable index set,
by the explicit unit-mass window construction. Uniqueness of the coordinate now follows from
divergence of `sum 1/p` alone, with no reader at all.

### Mathematical delta

Combining with `(QW)`, the residue at the moving first wall lies in `{-1,0,+1}`. Therefore

`[OPEN CORE — ROUTE_R_FIRST_WALL_SUB_QUANTUM_GAP]` it suffices to produce **one** bounded cofinal
unit profile `mu` on the primes and **one** threshold `r < 1` with

`eventually_N  ‖profileAverage mu N (routeRPrimeGammaXiCriticalWallField rho)‖ ≤ r`

at every Xi divisor point `rho`. Lean theorem
`RHTower.riemannHypothesis_of_eventually_norm_profileAverage_lt_one` closes RH from that inequality.
Exact vanishing is no longer required, and the reading device is no longer fixed. The remaining
unproved content is a source-derived strict bound, not an equality.
