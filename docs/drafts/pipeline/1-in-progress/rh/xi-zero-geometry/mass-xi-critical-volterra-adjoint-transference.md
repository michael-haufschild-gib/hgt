# Mass-Xi critical Volterra-adjoint transference

- **ID:** `mass-xi-critical-volterra-adjoint-transference`
- **Stage:** 1 — in progress
- **Route:** `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3
- **Primary claim:** `[LEAN-PROVED EXACT REDUCTION; UNIFORM OUTGOING FLUX OPEN]`
- **RH used:** no
- **Computation used:** no

## Exact frontier

`RHTower.XiMassCriticalErrorFlux` proves unconditionally, for `a>1/2` and `sigma>0`,

```text
Prime_a,sigma,u(H) -> 2 pi g_a,sigma,u(-i/2)
  + integral_(0,infinity) Ecrit(h) F'_a,sigma,u(h) dh.
```

Polar term has norm independent of `u`; terminal completed-error flux vanishes. Remaining
RH-equivalent source problem is uniform boundedness in `u` of canonical infinite current.

New-corpus audit:

- `HedenmalmThetaTraceKernel.thetaTraceSq_eq_source_variance` is exact positive trace calibration,
  but no theorem maps `Ecrit` or mass orbit into its source inverse.
- `HermiteL2ClosedSpan` now gives exact positive/negative even Fourier-sector decomposition, but
  no theorem makes normalized Chebyshev error an `L2` vector or bounded functional there.
- Suzuki Gamma-wall block Hardy transfer and weighted-tail coercivity convert a *realized literal
  trace-zero carrier* into weighted `H1`; their cards retain literal source realization as open.
- prime-normal flow resolves bounded self-adjoint prime breadth, but its Gamma/Feshbach source
  coupling remains open.
- translated-window sieve and Halasz estimates control finite Dirichlet polynomials in mean square;
  they do not give a pointwise cofinal completed-error current bound.

External primary audit found Hedenmalm's 2026 theta differential-pair spectral realization and
Suzuki's 2022--2026 screw/Weil operator constructions. Their stated results provide spectral
realizations or RH criteria, not a source-side uniform bound for this mass current.

## Hostile conjecture loop

### C41-A — Hedenmalm variance directly controls the mass current

`[CIRCULAR]`. The trace variance is a fixed scalar. A bound for the mass current requires an
additional source map whose boundedness on completed zeta modes is exactly the missing provider.
No current theorem supplies it.

**Failure constraint:** next conjecture must construct an exact source map before using positivity.

### C41-B — Hermite-sector completeness turns the current into a uniform `L2` pairing

`[INSIGNIFICANT / INAPPLICABLE]`. Plancherel makes the mass orbit's unweighted `L2` norm independent
of `u`, but the corpus does not place the critical normalized Chebyshev error in the dual `L2`
space. Exponential weighting recovers integrability only by moving to a shifted line whose mass
orbit has the already-classified `exp(lambda |u|)` corona growth.

**Failure constraint:** next conjecture must retain causal completion and cannot replace source
cancellation by absolute `L2` magnitude.

### C41-C — Apply Suzuki weighted-tail coercivity directly to `Ecrit`

`[CIRCULAR]`. Suzuki theorem assumes literal cutoff equation for a realized physical carrier.
Identifying `Ecrit` with such a carrier is absent and is source-bearing, not formal bookkeeping.

**Failure constraint:** determine exact differential expression selected by causal completion
before seeking an intertwiner.

## Positive survivor: critical Volterra-adjoint law

Put

```text
e(h) = criticalMellinNormalizedChebyshevError(h),
E(h) = criticalMellinCompletedError(h),
D_1/2 F(h) = (1/2)F(h) - F'(h).
```

Corpus identity on `h>=0` is

```text
E(h)=1-2 exp(-h/2)-e(h)-(1/2) integral_0^h e(s) ds.       (1)
```

For `H>=0`, every differentiable `F` with the displayed finite integrals satisfies

```text
integral_0^H E(h)F'(h) dh
 = F(0) - integral_0^H exp(-h/2)F(h) dh
   + integral_0^H e(h) D_1/2 F(h) dh
   + (E(H)+e(H))F(H).                                    (2)
```

`[PAPER-PROVED]`. Proof: expand `(1)`. Fundamental theorem gives
`integral F'=F(H)-F(0)`. Integration by parts gives

```text
-2 integral exp(-h/2)F'
=-2 exp(-H/2)F(H)+2F(0)-integral exp(-h/2)F.
```

Fubini on `0<=s<=h<=H` gives

```text
integral_0^H F'(h)(integral_0^h e(s)ds)dh
=F(H)integral_0^H e(s)ds-integral_0^H e(s)F(s)ds.
```

Collect terms and use `(1)` at `H`; this is `(2)`.

For actual mass profile, existing deep-shift bounds and the elementary local Chebyshev bound imply
`e(H)F(H)->0`; existing theorem already gives `E(H)F(H)->0`. Therefore

```text
xiMassCompletedErrorFlux(a,sigma,u)
 = F(0) - integral_0^infinity exp(-h/2)F(h)dh
   + integral_0^infinity e(h) D_1/2 F(h)dh.              (3)
```

This is not the RH proof. It removes the causal primitive from the open current. The exact
source-bearing object is normalized Chebyshev error acting on the critical outgoing derivative.

## Frozen primary conjecture

`[CONJECTURE] CRITICAL_OUTGOING_SOURCE_TRANSFERENCE`

There is a source-defined intertwiner from the completed Suzuki/Hedenmalm physical carrier to the
half-line Chebyshev distribution such that its boundary functional is

```text
Phi -> integral_0^infinity e(h) ((1/2)Phi(h)-Phi'(h)) dh,
```

and the intertwiner is bounded on the complete mass half-wave orbit for every fixed `a>1/2` and
`sigma>0`.

Risky consequence: together with `(3)`, boundedness forces the §9.3 fixed-line prime source bound
and hence RH. Falsifier: any exact source realization whose outgoing boundary norm necessarily has
the mass-independent `exp(|u|/2)` radiation corona cannot provide this intertwiner.

## Open core

`[OPEN CORE]` Prove the literal source-defined outgoing current is uniformly bounded in height, or
construct a source-derived intertwiner that proves this bound. A theorem merely assuming
boundedness of the displayed Chebyshev functional is rejected: Lean now proves that assumption is
exactly equivalent to RH.

## Gates

- [x] audit newest HTGeometry/RHTower theorem surfaces
- [x] repeat internal and external audit for exact connector
- [x] kill direct variance, bare `L2`, and assumption-only Gamma routes
- [x] dependency-close finite Volterra-adjoint identity on paper
- [x] formalize `(2)` and actual-mass infinite law `(3)` unconditionally
- [x] identify critical cofinal sum with legal bottom Euler integral
- [x] prove `RH ↔` uniform outgoing-current bound in Lean
- [ ] hostile-audit and construct the literal source intertwiner
- [ ] prove uniform current bound and RH

## 2026-08-08 live-corpus delta: regular Toeplitz realization is impossible

The newly formalized theorem
`RHTower.vonMangoldtToeplitzCountertraceRegularityNoGo` changes the admissible shape of the frozen
conjecture.  The canonical moment counterweights forced by exact finite-section opening
cancellation are unbounded; the corresponding symmetric Toeplitz counterdensity has neither a
bounded operator realization on `ℓ²(ℕ)` nor even an `ℓ²`-valued linear realization on the
finite-support core.

### C41-D — realize the outgoing Chebyshev functional by the canonical bounded Toeplitz operator

`[FALSIFIED; LEAN-PROVED NO-GO]`.  This is stronger than failure of a norm estimate: the literal
operator does not exist with values in `ℓ²` on the canonical algebraic core.  Hedenmalm/Hermite
completeness therefore cannot repair the route by completing this counterdensity in the ordinary
Hilbert norm.

**Positive survivor.**  The exact Volterra-adjoint law and the full adjacent-prime graph law point
to the same universal object: a boundary cohomology class, not a bounded Toeplitz state.  Bounded
adjacent graph gradients form the exact source coboundaries; the sole surviving constant class is
the cofinal flux.  Any viable Suzuki/Hedenmalm transference must therefore be one of:

1. a non-Toeplitz source-derived map that acts directly on this quotient;
2. a rigorously specified rigged/weighted space in which the unbounded counterdensity is closable
   and the mass orbit has a uniform graph-boundary trace;
3. an exact source identity annihilating the cofinal constant class before Hilbert completion.

A generic bounded-`L²` or bounded-Toeplitz intertwiner is now rejected before further work.  This
does not prove the uniform current bound; it removes an entire circular avenue and sharpens the
open core to construction of a source-derived cofinal-flux law.

## 2026-08-08 exact open-core bridge `[LEAN-PROVED]`

The paper identity `(2)` and infinite law `(3)` are now formalized unconditionally in
`RHTower.XiMassCriticalOutgoingCurrent`.  The module proves measurability and finite-interval
integration by parts/Fubini, a corpus-primitive global bound for `e`, both terminal limits, and
absolute integrability of the damped and outgoing currents.  No PNT remainder estimate, numerical
certificate, or RH hypothesis enters.

### C41-E — critical cofinal atoms and legal bottom Euler source have the same limit

`[PROVED; LEAN-PROVED]`.  `RHTower.XiMassCriticalOutgoingOpenCore` proves the critical atom weight
is exactly the depth-erased `LSeries.term` at `1/2`.  Absolute summability from the existing bottom
atomization gives convergence of the `Icc 2 floor(exp H)` cofinal sums to the legal bottom Euler
integral.  Uniqueness of limits then gives

```text
xiMassBottomPrimeIntegral(a,c,sigma+iu)
 = 2 pi g_a,sigma,u(-i/2) + xiMassCompletedErrorFlux(a,sigma,u).
```

Combining this with `(3)` yields the exact source decomposition

```text
BottomPrime(u) = ExplicitFace(u) + OutgoingFlux(u),

OutgoingFlux(u)
 = integral_0^infinity e(h) ((1/2)F_u(h)-F'_u(h)) dh.
```

Lean proves the explicit face is height-uniformly bounded using the actual corpus integral bound
for the mass Fourier profile, the exact pole norm, and the symbolic integral of `exp(-h/2)`.
Consequently

```text
XiMassBottomPrimeLineBound(a,c,sigma)
  iff XiMassCriticalOutgoingFluxLineBound(a,sigma),

RiemannHypothesis
  iff XiMassCriticalOutgoingFluxLineBound(a,sigma).
```

This is a strict proof-burden reduction and also an anti-theatre guard: any proposed theorem that
assumes the uniform outgoing bound has assumed RH verbatim.

### C41-F — use the new pinned-Volterra Hilbert metric to annihilate the outgoing boundary

`[FALSIFIED BY EXISTING LEAN THEOREM]`.  `HedenmalmPinnedVolterraBoundaryDefect` proves that any
bounded operator satisfying the exact Volterra anticommutator equation kills the constant mode;
no injective bounded composite metric can satisfy it.  This is the continuous counterpart of the
Toeplitz countertrace no-go.  Pinning exposes a rank-two boundary operator but cannot erase the
cofinal class with a faithful bounded metric.

### C41-G — import Suzuki finite negative-Stieltjes positivity as the missing source bound

`[INAPPLICABLE / SOURCE GAP EXPLICIT]`.  `SuzukiCarlemanStieltjesFlux` proves a finite positive
colligation lowers a central affine intercept and identifies the exact chord-mass gap.  Its module
explicitly leaves construction of the prime--Gamma Stieltjes measure and proof of that gap open.
No theorem maps the outgoing current to this finite colligation.  Applying the threshold without
that map would be circular.

### Higher universal principle

Prime-graph coboundaries, Toeplitz non-realizability, and pinned-Volterra noninjectivity are three
models of one obstruction: local exactness does not control the constant boundary-cohomology
class.  The operator `1/2-d/dh` is the correct adjoint boundary differential because it removes the
causal Volterra primitive and leaves precisely that class.  A successful proof must provide a
nonlocal all-prime conservation law for its cofinal flux; Hilbert completion, local Lipschitz
control, finite positive frames, and bounded diagonal/Toeplitz metrics cannot supply it.

## 2026-08-08 discrete remainder reduction `[LEAN-PROVED]`

### C41-H — transfer the new floor-summatory square-root law directly to outgoing flux

`[CIRCULAR]`.  `abs_floorSummatory_psiRemainder_add_le` controls the floor-averaged image of
`R(N)=psi(N)-N`.  Exact recovery uses `moebius_floor_inversion`; Mellin diagonalization inserts
`1/zeta(s)`.  The outgoing differential supplies the linear multiplier `s`, cancelling the causal
Volterra denominator, but does not supply a zeta factor.  Direct inversion therefore asks for the
same critical-half-plane zero exclusion as the target.

### C41-I — use the new frequency Lipschitz theorem as a uniform harmonic transference norm

`[FALSIFIED AS A CLOSING ESTIMATE]`.  `XiMassStripFourierLipschitz` is genuinely uniform in vertical
height, but harmonic summation by parts acts on the critically gauged coefficient
`sqrt(N) D_(1/2)F(log N)`.  The already-proved mass radiation corona gives this coefficient
`exp(|u|/2)` two-sided instability.  Local Lipschitz control does not bound its cofinal variation.

### C41-J — remove only the continuous interpolation and floor error

`[PROVED; LEAN-PROVED]`.  The exact identity

```text
e(h) = exp(-h/2) R(floor(exp h))
     + exp(-h/2) (floor(exp h) - exp h)
```

splits outgoing flux into a raw discrete Selberg-remainder current and a floor-sawtooth current.
The floor error has modulus at most one.  The actual zero-shift outgoing derivative has a
height-independent integral majorant, so Lean proves the sawtooth current is absolutely integrable
and uniformly bounded.  The new module
`RHTower.XiMassCriticalDiscreteRemainder` proves

```text
XiMassCriticalOutgoingFluxLineBound(a,sigma)
  iff XiMassCriticalDiscreteRemainderFluxLineBound(a,sigma),

RiemannHypothesis
  iff XiMassCriticalDiscreteRemainderFluxLineBound(a,sigma).
```

No numerical computation, PNT remainder, zero expansion, or RH hypothesis enters.

### C41-K — reflect vertical height by exact conjugation

`[PROVED; LEAN-PROVED]`.  On the real source axis the mass root is real and the mass test is even.
Passing conjugation through the actual strip-Fourier, derivative, density, and infinite-current
integrals gives

```text
conj(DiscreteFlux(u)) = DiscreteFlux(-u).
```

`RHTower.XiMassCriticalDiscreteRemainderSymmetry` therefore proves the full line-bound criterion is
equivalent to its restriction to `u>=0`, and proves RH equivalent to that one-sided criterion.

### C41-L — apply one-sided Selberg window average by absolute cell summation

`[FALSIFIED AS A CLOSING ESTIMATE]`.  The new theorem controls
`sum |R(n)|(1/n-1/(n+1))`, hence weight scale `|R(n)|/n^2`.  The critical current cell before phase
cancellation has scale `R(n)/n^(3/2)`.  Direct absolute transference loses a factor `sqrt(n)` and
cannot yield a uniform vertical bound.  Any use of this theorem must retain mass phase across
cells or prove a new oscillatory window norm.

### C41-M — discard the superluminal logarithmic-time tail

`[PROVED; LEAN-PROVED]`.  Fix `1/2<d<a`.  For `u>=0`, depth-shift decay of the actual outgoing
derivative and only `|R(N)|<=8N` give

```text
norm(discreteDensity(u,h))
  <= 8 J_(sigma,d) exp(d*u + (1/2-d)*h).
```

At `H_d(u)=d*u/(d-1/2)`, exact integration proves

```text
norm(integral_(H_d(u))^infinity discreteDensity(u,h) dh)
  <= 8 J_(sigma,d)/(d-1/2),
```

uniformly in `u`.  `RHTower.XiMassCriticalDiscreteRemainderCone` proves the full current equals its
finite cone part plus this tail and hence

```text
RiemannHypothesis
  iff uniformBound(u>=0, integral_0^(H_d(u)) discreteDensity(u,h) dh).
```

This removes the opposite vertical cone and all superluminal logarithmic time without a PNT
remainder or cancellation assumption.

### C41-N — round the cone to complete cells and atomize exactly

`[PROVED; LEAN-PROVED]`.  Let `H=d*u/(d-1/2)` and `M=floor(exp H)`.  The damped profile
`K_u(h)=exp(-h/2)F_u(h)` satisfies the actual derivative identity

```text
K'_u(h) = -exp(-h/2) ((1/2)F_u(h)-F'_u(h)).
```

Exact cell integration and finite Abel summation give

```text
integral_0^log(M+1) discreteDensity(u,h) dh
  = -K_u(0)
    + sum_(n=2)^M (vonMangoldt(n)-1) K_u(log n)
    - R(M) K_u(log(M+1)).
```

`RHTower.XiMassCriticalCenteredAtomCone` proves both new boundary pieces uniformly bounded.  The
overflow from `H` to `log(M+1)` lies in the absolutely controlled tail.  The terminal term uses
only `|R(M)|<=8M`, `M<=exp(H)`, and deep-shift decay; cone-edge exponents cancel exactly.  Hence

```text
RiemannHypothesis
  iff uniformBound(u>=0,
    sum_(n=2)^floor(exp(H_d(u)))
      (vonMangoldt(n)-1) exp(-log(n)/2) F_u(log n)).
```

This removes improper integration and all cell-edge terms from the open obligation.

### C41-O — expose the joint mass/Dirichlet phase before taking norms

`[PROVED; LEAN-PROVED]`.  Finite sum--integral exchange gives the exact identity

```text
centeredAtomConeSum(a,sigma,d,u)
  = integral_x xiMassAnalyticTest(a,sigma+i*u,x)
      * sum_(n=2)^floor(exp(H_d(u)))
          (vonMangoldt(n)-1) n^(-1/2) exp(-i*x*log(n)) dx.
```

Every term is genuinely integrable under `exp(-sigma*|x|)`.  The module
`RHTower.XiMassCriticalCenteredDirichletCone` proves RH equivalent to uniform boundedness of this
finite pairing on `u>=0`.  This interface preserves the joint mass and arithmetic phase.

### C41-P — close the Dirichlet face with current Perron/van der Corput machinery

`[FAILED WITH EXACT GAP]`.  `PerronPrimeSumBound` assumes a safe line `Re s>=1` and returns
cutoff-dependent sieve masses.  The cone polynomial is at exponent `1/2`; transferring the safe
bound there is precisely the critical zero barrier.  `CCMFirstRowVanDerCorputBlocks` bounds a
specific squared difference phase after Gram expansion, not the pointwise first-order centered
polynomial above.  No existing theorem couples either estimate to this moving mass pairing.

Positive survivor: the exact Dirichlet pairing in C41-O is now available for a future hybrid
stationary-phase/mean-square theorem, with no continuation or improper-series seam.

### C41-Q — expose exact Lorentz saddle and Route N boost coordinates

`[PROVED; LEAN-PROVED]`. Before estimating the arithmetic polynomial, write its `n`th joint phase
with `h=log n` as

```text
Theta_(a,u,h)(x)=u sqrt(x^2+a^2)+h x.
```

`RHTower.HedenmalmGammaSewnXiMassTimelikeBoostBridge` proves the exact classification:

```text
0<=h<u:
  q=sqrt(u^2-h^2),
  unique x_*=-a h/q,
  Theta'(x_*)=0,
  Theta(x_*)=a q;

0<u<=h:
  Theta'(x)>0 for every x.
```

Hence frequencies `log n<u` are precisely timelike stationary atoms; `log n>=u` are spacelike
nonstationary atoms. This is a strict geometric refinement of the earlier coarse superluminal
tail `h>d*u/(d-1/2)`.

The same module proves that Route N reciprocal Sonin amplification `A` supplies canonical unit
proper-time coordinates

```text
u_A=(A+A^-1)/2,
h_A=(A-A^-1)/2,
x_*=-a(A-A^-1)/2.
```

Route N Burnol holonomy is `A-A^-1`, nonmetricity is `A+A^-1-2`, and C27 affine residue is
multiplicity times `-log A/(2 log p)`. Thus Route N residue/escape and Route T mass propagation
are one boost charge, not independent proof pressures.

### C41-R — exact curved-contour rate and sharp spacelike cone

`[GEOMETRY PROVED; LEAN-PROVED; FOURIER LIFT AND CONE SUMMATION PROVED]`. Real-axis integration by parts only sees
`Theta'(x)>h-u` and loses the glancing layer. The mass substitution `x=a sinh t` reveals the missing
geometry. After a curved shift `t -> t-i theta`, put `c=cos theta`, `s=sin theta`. The squared
damping rate is

```text
lambda(c,s)^2=(sigma*c+h*s)^2-(u*s)^2,   c^2+s^2=1, c,s>=0.
```

Let

```text
zeta_(sigma,u,h)=(sigma+i*u)^2+h^2,
kappa_(sigma,u,h)=Re sqrt(zeta_(sigma,u,h)).
```

`RHTower.XiMassSpacelikeContourOptimality` proves the exact variational identity

```text
max_(c^2+s^2=1, c,s>=0) lambda(c,s)^2 = kappa_(sigma,u,h)^2,
```

constructs an actual nonnegative maximizing contour, and proves in the strict spacelike chamber
`0<u<h`

```text
h-u < sqrt(h^2-u^2) < kappa_(sigma,u,h).
```

Thus horizontal strip translation is quantitatively suboptimal, not merely technically coarse.
At `sigma -> 0`, balancing the critical coefficient growth `exp(h/2)` against the expected curved
mass decay `exp(-a*sqrt(h^2-u^2))` gives the exact algebraic threshold

```text
alpha_sharp(a)=a/sqrt(a^2-1/4),
h/2<a*sqrt(h^2-u^2)  iff  alpha_sharp(a)*u<h,
alpha_sharp(a)<a/(a-1/2).
```

The last comparison is strict for every legal `a>1/2`. C41-S now supplies the Bessel-strength
contour estimate and proves that the optimizer is an actual interior angle. The glancing null layer
remains separate because `kappa` loses linear growth as `h/u -> 1` and `sigma -> 0`.

### C41-S — prove the Bessel-strength Fourier lift

`[PROVED; LEAN-PROVED]`. For

```text
F_(sigma,u)(h)=int_R exp(-(sigma+i*u)*sqrt(x^2+a^2))*exp(-i*h*x) dx.
```

`RHTower.XiMassHyperbolicFourierRepresentation` first proves the exact branch-free identity

```text
F_(sigma,u)(h)
 = int_R a cosh(t) exp(-(sigma+i*u)a cosh(t)) exp(-i*h*a*sinh(t)) dt.
```

`RHTower.XiMassHyperbolicCurvedContourDecay` then proves the one-sided deformation
`t -> t-i*theta` for every `0<=theta<pi/2`. With

```text
A=sigma*cos(theta)+h*sin(theta),
B=u*sin(theta),
q=sqrt(A^2-B^2),
r=arsinh(B/q),
```

the Lorentz translation `A cosh(t)+B sinh(t)=q cosh(t+r)` gives

```text
|F_(sigma,u)(h)| <= 2*a*exp(r)*K_1(a*q).              (T.41-S.1)
```

The same module proves the coefficient-faithful Schlaefli comparison

```text
K_1(s) <= exp(-(s-s0))*K_1(s0),   0<s0<=s,            (T.41-S.2)
```

so no fixed fraction of the exponent is lost. Finally
`RHTower.XiMassOptimalCurvedBesselDecay` proves C41-R's maximizing nonnegative contour is an
actual interior angle and that its `q` equals

```text
kappa=Re sqrt((sigma+i*u)^2+h^2).
```

Thus `(T.41-S.1)` holds at the exact optimal propagation rate `a*kappa`, and `(T.41-S.2)` gives a
fixed-base bound with full exponential coefficient `1`. All capstones use only `propext`,
`Classical.choice`, and `Quot.sound`.

### C41-T — close the complete sharp-spacelike atom cone

`[PROVED; LEAN-PROVED]`. The moving optimal contour contains boost prefactor `exp(r)`. C33 proves
this factor cannot destroy summability. Whenever `alpha>1`, `B>=0`, `alpha*B<=A`, and
`q^2=A^2-B^2`,

```text
exp(arsinh(B/q)) <= (alpha+1)/(alpha-1).              (T.41-T.1)
```

For every `alpha>alpha_sharp(a)`, put

```text
beta(alpha)=sqrt(1-alpha^-2),
p(a,alpha)=1/2+a*beta(alpha).
```

Lean proves `p(a,alpha)>1`, `beta(alpha)h<=sqrt(h^2-u^2)` on `alpha*u<=h`, and the coefficient-
faithful profile bound

```text
|exp(-h/2) F_u(h)| <= C(a,alpha) exp(-p(a,alpha)h).  (T.41-T.2)
```

At `h=log n`, the centered coefficient is dominated by `Lambda(n)+1`; both
`sum Lambda(n)n^-p` and `sum n^-p` converge for `p>1`. Module
`RHTower.XiMassSharpSpacelikeConeSummability` therefore proves absolute summability of all atoms
with `alpha*u<=log n`, uniformly in `u` and every finite cutoff. It also proves exact identity

```text
full finite cone = sharp-spacelike finite cone + timelike/glancing finite cone, (T.41-T.3)
```

with complementary condition `log n<alpha*u`. No limiting boundary atom or remainder is created.
Headline C33 capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

### C41-U — arbitrarily sharp residual-cone criterion

`[PROVED; LEAN-PROVED]`. C33's partition is not tied to one mass-dependent slope. For every
`alpha>1`, Lean constructs the legal parameter

```text
a=alpha/sqrt(alpha^2-1)>1/2,
alpha_sharp(a)=a/sqrt(a^2-1/4)<alpha.                 (T.41-U.1)
```

For each `sigma>0`, suitable legal `c,d` then give the exact equivalence

```text
RH iff the finite centered residual sum supported on log n<alpha*u
       is uniformly bounded for u>=0.                (T.41-U.2)
```

The proof is bidirectional: add or subtract C33's cutoff-independent sharp-spacelike bound from
the full Route T criterion. Thus Route T's remaining arithmetic obstruction can be localized to
every fixed strict enlargement of the causal cone, with `alpha` arbitrarily close to `1`; it is
not a broad-cone artifact. Module `RHTower.XiMassTimelikeGlancingResidualCriterion` is
umbrella-wired. Its headline capstones use only `propext`, `Classical.choice`, and `Quot.sound`.

### Updated open core

For any legal `1/2<d<a`, prove the height-uniform finite centered-atom bound

```text
sum_(n=2)^floor(exp(d*u/(d-1/2)))
  (vonMangoldt(n)-1) exp(-log(n)/2) F_u(log n).
```

Continuous interpolation, floor sawtooth, negative vertical heights, superluminal tail, partial
cell, and terminal remainder are discharged.  Remaining obstruction is cofinal cancellation of
centered von Mangoldt atoms inside the finite mass light cone.  Closure requires an oscillatory
transference that neither inverts the floor transform nor takes termwise absolute values at
critical scale.

C41-R--C41-T now prove the exact optimal contour rate, its interior angle realization, the
full-exponent Bessel lift, uniform boost control, and actual absolute summability of every strict
sharp-spacelike cone. This is no longer an inferred decay claim: `(T.41-T.3)` is an exact finite
atom partition and its first summand has one cutoff-independent Lean bound. Remaining open core is
source-level cofinal cancellation in the explicit complementary sum `log n<alpha*u`. By C41-U,
`alpha>1` may be chosen arbitrarily close to the true causal slope `1`; preferably prove the law
before norms in exact joint pairing.

Equivalently, prove uniform boundedness of the exact integral pairing in C41-O.  This is the only
current form that exposes both mass and arithmetic phases before a norm; it is preferred for any
new hybrid oscillatory estimate.
