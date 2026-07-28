# Time has an observer-dependent dimension

- **ID:** observer-dependent-temporal-dimension
- **Stage:** 1-in-progress
- **Type:** NEW INVARIANT / UNIVERSAL QUANTUM DYNAMICS LAW
- **Working title:** *Time has an observer-dependent dimension*
- **Status:** paper proof and exact-object novelty audit in progress
- **Parent:** finite observer-coherence law, graph-rank recurrence law,
  worst-spectrum sharpness, finite contraction return boundary

## Headline, stated without metaphysics

A dynamical law may supply one time parameter, but an observer does not in
general see one periodic phase. The observer sees only the frequencies carried
by its spectral record. Those frequencies generate two canonical objects:

\[
 \Gamma_{\mathcal O}
 =\left\langle \operatorname{supp}\mu_{\mathcal O}\right\rangle_{\mathbb Z}
 \subset\mathbb R,\qquad
 \Omega_{\mathcal O}
 =\operatorname{span}_{\mathbb Q}
   \operatorname{supp}\mu_{\mathcal O}\subset\mathbb R.
\]

Here \(\mu_{\mathcal O}\) is the positive spectral measure of the observed
displacement signal. The exact effective dimension is the rational rank of
\(\Omega_{\mathcal O}\); the exact return type is the topology of
\(\Gamma_{\mathcal O}\).

This is an operational dimension of the observed temporal orbit. It is not a
claim that spacetime has a variable coordinate dimension.

## Abductive jump — conjecture before proof

**Relational temporal-dimension conjecture.** In a globally reversible, or
globally stationary constrained, universe, experienced temporal dimension and
the macroscopic arrow are properties of an observer's history space rather
than of an external evolution parameter. The dimension is recoverable from the
small-return scaling of that observer's record. In the thermodynamic or QFT
limit, divergence of this observer dimension drives recurrence density to zero
and is the mechanism by which a reversible microscopic law acquires a
nonreturning macroscopic history. Different observer algebras on the same
global state can therefore have different temporal dimensions and different
finite-versus-infinite return structure.

This is a conjecture generated from the joined evidence below, not a theorem
selected because a proof route is presently visible. Provability is a
downstream question. No manuscript claim may use the conjecture until its
finite, thermodynamic-limit, constrained-system, and physical-model bridges
have been separately closed.

### Predicted consequences

1. For every finite pure-point observer, the logarithmic small-return
   probability exponent equals its rational visible-frequency rank.
2. Combining observers obeys a temporal rank law: two individually periodic
   records can jointly be aperiodic, and observer refinement cannot lower
   temporal dimension.
3. A sequence of observer records whose temporal dimensions diverge has
   vanishing fixed-resolution return density under a dimension-uniform
   nondegeneracy law.
4. A genuine stationary constrained quantum model admits different internal
   observer algebras with different temporal dimensions while retaining no
   observable external clock origin.
5. A local QFT model supplies a continuous or unbounded-rank observer spectrum
   that realizes the nonreturning limit without inserting microscopic
   nonunitarity.
6. A finite multiqubit or qudit experiment can recover temporal dimension as a
   log-log return-frequency slope and watch that slope change when accessible
   modes are removed.

Any false item fractures the conjecture and must be recorded; surviving finite
parts are not by themselves evidence for the thermodynamic, QFT, or
experienced-time clauses.

## Definition

For an arbitrary positive Borel spectral measure \(\mu_{\mathcal O}\) on the
real frequency axis, define the visible frequency group, visible frequency
module, and observer temporal dimension by
\[
 \Gamma(H,\mathcal O)
 =\operatorname{cl}_{\rm alg}^{\mathbb Z}
   (\operatorname{supp}\mu_{\mathcal O}),\qquad
 \Omega(H,\mathcal O)
 =\operatorname{span}_{\mathbb Q}
   (\operatorname{supp}\mu_{\mathcal O}),
\]
\[
 \boxed{\quad
 \dim_{\rm time}(H,\mathcal O)
 =\dim_{\mathbb Q}\Omega(H,\mathcal O).\quad}
\]
The dimension is a cardinal and may be finite or infinite. No finite spectrum,
finite observer family, or pure-point assumption enters this definition.

For a finite Hamiltonian with distinct energy sectors
\(E_1,\ldots,E_d\), and a finite observer family \(B^{(a)}\) with
nonnegative weights \(\lambda_a\), put
\[
 W_{ij}=\sum_a\lambda_a|B^{(a)}_{ij}|^2.
\]
The coherence graph \(G_{\mathcal O}\) joins \(i\) and \(j\) when
\(W_{ij}>0\) or \(W_{ji}>0\). Its spectral measure is atomic on the
visible gaps, so the general definition reduces exactly to
\[
 \Omega(H,\mathcal O)=
 \operatorname{span}_{\mathbb Q}
 \{E_i-E_j:\{i,j\}\in E(G_{\mathcal O})\}.
\]

Because the visible gaps are differences inside graph components,
\[
 0\leq\dim_{\rm time}(H,\mathcal O)
 \leq d-c(G_{\mathcal O}).
\]
The upper endpoint is the observer's topological phase capacity; the actual
temporal dimension can be smaller because of arithmetic relations among
visible gaps.

## Theorem A — universal lattice--continuum law

For every observer spectral measure, with no cardinality restriction,
exactly one of the following temporal types occurs:

1. **stationary:** \(\Gamma_{\mathcal O}=\{0\}\);
2. **clock-lattice:** there is a unique positive fundamental frequency
   \(\omega_{\mathcal O}\) with
   \(\Gamma_{\mathcal O}=\omega_{\mathcal O}\mathbb Z\);
3. **gapless:** \(\Gamma_{\mathcal O}\) is dense in \(\mathbb R\).

Moreover:

- the observed record is stationary at every time exactly in case 1;
- a positive exact return exists exactly in cases 1 or 2;
- every nonstationary exact return is an integer multiple of
  \(2\pi/\omega_{\mathcal O}\);
- no positive exact return exists in case 3.

Thus every observer sees either no clock, one exact frequency lattice, or a
gapless temporal frequency group. There is no fourth possibility.

### Paper proof

Let \(S=\operatorname{supp}\mu_{\mathcal O}\). Exact return at \(T\ne0\)
means
\[
 e^{iT\omega}=1\qquad(\omega\in S).
\]
For the spectral integral this pointwise support statement is equivalent to
zero observed displacement: the integrand is continuous and nonnegative, so
zero integral makes it vanish almost everywhere; its zero set is closed and
therefore contains the support. The converse follows because the support is
conull.

The exponential condition is equivalent to
\[
 S\subseteq (2\pi/T)\mathbb Z,
\]
and hence, by algebraic generation,
\[
 \Gamma_{\mathcal O}\subseteq(2\pi/T)\mathbb Z.             \tag{A1}
\]
Every subgroup of a cyclic group is cyclic. Conversely, if
\(\Gamma_{\mathcal O}=\omega\mathbb Z\), then
\(T=2\pi/|\omega|\) is a positive exact return when \(\omega\ne0\);
when \(\omega=0\), every time returns.

Finally every additive subgroup of the Archimedean line \(\mathbb R\) is
either cyclic or dense. The two alternatives are exclusive. Combining this
classification with (A1) proves the trichotomy and every return statement.

## Theorem A2 — dimension and the infinite rank-one fracture

\[
 \dim_{\rm time}=0
 \quad\Longleftrightarrow\quad
 \Gamma_{\mathcal O}=\{0\}
 \quad\Longleftrightarrow\quad
 \text{the observed record is stationary}.
\]
A nonstationary clock-lattice observer has
\(\dim_{\rm time}=1\). Every observer with
\(\dim_{\rm time}\ge2\), finite or infinite, is gapless and has no positive
exact return.

The converse “dimension one implies periodic” holds for finitely generated
visible groups, hence for every finite Hamiltonian/observer packet, but fails
for infinite spectra. A rank-one group such as
\(\mathbb Z[1/2]\) is dense and has no positive exact return. Therefore
infinite temporal structure has two independent invariants:

\[
 \boxed{\text{rational dimension}\quad+\quad
        \text{lattice versus dense type}.}
\]

This is the exact infinite extension. It removes the false inference that
rank one alone guarantees a clock once infinitely many visible frequencies
are allowed.

For a finite observer:

1. \(\dim_{\rm time}=0\) iff its record is stationary;
2. \(\dim_{\rm time}=1\) iff it is nonstationary and exactly periodic;
3. \(\dim_{\rm time}\ge2\) iff it has no positive exact return.

The same Hamiltonian can therefore be timeless, periodic, or gapless to
different observation algebras.

## Theorem B — observer monotonicity and exact quotient

If
\[
 \operatorname{supp}\mu_{\mathcal O_1}
 \subseteq\operatorname{supp}\mu_{\mathcal O_2},
\]
then
\[
 \Gamma(H,\mathcal O_1)\subseteq\Gamma(H,\mathcal O_2),
 \Omega(H,\mathcal O_1)\subseteq\Omega(H,\mathcal O_2),
 \qquad
 \dim_{\rm time}(H,\mathcal O_1)
 \leq\dim_{\rm time}(H,\mathcal O_2).
\]
In particular, absolute continuity
\(\mu_{\mathcal O_1}\ll\mu_{\mathcal O_2}\) implies all three conclusions.
Adding observations can reveal temporal dimensions; discarding observations
cannot create them.

For a finite coherence graph, support inclusion reduces to edge inclusion.
At the graph level the full relative-phase space has dimension
\(d-c(G_{\mathcal O})\). The temporal frequency module is the arithmetic
subspace actually traversed by the Hamiltonian.

## Theorem C — finite-resolution dephasing filtration

For a signal threshold \(\theta>0\), define the operational graph at
environmental time \(s\) by
\[
 \{i,j\}\in G_{\theta}(s)
 \quad\Longleftrightarrow\quad
 W_{ij}(s)>\theta\ \text{or}\ W_{ji}(s)>\theta,
\]
and define
\[
 \dim_{\rm time}^{(\theta)}(s)
 =\dim_{\mathbb Q}\operatorname{span}_{\mathbb Q}
 \{E_i-E_j:\{i,j\}\in E(G_\theta(s))\}.
\]

If every coherence weight is nonincreasing in \(s\), then
\[
 s\le t\Longrightarrow G_\theta(t)\le G_\theta(s)
\Longrightarrow
\dim_{\rm time}^{(\theta)}(t)
\le\dim_{\rm time}^{(\theta)}(s).
\]
Hence finite-resolution temporal dimension is an integer-valued monotone
filtration.

For exponential pure dephasing
\[
 B_{ij}(s)=
 e^{-\frac12(\ell_i-\ell_j)^2s}B_{ij}(0),
\]
the squared observer weights decay as
\[
 W_{ij}(s)=
 e^{-(\ell_i-\ell_j)^2s}W_{ij}(0).
\]
Every nonzero coherence remains nonzero at every finite \(s\), so exact
zero-threshold dimension does not change at finite time. For every fixed
positive threshold, edges cross at the explicit times
\[
 s_{ij}=
 \frac{\log(W_{ij}(0)/\theta)}
      {(\ell_i-\ell_j)^2}
\]
whenever numerator and denominator are positive. Continuous loss therefore
produces discrete operational changes.

## Theorem D — arbitrary dimension-loss schedules are physically realizable

For every \(r\ge1\), every threshold \(0<\theta<1\), and every ordered list
of positive times
\[
 0<\tau_1\le\cdots\le\tau_r,
\]
there is an \((r+1)\)-level Hamiltonian, a self-adjoint star observer, and one
diagonal Lindblad dephasing operator such that:

1. the \(r\) star gaps are rationally independent;
2. star edge \(j\) crosses threshold exactly at \(\tau_j\);
3. the operational temporal dimension equals the number of edges not yet
   crossed;
4. it therefore follows the prescribed stepwise schedule from \(r\) to
   zero.

### Construction

Use a hub \(0\), leaves \(1,\ldots,r\), and a self-adjoint observer whose
only nonzero off-diagonal entries are the star pairs. For distinct primes
\(p_1,\ldots,p_r\), choose
\[
 E_0=0,\qquad E_j=\log p_j.
\]
Unique factorisation makes the star gaps rationally independent. Give all
star edges common initial squared weight one.
Put
\[
 \ell_0=0,\qquad
 \ell_j=\sqrt{\log(1/\theta)/\tau_j}.
\]
Then star weight \(j\) is
\[
 e^{-\ell_j^2s},
\]
which equals \(\theta\) exactly at \(s=\tau_j\). A diagonal self-adjoint
\(L=\operatorname{diag}(\ell_0,\ldots,\ell_r)\) generates
\[
 \mathcal L(B)=LBL-\tfrac12(L^2B+BL^2),
\]
whose \((i,j)\) entry is
\[
 -\tfrac12(\ell_i-\ell_j)^2B_{ij}.
\]
Thus the displayed exponential is the exact Lindblad solution. Each active
star gap is an independent basis vector, so temporal dimension is exactly
the active-edge count.

## Theorem E — recurrence consequence

The existing observer graph law gives a spectrum-uniform deadline with
exponent \(d-c(G)\). The temporal dimension refines the exponent for a fixed
spectrum:

If every visible gap is represented using \(r=\dim_{\rm time}\) rationally
independent basis frequencies with a finite integer-coordinate height
\(\mathcal H\), simultaneous approximation of only those \(r\) basis
frequencies gives a recurrence deadline of order
\[
 \varepsilon^{-r}
\]
with an explicit factor depending on \(\mathcal H\), not on the number of
invisible sectors. Worst-spectrum constructions attain every \(r\), so the
rank exponent cannot be reduced uniformly.

Under the dephasing filtration, the operational recurrence exponent drops
with \(\dim_{\rm time}^{(\theta)}\). Smooth loss of coherence can therefore
cause abrupt reductions in observable recurrence complexity.

## What would be new

Classical parents already contain:

- Kronecker flows and rational frequency rank;
- commensurate-gap criteria for exact quantum revival;
- graph connected components and incidence rank;
- Lindblad pure dephasing;
- Poincaré and quantum recurrence.

Novelty is claimed only for one joined invariant and law:

1. arbitrary finite observer families select a coherence graph;
2. the rational span of only observer-visible gaps is the exact temporal
   dimension;
3. this dimension gives the stationary/periodic/nonreturning classification;
4. physical dephasing induces a monotone finite-resolution dimension
   filtration;
5. every finite dimension-loss schedule is realizable by one physical
   dephasing generator;
6. the same dimension controls recurrence complexity.

An exact-object literature match to this joined law kills the paper.

## Hostile review requirements

1. **“Dimension of time” is clickbait.** The manuscript must define it before
   using the phrase and repeatedly distinguish it from spacetime dimension.
2. **Graph capacity is not orbit dimension.** The rational frequency-module
   theorem is mandatory.
3. **Observer dependence is already known qualitatively.** Exact
   stationary/periodic/nonreturning classification, monotonicity, physical
   schedule realization, and recurrence consequence must be central.
4. **Threshold is arbitrary.** Interpret \(\theta\) as a certified
   signal-to-noise floor and show covariance under common rescaling of
   observer weights and threshold.
5. **Dephasing is not a fundamental arrow of time.** Claim an operational
   dimension-loss arrow under a named Markovian channel, not a derivation of
   thermodynamic or cosmological time.
6. **A star observable may be engineered.** Supply a local qubit/qudit
   realization or restrict claims to finite-level platforms.
7. **Exact periods are nongeneric.** This is a conclusion of the rank law,
   not an omitted caveat.
8. **Continuous spectra and thermodynamic limits.** Either extend the
   invariant to countable frequency modules and state the infinite-rank
   boundary, or keep “every finite quantum observer” explicit.

## Formalization gates

- [x] exact weighted observer displacement identity
- [x] graph phase capacity \(d-c(G)\)
- [x] graph-capacity recurrence deadline
- [x] worst-spectrum rank exponent
- [ ] visible rational frequency module definition
- [ ] temporal dimension bounded by graph capacity
- [ ] temporal dimension zero/stationary equivalence
- [ ] exact positive period iff temporal dimension at most one
- [ ] observer monotonicity
- [ ] threshold-graph monotonicity and temporal-rank filtration
- [ ] diagonal Lindblad entry and exponential solution identities
- [ ] arbitrary star schedule realization
- [ ] fixed-spectrum rank-height recurrence refinement
- [ ] countable/infinite-rank boundary
- [ ] direct axiom and lint audits

## Promotion criterion

Promotion requires all theorem gates, an exact-object literature audit, a
physical realization whose assumptions are stated without rhetoric, and a
hostile general-journal review that judges the operational temporal-dimension
law—not formal verification or terminology—to be the scientific advance.
