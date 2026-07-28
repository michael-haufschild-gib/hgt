# Positive-energy observation boundary

- **ID:** positive-energy-observation-boundary
- **Stage:** 5-failed
- **Type:** RETIRED AS PAPER ANCHOR; boundary lemmas retained
- **Status:** killed by direct prior art before formalization
- **Question:** What observation, rather than what waiting time, separates a
  determined scalar future from an ambiguous one?

## Correction to the motivating question

“Can any finite observational history determine a system’s future?” is not a
well-posed universal question. “Finite” can mean:

1. finitely many samples;
2. finitely many derivatives at one instant;
3. an exact continuous record on a finite interval;
4. a finite-precision record;
5. observation through an incomplete channel.

These are mathematically inequivalent. Any paper that treats them as one
limitation overstates its result.

## Candidate boundary law

For the scalar spectral response
\[
 A_\mu(t)=\int_{\mathbb R}e^{itE}\,d\mu(E)
\]
of a finite positive measure:

### E1 — Exact interval determinacy

If two finite positive measures have a common lower spectral bound and their
responses agree at every time in one nonempty open interval, then the measures
are equal. Consequently their scalar responses agree at every real time.

This determines the spectral measure seen by the chosen preparation and
probe. It does not determine an unobserved orthogonal sector or the complete
Hamiltonian.

### E2 — Infinite instantaneous data can fail

There are two distinct probability measures supported in the positive
half-line whose moments of every nonnegative integer order agree. Their
characteristic functions therefore have the same derivatives of every order
at zero, wherever the derivative–moment identity is invoked, but are not the
same function.

The intended explicit witness is the lognormal Stieltjes pair obtained from a
Gaussian density multiplied by
\[
 1\pm\varepsilon\sin(2\pi y),\qquad 0<\varepsilon\le1,
\]
and pushed forward under \(y\mapsto e^y\). For every integer \(n\ge0\),
\[
 \int e^{ny}\phi(y)\sin(2\pi y)\,dy
 =
 \operatorname{Im}\exp\!\left((n+2\pi i)^2/2\right)
 =0,
\]
while the two measures differ because their signed density difference is
\(2\varepsilon\phi(y)\sin(2\pi y)\), which is nonzero on a set of positive
measure.

### E3 — Noisy interval instability

For every target time \(T>0\), every strict earlier horizon \(0\le H<T\), and
every error tolerance \(\delta>0\), finite nonnegative-energy spectral
measures exist whose complete scalar responses are uniformly
\(\delta\)-close on \([-H,H]\), yet whose target-time return probabilities are
zero and one. Hence no prediction rule from the noisy record can have worst
case terminal error below \(1/2\).

### E4 — Resource-restored stability

For bounded generators with norm at most \(\Lambda\), agreement of the first
\(N\) scalar response coefficients gives an exact exponential-tail bound.
At action \(u\le N/e\), the response discrepancy is
\(O(N^{-1/2})\), dimension independently. Conversely, local Hermitian path
Hamiltonians attain complete terminal ambiguity with
\(\Lambda T=\Theta(R)\) behind a common radius-\(R\) record. Thus energy–time
action, not Hilbert-space dimension, is the sharp resource controlling stable
continuation in this model class.

## Dependency-closed paper proof of E1

Translate the common lower bound to zero. Put
\[
 F_\mu(z)=\int_0^\infty e^{izE}\,d\mu(E),\qquad \operatorname{Im}z\ge0.
\]
For \(\operatorname{Im}z>0\), the integrand and every local first difference
quotient are dominated by an integrable bounded function, because
\(E e^{-cE}\) is bounded for every \(c>0\). Thus \(F_\mu\) is holomorphic in
the upper half-plane. Dominated convergence makes it continuous on the closed
upper half-plane.

Let \(F=F_\mu-F_\nu\). On a vertical strip whose real boundary segment lies
inside the observation interval, glue \(F\) above the real axis to zero below
it. The assumed boundary equality makes the glued function continuous.
It is holomorphic off the real axis. Morera/Painlevé reflection makes it
holomorphic across the axis. It vanishes on the lower open half-strip, so the
identity theorem makes it vanish throughout the connected strip. Analytic
continuation in the upper half-plane gives \(F=0\) there and boundary
continuity gives \(A_\mu=A_\nu\) on all real times. Uniqueness of
characteristic functions gives \(\mu=\nu\).

## Exact meaning of “infinite history”

- An exact interval already contains enough information to determine the
  complete future of this one scalar response under a common lower energy
  bound.
- The entire exact scalar history determines no more than its spectral
  measure. Direct-summing any invisible Hilbert space and arbitrary
  self-adjoint dynamics leaves that history unchanged.
- Infinitely many derivatives at one time are strictly weaker than an exact
  interval for unbounded positive spectra.
- Any nonzero error radius reopens maximal future ambiguity unless an energy
  or tail budget is supplied.

## Prior-art collisions

- Hegerfeldt’s positive-energy analyticity theorem already uses the
  semibounded Hamiltonian boundary principle. E1 is a boundary lemma, not a
  novelty claim.
- Hsu (1954) constructed distinct characteristic functions agreeing near
  zero without a one-sided spectral restriction. This kills exact-interval
  novelty for two-sided spectra.
- Classical Stieltjes classes and modern quantum characteristic-function
  papers already establish complete moment indeterminacy. E2 is a necessary
  boundary witness, not a novelty claim.
- Khalfin/Paley–Wiener results already connect a lower energy bound to
  nonexponential long-time survival.

The candidate novel object is therefore only the sharp combined
exact/noisy/resource classification and its matched linear local action law.
That combined claim still requires an exact-object literature audit. It must
not be described as Nature-level until that audit and a hostile significance
review succeed.

## Hostile review

1. **Scalar response is not “the system’s future.”** Required correction:
   state every determinacy theorem for a named response or for an
   informationally complete family; prove the invisible-sector obstruction.
2. **Exact continuum data have infinite information and are physically
   inaccessible.** Required correction: make E3 and E4 central, not caveats.
3. **E1 and E2 are classical.** Required correction: cite them as boundary
   lemmas and locate novelty only in a theorem not already implied by the
   cited literature.
4. **A trichotomy can be a collage.** Required correction: derive all regimes
   from one observation topology and one minimax prediction functional.
5. **The local upper witness is engineered.** Required correction: do not
   claim typicality, cosmology, gravity, QFT, or a device prediction without a
   transfer theorem.
6. **Popular wording can overstate ontology.** “The future is encoded in
   every slice of the past” is defensible only as “the complete future of a
   positive-energy scalar response is mathematically fixed by every exact
   nonzero time interval.”

## Formalization gates

- [ ] E1 lower-bound translation, upper-half-plane transform continuity,
  holomorphy, reflection, identity, and characteristic-function uniqueness
- [ ] E2 explicit positive-support probability pair, distinctness, all
  moments, and complete derivative equality
- [x] E3 finite nonnegative-energy approximate-window maximal separation
- [x] E4 bounded-generator exact-tail lower law
- [x] E4 finite local Hermitian linear-cost upper law
- [x] E4 unbounded infinite phase-ladder lift
- [ ] invisible direct-sum sector theorem
- [ ] exact-object novelty audit of combined minimax topology

## Promotion criterion

Do not promote this card unless:

1. every displayed mathematical claim is dependency-closed on paper;
2. every manuscript claim maps to an unconditional theorem;
3. the combined law, not merely its classical boundary lemmas, survives
   exact-object novelty search;
4. a hostile general-journal review finds a concrete broad scientific
   consequence rather than philosophical wording alone.

## No-go closure

- **Killing mechanism:** every proposed headline component has direct prior
  art: positive-energy boundary analyticity (Hegerfeldt/Khalfin),
  infinite-moment indeterminacy (classical Stieltjes classes), and unstable
  quantum extrapolation under finite precision (including Manos,
  Weilenmann and Navascués, 2025). Their conjunction is a useful taxonomy,
  not a discovery whose novelty is beyond reasonable dispute.
- **Strongest positive survivor:** the exact-interval lemma remains useful as
  a scope boundary for later work, and the existing matched linear
  energy–time continuation law remains a separate theorem.
- **New insight extracted:** observation duration is not the correct
  universal variable. Finitely many samples, an infinite jet, an exact
  interval, finite precision, and an incomplete observation channel define
  different information topologies and must never be conflated.
- **Disposition:** no paper promotion. Search instead for a new invariant
  that makes observer dependence itself quantitative and predicts a new
  recurrence or decoherence transition.
