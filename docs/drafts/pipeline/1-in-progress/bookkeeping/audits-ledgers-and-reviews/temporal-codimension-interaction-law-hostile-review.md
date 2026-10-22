# Hostile review — temporal-codimension interaction law

- **Target:** `temporal-codimension-interaction-law.md`
- **Review standard:** renowned general scientific journal
- **Round:** pre-proof antagonist pass 1
- **Verdict:** `PROMISING CONCEPT; REJECT IN PRESENT FORM`

## Editorial assessment

The proposed reinterpretation is coherent and potentially important:
observable quantum recurrence is treated as return to a resolution cell in an
observer-relative compact temporal hull, and interaction changes the
dimension of that hull. This is materially stronger than the previous
five-part “anatomy.”

The submission is not publishable yet. Most of the universal hull machinery
is recognizable as Kronecker--Weyl equidistribution, compact-group harmonic
analysis, Wiener decomposition and finite-dimensional rank identities. The
only possible general-interest anchor is the claim that generic local
interaction creates exponentially many independent temporal directions,
together with a physical finite-time crossover law. Neither is presently
proved.

## Round-2 reassessment after new theorems

The first review forced real progress. It did not clear the paper.

| Objection | New evidence | Round-2 status |
|---|---|---|
| Classical core deletable | Universal Haar/Wiener law is now explicitly infrastructure. Principal candidate is bounded-degree spectral maximality. | Still editorially dangerous, but correctly framed. |
| Exact rank nonrobust | `finite-horizon-observer-temporal-profile-stability.md` proves a Lipschitz orbit bound and covering/return-set sandwiches. | Lower crossover and stability closed; upper crossover open. |
| Local maximality open | The qubit path theorem is upgraded by `nearest-neighbor-qudit-projective-spectral-maximality.md`: almost every qudit path has rank \(q^n-1\), and every interaction graph containing a spanning path inherits it. | Closed for every local dimension on a standard bounded-degree family; connected graphs without a spanning path remain open. |
| Density confused with first return | `local-chain-metric-recurrence-exponents.md` proves exact continuous and stroboscopic exponents on the local spectral manifold using analytic nondegeneracy and metric extremality. | Closed on paper; formal dependency and specialist audit open. |
| Manufactured question | A 2024 autonomous two-body research talk asks explicitly whether generic two-body eigenenergies are rationally independent and whether every two-body Hamiltonian has hidden resonances. | Strong relevance evidence; not priority clearance. |
| No new prediction | The joined theorem predicts that static nearest-neighbour \(q\)-level locality generically realizes \(q^n-1\) clocks, recurrence density exponent \((q^n-1)/2\), and continuous first-return exponent \((q^n-2)/2\) for quadratic deficit. | Genuine new consequence if proofs and priority survive. |

**Round-2 verdict:** `MAJOR THEORETICAL CORE FOUND; STILL REJECT`.

Remaining rejection reasons are narrower and more serious: proof
specialization, exact priority, formal closure of metric extremality,
finite-resolution constants/protocol, and physical interpretation. A Nature
claim cannot rest on an unaudited analytic-symmetrization step or on
asymptotic ranks that no finite protocol can distinguish.

### Nature editorial screen

Nature's current criteria require original research of outstanding scientific
importance and an interdisciplinary conclusion. The editor's review gate asks
whether results appear novel, arresting, immediate in implication and
far-reaching:
[editorial criteria](https://www.nature.com/nature/for-authors/editorial-criteria-and-processes).

| Editorial test | Current evidence | Verdict |
|---|---|---|
| Original | No exact collision found; a 2024 source poses the generic two-body resonance question as open. | `PROVISIONAL`, not cleared. |
| Arresting/unexpected | Degree-two one-dimensional locality with \(O(n)\) coupling parameters generically creates \(q^n-1\) independent projective clocks. | `PASS IF PROOF SURVIVES`. |
| Immediate implication | Answers whether two-body locality forces hidden resonances and computes exact recurrence density/first-hit exponents in the same physical family. | `PASS IF FORMALIZED`. |
| Far-reaching | Connects local many-body interaction, recurrence, observer visibility, integrability, open/infinite spectral phases and entropy-based recurrence certification. | `PROMISING`; gravity remains certification only. |
| Interdisciplinary readability | “Interaction creates exponentially many relative clocks” is intelligible; current cards are not a readable Article. | `FAIL NOW`. |
| Technical establishment | Qudit endpoint induction, metric extremality, constants and operational profile are not formally or independently audited. | `FAIL NOW`. |

## Fatal objections

### 1. The universal core can still be deleted as classical background

Equations identifying asymptotic density with Haar target volume and the
small-target exponent with torus dimension are expected consequences of a
linear flow and a nondegenerate minimum. Atomic/continuous decomposition is
classical spectral theory.

**Demand:** State those results as infrastructure. The paper's principal
theorem must be a new structural result about physical local Hamiltonians or
an equally strong nonclassical consequence. If clauses IV and the crossover
law disappear, the manuscript must not claim a new universal physical law.

### 2. Exact rational rank is not a robust observable

Rational independence changes under arbitrarily small perturbation and cannot
be certified from finite-precision spectral data. Calling the exact jump
\(O(n)\to q^n-1\) a physical phase transition risks promoting an
infinite-time arithmetic distinction into an experimentally meaningful
effect.

**Demand:** Introduce a finite-horizon, finite-resolution temporal information
profile. Prove that it converges to exact hull rank and quantify its stability
under perturbations and measurement error.

### 3. “Arbitrarily weak interaction” has no instantaneous consequence

For \(H_\delta=H_0+\delta V\), Duhamel's estimate gives
\[
 \|e^{-itH_\delta}-e^{-itH_0}\|
 \leq |t|\,|\delta|\,\|V\|.
\]
Thus no fixed-resolution experiment can distinguish the two dynamics before
a time at least of order \(1/(|\delta|\|V\|)\). If the first broken spectral
relation appears only at perturbative order \(r\), the relevant scale can be
\(|\delta|^{-r}\) or worse.

**Demand:** Prove a two-sided crossover theorem. Identify the first
relation-breaking spectral scale and show when the effective temporal
dimension changes. Replace “the smallest interaction postpones repetition”
by a statement that includes the waiting time needed to resolve that
interaction.

### 4. Generic local maximality is the whole paper and remains open

No theorem currently proves maximal projective spectral rank for every
connected bounded-degree interaction graph. A complete-graph perturbative
argument is insufficient for local many-body physics. Noncommuting
free-fermion and integrable models show that noncommutativity alone does not
create maximal rank.

**Demand:** Prove the full-measure theorem on a physically standard
bounded-degree family, preferably a one-dimensional nearest-neighbour chain,
before using “local interaction” in the headline. Then extend to every
connected graph or state the exact graph class.

### 5. Density is not first recurrence time

Inverse Haar volume is a recurrence frequency, not automatically the first
return time of one fixed deterministic orbit. Liouville frequencies and
shrinking-target anomalies separate the two.

**Demand:** Prove the stated metric-Diophantine exponents on the actual local
spectral parameter manifold, not on ambient unconstrained frequency space.
Report exceptional-set size and distinguish continuous from stroboscopic
time.

### 6. “Double eternity” hides nonuniform constants

An exponent \(q^n-1\) does not by itself give a physically meaningful
finite-size return estimate. Curvature determinants, minimal visible weights,
near resonances and the perturbation crossover can dominate at accessible
sizes.

**Demand:** Give finite-\(n\), finite-resolution inequalities with explicit
constants or a controlled thermodynamic scaling regime. Do not infer a
practical timescale from the asymptotic exponent alone.

### 7. Observer composition uses a formal meet

The intersection \(M_{\mathcal O}\cap M_{\mathcal P}\) is a valid vector-space
object, but it need not be realized by a physical reporter common to both
families. Equation `(8)` is rank valuation, not yet an operational
information law.

**Demand:** Either construct the common reporter under explicit closure
assumptions or call the intersection shared spectral content rather than an
observer meet.

### 8. “Dimension of time” risks semantic inflation

The invariant is dimension of a compact relative-phase hull. Similar tori
already occur in quasiperiodic dynamics. Rebranding frequency rank as time
dimension is not a discovery.

**Demand:** Demonstrate one new prediction that is naturally expressed and
proved through this dimension but was not available from standard
quasiperiodic language. The local interaction theorem plus measurable
crossover could meet this demand.

### 9. Infinite and open-system coverage is uneven

Stationary positive-definite records, finite contractions and arbitrary
nonstationary quantum channels are different classes. General nonunital CPTP
dynamics need not be Hilbert--Schmidt contractive. Infinite pure-point
records can have finite rational rank but singular small-target geometry when
their character second moment diverges.

**Demand:** State one exact domain. For infinite atomic hulls, use the exact
target-information profile rather than claiming a universal rank exponent
without regularity. For open dynamics, specify norm, invariant state and
peripheral decomposition assumptions.

### 10. Black-hole relevance is presently diagnostic, not predictive

The law shows that entropy alone does not fix recurrence. It does not prove
that a black-hole Hamiltonian is finite-dimensional, local in the required
sense, maximally nonresonant or visible to any proposed reporter.

**Demand:** Keep black holes as a consequence for model certification unless
one concrete gravitational model satisfies every premise. Do not sell a
change in black-hole physics from a spin-system theorem.

## Strong positive survivor

The following remains a credible master discovery target:

> A finite-resolution temporal information profile is a stable physical
> invariant of a system--reporter pair. Its infinite-time limit is the
> relative spectral rank; its target volume gives recurrence density; and a
> generic bounded-degree local interaction makes the profile flow from
> \(O(n)\) to \(q^n-1\) across a quantifiable perturbative crossover.

This would do more than rename a torus. It would prove that interactions
create independently measurable temporal directions and determine exactly
how their activation changes recurrence.

## Required theorem package before reconsideration

1. Generic maximal projective rank on a bounded-degree local Hamiltonian
   family.
2. Ambient-to-spectral-manifold metric-Diophantine transfer.
3. Finite-resolution temporal information definition with perturbation
   stability.
4. Two-sided interaction crossover law.
5. Explicit small-target constants or controlled bounds.
6. Operational rank/profile estimation protocol.
7. Exact primary-source collision audit.
8. Manuscript-wide removal of claims that equate frequency rank with
   spacetime dimension or accessible first-return time.

## Rejection triggers after revision

- local maximality is proved only for an all-to-all model;
- the perturbation result remains purely infinite-time;
- temporal dimension is definitionally equal to a known frequency rank with
  no new prediction;
- first-return claims use inverse density without Diophantine proof;
- black-hole language outruns the verified model class;
- the paper still reads as old results attached to a new noun.
