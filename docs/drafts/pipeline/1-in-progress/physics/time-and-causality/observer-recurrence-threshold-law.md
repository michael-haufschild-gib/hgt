# How much of time can repeat is observer-dependent

- **ID:** `observer-recurrence-threshold-law`
- **Stage:** 1-in-progress
- **Type:** FROZEN CONJECTURE / UNIVERSAL SPECTRAL DYNAMICS LAW
- **Frozen:** `2026-07-28T21:35:00Z`
- **Scientific status:** `[TRUTH SURVIVES FIRST PASS; SUBSUMED BY DISTRIBUTION LAW]`
- **Parent manuscript:** `../../4-publication-ready/projective-quantum-recurrence-rate-distortion`
- **Failed predecessor:** `observer-orbit-recurrence-law.md`

## Public discovery

> **How much of a quantum history can keep returning depends on what the observer can see.**

The proposed law does not say that an observer changes the external time parameter. It says that
the repeatable fraction of a temporal record is an exact invariant of the system--observer pair,
not of the system, entropy, or Hilbert-space dimension alone.

## Frozen technical conjecture

Let \(U_t\) be any strongly continuous unitary evolution on any complex Hilbert space, finite or
infinite dimensional. Let a nonzero physical state--reporter pair determine its normalized positive
spectral measure \(\mu_{\mathcal O}\), return amplitude
\[
 A_{\mathcal O}(t)=\int_{\mathbb R}e^{itE}\,d\mu_{\mathcal O}(E),
\]
and return fidelity \(F_{\mathcal O}(t)=|A_{\mathcal O}(t)|^2\). Write
\[
 a_{\mathcal O}
   =\mu_{\mathcal O,\mathrm{pp}}(\mathbb R)
\]
for total mass of the pure-point part. Then:

1. **Exact positive-density boundary.** For every \(0\leq\eta<a_{\mathcal O}^2\),
   \[
   \liminf_{T\to\infty}\frac{1}{2T}
   \left|\{t\in[-T,T]:F_{\mathcal O}(t)>\eta\}\right|>0.
   \]
   For every \(a_{\mathcal O}^2<\eta\leq1\), the same normalized measure tends to zero.
   Behaviour exactly at \(\eta=a_{\mathcal O}^2\) is arithmetic and is not claimed universal.
2. **Recurrence tomography.**
   \[
   a_{\mathcal O}^2
   =\sup\left\{\eta\in[0,1]:
      \liminf_{T\to\infty}\frac{|\{F_{\mathcal O}>\eta\}\cap[-T,T]|}{2T}>0
     \right\}.
   \]
   Thus time-domain return statistics recover total pure-point spectral weight without resolving
   individual energy levels.
3. **Bounded-gap phase.** Returns above every subunit fidelity occur with bounded gaps exactly
   when \(a_{\mathcal O}=1\), equivalently when the observer spectrum is pure point.
4. **Density-arrow phase.** Every positive-fidelity return set has zero time density exactly when
   \(a_{\mathcal O}=0\), equivalently when the observer spectrum is atomless.
5. **Permanent-escape phase.** Return fidelity eventually stays below every positive threshold
   exactly when the spectral measure is Rajchman. Absolute continuity is sufficient but not
   necessary.
6. **Observer dependence.** Two reporters coupled to one stationary quantum system can have
   different values of \(a_{\mathcal O}\), including the endpoints zero and one. Reporter
   refinement acts on the selected spectral measure; no system-only entropy scalar determines the
   recurrence phase.

The conjecture quantifies over arbitrary spectral type: finite pure point, countably infinite pure
point, mixed, singular continuous, and absolutely continuous. Sparse rigidity returns of a
continuous spectrum do not falsify it because a subsequence and a positive-density return
population are different claims.

No proof route is part of the conjecture.

## Quantitative finite sector

The existing manuscript must become the exact finite-resolution sector of this law:

```text
universal all-spectrum law
  -> pure-point mass one gives bounded-gap recurrence
  -> observer coherence graph gives visible phase dimension
  -> reverse-water target information gives finite target cost
  -> minimax Diophantine theorem gives a spectrum-uniform deadline
  -> contraction theorem adds a finite-system loss ceiling.
```

This hierarchy resolves the earlier collage problem. Spectral type answers **which recurrence
phase**; observer rank and target information answer **how difficult recurrence is inside the
pure-point phase**. Fixed-spectrum arithmetic remains separate from minimax target geometry.

## Physical question answered

The law answers:

> Which part of an arbitrarily large quantum system can recur often enough to constitute a
> repeatable clock or history?

Answer: exactly the pure-point spectral weight selected by the physical reporter. Finite entropy
and finite generalized entropy do not replace this invariant.

For the semiclassical de Sitter observer model with a continuous clock Hamiltonian, the law would
put the clock in the zero-density recurrence phase. That is an application to the published model,
not a claim that finite-\(G\) cosmology has been solved. Conversely, a countably infinite
pure-point clock remains bounded-gap recurrent at every finite fidelity resolution, so infinite
dimension alone does not create an arrow.

## Exact falsifiers

Retire or strengthen the conjecture if any of the following exists:

1. a probability spectral measure with atomic mass \(a\) and positive lower-density return above
   some fidelity \(>a^2\);
2. a probability spectral measure with \(a>0\) but zero lower-density return below some fidelity
   \(<a^2\);
3. a non-pure-point measure whose return sets are relatively dense at every subunit fidelity;
4. a pure-point probability measure lacking bounded-gap approximate returns;
5. an atomless measure with a positive-density positive-fidelity return set;
6. a prior theorem stating the same atomic-mass threshold, its inverse recurrence-tomography
   formula, and the bounded-gap/zero-density/Rajchman hierarchy in quantum-observer form.

Every failed clause must yield its strongest exact survivor.

## Nature gate

```text
Truth audit at arbitrary spectral type:        OPEN
Exact-object mathematical novelty:             OPEN
Quantum recurrence novelty:                    OPEN
Observer/GNS operational bridge:               OPEN
Finite water and graph laws unified:           OPEN
Experimental recurrence-tomography protocol:   OPEN
de Sitter interpretation delimited:            OPEN
Dependency-closed paper proof:                  OPEN
Unconditional formal trace:                    OPEN
Hostile Nature review:                          OPEN
```

No manuscript claim or formal infrastructure is authorized until falsity, rediscovery, and
dependency-closure audits pass.

## Successor

The threshold statement survives its first truth audit but is not strong
enough to carry a general-interest paper by itself. It is now clause 2 of
`observer-time-recurrence-distribution-law.md`, whose master claim determines
the complete long-time record distribution, observer temporal dimension and
finite return exponent from one canonical visible-gap measure.
