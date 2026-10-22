# Eternal hypertranscendental time forces screen growth or causal openness

- **ID:** `finite-factor-eternal-time-screen-trilemma`
- **Stage:** 1-in-progress
- **Type:** CONDITIONAL THEOREM (paper) / PHYSICAL CONJECTURE
- **Source:** stronger replacement after finite-trace counterexample to HT capacity growth
- **Statement:** A future-complete nested family of genuinely finite-dimensional holographic
  factors with bounded dimension eventually stabilizes; if its stabilized closed dynamics is
  autonomous, every exact scalar correlation is DA. An HT clock therefore forces unbounded factor
  dimension or permanent causal openness.

## Candidate headlines

> **Time forces a finite-qubit universe to grow—or remain open.**

Black-hole version, not yet justified:

> **Time forces the universe to expand—or form a horizon.**

The second wording is authorized only if permanent causal openness is independently classified as
horizon flux.

## Exact finite-factor theorem F1 `[PAPER-PROVED]`

Let

```text
H_0 -> H_1 -> H_2 -> ...
```

be isometric inclusions of finite-dimensional Hilbert spaces. If

```text
sup_n dim H_n < infinity,
```

then there is `N` such that every inclusion `H_n -> H_(n+1)` is unitary for `n>=N`.

### Proof

The dimensions form a nondecreasing sequence of natural numbers bounded above. It eventually
stabilizes. An isometry between finite-dimensional Hilbert spaces of equal dimension is
surjective and hence unitary. ∎

## Exact dynamical theorem F2 `[PAPER-PROVED] [BRIDGE]`

If, after the stabilization in F1, the common factor carries a fixed autonomous unitary evolution

```text
U(t)=exp(-itH),
```

then every scalar correlation built from finitely many fixed operators and states is an
exponential polynomial and hence DA. This is theorem T1 on
`fixed-hologram-hypertranscendental-time-trilemma.md`.

Therefore:

```text
HT late-time correlation
  -> unbounded dim H_n
     or failure of eventual closed autonomous factor dynamics.             (T)
```

This implication does not use entropy, jet-counting, algorithmic complexity, or an
independence-to-bits assumption.

## Conditional holographic corollary `[PAPER-PROVED RELATIVE TO H1--H4]`

Assume a future-complete observer has nested causal diamonds `D_n` with:

1. **H1 — strong finite-factor holography:** each diamond is represented by a
   finite-dimensional factor `H_n`, and diamond inclusion gives an isometric inclusion
   `H_n -> H_(n+1)`;
2. **H2 — area dimension bound:**
   `log(dim H_n) <= A_n/(4 G hbar)`;
3. **H3 — causal closure:** if no information crosses an inaccessible future boundary, bounded
   area makes the stabilized factor an exact closed autonomous system;
4. **H4 — physical HT clock:** one fixed relational scalar correlation remains HT in the
   future-complete theory.

Then

```text
sup_n A_n = infinity
```

or information crosses an inaccessible future boundary.

### Proof

If area were bounded, H2 would bound the integer dimensions. F1 would stabilize the factors.
If no information crossed an inaccessible boundary, H3 would give fixed finite-dimensional
autonomous dynamics, contradicting H4 by F2. ∎

## Operational replacement: an age--area decoding law

The finite-factor premise can be removed if holography is stated as an operational accessible-
information bound rather than a Hilbert-dimension claim.

### Definition

Fix `N>=2`. An `(N,epsilon)` **absolute-age code** on one causal screen consists of:

1. screen states `rho_0,...,rho_(N-1)`, with the label `J` uniform on `{0,...,N-1}`;
2. one state-independent screen measurement whose output `Jhat` obeys
   `Pr[Jhat!=J]<=epsilon`.

The states may live in a diffuse or infinite-dimensional algebra. No finite-factor hypothesis is
made.

### Theorem O1: accessible information required by a clock `[PAPER-PROVED] [BRIDGE]`

For `0<=epsilon<1`,

```text
chi({rho_j}/N)
  >= log N - h_2(epsilon) - epsilon log(N-1)
  >= (1-epsilon) log N - h_2(epsilon),                       (O1)
```

where `chi` is the Holevo information and

```text
h_2(epsilon)
  = -epsilon log epsilon -(1-epsilon) log(1-epsilon).
```

#### Proof

Fano's inequality gives

```text
H(J|Jhat)<=h_2(epsilon)+epsilon log(N-1).
```

Since `J` is uniform,

```text
I(J:Jhat)
  =log N-H(J|Jhat)
  >=log N-h_2(epsilon)-epsilon log(N-1).
```

The Holevo bound gives `I(J:Jhat)<=chi`. Finally
`log(N-1)<=log N`. ∎

### Corollary O2: conditional age--area law

Suppose every age ensemble recoverable from a causal screen of area `A` satisfies the operational
holographic bound

```text
chi<=C(A).
```

Then every `(N,epsilon)` absolute-age code satisfies

```text
C(A)>=(1-epsilon) log N-h_2(epsilon).                         (O2)
```

If the relevant gravitational setting supplies

```text
C(A)<=A/(4 G hbar),
```

then

```text
A>=4 G hbar ((1-epsilon) log N-h_2(epsilon)).                 (O3)
```

For age resolution `Delta` over a proper-time range `[0,T]`, take
`N=floor(T/Delta)+1`. A single screen decoder that retains fixed error for arbitrarily large `T`
therefore requires unbounded area, unbounded external memory, or eventual clock ambiguity.

### What this repairs

1. O1 applies to Type I, II, and III realizations whenever the finite Holevo quantities exist.
   The fixed finite-trace zeta-clock countermodel no longer refutes the information-theoretic
   implication.
2. The premise is operational: one measurement must recover an age label. It does not identify
   algebraic independence, trace, or von Neumann entropy of one state with memory capacity.
3. Approximate clocks and finite error are native; no exact orthogonality is required.

### What this does not repair

1. Hypertranscendence does **not** imply the absolute-age decoding premise. An HT scalar response
   can approach itself arbitrarily closely, decay below every fixed noise floor, or be realized by
   states whose distinguishability vanishes with age.
2. A bounded scalar observable has compact output range, so it cannot by itself separate
   infinitely many ages by one fixed positive margin. An eternal fixed-resolution clock needs an
   expanding record, an unbounded observable, or a growing family of observables.
3. The quantum Bousso bound controls vacuum-subtracted entropy on a light-sheet. It does not,
   without an additional ensemble theorem, state the screen Holevo-capacity premise used in O3.
   Holographic code-subspace and alpha-bit bounds provide model-specific versions, not a universal
   causal-screen theorem.
4. O1--O3 are Fano, Holevo, and an entropy-capacity assumption composed. They are not new
   mathematics and do not explain the observed Friedmann expansion rate.

Thus the exact surviving target is now:

```text
physical source-selected HT clock
  + locality, finite energy, and stable readout
  -> (N,epsilon) absolute-age codes for unbounded N.          (O4)
```

Without O4, “time forces the universe to grow” remains unsupported. If O4 is adopted as the
definition of absolute time rather than derived from source physics, the resulting area law is a
conditional operational principle, not a discovery.

## Hostile boundary

F1 and F2 are elementary. Every physical conclusion is concentrated in H1, H3, and H4.

1. `[LITERATURE]` The covariant entropy bound does not imply H1. Type II gravitational algebras
   with finite generalized entropy directly evade it.
2. H3 is stronger than “no event horizon.” Relational evolution in a finite factor may look
   nonautonomous if the clock or geometry has been excluded from the factor.
3. H4 is not universal. Many exact free-field correlators, including hypergeometric de Sitter
   correlators, are DA.
4. “Information crosses an inaccessible boundary” includes environment, omitted gravitational
   degrees, singular boundary conditions, or a horizon. The theorem does not classify these as
   black holes.
5. Unbounded causal-diamond area occurs even in static Minkowski spacetime; it is not cosmic
   expansion.

## `[OPEN CORE]`

The first implication that would change scientific status is:

```text
finite generalized area of a causally complete quantum-gravitational diamond
  + exact relational closure
  -> strong finite-factor holography H1 and autonomous closure H3.
```

Current gravitational algebra results point in the opposite direction: finite generalized entropy
is compatible with infinite-dimensional Type II algebras. A successful successor may therefore
need to reject finite-qubit holography rather than derive expansion from it.

## Failure-driven stronger conjecture

### Algebra-type clock conjecture `[CONJECTURE]`

In quantum gravity, the differential-algebraic type of an exact autonomous relational clock
distinguishes finite Type I holography from diffuse Type II/III holography:

```text
finite Type I_n  -> every exact autonomous scalar clock is DA;
diffuse finite algebra -> HT autonomous clocks can exist at finite trace;
physical horizon algebra + source-selected KMS/modular constraints
  -> a specific HT/DA class determines the admissible algebra type.
```

The first two clauses are paper-proved. The third is the first nontrivial physical conjecture.
It asks whether HT can classify horizon algebra rather than falsely counting entropy.

## External parents

- R. Bousso, *A Covariant Entropy Conjecture*, arXiv:hep-th/9905177.
- R. Bousso, *The Holographic Principle for General Backgrounds*,
  arXiv:hep-th/9911002.
- N. Bao, S. M. Carroll, and A. Singh, *The Hilbert Space of Quantum Gravity Is Locally
  Finite-Dimensional*, arXiv:1704.00066.
- V. Chandrasekaran, G. Penington, and E. Witten, *Large N algebras and generalized entropy*,
  arXiv:2209.10454.
- T. Banks, W. Fischler, and S. Paban, *Recurrent Nightmares? Measurement Theory in de Sitter
  Space*, arXiv:hep-th/0210160.
- R. Bousso, H. Casini, Z. Fisher, and J. Maldacena, *Proof of a Quantum Bousso Bound*,
  arXiv:1404.5635.
- P. Hayden and G. Penington, *Learning the Alpha-bits of Black Holes*, arXiv:1807.06041.

## Nature gate

```text
Conditional theorem:                CLOSED ON PAPER
Finite-entropy premise sufficient:  NO
Operational age--area theorem:      YES, CONDITIONAL ON HOLEVO-CAPACITY BOUND
HT -> stable age decoding:          NO
Universal physical HT source:       OPEN
Horizon classification:             OPEN
Cosmic-expansion implication:       FALSE AS STATED
Nature-ready:                        NO
```

## Lean gate

Held. F1/F2 are known support lemmas and do not close the physical open core. Formalization before
the algebra-type or horizon-source theorem would violate the research cost gate.

## Log

- 2026-07-28 — derived after a fixed Type II/finite-trace zeta clock killed the entropy-to-growth
  route. Replaced finite entropy by a genuine nested finite-factor hypothesis and separated
  unbounded causal-screen area from cosmological expansion.
- 2026-07-28 — removed the finite-factor assumption at the operational layer: Fano plus Holevo
  gives the exact `(N,epsilon)` age-capacity lower bound and hence a conditional logarithmic
  age--area law. This does not rescue the headline because HT does not imply stable age decoding,
  and the quantum Bousso bound is not yet a universal screen-Holevo-capacity theorem.
