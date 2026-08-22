# Universal typed-event network fixed-carrier no-go

- **ID:** `universal-typed-event-network-fixed-carrier-no-go`
- **Stage:** 2-fully-proven
- **Type:** UNIVERSAL LINEAR/QUANTUM NETWORK REPRESENTATION THEOREM / PHYSICAL NO-GO
- **Status:** `[PAPER-PROVED] [LEAN-PROVED] [REDISCOVERED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `event-order-diamond-carrier-boundary.md`
- **Physical target:** `../../1-in-progress/actuality-creates-future-law.md`

## Exact theorem

Let \(R\) be a ring, let \(I\) be a set of event types, and let \(M_i\) be a left
\(R\)-module for every \(i\in I\). Put

\[
W=\bigoplus_{i\in I}M_i,
\]

with canonical inclusion \(\iota_i:M_i\to W\) and component projection
\(\pi_i:W\to M_i\). For every typed linear event

\[
f:M_i\longrightarrow M_j
\]

define its fixed-carrier corner lift by

\[
\widehat f=\iota_j f\pi_i\in\operatorname{End}_R(W).                 \tag{1}
\]

Then:

1. **exact recovery**

   \[
   \pi_j\widehat f\iota_i=f;                                       \tag{2}
   \]

2. **faithfulness**

   \[
   \widehat f=\widehat g\Longrightarrow f=g;                        \tag{3}
   \]

3. **exact typed composition**, for \(g:M_j\to M_k\),

   \[
   \widehat g\,\widehat f=\widehat{gf};                             \tag{4}
   \]

4. **typed identities become corners**

   \[
   \widehat{\operatorname{id}_{M_i}}=\iota_i\pi_i=:P_i;             \tag{5}
   \]

5. every finite composable history, every equality between histories, and every linear
   combination of parallel histories is recovered exactly by source inclusion and target
   projection from endomorphisms of the one fixed carrier \(W\).

If \(I\) is countable and every \(M_i\) is a separable complex Hilbert space, the Hilbert direct
sum \(W=\bigoplus_i^{\ell^2}M_i\) is one separable Hilbert space and the same construction applies
to bounded maps. If only finitely many finite-dimensional carriers occur, \(W\) is
finite-dimensional with

\[
\dim W=\sum_i\dim M_i.                                              \tag{6}
\]

## Proof

The direct-sum maps satisfy

\[
\pi_i\iota_i=\operatorname{id}_{M_i}.                               \tag{7}
\]

Substituting `(1)` and `(7)` gives

\[
\pi_j\widehat f\iota_i
=\pi_j\iota_j f\pi_i\iota_i
=f,
\]

which proves `(2)`. Applying `(2)` to equal lifts proves `(3)`.

For composable \(f:M_i\to M_j\) and \(g:M_j\to M_k\),

\[
\widehat g\,\widehat f
=\iota_k g\pi_j\iota_j f\pi_i
=\iota_k(gf)\pi_i
=\widehat{gf},
\]

proving `(4)`. Equation `(5)` is the definition `(1)` applied to the identity.

Induction on history length now gives

\[
\widehat{f_n}\cdots\widehat{f_1}
=\widehat{f_n\cdots f_1}.                                          \tag{8}
\]

Linearity of \(f\mapsto\widehat f\), followed by `(2)`, recovers every linear combination of
parallel histories. This includes every order defect. The countable Hilbert statement uses the
standard Hilbert direct sum; canonical inclusions are isometries, projections are their adjoints,
and

\[
\|\widehat f\|=\|f\|.
\]

Countable sums of separable Hilbert spaces are separable. Equation `(6)` is finite-dimensional
direct-sum additivity. ∎

## Completely-positive operational corollary

Let \(H_i,H_j\) be Hilbert carriers and let

\[
\Phi:\mathcal T(H_i)\longrightarrow\mathcal T(H_j)
\]

be a normal completely positive trace-nonincreasing quantum operation on trace-class operators.
For the Hilbert direct-sum isometries \(J_i:H_i\to W\), define

\[
\widehat\Phi(\rho)
=J_j\Phi(J_i^*\rho J_i)J_j^*.                                      \tag{9}
\]

Compression, \(\Phi\), and corner inclusion are completely positive, so `(9)` is completely
positive. For positive \(\rho\),

\[
\operatorname{Tr}\widehat\Phi(\rho)
\leq\operatorname{Tr}(J_i^*\rho J_i)
\leq\operatorname{Tr}\rho,
\]

so it is trace-nonincreasing. If \(\rho\) is supported on the \(i\)-corner and \(\Phi\) is
trace-preserving, normalization is preserved exactly. For composable quantum operations,
the middle identity \(J_j^*J_j=1\) proves the exact analogue of `(4)`.

Thus positivity, valid-history normalization, and complete-positive composition do not by
themselves obstruct fixed-carrier realization. Quantum instruments already admit
trace-nonincreasing branches; in finite dimension a complementary failure branch can record an
invalid type input without changing any valid history.

## Hostile physical verdict

`[FALSIFIED]` The following proposed escape from the one-diamond dilation no-go is false:

> An unbounded or complete typed history, by virtue of having different Hilbert carriers,
> eventually obstructs every one-carrier realization.

It does not. The direct sum is a fixed carrier for the entire set-indexed network. Countably many
separable event carriers still produce one separable Hilbert space. Complete positivity and
valid-history normalization survive in corners.

Consequently:

> **Changing Hilbert-space type is not an invariant meaning of physical carrier creation.**

One must first specify which additional physical structure a permissible fixed-carrier
realization must preserve. Without that admissibility class, “not reducible to one larger fixed
carrier” has no mathematical content.

This also proves a finite-observation boundary. Every finite family of finite-dimensional typed
quantum events has a finite-dimensional fixed-carrier realization. No finite observation of that
bare network can certify fundamental carrier creation against alternatives with unconstrained
hidden carrier dimension.

## Strongest positive survivor

`[PAPER-PROVED]` Every genuine carrier-creation witness must obstruct a
**structure-preserving** corner realization. At least one additional structure must be specified
and shown not to survive `(1)` or `(9)`:

1. a source-derived finite resource ceiling or canonical minimality law;
2. a global unit or intervention-completeness condition stronger than normalization on valid
   typed histories;
3. spacelike tensor composition, algebraic locality, or a factorization net;
4. continuous, smooth, or covariant variation over physical history space;
5. a Morita-stable topological or anomaly class; or
6. gravitational constraints that forbid the orthogonal type flag introduced by the direct sum.

The first exact physical open core is therefore

`MONOIDAL-LOCALITY OBSTRUCTION TO FIXED-CARRIER REALIZATION`:

> derive a relational event network with both causal/sequential composition and physical
> spacelike composition; then prove that no one-carrier corner realization preserves the latter
> together with gauge invariance and gravitational dressing.

This is stronger and more precise than seeking a larger order defect. It identifies the missing
physical datum: not another map, but the rule saying which events are independently composable.

## Literature and rediscovery audit

- `[LITERATURE]` Ghez, Lima, and Roberts prove that every \(C^*\)-category has a concrete
  realization and that \(W^*\)-categories can be regarded as pieces of a larger von Neumann
  algebra. They explicitly identify tensor structure as additional data beyond the bare
  categorical realization: P. Ghez, R. Lima, and J. E. Roberts, *W*-categories*,
  Pacific J. Math. **120** (1985), 79--109,
  <https://msp.org/pjm/1985/120-1/pjm-v120-n1-p06-s.pdf>.
- `[LITERATURE]` Hawkins, Markopoulou, and Sahlmann formulate quantum causal histories using
  matrix algebras and completely positive maps between causally related events:
  <https://arxiv.org/abs/hep-th/0302111>.
- `[LITERATURE]` Chiribella, Toigo, and Umanità prove dilation theorems for normal quantum
  supermaps and superinstruments on separable von Neumann-algebraic systems:
  <https://arxiv.org/abs/1012.3197>.
- `[LITERATURE]` Doplicher and Roberts reconstruct a compact gauge group from the symmetric tensor
  \(C^*\)-category of sectors. This shows exactly why monoidal/local structure, not a bare
  fixed-carrier embedding, is the relevant internal-force datum:
  <https://annals.math.princeton.edu/1989/130-1/p03>.
- `[LITERATURE]` Brunetti and Ruzzi attach symmetric tensor \(C^*\)-categories of sectors to
  globally hyperbolic spacetimes and transport sector data covariantly:
  <https://arxiv.org/abs/gr-qc/0511118>.
- `[LITERATURE]` Donnelly and Giddings prove that gravitational dressing obstructs the ordinary
  organization of physical observables into local commuting subalgebras:
  <https://arxiv.org/abs/1607.01025>.

The linear theorem is an elementary corner form of established concrete-category/linking-algebra
theory. It is not new scientific knowledge. Its value is the exact closure of a live physical
escape route and the isolation of the monoidal/locality residue.

## Lean status

The arbitrary-network algebraic theorem is `[LEAN-PROVED]` in
`formal/GaloisForLFunctions/HTGeometry/EventNetworkFixedCarrier.lean`. It proves exact recovery,
faithfulness, typed composition, identities as corners, addition, subtraction, and scalar
weighting over the stated coefficient classes.

Focused final build:

```text
lake build GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier
✔ [1211/1211] Built GaloisForLFunctions.HTGeometry.EventNetworkFixedCarrier
Build completed successfully (1211 jobs).
```

The axiom audit for every declaration reports only:

```text
propext
Classical.choice
Quot.sound
```

Repository formal lint passed. The completely-positive operational corollary remains
paper-proved rather than Lean-formalized; it is not needed for the algebraic no-go.

### Trace-class corner checkpoint (2026-08-15)

`HTGeometry/TraceClassQuantumCorner.lean` now proves reusable unconditional infrastructure on
the project’s actual approximation-number Schatten-one subtype:

- `memSchattenClass_one_sandwich` and `traceClassSandwich_comp` close trace-class preservation
  and exact composition for every bounded Hilbert sandwich;
- `TraceClassQuantumOperation` closes composition, complete positivity at every finite matrix
  level, trace nonincrease, and order-normality for operations carrying those proved properties;
- `cornerLift_include`, `cornerLift_comp`, and
  `trace_cornerLift_include_eq_of_tracePreserving` close exact valid-corner recovery,
  compositionality, and normalization for certified corners.

The focused leaf build and axiom audit pass with only `propext`, `Classical.choice`, and
`Quot.sound`.  This does **not** yet construct the inclusion and compression operations for the
literal Hilbert direct sum: their complete positivity, trace inequality, and normality are still
fields of `TraceClassQuantumCorner`.  Therefore the completely-positive corollary remains open
and this card stays in Stage 2.

## Gates

- [x] exact all-history claim stated
- [x] dependency-closed algebraic and Hilbert proof
- [x] complete-positive operational corollary
- [x] hostile falsity and rediscovery audit
- [x] strongest positive survivor and new physical open core
- [x] arbitrary-network algebraic theorem formalized in Lean
- [x] genuine trace-class sandwich closure and certified-corner composition formalized in Lean
- [ ] literal Hilbert-direct-sum corner proved completely positive, normal, and trace-nonincreasing
- [ ] monoidal-locality obstruction derived from physics

## Log

- 2026-07-29 — generalized the finite-diamond block dilation to every set-indexed typed linear
  event network. Killed bare positivity, normalization, and unbounded-history escapes; isolated
  monoidal/locality preservation as the first physical structure not supplied by a direct sum.
- 2026-07-29 — formalized the arbitrary-network algebraic core in
  `EventNetworkFixedCarrier.lean`; focused build, axiom audit, and repository lint passed.
- 2026-08-15 — added and audited genuine trace-class sandwich and certified-corner infrastructure;
  retained Stage 2 because the literal direct-sum CP corner construction remains unproved.
