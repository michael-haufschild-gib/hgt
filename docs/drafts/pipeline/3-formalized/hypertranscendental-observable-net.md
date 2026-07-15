# Hypertranscendental observable net

- **ID:** hypertranscendental-observable-net
- **Stage:** 3-formalized
- **Type:** PROVED IN LEAN / GENERAL HYPERTRANSCENDENTAL GEOMETRY
- **Source:** nets of local observables, finite observer resolution, and locally covariant physics
- **Statement:** For a hypertranscendental clock, finite jet-observable fields recover the clock-resolution order exactly: `P_M ≤ P_N` if and only if `M ≤ N`.

## Goal

Formalize the statement that hypertranscendence supplies the observability structure of a clock,
not a temporal evolution.  The clock reading is the position of a finite observable field inside a
strictly nested net.

## Gates

- [x] 0 → 1 in-progress: the observable-net order reconstruction statement was isolated from the existing fresh-jet theorem
- [x] 1 → 2 fully-proven: exact jet visibility, strict monotonicity, inclusion reconstruction, and equality rigidity proved
- [x] 2 → 3 formalized: scratch certification, exact-module cache build, direct source check, and axiom audit pass
- [ ] 3 → 4 publication-ready: compare the jet net's intrinsic order with a concrete analytic or operator-algebraic observer net

## Physics source

- R. Brunetti, K. Fredenhagen, and R. Verch, *The generally covariant locality principle -- A new paradigm for local quantum physics*, arXiv:math-ph/0112041, formulates locally covariant QFT as a covariant assignment of observable algebras with injective morphisms, recovering Haag--Kastler observable nets.
- K. Jensen, S. Raju, and A. J. Speranza, *Holographic observers for time-band algebras*, arXiv:2412.21185, constructs observer-dependent coarse-grained algebras whose resolution is limited by the observer's characteristics.

The order-reconstruction theorem below is a transfer of the observable-net principle to the
hypertranscendental jet filtration.  It is not claimed as a theorem from those physics papers.

## Exact relation

For a hypertranscendental element `x`, let

```text
P_N = F(differentialJet 0 x, ..., differentialJet (N-1) x)
```

inside the ambient differential field.  Algebraic independence of the complete jet family gives
the exact visibility test

```text
differentialJet n x belongs to P_N  iff  n < N.           (1)
```

Consequently every refinement is strict,

```text
M < N  implies  P_M < P_N,                                (2)
```

and the inclusion order reconstructs the clock resolution:

```text
P_M ≤ P_N  iff  M ≤ N,                                    (3)
P_M = P_N  iff  M = N.                                    (4)
```

Equations `(1)`--`(4)` contain no flow, Hamiltonian, or state propagation.  The natural number
`N` is recoverable solely from the algebra of rational observables visible at that resolution.

## Formalization

`formal/GaloisForLFunctions/HTGeometry/HypertranscendentalObservableNet.lean` proves:

- `differentialJet_mem_jetObservableField_iff_lt`;
- `hypertranscendental_jetObservableField_strictMono`;
- `hypertranscendental_jetObservableField_le_iff`;
- `hypertranscendental_jetObservableField_eq_iff`.

## Direct corpus application

`formal/GaloisForLFunctions/HTGeometry/DifferentialClockResolutionRigidity.lean` combines the
observable net with the existing derivation-preserving embedding covariance.  For any field
embedding `e` preserving the derivation, it proves

```text
map e P_M ≤ P_N(e x)  iff  M ≤ N,
map e P_M = P_N(e x)  iff  M = N.
```

Thus a one-way, non-surjective reference-frame change preserves and reflects clock resolution; an
ambient inverse is unnecessary.

## Corpus value

The theorem upgrades monotonicity of the jet filtration to a faithful order embedding.  It makes
resolution inferable from field inclusion, proves that no finite clock reading is observationally
redundant, and supplies exact membership and equality rewrites for later HT arguments.  Its first
consumer discharges any separate resolution-matching premise for derivation-preserving field
embeddings.  This is a general hypertranscendental theorem; zeta and `RHTower` are not involved.

## Status

[PROVED IN LEAN] Both exact-module cache builds and touched-file checks pass.  The four net exports
and two embedding-rigidity consumers depend only on Lean's standard `propext`, `Classical.choice`,
and `Quot.sound` axioms.  No full project build, numerical experiment, or concurrent Lean process
was run.
