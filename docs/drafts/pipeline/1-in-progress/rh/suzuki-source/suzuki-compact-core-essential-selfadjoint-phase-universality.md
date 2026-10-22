# Suzuki compact-core essential self-adjointness and phase universality

- **ID:** `suzuki-compact-core-essential-selfadjoint-phase-universality`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / FAILED OPERATOR-LIMIT SUBCLASS
- **Source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 7.3--7.6; compact-test translation exhaustion
- **Statement:** Under RH, Suzuki's compactly supported differential operator is essentially
  self-adjoint, and every finite-aperture extension-angle schedule has the same generalized strong
  resolvent limit.  Extension phase cannot select a nontrivial global Livšic boundary block.
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED BOUNDED CAYLEY CORE]`
  `[SOURCE-SPECIFIC CORRECTION]`
  `[GENERIC CORE MECHANISM CLASSICAL] [NOVELTY UNVERIFIED] [NOT RH]`

## Goal

Audit surviving two-angle Suzuki route at operator level.  Suzuki Section 7 expects a selected
phase `theta(a)` to make finite self-adjoint extensions converge to global Hilbert--Pólya
translation generator.  Existing corpus strengthened that expectation to a boundary-phase-locking
theorem under a stable global deficiency-one hypothesis.  Actual compact-test exhaustion has a
different terminal object: its graph closure is self-adjoint, hence has deficiency zero.

This theorem is not a no-go for every scalar compact-open limit of the finite Livšic functions.
It is class-complete only for attempts that identify such a limit with a boundary block of the
graph-exhaustion operator.  Full Route G remains open until scalar two-angle producer is constructed
or refuted independently.

## Gates

- [x] 0 → 1 in-progress: exact source object, competing claims, proof, and falsifiers stated
- [ ] 1 → 2 fully-proven: external parent-theory audit and source-specialization recheck
- [ ] 2 → 3 formalized: invariant-core essential-self-adjoint theorem in Lean; bounded Cayley and
  Suzuki rank-drop connectors complete
- [ ] 3 → 4 publication-ready: only after specialist priority review

## Competing terminal conjectures

### `C-PHASE-LOCK` `[FALSIFIED FOR COMPACT-TEST GRAPH EXHAUSTION]`

The compact-test exhaustion converges to a global symmetric operator of deficiency `(1,1)`, and
one finite boundary phase must be locked to select Suzuki's Xi extension.

Falsifier: compact tests form an invariant core for global translation generator.  This is proved
below, so graph closure is self-adjoint and has no boundary block to select.

### `C-PHASE-UNIVERSAL` `[PROVED HERE]`

Under RH, every finite extension-angle schedule converges in generalized strong resolvent sense to
same global translation generator.  Finite deficiency line escapes strongly at infinity.

### `C-SCALAR-SURVIVOR` `[CONJECTURE; RH-BEARING OPEN CORE]`

Despite operator phase universality, canonically normalized moving boundary vectors may retain a
nontrivial scalar two-angle compact-open limit identifying a normalized Xi/de Branges carrier.

Falsifier: prove actual Suzuki normalization forces anchored Livšic quotient to zero locally
uniformly.  Strong graph convergence alone is insufficient because normalized defect vectors move
with aperture; this extra scalar theorem is not proved here.

## Abstract invariant-core theorem `[PROVED HERE]`

Let `H` be a complex Hilbert space, let `U(t)=exp(i t A)` be a strongly continuous unitary group
with self-adjoint generator `A`, and let `D` be a dense linear subspace such that

```text
D subset dom(A),
U(t)D subset D                 for every real t.          (1)
```

Then restriction `A|D` is essentially self-adjoint.

### Proof

It is enough to prove both ranges `ran(A|D+i)` and `ran(A|D-i)` dense.  Suppose `y` is orthogonal
to `ran(A|D+i)`.  Fix `x in D` and put

```text
f(t)=<U(t)x,y>.                                          (2)
```

Invariance gives `U(t)x in D`; generator theory gives

```text
f'(t)=i <A U(t)x,y>.                                    (3)
```

Range orthogonality says

```text
<A U(t)x,y>+i<U(t)x,y>=0,                               (4)
```

so `f'=f`.  Hence `f(t)=exp(t)f(0)`.  Unitarity bounds `|f(t)|` uniformly on the whole real line;
letting `t` tend to positive infinity gives `f(0)=0`.  Density of `D` gives `y=0`.  For
`ran(A|D-i)`, same calculation gives `f'=-f`, and boundedness as `t` tends to negative infinity
again gives `f(0)=0`.  Both ranges are dense, so deficiency indices vanish and closure of `A|D`
is `A`. `QED`

## Abstract phase-universality theorem `[PROVED HERE]`

Let closed subspaces `H_a` increase strongly to `H`, and let closed symmetric operators `S_a` on
`H_a` be nested restrictions of self-adjoint `A` such that

```text
closure(union_a graph(S_a))=graph(A).                   (5)
```

Write

```text
M_(a,+)=ran(S_a+i),
Q_(a,+)=orthogonal projection onto M_(a,+),
E_(a,+)=P_a-Q_(a,+).                                    (6)
```

Then `Q_(a,+)` tends strongly to identity and `E_(a,+)` tends strongly to zero.  Let `V_A` be
Cayley transform of `A`.  Every self-adjoint extension `B_a` of `S_a` has embedded Cayley transform

```text
I_a C_(B_a) P_a=V_A Q_(a,+)+Z_a E_(a,+),               (7)
```

where boundary block `Z_a` is unitary on deficiency space.  Therefore

```text
I_a C_(B_a)P_a -> V_A                                  (8)
```

strongly for every choice of `Z_a`, and Cayley resolvent identity gives

```text
I_a(B_a+i)^(-1)P_a -> (A+i)^(-1)                       (9)
```

strongly.

### Proof

For `(S_a+i)x`, graph density `(5)` approximates every `(A+i)x`.  Since `A+i` is onto, union of
`M_(a,+)` is dense in `H`; monotone projection convergence gives `Q_(a,+)->I`.  Also `P_a->I`, so
`E_(a,+)=P_a-Q_(a,+)->0`.  On `M_(a,+)`, finite partial Cayley map equals restriction of `V_A`.
Thus first term in `(7)` tends strongly to `V_A`; second tends strongly to zero because
`||Z_a||=1`.  This proves `(8)`, and affine Cayley resolvent formula proves `(9)`. `QED`

## Exact Suzuki specialization `[PROVED FROM RH]`

Assume RH.  Suzuki's `H(A_infinity)` is positive Weil completion of `C_c^infinity(R)`.  Translations
are a strongly continuous unitary group, and their self-adjoint generator `D` satisfies

```text
D[v]=[i v']                     for v in C_c^infinity(R). (10)
```

Compact tests are dense and translation-invariant.  Invariant-core theorem yields

```text
closure(D_infinity)=D=D_(pi/2).                         (11)
```

Thus inclusion `closure(D_infinity) subset D_(pi/2)` in Suzuki Section 7.3 is equality.  This does
not identify compact-test derivative with separate de Branges minimal multiplication operator
`U^(-1) M U`: Suzuki Section 7.4 explicitly says relation of `C_c^infinity(R)` to its domain is
unclear.  That proper minimal operator may have deficiency `(1,1)`, but it is not graph closure of
finite compact-test differential operators.

For finite apertures, union of domains `C_c^infinity(-a,a)` is `C_c^infinity(R)`, so `(11)` gives
graph exhaustion `(5)`.  Abstract phase-universality theorem proves `(9)` for every schedule
`theta(a)`.  Finite phase affects boundary spectral pollution but not generalized strong resolvent
limit.

## Lean formalization

Exact unconditional rank-drop statements are formalized in

```text
formal/GaloisForLFunctions/HTGeometry/NestedExhaustionPhaseUniversality.lean
formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCompactCorePhaseUniversality.lean
```

Capstones:

```text
tendsto_cayleyAssembly_of_deficiency_vanishes
tendsto_deficiency_starProjection_zero
tendsto_cayleyAssembly_of_dense_nested_ranges
tendsto_cayleyResolvent_of_dense_nested_ranges
tendsto_suzukiCompactCoreDeficiencyProjection_zero
tendsto_suzukiApertureCayley_allBoundarySchedules
tendsto_suzukiApertureResolvent_allBoundarySchedules
```

Both source files pass `lake env lean`.  Targeted module builds pass; no umbrella or full build was
run.  Axiom audit reports exactly `propext`, `Classical.choice`, and `Quot.sound` for every capstone.
Both modules are wired into `HTGeometry.lean` and `RHTower.lean`.

Mathlib has no Stone theorem or ready invariant-core essential-self-adjoint theorem.  Equation
`(11)` therefore remains paper-proved but not yet represented as an unbounded-operator Lean theorem;
the source-facing Lean theorem takes exact dense shifted-range conclusion as explicit hypothesis.

## Hostile audit

1. **RH visibility.** Suzuki specialization uses RH only to obtain positive global Weil Hilbert
   space and unitary translations.  Abstract theorems are unconditional.
2. **Wrong global operator.** De Branges minimal multiplication has deficiency `(1,1)` but is not
   shown to contain compact tests.  It cannot be substituted for graph closure in `(5)`.
3. **No scalar overreach.** `E_a->0` strongly does not force a normalized moving unit vector in
   `ran(E_a)` to converge.  Hence theorem does not prove `Theta_a->0`.
4. **No spectral overreach.** Strong resolvent convergence gives target spectral inclusion under
   standard extra hypotheses but does not exclude spectral pollution.
5. **No phase-lock residue.** With global deficiency zero there is no transported nonzero boundary
   unitary; any theorem assuming stable deficiency rank one is inapplicable to this exhaustion.
6. **No RH proof.** Result is conditional source classification under RH and an unconditional
   operator theorem.  It neither proves source positivity nor identifies Xi divisor.

## No-go closure

- **Exact killing theorem/mechanism:** invariant-core essential self-adjointness forces global
  compact-test graph closure to have deficiency zero, so no selected finite phase can converge to
  a nontrivial global deficiency-one boundary block.
- **Strongest positive survivor:** all finite extension-angle schedules have same generalized
  strong resolvent limit under RH; phase selection is unnecessary at operator level.
- **New insight:** any live two-angle Suzuki proof must be a scalar moving-boundary/source-limit
  theorem, not convergence to boundary block of compact-test graph limit.
- **Status:** paper proof dependency-closed; generic parent theory classical; exact Lean
  formalization and external source-specialization audit pending.  Full Route G remains open.

## Anti-theatre checkpoint

1. Exact unresolved arrow changed: operator phase selection is removed; scalar normalized defect
   limit remains.
2. Prior theorem preventing rediscovery: existing nested-exhaustion phase-locking law applies only
   when global deficiency rank stays one.  Present theorem proves actual Suzuki rank is zero.
3. Falsifier: one compact test not in generator domain, failure of translation invariance, or one
   non-dense range `ran(D_infinity +/- i)`.
4. Result proves source/operator classification, not RH and not a restated sign condition.

## Log

- 2026-08-01 — primary-source audit of Suzuki Sections 7.3--7.6 exposed mismatch between compact
  derivative closure and separate de Branges minimal multiplication operator.  Invariant-core and
  phase-universality proofs completed on paper.  Full Suzuki route deliberately left open.
