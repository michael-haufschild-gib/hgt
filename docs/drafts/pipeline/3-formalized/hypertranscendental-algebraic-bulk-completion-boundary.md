# The algebraic bulk of hypertranscendence is universal; source identity lives at completion

- **ID:** `hypertranscendental-algebraic-bulk-completion-boundary`
- **Stage:** 3-formalized
- **Type:** GENERAL HT FINITE-JET HOMOGENEITY / COMPLETION-BOUNDARY THEOREM
- **Scientific status:** `[CORE THEOREM LEAN-FORMALIZED] [UNPOLARIZED COMPLETION NO-GO] [POLARIZED COMPLETION-MODULI CONJECTURE OPEN] [NOT AN RH RESULT]`
- **Parents:**
  `hypertranscendental-two-scale-factorial-wall.md`,
  `hypertranscendental-controlled-cohomology-and-bornological-shape.md`,
  `../2-fully-proven/new_scientific_knowledge/hypertranscendental-capacity-field-realization-covariance.md`
- **Successor:**
  `../2-fully-proven/needs-audit/hypertranscendental-minimal-polarized-critical-completion-architecture.md`
- **Statement:** All one-generator hypertranscendental sources have the same marked finite
  differential-algebraic jet fields.  Hence differential algebra supplies a universal free bulk
  but cannot distinguish the sources.  Any source-specific law must be carried by extra
  polarized completion data on that bulk: analytic domains, growth bornology, continuation,
  monodromy, signed Hermitian orientation, and boundary duality.

## 1. Universal finite-jet homogeneity

Let `F` be a differential field and let `x` and `y` be hypertranscendental over `F`, possibly in
different differential field extensions.  For `L>=0`, write

```text
A_L(x)=F(x,Dx,...,D^(L-1)x),
A_L(y)=F(y,Dy,...,D^(L-1)y).                                    (1)
```

Hypertranscendence makes each displayed jet packet algebraically independent over `F`.  Therefore
evaluation gives marked field equivalences

```text
F(X_0,...,X_(L-1))  ~=  A_L(x),
F(X_0,...,X_(L-1))  ~=  A_L(y).                                 (2)
```

### Theorem A: marked finite-jet homogeneity

For every `L` there is an `F`-algebra equivalence

```text
Phi_L(x,y):A_L(x) ~= A_L(y)                                    (3)
```

such that

```text
Phi_L(x,y)(D^i x)=D^i y                 for every i<L.          (4)
```

The equivalence is canonical relative to the marked generator and the common derivation order.
The maps `(3)` are compatible with the natural finite-jet inclusions because both composites send
every common coordinate `D^i x` to `D^i y`.

**Proof.**  Compose the inverse of the first equivalence in `(2)` with the second.  Equation `(4)`
is the coordinate formula for the two evaluation maps.  Compatibility follows because a field
homomorphism out of `A_L(x)` is determined by the `L` marked generators. `QED`

The definition `hypertranscendentalFiniteJetEquiv` and theorem
`hypertranscendentalFiniteJetEquiv_generator` are Lean-formalized.

## 2. The finite-algebraic classification no-go

Call an invariant **finite differential-algebraic** if, at some order `L`, it factors through the
isomorphism class of the marked field `(A_L(x);x,Dx,...,D^(L-1)x)`.

### Theorem B: no finite differential-algebraic invariant distinguishes HT sources

Every finite differential-algebraic invariant is constant on the class of one-generator
hypertranscendental sources over `F`.

**Proof.**  Theorem A identifies every pair of its inputs in the marked category through which the
invariant factors. `QED`

This is stronger than the statement that no finite differential equation defines a particular
HT function.  It says that the entire marked rational geometry of every finite jet stage is the
same for all HT sources.  Adding more finite algebraic coordinates never begins to identify
Gamma, zeta, or any other source.

The strong positive replacement is exact.  Let

```text
U_F = F(X_0,X_1,X_2,...),              D X_i = X_(i+1).          (5)
```

Every one-generator HT source is an analytic realization of the same free differential-rational
bulk `(5)`.  Hypertranscendental functions are therefore not different algebraic objects with
unknown equations.  They are different completions or embeddings of one universal free object.

## 3. The bulk is free and the tail flag is separated

The existing jet-tail theorem gives a second exact structural constraint.  For

```text
T_n(x)=F(D^n x,D^(n+1)x,...),                                  (6)
```

one has

```text
T_(n+1)(x) < T_n(x)                       for every n,           (7)
intersection_n T_n(x) <= algebraicClosure(F).                   (8)
```

If `F` is relatively algebraically closed in the ambient field, the intersection in `(8)` is
exactly `F`.  Thus the free bulk carries a strictly descending, separated infinite flag.  No
transcendental core is present at every tail depth; each finite stage contributes genuinely new
algebraic capacity, while the common tail contains no hidden transcendental generator.

Equations `(7)` and `(8)` are already Lean-formalized as
`hypertranscendentalOver_jetTailField_strictAnti` and
`hypertranscendentalOver_iInf_jetTailField_le_algebraicClosure`.

## 4. The polarized completion boundary

Theorems A and B locate where a new theory can and cannot live:

```text
universal algebraic bulk:     the free differential field U_F,
source-specific structure:    polarized completions and boundary gluing of U_F.        (9)
```

A finite cylinder in the jet variables sees the generic point of affine space.  A nontrivial
source constraint cannot be a proper finite-cylinder algebraic closed condition, since Theorem A
would transport it to every HT source.  It must instead be visible only after adding non-finitary
structure such as:

1. a family of analytic domains or continuation charts;
2. a Gevrey-weighted bornology on the source-depth by observable-order cone;
3. a nonabelian connection comparing those charts;
4. a signed Hermitian polarization retaining all finite inertia strata;
5. positivity as the distinguished zero-negative-index chamber and a self-dual boundary
   involution;
6. controlled, rather than algebraic, admissibility of gauges.

This gives a precise replacement for the earlier time metaphor:

> **Hypertranscendence is a universal free algebraic bulk whose entire source identity is
> displaced to the thin boundary of an analytic completion.**

“Thin” here does not mean measure zero.  It means invisible to every finite algebraic cylinder
while detectable by the completed all-order diagram.  The Möbius factorial wall supplies the
first exact example: every fixed jet comparison tends to the identity, but the unweighted
all-order comparison remains unbounded.

The Gevrey exponent is not free.  For tangent Möbius charts, an exponent below one rejects every
nonidentity comparison, an exponent above one makes every finite parameter square-summable, and
exactly exponent one retains a proper finite capacity wall.  Thus the completion-moduli problem
already has a uniquely critical Gevrey order; only its exponential radius scale remains chart
dependent.

### Theorem C: unpolarized completion is not conservative

The existing universal prime-log orientation family contains representatives `g_k`, one for every
finite `k`, with the same embedded differential field, the same finite localized differential
matroids, and the same compact-open completed ring, but with Pick/Krein negative index `k`.
Consequently neither the algebraic bulk nor its ordinary analytic completion determines positivity
or orientation.

This no-go is already present in the project corpus and is not new science here.  Its strong
positive consequence is mandatory: the completion shape must be **polarized**.  The signature of
finite Hermitian evaluation forms, or an equivalent Krein orientation sheaf, is an independent
component alongside the growth bornology.  Magnitudes do not reconstruct signs.

## 5. The higher conjecture

Define provisionally the **polarized HT completion shape** of a source `x` to be the free bulk `(5)`
equipped with its source-natural analytic charts, the critical Gevrey-weighted capacity bornology
on their full scale cone, their nonabelian comparison connection, a signed Hermitian/Krein
polarization, and any intrinsic self-duality.

**[CONJECTURE: POLARIZED COMPLETION-MODULI PRINCIPLE.]**  The polarized HT completion shape is a
faithful invariant of source-natural one-generator hypertranscendental analytic germs up to
differential analytic equivalence.  Equivalently, two such sources with equivalent polarized
completion shapes differ by an admissible analytic differential coordinate change.

**[CONJECTURE: BOUNDARY LOCALIZATION.]**  Every persistent reconstruction obstruction of an HT
source factors through the failure of the canonical finite-jet pro-equivalence `(3)` to extend to
an equivalence of polarized HT completion shapes.  Continuation, positivity, monodromy, spectral
incompleteness, and noncanonical boundary conditions are candidate boundary functors of this one
extension defect.

These conjectures are falsifiable.  A pair of analytically inequivalent HT germs with equivalent
polarized completion shapes refutes Polarized Completion-Moduli.  A persistent source-natural obstruction unchanged
by all completion-shape data refutes Boundary Localization and exhibits a missing independent
component.

## 6. Novelty and anti-theatre gate

Theorem A is a direct consequence of the classical free differential-polynomial model; it is not
claimed as a new literature theorem.  Jet/prolongation spaces and generic differential types are
also established parent theories.  The candidate new contribution is the conjunction:

```text
finite-jet marked homogeneity
+ separated infinite tail flag
+ forced Gevrey product bornology
+ controlled nonabelian completion connection
+ signed Hermitian polarization
= a polarized completion-moduli problem for HT functions.                    (10)
```

Searches found no source formulating `(10)` as a classification program for hypertranscendental
analytic functions, but absence remains provisional until specialist review.  Vocabulary alone
does not pass novelty.  The paper-scale result begins only with a proof of Polarized
Completion-Moduli or a
counterexample that forces a new component.

Significance is high if either conjecture is resolved: differential algebra collapses the
algebraic moduli to one free object, so a successful completion theory would create the first
source-sensitive structural classification of HT functions.  Without a conservativity or
reconstruction theorem, the current object remains a rigorously forced research program rather
than a Fields-scale discovery.

## 7. Lean certificate

`formal/GaloisForLFunctions/HTGeometry/HypertranscendentalClockBoundary.lean` verifies:

- `hypertranscendentalFiniteJetEquiv`;
- `hypertranscendentalFiniteJetEquiv_generator`;
- arbitrary-pseudometric `IsUniformlyBoundedAround` and `IsMetricBornologicallyCofinal`;
- `uniformlyBoundedAround_of_metricBornologicallyCofinal`;
- `uniformlyBoundedAround_iff_subsample_of_metricBornologicallyCofinal`.

Imported formal foundations verify finite-jet algebraic independence, finite-jet universal
parametrization, strict tail descent, and algebraic triviality of the common tail.

## 8. Gates

- `[PASS]` exact universal finite-jet equivalence, including marked generators
- `[PASS]` finite-stage classification no-go
- `[PASS]` unpolarized field-plus-completion theory excluded by the existing orientation family
- `[PASS]` strong positive replacement: source moduli is a polarized completion problem
- `[PASS]` nonabelian metric-bornological cofinality formalized
- `[PASS]` no time or propagation interpretation required
- `[PASS]` RH appears only as a possible downstream realization
- `[FAIL until proved]` Polarized Completion-Moduli faithfulness
- `[FAIL until proved]` Boundary Localization for actual obstruction functors
- `[FAIL until audited]` specialist external novelty review of the full package
