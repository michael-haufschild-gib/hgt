# Polarized fracture incidence has exact, closure-only, and dual-certificate phases

- **ID:** `polarized-fracture-incidence-trichotomy`
- **Stage:** 3-formalized
- **Type:** FORMAL FUNCTIONAL-ANALYTIC BRIDGE / POSITIVITY EFFECTIVITY / FARKAS TRICHOTOMY
- **Scientific status:** `[UNCONDITIONALLY LEAN-FORMALIZED] [PARENT CONIC DUALITY]`
  `[ARCHITECTURAL CONSEQUENCE FOR HT] [NOT AN RH RESULT]`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/PolarizedFractureIncidence.lean`
- **Parent:** `calibrated-fracture-incidence-kernel-cokernel.md`
- **Statement:** A polarized realization has three—not two—possible incidence phases: an actual
  positive lift, a closure-only nonattainment point invisible to every continuous dual positivity
  reporter, or a strict dual obstruction certificate.  Closedness of the positive image is exactly
  the hypothesis that removes the middle phase.

## Setup

Let `C` be a proper cone in a real Hilbert space `E`, let

```text
f:E->F
```

be continuous linear, and let `b in F` be the target produced by the calibrated fracture packet.
Write

```text
Exact(C,f,b) iff b in f(C),
Weak(C,f,b)  iff b in closure(f(C)).                       (1)
```

A strict dual certificate is a vector `y in F` such that

```text
f^*(y) belongs to the dual cone C^vee,
<b,y><0.                                                   (2)
```

The first condition makes `<f(x),y>>=0` for every admissible `x in C`, so `(2)` separates `b`
strictly from every actual and approximate positive lift.

## Exact three-phase theorem `[PROVED + LEAN]`

Exactly one of the following compatible descriptions applies:

1. **Exact effectivity:** `b in f(C)`.
2. **Closure-only nonattainment:** `b in closure(f(C))` but `b notin f(C)`.
3. **Strict dual obstruction:** a certificate `(2)` exists.

Lean proves the load-bearing equivalences

```text
Weak(C,f,b)
  iff <b,y>>=0 for every y with f^*(y) in C^vee,            (3)

not Weak(C,f,b)
  iff a strict dual certificate exists.                    (4)
```

Consequently phase 2 has no positive lift but passes every continuous dual-cone positivity test.
No strict Farkas reporter can detect it.

## Cofinal positive approximation `[PROVED + LEAN]`

If `x_n in C` and

```text
f(x_n) -> b,                                               (5)
```

then `Weak(C,f,b)` holds.  If additionally `b notin f(C)`, the target is in phase 2.  Thus a
cofinal family of finite positive realizations can converge to a target for which no effective
positive realization exists.

This is the exact positive content behind an all-scale obstruction: the finite stages are not
false or irrelevant.  They converge correctly, but the positive image fails to be closed.

## Closed-image positive theorem `[PROVED + LEAN]`

If `f(C)` is closed, then

```text
Weak(C,f,b) iff Exact(C,f,b),                               (6)
```

and the trichotomy collapses to the classical Farkas alternative:

```text
an actual positive lift exists
or a strict dual obstruction certificate exists.          (7)
```

Closedness is therefore not technical housekeeping.  It is the exact promotion theorem from
all continuous dual positivity tests to actual source effectivity.

## No-go and positive successor

```text
[NO-GO]
Passing every finite or continuous dual positivity test implies existence of a positive
source-effective lift.

[POSITIVE]
It implies only closure membership.  Closedness, compactness, coercivity, or an equivalent
attainment theorem is the additional source law that promotes weak positivity to effectivity.
```

The no-go is not special to HT.  Weak infeasibility and nonclosed projections of closed cones are
standard in conic optimization.  The HT significance is the identification of this middle phase
as the common linear model of critical all-scale and nonclosed spectral-range obstructions.

## Parent and novelty boundary

Farkas separation, proper dual cones, weak infeasibility, and bad nonclosed projections are parent
mathematics.  In particular:

- Liu--Pataki, *Exact duals and short certificates of infeasibility and weak infeasibility in conic
  linear programming*, `https://arxiv.org/abs/1507.00290`;
- Pataki--Touzov, *An echelon form of weakly infeasible semidefinite programs and bad projections
  of the psd cone*, `https://arxiv.org/abs/2110.11437`.

This formal theorem is not new scientific knowledge.  The candidate-new HT claim begins only with
a source-canonical construction showing that several natural analytic obstruction chains are
realizations of the same projected cone and that their critical failure is its nonclosed-image
phase.

## RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` The report's source-sign and critical-all-scale obstructions may be
two phases of one polarized source incidence:

```text
strictly outside closure  -> a negative Weil/Hankel/Herglotz/spectral reporter;
closure but not image     -> every finite or continuous positivity test passes, but the critical
                             source state is not attained;
inside image              -> a positive source-effective lift exists.       (8)
```

This becomes an RH theorem only if the prime--archimedean source constructs `C`, `f`, and `b`
without the Xi divisor and proves exact incidence or closedness at the critical boundary.

## Lean declarations

- `ExactPolarizedIncidence`
- `WeakPolarizedIncidence`
- `HasStrictPolarizedCertificate`
- `exactPolarizedIncidence_implies_weak`
- `weakPolarizedIncidence_iff_forall_dual_nonneg`
- `not_weakPolarizedIncidence_iff_strictCertificate`
- `closureOnlyPolarizedIncidence_forall_dual_nonneg`
- `closureOnlyPolarizedIncidence_no_strictCertificate`
- `weakPolarizedIncidence_of_tendsto_exact`
- `closureOnlyPolarizedIncidence_of_tendsto_exact_of_not_exact`
- `polarizedIncidence_trichotomy`
- `weakPolarizedIncidence_iff_exact_of_isClosed_image`
- `exactPolarizedIncidence_or_strictCertificate_of_isClosed_image`

## Verification

- The new module had no cached object, so exactly its named target was built.
- The touched source then passed direct `lake env lean` verification.
- No full build was run.
- No `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declaration was introduced.

## Gates

- [x] exact positive incidence defined
- [x] closure-valued weak incidence defined
- [x] continuous dual characterization proved
- [x] strict certificate equivalence proved
- [x] closure-only dual blindness proved
- [x] cofinal positive approximation theorem proved
- [x] exact three-phase trichotomy proved
- [x] closed-image promotion theorem proved
- [x] every no-go paired with a positive attainment condition
- [x] parent weak-infeasibility literature identified
- [x] theorem demoted to parent mathematics
