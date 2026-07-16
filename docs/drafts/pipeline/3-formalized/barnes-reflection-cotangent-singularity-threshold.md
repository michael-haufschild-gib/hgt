# Cotangent singularity is the exact hypertranscendence threshold for Barnes reflection

- **ID:** `barnes-reflection-cotangent-singularity-threshold`
- **Stage:** 3-formalized / independent novelty audit required
- **Type:** CROSS-CATEGORY THRESHOLD THEOREM
- **Scientific status:** `[PROVED FROM PARENTS] [LEAN-FORMALIZED] [NOVELTY UNVERIFIED]`
- **Parents:**
  - `../new_scientific_knowledge/barnes-multiple-gamma-translation-annihilator.md`
  - `../new_scientific_knowledge/all-order-multiple-sine-stanley-reisner-differential-matroid.md`
  - `hypertranscendental-critical-locus-universality.md`
- **Statement:** For positive rationally independent Barnes periods and every order `N>=1`,
  reflection produces a hypertranscendental multiple sine exactly when the intrinsic cotangent
  singular scheme of the parent Barnes annihilator hypersurface is nonempty.  Equivalently, the
  analytic hypertranscendence threshold and the algebraic singularity threshold both occur at
  `N=2`.

## 1. Exact theorem

Let

```text
A_N=F[t_1^(+-1),...,t_N^(+-1)],
x_i=t_i-1,
f_N=product_(i=1)^N x_i,
B_N=A_N/(f_N).
```

Write `S_N` for the Barnes--Kurokawa multiple sine with positive periods
`omega_1,...,omega_N` linearly independent over `Q`.  Define the intrinsic principal critical
ideal

```text
Crit_F(f)=(f,Df : D in Der_F(A_N,A_N)).                 (1)
```

Then

```text
S_N is hypertranscendental
  <=> (log S_N)' is hypertranscendental
  <=> Crit_F(f_N) != A_N
  <=> Sing(B_N/F) is nonempty
  <=> N>=2.                                             (2)
```

Here `Sing(B_N/F)` denotes the scheme cut out by the appropriate Fitting ideal of
`Omega_(B_N/F)`.  The equivalence in `(2)` concerns this Barnes hierarchy; it is not asserted for
arbitrary reflection identities.

## 2. Algebraic half `[LEAN-FORMALIZED]`

The parent criticalization theorem proves

```text
Crit_F(f_N)=(product_(j!=i)x_j : 1<=i<=N)=I_(N-1).      (3)
```

The squarefree degree-`r` ideal is the unit ideal exactly for `r=0`.  Applying this with
`r=N-1` gives

```text
Crit_F(f_1)=A_1,
Crit_F(f_N)!=A_N for N>=2.                              (4)
```

Equivalently, `B_1=A_1/(x_1)` is smooth over `F`, whereas every `B_N` with `N>=2` has a nonempty
normal-crossing singular scheme.  In conormal form,

```text
B_N --df_N--> B_N^N --> Omega_(B_N/F) --> 0,
1 |--> (product_(j!=1)x_j,...,product_(j!=N)x_j),        (5)
```

and its cotangent Fitting degeneracy ideal pulls back to `(3)`.

Lean declarations in
`formal/GaloisForLFunctions/HTGeometry/SquarefreeVeroneseIdeal.lean` and
`formal/GaloisForLFunctions/HTGeometry/BarnesCotangentSingularityThreshold.lean`:

- `veroneseIdeal_eq_top_iff`;
- `normalCrossingDerivationalCriticalIdeal_eq_top_iff`.
- `normalCrossingCriticalIdeal_ne_top_iff` and
  `normalCrossingCotangentSingularityThreshold`, proving the exact order-two onset;
- `normalCrossingRestriction` and `normalCrossingRestriction_surjective`, constructing the
  canonical restriction `A/(f_N) -> A/I_crit`;
- `ker_normalCrossingRestriction`, identifying its loss ideal exactly;
- `normalCrossingCotangentFittingIdeal_eq_singularIdeal` and
  `comap_normalCrossingCotangentFittingIdeal`, identifying the gradient presentation Fitting
  ideal in the hypersurface and its pullback to `A`;
- `normalCrossingRestrictionCertificate`, packaging the canonical exact restriction law.

The algebraic modules and
`formal/GaloisForLFunctions/HTGeometry/GammaPhaseCompletion.lean` passed exact targeted builds when
their `.olean` files were absent, followed by direct Lean verification. No full build was run.
`BarnesReflectionAnalyticThresholdInput` states the named all-order analytic parent at its exact
interface, without installing it as an axiom, and
`barnesReflection_cotangentSingularity_exactThreshold` joins both analytic thresholds to the
internally proved cotangent threshold. Thus the complete implication surface of `(2)` is formalized;
an internal construction of the classical analytic parent remains a strengthening rather than a
gap in this theorem's checked dependency contract.

## 3. Analytic half `[PROVED BY PARENT]`

At order one,

```text
S_1(z;omega)=2 sin(pi z/omega),
(log S_1)'=(pi/omega)cot(pi z/omega),                    (6)
```

so both functions are differentially algebraic.  For every `N>=2`, the parent all-order theorem
computes the exact structural annihilator

```text
Ann_DA((log S_N)')=I_(N-1)                              (7)
```

and its complete nonlinear differential matroid.  Since `I_(N-1)` is proper, `(log S_N)'` is
hypertranscendental.  If `S_N` were differentially algebraic then its logarithmic derivative would
be differentially algebraic, so `S_N` is hypertranscendental as well.  Conversely, the parent
multiplicative classification applies to the exponent polynomial `1`, so the two analytic
formulations in `(2)` agree throughout the hierarchy.

## 4. Complete singular-restriction law `[PROVED FROM PARENTS]`

Let

```text
J_N=Fitt_(N-1)(Omega_(B_N/F))=I_(N-1)/(f_N).             (8)
```

Since `(f_N) subset I_(N-1)`, there is a canonical exact sequence

```text
0 -> J_N -> B_N -> A_N/I_(N-1) -> 0.                    (9)
```

The target algebra in `(9)` computes the complete nonlinear structural differential matroid of
`S_N`.  Therefore Barnes reflection induces, at the level of exact dependence geometry, the
restriction map

```text
O(V(f_N)) -> O(Sing(V(f_N)))                             (10)
```

and its loss module is exactly the cotangent Fitting ideal `J_N`.  This proves more than equality
of two thresholds:

```text
[SINGULAR-RESTRICTION THEOREM]
The complete structural differential matroid of the reflected multiple sine is the linear
matroid of the coordinate algebra of the intrinsic singular scheme of the parent Barnes
annihilator hypersurface.
```

At `N=1`, the singular scheme is empty and `(10)` has zero target, matching differential
algebraicity of ordinary sine.  At every `N>=2`, the singular scheme is nonempty and its coordinate
algebra retains unbounded monomial directions, matching hypertranscendence.  Thus `(9)` gives both
the exact part reflection destroys and the exact part on which HT capacity survives.

## 5. Sharp no-go and positive theorem

```text
[NO-GO] Reflection symmetry preserves hypertranscendence.
```

The Barnes gamma function at order one is hypertranscendental, while its reflected quotient is
the differentially algebraic sine function.  Functional symmetry is therefore not an adequate
selector of hypertranscendence.

```text
[THEOREM] In the full rationally independent Barnes hierarchy, reflection preserves
          hypertranscendence exactly after the parent annihilator hypersurface becomes
          cotangent-singular.
```

This is stronger than observing that all `S_N`, `N>=2`, are hypertranscendental.  It identifies a
presentation-independent geometric event in the exact dependence scheme that selects the analytic
survival of hypertranscendence under reflection.

## 6. What the theorem does and does not explain

The theorem proves equality of two independently defined thresholds:

1. an analytic threshold in differential algebra;
2. an algebraic threshold in the cotangent Fitting geometry of an exact annihilator scheme.

It does not yet prove a causal theorem saying that singularity forces hypertranscendence for an
arbitrary source.  Objectwise universality of simplicial HT constraint topologies forbids that
naive generalization: the same finite singular scheme can coexist with different analytic
realizations and residue orientations.

The nontrivial positive successor is therefore not a universal singularity criterion for a bare
scheme.  It is a law for a **coupled source morphism**:

```text
[CONJECTURE -- CRITICAL SURVIVAL LAW]
For a calibrated reflection or completion morphism between finitely sourced HT objects, the
target differential matroid is the realized derived critical support of that morphism.  Its lost
capacity is the image of the relative cotangent defect; its surviving capacity is the quotient
supported on the derived critical locus.
```

The Barnes hierarchy proves the first complete infinite family of this conjectural law: its
classical critical module is represented by the codimension-two Hilbert--Burch resolution of
`R/I_(N-1)`.  This resolution is not the derived critical structure sheaf.  The latter is the
Koszul cdga on the coface gradient sequence and has nonzero excess homology from `N=3` onward, as
proved in `normal-crossing-derived-critical-excess-phase-law.md`.

## 7. Significance gate

### Why this could matter

- It identifies the complete nonlinear dependence geometry of an analytic special-function
  hierarchy with an intrinsic singular scheme across every order, rather than matching one
  scalar invariant at one isolated function.
- It replaces reflection as a superficial symmetry with a source-critical morphism carrying an
  exact cotangent defect.
- It identifies the first falsifiable selector for the proposed unified theory: derived cotangent
  defect, not time, hierarchy order, or functional-equation symmetry.

### Why this is not yet a standalone major result

The algebraic threshold `(4)` is elementary once the exact annihilator is known.  The paper-scale
content is the complete singular-restriction law `(9)`--`(10)`, which joins the parent all-order
differential-matroid theorem `(7)` to the intrinsic Fitting identification `(5)`.  Publication
should package these statements as one cross-category theorem, not advertise `(4)` alone.

Verdict: **potentially paper-worthy with the all-order parent; not Fields-scale by itself.**

## 8. Novelty gate

The targeted primary-literature pass found the following boundary.

1. Kurokawa--Koyama, *Multiple Sine Functions*, Forum Math. 15 (2003), gives the hierarchy and
   reflection/translation recurrence.
2. Kurokawa--Wakayama, *Differential Algebraicity of Multiple Sine Functions*, Lett. Math. Phys.
   71 (2005), DOI `10.1007/s11005-004-5921-8`, proves DA when all periods are commensurable.
3. Kato, *Hypertranscendence of the Multiple Sine Function for a Complex Period*, Proc. Japan
   Acad. Ser. A 95 (2019), DOI `10.3792/pjaa.95.16`, proves HT when a period ratio is non-real.
4. Kato's 2021 multiple-elliptic-gamma paper explicitly describes the non-rational multiple-sine
   differential-algebraicity problem as obscure outside that complex-period result.

Thus the positive-real rationally independent regime used by the all-order parent lies in an
explicit gap between the commensurable DA theorem and the non-real-ratio HT theorem. The search
also found no paper identifying any multiple-sine differential matroid with the cotangent
singular scheme or Fitting degeneracy of a Barnes annihilator hypersurface.

This negative search is not proof of novelty.  Promotion requires an independent specialist audit
of:

1. differential-algebraic classification of positive real multiple-sine periods;
2. singularity-theoretic interpretations of multiple-sine reflection;
3. difference-Galois formulations of Barnes recurrence;
4. possible equivalent statements hidden in D-module or GKZ language.

Until that audit clears, the correct label is `[NOVELTY UNVERIFIED]`.

## 9. Anti-theatre gate

- The Lean theorem is not presented as the scientific discovery; it certifies the exact algebraic
  threshold used by `(2)`.
- The cross-category equivalence depends on the substantive all-order analytic parent.
- The universal generalization is explicitly conjectural and has a named counterpressure from
  objectwise topology universality.
- No RH consequence is claimed.

## 10. RH pressure test only

`[CONJECTURE; NOT AN RH RESULT]` If a zeta functional-equation object has an exact source morphism,
then zeros on the critical line should be sought as self-dual support of its derived cotangent
defect, not as a direct consequence of reflection.  This is meaningful only after constructing the
source morphism independently of the zeros.
