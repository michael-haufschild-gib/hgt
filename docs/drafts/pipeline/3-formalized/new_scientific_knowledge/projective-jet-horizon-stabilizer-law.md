# The HT jet flag is tail-trivial and has an exact projective stabilizer

- **ID:** `projective-jet-horizon-stabilizer-law`
- **Stage:** 3-formalized
- **Type:** GENERAL HT THEOREM / DIFFERENTIAL-BIRATIONAL FLAG RIGIDITY
- **Scientific status:** `[FORMALIZED UNCONDITIONALLY] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Novelty verdict:** Algebraic independence of the jets, differential Lüroth theory, and the
  homographic relation between generators are established parents. The candidate new object is the
  combined geometry they induce: a strict descending jet-tail flag with an algebraic zero-one
  residual whose full homographic stabilizer is exactly the constant-slope affine subgroup.
  Exact-statement and adjacent primary-source searches found no filtered-generator theorem of this
  form. Novelty remains provisional pending independent specialist scrutiny.
- **Significance verdict:** The theorem converts the negative definition of HT into a positive,
  generator-sensitive structure carried by every HT element. It distinguishes projective
  generators that the whole differential field cannot distinguish and proves that no
  transcendental datum survives arbitrarily deep derivative horizons.
- **Formal owner:** `formal/GaloisForLFunctions/HTGeometry/ProjectiveJetHorizon.lean`
- **Primary lane:** nature of hypertranscendental functions; static constraint geometry
- **Secondary audit:** coordinate firewall for RH-facing HT sources; not an RH route

## The theorem `[PROVED] [FORMALIZED]`

Let `K` be a differential field, let `L/K` be a differential-field extension, and let `f in L`
be hypertranscendental over `K`. Define the static jet-tail fields

```text
T_n(f) = K(delta^n f, delta^(n+1) f, ...),  n >= 0.          (1)
```

Then the following hold.

### 1. Strict jet flag

For every `n`,

```text
T_(n+1)(f) < T_n(f).                                        (2)
```

Indeed, `delta^n f` belongs to `T_n(f)` and is transcendental over
`T_(n+1)(f)`.

### 2. Relative tail zero-one law

The infinite residual of the flag contains no transcendental information over the base:

```text
intersection_(n >= 0) T_n(f) <= K_alg,L,                    (3)
```

where `K_alg,L` is the relative algebraic closure of `K` in `L`. Consequently, whenever
`K` is relatively algebraically closed in `L`,

```text
intersection_(n >= 0) T_n(f) = K.                           (4)
```

Thus any datum visible beyond every derivative horizon is already algebraic over the source base;
under the natural no-hidden-algebraic-constants condition, it is a base datum.

### 3. Exact projective stabilizer

For `a,b,c,d in K` with `Delta=ad-bc != 0`, put

```text
z = (a f+b)/(c f+d).                                        (5)
```

Then

```text
T_1(z)=T_1(f)
iff
c=0 and delta(a/d)=0.                                      (6)
```

The right side also satisfies the stronger equivalence

```text
(for every n, T_n(z)=T_n(f))
iff
c=0 and delta(a/d)=0.                                      (7)
```

Hence the first derivative horizon detects preservation of the whole flag. The full homographic
freedom of a differential-rational generator is reduced to affine changes

```text
z=alpha f+beta,  alpha != 0,  delta alpha=0,  beta in K.    (8)
```

This is the parabolic subgroup fixing projective infinity, with its dilation restricted to a
differential constant.

## Physical and topological interpretation

Equations (1)--(8) describe a static information geometry, not a time evolution.

- Derivative order indexes nested simultaneous constraints; it does not propagate or construct
  `f`.
- The strict flag is a one-sided horizon structure: every finite horizon loses exactly the current
  jet as an algebraically independent direction.
- The zero-one law says that infinite horizon depth erases every transcendental observable.
- The stabilizer theorem says that the flag marks a projective end. Inversion and every genuine
  projective denominator change the horizon even though they preserve the generated differential
  field and preserve HT.

The closest physical analogue is therefore neither a Hamiltonian flow nor a Wheeler--DeWitt
equation. It is a filtered boundary observable with tail triviality and spontaneous reduction of
projective gauge symmetry to a parabolic stabilizer.

## Proof

### Algebraic independence and strictness

Hypertranscendence gives algebraic independence over `K` of the sequence

```text
f, delta f, delta^2 f, ... .                                (9)
```

For every `n`, algebraic independence after adjoining the strict tail implies that
`delta^n f` is transcendental over `T_(n+1)(f)`. Since it lies in `T_n(f)), (2) follows.

### Tail zero-one law

Write `j_n=delta^n f`. In the algebraic matroid of `L/K`, the sets

```text
J_n={j_m:m>=n}                                               (10)
```

are subsets of the independent set `{j_m:m>=0}`, and

```text
intersection_n J_n = empty.                                 (11)
```

Matroid closure commutes with intersections of subsets of one independent set. Membership in
`T_n(f)` makes an element algebraic over the algebra generated by `J_n`; therefore an element
in every `T_n(f)` belongs to the closure of every `J_n`. By (11), it belongs to the closure of
the empty set, which is the relative algebraic closure of `K`. This proves (3), and (4) follows
from relative algebraic closedness.

### Projective necessity

Hypertranscendence supplies

```text
f is transcendental over T_1(f),
delta f is transcendental over K.                           (12)
```

The derivative of (5) is

```text
delta z =
  ((delta a)c-a(delta c)) f^2
  + ((delta a)d+(delta b)c-a(delta d)-b(delta c)) f
  + ((delta b)d-b(delta d))
  + Delta delta f
  ---------------------------------------------------------- .   (13)
                     (c f+d)^2
```

If `delta z in T_1(f)`, clearing the denominator produces a quadratic polynomial over
`T_1(f)` annihilating `f`. By (12), every coefficient vanishes.

If `c != 0`, the quadratic coefficient puts `delta z` in the embedded base field. The constant
coefficient then puts `Delta delta f` in the base field, contradicting (12). Hence `c=0`.

Now write `z=alpha f+beta`, with `alpha=a/d` and `beta=b/d`. Then

```text
delta z=(delta alpha)f+alpha delta f+delta beta.             (14)
```

Membership in `T_1(f)` and the first part of (12) force `delta alpha=0`.

### Projective sufficiency

If `c=0` and `delta(a/d)=0`, then `alpha=a/d` is a nonzero differential constant and

```text
delta^n z=alpha delta^n f+delta^n beta                       (15)
```

for every `n`. Solving (15) in both directions gives `T_n(z)=T_n(f)` for every `n), proving
(6) and (7).

## Collision and falsification audit

1. **Differential-indeterminate collision.** The bare statement that one jet is transcendental
   over its strict successors is standard algebraic independence and is graded `[BRIDGE]`.
2. **No-DA-shadow collision.** The retired `differential-rational-no-da-shadow` card is
   source-killed by ADH Lemma 4.1.5. It concerns nonconstant rational observables remaining
   differentially transcendental; it does not state the tail intersection or its projective
   stabilizer.
3. **Differential Lüroth collision.** Differential Lüroth theory states that two generators are
   related by a homographic map and that all generators have the same differential order. It does
   not identify which homographies preserve the descending future-jet fields.
4. **Projective inversion attack.** For `z=1/f`, one has
   `delta z=-(delta f)/f^2`. The whole generated differential field is unchanged, but (6) proves
   that the first horizon changes. This witnesses that the flag contains real information absent
   from the whole field.
5. **DA boundary.** For `f'=f`, the flag collapses immediately. Such an element is DA, so this is
   a boundary witness rather than a counterexample.
6. **Hidden-flow attack.** No flow, carrier, time parameter, semigroup, transport, master
   constraint, or evolution equation occurs.
7. **Computational dependence.** None. The discovery, proof, and formalization are symbolic.

## Literature boundary

The primary paper D'Alfonso--Jeronimo--Solerno, *Effective differential Lüroth's theorem*,
Journal of Algebra 406 (2014), proves order bounds and records that arbitrary Lüroth generators are
related by a homographic map over the base. Ritt and Kolchin are its classical parents.

Searches for the exact derivative-tail intersection, strict jet-tail flag, filtered homographic
automorphism, and projective stabilizer formulations found no matching theorem. Searches also
covered modern differential Lüroth, differential rational parametrization, Kolchin-dimension,
jet-filtration, and differential-rational automorphism terminology. This supports a candidate-new
verdict, not a claim of exhaustive priority.

## Lean realization

Module:
`formal/GaloisForLFunctions/HTGeometry/ProjectiveJetHorizon.lean`.

Headline declarations:

- `hypertranscendentalOver_jetTailField_strictAnti`;
- `hypertranscendentalOver_iInf_jetTailField_le_algebraicClosure`;
- `hypertranscendentalOver_iInf_jetTailField_eq_bot`;
- `mobius_jetTailField_one_eq_iff`;
- `mobius_all_jetTailField_eq_iff`;
- `jetTailField_inv_ne_of_hypertranscendentalOver`.

The proof also formalizes the algebraic-matroid tail lemma, coefficient separation, denominator
nonvanishing, affine residual, and all-tail sufficiency.

Verification:

- isolated source check: passed;
- targeted module build: passed;
- formal lint: passed;
- axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`;
- no full build was run.

## RH-impact audit

`[USEFUL FORMULATION CONSTRAINT; NOT RH PROGRESS]`

An RH-facing construction based on an HT source cannot treat the whole generated differential field
as its complete coordinate-free content: projective inversion preserves that field and HT while
changing the jet flag. A horizon-native selector must either be invariant only under the
constant-slope affine subgroup or carry extra source data that marks projective infinity.

The theorem does not locate zeros, prove a critical-line statement, or close any RH bottleneck. Its
useful impact is a coordinate-invariance firewall against overclaiming.

## Gates

- [x] exact source-pure theorem isolated
- [x] strict flag proved
- [x] relative tail zero-one law proved
- [x] exact projective stabilizer proved
- [x] parent-theory and failed-route collisions audited
- [x] primary exact-statement searches completed
- [x] significance gate passed for the combined geometry
- [x] candidate-novelty gate passed provisionally
- [x] Lean formalization completed under `HTGeometry`
- [x] targeted build, lint, and axiom audit passed
- [x] RH impact graded without upcasting
