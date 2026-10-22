# Primitive one-level Fourier--Stokes recognition and rigidity

## Metadata

- **Stage:** 1 — in progress
- **Created:** 2026-08-03
- **Area:** irregular connections; Stokes circles; nonabelian Hodge diagrams; Fourier transform;
  plane-branch/conormal geometry
- **Status:** `[CONJECTURE] [NOVELTY UNVERIFIED]`
- **Authorship boundary:** the Airy-tower manuscript and every pre-existing Stokes module are prior
  corpus. This card claims no credit for them. New work begins with the two-parameter primitive
  recognition theorem below.

## 1. Internal frontier

`[LOCAL-RESEARCH]` The existing Airy route classifies the zero-loop sublocus `b=1`, including an
elementary recognition theorem with additional high integral separation terms. It does not classify
arbitrary primitive one-level types `(a,b)`.

`[LOCAL-RESEARCH]` `stokes-cartan-contact-complexity-tomography.md` proves strict reconstruction of
the branching skeleton from a ramification-decorated diagram and asks for a recursive description
of decorated fibres. It does not show rigidity or a product law for a nontrivial ramified locus.

`[CORPUS]` Exact loop and pair source formulas, cyclic Galois actions, contact ultrametricity, and
finite coefficient realization infrastructure exist in `formal/GaloisForLFunctions/HTGeometry/`.
They are inputs for later formalization, not new results of this card.

## 2. External frontier

`[LITERATURE]` Douçot, arXiv:2509.24861, proves rescaled ultrametricity for all decorated
nonabelian Hodge diagrams and characterizes untwisted fission graphs. The twisted criterion is
necessary only.

`[LITERATURE]` Boalch--Douçot--Rembado, arXiv:2209.12695 / PRIMS 61 (2025), classifies admissible
deformation classes by fission trees and proves realization. It does not characterize their Cartan
shadows numerically.

`[LITERATURE]` Douçot, arXiv:2503.16102 / BLMS 58 (2026), classifies level data under basic
Fourier/Möbius/twist simplification and identifies one-level elementary Fourier transforms. It does
not give arbitrary-size diagram recognition.

`[LITERATURE]` Douçot--Hohl, arXiv:2402.05108 / JLMS 112 (2025), computes Fourier transforms of
analytic Stokes data for a broad one-level family. It does not characterize which integer Cartan
matrices arise.

`[LITERATURE]` Hiroe, arXiv:1406.5788, relates ramified exponential factors, plane branches,
irregularity, and Fourier resolution. The loop identity below is compatible with the Milnor number
of a coprime monomial branch; that comparison is not claimed as new.

No checked source states the exact pair spectrum, typed recognition theorem, fission-tree rigidity,
or Fourier involution below. Exact-phrase absence is not priority evidence; the theorem remains
`[NOVELTY UNVERIFIED]` until the statement-specific audit is complete.

## 3. Primitive reduced one-level locus

Let `T` be the set of coprime pairs

```text
tau = (a,b),  a>=1, b>=1, gcd(a,b)=1.
```

A reduced primitive one-level Stokes circle of type `tau=(a,b)` is the Galois orbit of a finite
Puiseux polynomial

```text
q(z) = c z^((a+b)/a) + sum_(1<=gamma<a+b) c_gamma z^(gamma/a),  c != 0,
```

with minimal ramification `a`. A common integral polynomial above all primitive slopes has already
been removed by one global exponential twist. Thus the only level is `(a+b)/a`; lower terms are
inconsequential after this coprime exponent reduces the cumulative gcd to one. The case `a=1` is
the untwisted primitive polynomial locus.

Put

```text
x(tau)=b/a,       alpha(tau)=1+b/a,       mu(tau)=(a-1)(b-1).
```

The involution `F(a,b)=(b,a)` is the arithmetic shadow of the one-level local Fourier step.

## 4. First conjecture and killing mechanism

`[CONJECTURE A]` Vertex admissibility and exact pairwise spectra alone characterize finite reduced
primitive one-level diagrams.

`[FALSIFIED]` Take three labels of Airy type `(a,b)=(2,1)`. Every edge in `{0,1,2}` is pairwise
realizable, but the triangle with edge values `0,1,2` has a unique largest rescaled contact and
cannot arise from a common Puiseux family. Pairwise realizability does not enforce coefficient
transitivity.

**Representation lesson.** The missing datum is not another pair invariant. It is the laminar
equivalence structure of common truncations, numerically expressed by the acute-isosceles law.

**Stronger conjecture forced by the failure.** Add ultrametric compatibility, but exploit primitive
types to show every mixed-type triangle is automatically compatible. Only equal-type blocks carry
genuine global constraints.

## 5. Frozen conjecture

Let `N` be finite. A typed symmetric integer diagram consists of types
`tau_i=(a_i,b_i) in T` and a symmetric matrix `B=(B_ij)`.

For two types define the local spectrum

```text
Spec(tau_i,tau_j) =
  {a_j b_i},                         if b_i/a_i > b_j/a_j,
  {a_i b_j},                         if b_j/a_j > b_i/a_i,
  {mu(tau_i),...,a_i b_i},           if tau_i=tau_j.
```

`[CONJECTURE B — PRIMITIVE ONE-LEVEL RECOGNITION]` The following are equivalent.

1. There is a finite reduced primitive one-level irregular class with labelled types `tau_i` and
   core matrix `B`.
2. All three conditions hold:
   - `B_ii=mu(tau_i)` for every `i`;
   - `B_ij in Spec(tau_i,tau_j)` for every distinct pair;
   - for each fixed type block `N_tau={i | tau_i=tau}`, every triangle in the restricted edge
     matrix is acute isosceles (the two largest entries coincide).

Equivalently, the complete rescaled contact matrix

```text
K_ii=1+(B_ii-1)/a_i^2,       K_ij=1+B_ij/(a_i a_j)
```

is ultrametric; the mixed-type part of this condition is forced by the pair spectra.

`[CONJECTURE C — DIAGRAM RIGIDITY]` On this locus, `(B,tau)` determines the complete labelled
fission tree, not only its branching skeleton. For an equal-type edge `B_ij<a_i b_i`, its fission
numerator is uniquely

```text
gamma_ij = B_ij - a_i b_i + a_i + b_i,
```

while `B_ij=a_i b_i` means separation at the mandatory primitive level. Different types separate
at the larger primitive slope. Thus the decorated fibre of admissible deformation classes is a
singleton.

`[CONJECTURE D — FOURIER INVOLUTION]` Simultaneously swapping every type `(a_i,b_i)` to `(b_i,a_i)`
preserves `B`, the recognition conditions, and the reconstructed typed fission data after the
canonical reversal of primitive slope order. In particular, the recognition category carries an
exact involution lifting the one-level Fourier rank swap.

## 6. Why the formulas are forced

For one type `(a,b)`, write `r=a`, `s=a+b`. The known loop formula gives

```text
B_ii=(r-1)(s-r-1)=(a-1)(b-1)=mu(a,b).
```

For unequal residual slopes `b_i/a_i>b_j/a_j`, the first difference is the primitive term of label
`i`, and the zero-common-part edge formula gives

```text
B_ij=a_j((a_i+b_i)-a_i)=a_j b_i.
```

For equal reduced slopes the types coincide. Distinct primitive coefficient orbits separate at the
mandatory level and give `ab`. If representatives have the same primitive coefficient orbit, the
first lower difference is at `gamma/a`, `1<=gamma<a+b`, and the common-level formula gives

```text
B_ij=(a+b)(a-1)+gamma-a^2
    =ab-a-b+gamma.
```

As `gamma` runs from `1` to `a+b-1`, this is every integer from `(a-1)(b-1)` to `ab-1`. Adding the
mandatory-orbit value `ab` proves the exact interval.

## 7. Proposed sufficiency mechanism

Inside a fixed type block, acute-isosceles edge values define nested equivalence relations

```text
i ~_m j  iff  i=j or B_ij<=m.
```

Their classes form a finite dendrogram. At its top value `ab`, assign primitive coefficients to
children with pairwise distinct `a`th powers; this separates their Galois orbits. At a lower value
`m`, attach the exponent

```text
gamma(m)/a = (m-ab+a+b)/a
```

and give the children distinct complex coefficients. The coprimality of `a` and `a+b` makes the
stabilizer of the primitive coefficient trivial, so ordinary coefficient inequality is sufficient
below the mandatory level.

Order the distinct type blocks by residual slope `b/a`. At the primitive level of each block,
attach the entire union of lower-slope blocks as the unique zero-coefficient residual child. Assign
nonzero primitive coefficients with distinct `a`th powers to the active same-type children. This
produces one simultaneous finite family of Puiseux polynomials. Every pair first differs at its
prescribed dendrogram node, so the source formula returns exactly `B_ij`.

The construction uses no pairwise witnesses chosen independently. One global coefficient family
realizes all pairs.

## 8. Hostile attacks still open

1. **Coefficient collection:** prove that stages with the same rational exponent but in disjoint
   type blocks cannot cancel a prescribed first difference.
2. **Mandatory residual child:** prove mixed-type spectra force all lower-slope labels at a
   primitive stage into one child, as required by the fission-tree sibling axiom.
3. **Full fission rigidity:** check whether admissible/empty unary vertices ignored by the reduced
   definition can create distinct admissible deformation classes. The statement must count only
   canonical fission data, not arbitrary coefficient support.
4. **Fourier semantics:** distinguish the unconditional combinatorial involution from analytic
   Fourier transformation; import a stationary-phase theorem only with exact hypotheses.
5. **Priority:** search plane-branch equisingularity, Eggers--Wall trees, one-level Stokes-data
   algorithms, and recent fission-tree work for an equivalent typed recognition theorem.

## 9. Exact open core

`[OPEN CORE]` Close attacks 1--3 and prove the simultaneous realization and uniqueness theorem
without hiding prescribed edges in a certificate. No Lean implementation is permitted before this
paper proof closes.

## 10. Significance test

If true, the theorem gives the first complete arbitrary-size numerical recognition theorem for a
Fourier-stable family containing every coprime primitive ramification type, not only the zero-loop
Airy boundary. It also identifies a nontrivial locus on which the Cartan shadow is faithful to the
full fission tree and supplies a type-block product decomposition of the inverse problem.

The result is not publication-level if it reduces to the general fission-tree realization theorem
after restating a fission certificate, or if the exact spectrum already appears in plane-branch
language. Those are killing conditions, not caveats.

## 11. Gates

- [x] Existing Airy paper excluded from authorship credit
- [x] Internal frontier and dead-route boundary checked
- [x] Current primary external sources identified
- [x] Pair-only conjecture falsified with exact three-vertex obstruction
- [x] Stronger typed-ultrametric conjecture frozen
- [ ] Statement-specific parent-theory/priority audit complete
- [ ] Hostile attacks 1--3 closed
- [ ] Complete dependency-closed paper proof
- [ ] Stage 2 promotion
- [ ] Exact unconditional Lean theorem
- [ ] Distinct manuscript and hostile journal review
