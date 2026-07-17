# The hypertranscendental obstruction object is a stabilizer-enriched realization stack

- **ID:** `hypertranscendental-stabilizer-enriched-realization-stack`
- **Stage:** 5-failed
- **Type:** FALSIFIED NOVELTY CLAIM / OVERSTRONG SOURCE-CANONICAL STACK CONJECTURE
- **Scientific status:** `[RETIRED BY ANTI-THEATRE GATE]`
  `[ALGEBRAIC STABILIZER SEED SURVIVES] [POSITIVE DIFFERENTIAL-LOCALIZATION SUCCESSOR]`
  `[NOT AN RH RESULT]`
- **Exact algebraic seed:**
  `../3-formalized/not_new_scientific_knowledge/orbit-marker-source-face-reconstruction.md`
- **Triptic seed:**
  `../2-fully-proven/new_scientific_knowledge/triptic-orbit-residue-reciprocity.md`
- **Conormal seed:**
  `../1-in-progress/hypertranscendental-conormal-integrability-correspondence.md`
- **Statement:** The typed stabilizer calculation is correct, but promoting it to a new universal
  realization stack fails.  The fracture-hypercube/Postnikov program already contains that
  architecture, the FHRZ gerbe already contains the strongest triptic stack geometry, and a bare
  source with nontrivial gauge cannot canonically supply a section of the proposed stack.

## Terminal verdict

Three independent gates retire the conjecture as stated.

1. **Novelty failure.**  A stabilizer-enriched realization stack over source moduli is already the
   substance of the existing capacity-descent/fracture-hypercube program.  Renaming it does not add
   a theorem.
2. **Source-canonicality failure.**  The Gamma collision proves that a bare source, even with one
   regular pointing and any finite jet, does not choose a solution.  Any stack constructed solely
   from that bare source inherits the forgotten gauge.  Its maximal reconstruction stratum is
   still governed by the normalized common-kernel criterion.
3. **Triptic parent collision.**  FHRZ already construct the elliptic gamma function as a
   meromorphic section of a Hermitian holomorphic abelian gerbe on the universal oriented triptic
   curve and identify it with a pseudodivisor gerbe.  “Orbit residue is gerbe descent” is not a new
   theorem at the ordinary-divisor level.

The nontrivial positive residue is sharper.  The DA-complete triptic orbit marker is a
`C[delta]`-valued differential thickening of the ordinary pseudodivisor.  Every fixed finite
coefficient depth loses explicit aperiodic HT classes, while the cofinal all-order marker is
complete modulo DA.  This successor is developed in
`../1-in-progress/hypertranscendental-differential-pseudodivisor-prolongation.md`.

The exact typed-marker stabilizer theorem below remains valid reusable infrastructure.  It is not
evidence for the retired novelty claim.

## 1. Decisive no-go: fibrewise completeness is not horizontal conservativity

The proposed fully faithful functor from source systems to unmarked pointed conormal modules is
false.

First, the Barnes multiple-sine and multiple-elliptic-gamma hierarchies can have the same pointed
normal-crossing critical module at equal source rank while having different analytic source
realizations.  Second, the full logarithmic characteristic arrangement is invariant under deck
translation and reflection.  Third, in the triptic class the common orbit-residue divisor lives on

```text
G=C/(Z+Z tau+Z sigma).
```

It records the total period subgroup but not its two labelled rank-two face lattices

```text
Lambda_tau=Z+Z tau,       Lambda_sigma=Z+Z sigma.
```

A shear such as `tau -> tau+sigma` leaves the total rank-three subgroup unchanged while changing
one face.  Thus even a complete invariant of `Q/(Q intersect Mer_DA)` for each fixed source frame
need not distinguish source frames.  Completeness inside every fibre does not imply faithfulness
over the base.

This is not merely another negative statement.  It identifies exactly what was missing:
**horizontal source transport**.

## 2. Exact positive successor: retain the boundary realization cospan

Before the two triptic boundary divisors are pushed to their common quotient, retain the typed
diagram

```text
 D_tau in A[C/Lambda_tau]  ---->  D in A[C/H_3]
             |                             |
             |                             |
 D_sigma in A[C/Lambda_sigma] ---->  D in A[C/H_3].       (1)
```

Every object in (1) carries the ambient translation action.  For a marker `D_H` on `C/H`, put

```text
Per_H(D_H)=pi_H^(-1)(Stab(D_H)).                            (2)
```

The Lean-formalized theorem gives the exact reconstruction law

```text
Per_H(D_H)=H  iff  Stab(D_H)=0.                             (3)
```

Every nonzero finite marker has finite stabilizer, and a nonzero atom has trivial stabilizer.
Consequently:

- the common marker in (1) reconstructs at most the total subgroup `H_3), up to its finite
  stabilizer;
- the typed pair reconstructs `Lambda_tau`, `Lambda_sigma`, their intersection, and their join
  exactly on the aperiodic stratum;
- on a symmetric stratum the two finite stabilizers are the exact source-face inertia, not an
  unspecified failure of normalization;
- even on the aperiodic stratum, `Zq=Z(-q)`, so an oriented primitive normal remains additional
  data.

This is the maximal positive replacement for full faithfulness of the unmarked conormal skeleton.

### Standard triptic face effectivity `[PROVED FROM PARENTS]`

For the standard elliptic-gamma logarithmic derivative `Psi`, the two boundary functions are the
theta logarithmic derivatives.  The existing exact theta-divisor theorem gives one simple
residue-one pole on each elliptic boundary.  Hence both pre-pushforward orbit markers are nonzero
atoms.  Applying (3) and the formalized rank-three incidence theorem gives

```text
Per_(Lambda_tau)(D_tau)=Lambda_tau,
Per_(Lambda_sigma)(D_sigma)=Lambda_sigma,
Lambda_tau intersect Lambda_sigma=Z,
Lambda_tau+Lambda_sigma=H_3.                                (3a)
```

Therefore the standard typed triptic boundary cospan reconstructs its two labelled source faces
exactly.  The common atom on `C/H_3` reconstructs only `H_3`, not the decomposition in (3a), and
still cannot choose the sign of a primitive normal.

Equation (3a) is a theorem obtained from the existing analytic theta-divisor and triptic-reciprocity
parents plus the new Lean-checked algebraic gate.  It is not claimed as standalone new science.
The live candidate novelty is the horizontal descent/gerbe comparison below.

## 3. `[CONJECTURE -- STABILIZER-ENRICHED REALIZATION-STACK PRINCIPLE]`

Let `Src_HT` be the category of regular source-minimal HT constraint systems, with source
specializations and changes of presentation retained.  There is a stack

```text
Real_DA -> Frame_src                                             (4)
```

whose fibre over a source frame is the category of DA-relative conormal realizations, not merely
their common support or cyclic module.  An object of `Real_DA` contains:

```text
(derived conormal skeleton,
 typed boundary-realization cospan,
 residual stabilizer groupoids,
 primitive-kernel orientation local system,
 analytic completion and polarized real form).                 (5)
```

The source-to-realization functor

```text
Src_HT -> Cart(Real_DA/Frame_src)                               (6)
```

is fully faithful up to DA gauge and source Morita equivalence on its source-effective essential
image.  Its coarse object in one fibre is the DA-relative cyclic/conormal module.  Its inertia is
the exact common invisible gauge or orbit-marker stabilizer.  Its failure to admit a cartesian lift
across a source face is the global obstruction.

The aperiodic locus is the effective coarse-moduli stratum of (4), not the whole theory.  Nontrivial
finite stabilizers are retained as legitimate stack inertia rather than quotienting them away.

## 4. One object, several obstruction receivers

The conjecture predicts the following dictionary:

```text
exact reconstruction ambiguity = inertia of the realization object;
noncanonical boundary          = noncontractible fibre of cartesian lifts;
monodromy                      = holonomy of the orientation/normalization local system;
continuation failure           = failure of a cartesian lift across source specialization;
positivity failure             = failure of the transported object to admit the required
                                 polarized real form;
spectral incompleteness        = nonclosed image of the completed realization morphism;
integrality failure            = failure to lift the coarse complex realization to the
                                 integral stabilizer/gerbe object.               (7)
```

These are not asserted to be equal numbers.  They are conservative realizations of the same
horizontal descent defect.  A defect may move between inertia, monodromy, cokernel, closure, and
signature under realization without disappearing from the full stack.

This gives a precise higher-level version of the working hypothesis that different RH proof chains
see different representations of one obstruction interval.  The common object is not a topology
on one HT germ.  It is the failure of a DA-relative conormal realization to descend horizontally
over the moduli of source constraints.

## 5. Why this is a serious constraint on hypertranscendental functions

Hypertranscendence alone says that no finite algebraic-differential equation generates the germ.
The conjecture adds a positive structural restriction:

> **[CONJECTURE]** Natural source-minimal HT germs occur only as effective sections of (4), and
> their allowable conormal skeletons, stabilizer inertia, source-face specializations, and
> polarizations must satisfy cartesian descent together.

Thus an abstract annihilator, derived critical locus, or spectral model is not automatically
realizable by an HT source.  Realizability requires a compatible global source-frame stack.  This
is a Helmholtz-type integrability condition one categorical level above conormal integrability.

## 6. Triptic prediction and next theorem

For the irrational triptic class, the paper-level marker and stabilizer computation is now (3a).
The remaining tasks are:

1. package the actual theta boundary markers and their pushforwards as a typed cospan in Lean;
2. identify the remaining sign line with the oriented rank-three datum used by the gamma gerbe;
3. prove that orbit-residue reciprocity is the coarse shadow of cartesian descent for that gerbe.

The third item is the first genuinely new theorem target.  The stabilizer calculation alone is
parent algebra.  A successful theorem would connect the new cross-curve DA-complete residue
invariant to the independently constructed oriented triptic gerbe and explain why coarsening
preserves the obstruction while erasing its source-face origin.

The mandatory nontriptic test is the Barnes hierarchy.  If the construction only restates the
Felder--Henriques--Rossi--Zhu gerbe, it fails the field-building gate.

## 7. RH meaning

This is not an RH theorem and supplies no zero-free statement.  It changes where an RH application
must look.

A proof chain may possess an exact or even complete invariant inside its chosen representation and
still fail because it has forgotten horizontal source transport.  Therefore no fixed-fibre
spectral, positivity, continuation, or boundary criterion is enough.  A valid zeta application
must:

1. construct the source-frame realization stack from Euler--Gamma--theta data without inserting
   the critical zeros;
2. show that the existing proof chains are conservative realization functors of its horizontal
   defect;
3. prove that the polarized transport degeneracy spectrum is intrinsic and self-dual;
4. only then compare that spectrum with the critical zeros.

The conjectural statement that the critical zeros are a common self-dual degeneracy spectrum now
has a candidate carrier: the polarized horizontal transport of (4), not the unmarked conormal
support.

## 8. Novelty gate

### Parent mathematics

- Stabilizers of group actions and recovery of a subgroup from the stabilizer of a coset or atom
  are elementary parent algebra.
- Microlocal sheaf and ind-sheaf theory already replaces singular support by categories or stacks
  of objects carrying realization data; direct primary anchors are Kashiwara--Schapira
  (`https://arxiv.org/abs/math/0108065`) and Waschkies on the stack-level microlocal
  Riemann--Hilbert correspondence (`https://arxiv.org/abs/math/0209341`).
- Felder--Henriques--Rossi--Zhu already construct the elliptic gamma function as a meromorphic
  section of a Hermitian holomorphic abelian gerbe over the universal **oriented** triptic curve:
  `https://arxiv.org/abs/math/0601337`.
- Their `SL_3(Z)`-equivariant geometry is the strongest direct threat to novelty of any triptic
  frame, orientation, or gerbe language.

Therefore none of “support is insufficient”, “use a stack”, “retain stabilizers”, or “orient the
triptic curve” is new scientific knowledge.

### Candidate-new residue

The candidate-new claim is the HT-specific theorem that:

1. DA-relative conormal modules and the new cross-curve orbit-residue invariants assemble into
   (4)--(6);
2. the typed stabilizer cospan is the exact horizontal information forgotten by the complete
   common divisor;
3. the receivers in (7) are conservative images of one source-specialization defect;
4. this construction survives a nontriptic HT hierarchy and produces a new analytic consequence.

Targeted searches located the parent microlocal, group-action, difference-Galois, and triptic-gerbe
theories, but no theorem with these four properties.  This is preliminary absence evidence, not
priority certification.

## 9. Anti-theatre gate and falsifiers

The conjecture is false or scientifically empty if any of the following occurs:

1. (4) is merely the category of all realizations with no source-canonical construction.
2. The triptic comparison reduces to renaming the existing gamma gerbe.
3. The stabilizer cospan adds data by hand that cannot be produced from the source boundary.
4. Two source-inequivalent systems have equivalent objects (5) after all stated markings.
5. One obstruction receiver in (7) changes while the proposed horizontal defect does not.
6. No theorem transfers information between two independent receivers.
7. The nontriptic Barnes test has no natural realization stack.

The publication gate requires an unconditional analytic theorem on a natural HT class, not more
categorical vocabulary.

## Gates

- [x] unmarked full-faithfulness conjecture attacked and killed
- [x] exact positive stabilizer replacement isolated
- [x] algebraic reconstruction core Lean-formalized
- [x] standard triptic theta markers proved atomic from existing analytic parents
- [x] standard typed triptic cospan proved to reconstruct both source faces
- [x] strongest triptic gerbe parent identified
- [x] RH scope kept secondary and explicitly nonconclusive
- [ ] actual analytic triptic boundary cospan packaged in Lean
- [ ] general finite-inertia strata computed analytically
- [ ] orbit-residue/gerbe descent comparison proved
- [ ] nontriptic Barnes test passed
- [ ] two independent obstruction realizations proved conservative
- [ ] independent novelty audit and priority search completed

## Log

- 2026-07-17 -- killed unmarked conormal full faithfulness; proved the finite-marker
  zero/nonzero/atom trichotomy and typed two-face reconstruction in Lean; proposed the
  stabilizer-enriched horizontal realization stack as the maximal positive successor.
