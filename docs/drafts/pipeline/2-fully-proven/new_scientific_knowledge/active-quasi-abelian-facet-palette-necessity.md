# Every full HT facet lattice is faithful on its active quasi-Abelian quotient

- **ID:** `active-quasi-abelian-facet-palette-necessity`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / NECESSARY ACTION-RELATIVE SOURCE GEOMETRY
- **Scientific status:** `[PROVED HERE] [FORMALIZED ALGEBRAIC CORE] [NOVELTY UNVERIFIED]`
- **Statement:** In every finite full Stanley--Reisner HT differential-matroid realization, the
  complete integral lattice of each facet embeds in the period quotient after its maximal compact
  complex subtorus is removed.

## Setup

Let `F` be a scalar meromorphic realization of the exact full localized Stanley--Reisner
differential matroid of a finite essential complex `Delta`.  For a facet `A`, the established facet
separator produces

```text
G_A=q_A(T)F
```

such that:

1. the complete orbit `{T^n G_A:n in Z^A}` is differentially algebraically independent;
2. the full period quotient `X_A` is noncompact and quasi-Abelian;
3. the complement incidence is exact;
4. `Z^A -> X_A` is injective;
5. `X_A` satisfies the generalized Riemann relations.

Let `B_A` be the maximal compact connected complex subgroup of `X_A`.  It is an Abelian variety.
Define the active quotient

```text
Act(X_A)=X_A/B_A.
```

## Active facet theorem `[PROVED HERE]`

The composite

```text
Z^A -> X_A -> Act(X_A)                                   (1)
```

is injective.

### Proof

Assume that a nonzero `n in Z^A` lies in the kernel of (1).  Because `Z^A` is torsion-free, the
map

```text
Z -> Z^A,   k |-> k n                                    (2)
```

is injective.  Restricting the complete facet orbit along (2) preserves differential algebraic
independence.  Hence

```text
{T^(kn)G_A:k in Z}                                       (3)
```

has infinite differential transcendence degree.

But the translation class of `n` lies in the compact Abelian kernel `B_A`.  The proper
compact-kernel theorem applies to the quotient `X_A -> Act(X_A)`: every meromorphic observable uses
only finitely many coefficient functions in the relative Abelian function field, and compact
kernel translation introduces no new coefficients.  Therefore the complete cyclic orbit (3) has
finite differential transcendence degree.  Contradiction.  Thus (1) is injective. `QED`

## Dimension consequence `[PROVED HERE]`

Let `aqaDim(Delta)` be the least ambient dimension of a quasi-Abelian facet palette satisfying the
existing exact incidence, generalized Riemann, and lattice conditions together with active
faithfulness (1).  Every full HT realization supplies such a palette in its own dimension.  Hence

```text
aqaDim(Delta)<=htDim(Delta).                              (4)
```

Together with the previous hierarchy,

```text
peDim<=qaDim<=aqaDim<=htDim<=ppDim<=ffsDim.               (5)
```

The remaining equality `htDim=aqaDim` is a sufficiency problem: prove all-order fixed-factor jet
interpolation on torusless quasi-Abelian quotients.

## Scientific meaning

Ambient noncompactness and faithfulness in the full period quotient are not the correct necessary
conditions.  A structural action can be faithful while moving only in a compact complex shadow,
where every single observable has finite orbit capacity.  The theorem identifies the first
action-relative law constraining hypertranscendental functions:

> A completely free structural orbit must be faithful at infinity, after all compact complex
> directions have been quotiented out.

This converts the elliptic-shadow no-go into a universal positive restriction on every facet of a
finite full HT constraint geometry.

## Lean boundary

The analytic proper-fibration theorem is paper mathematics.  Its exact use in the lattice argument
is formalized in
`formal/GaloisForLFunctions/HTGeometry/FiniteShadowCapacity.lean`:

```text
activeQuotient_injective_of_fullOrbitFree_of_kernelCyclic_not
```

The theorem assumes the compact-kernel cyclic family is not differentially independent and proves
injectivity of the active quotient map from complete orbit freedom and torsion-free cyclic
embedding.  The finite-shadow source of the analytic hypothesis is formalized by the exact matrix
rank theorems in the same module.  No compact-kernel analytic statement is installed as an axiom.

## Parent and novelty boundary

Parent inputs are the generalized Riemann period theorem of Capocasa--Catanese, proper direct-image
and relative function-field finiteness for Abelian fibrations, finite transcendence degree of
Abelian function fields, and the established project facet-separation theorem.  Searches did not
locate the action-relative conclusion (1), inequality (4), or an equivalent differential-orbit
capacity theorem.  Novelty remains unverified pending specialist audit.

## Gates

- [x] exact facet orbit extracted
- [x] proper compact-kernel finite-capacity theorem proved
- [x] compact collision converted to a cyclic differential-rank contradiction
- [x] active quotient lattice injection proved
- [x] dimension inequality `aqaDim<=htDim` proved
- [x] algebraic implication formalized in Lean
- [ ] independent complex-geometric proof audit
- [ ] exact-formulation literature audit
- [ ] promote to Stage 3 only after the relative analytic theorem has a direct Lean formalization

