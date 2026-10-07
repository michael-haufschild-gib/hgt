# Ramified conductor invariant channel

- **ID:** RH-CRIC-20261006
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean); BRIDGE / correction to geometric admission
- **Source:** `xi-conductor-nearby-cycle-degeneration.md`; `ConductorNearbyCycleSpecialization.lean`
- **Statement:** For every commutative ring `A`, the invariants of the `k`-fold nodal shear split as the conductor line plus the annihilator of `k` in `A`.

## Exact test and verdict

The unrestricted claim that the conductor line exhausts ramified invariants over every
coefficient ring is **FALSE**. For `A = Z/2Z`, the square of the shear is the identity;
its invariants are `A^2`, whereas conductor specialization has image `A × {0}`.

The replacement classification is a **BRIDGE**, classical linear algebra. It is being
formalized to correct an actual admission gap, not presented as new scientific knowledge or
a new RH producer. No existing Lean theorem is false: the existing theorem concerns the
unramified universal shear, not geometric monodromy of the ramified Legendre pullback.

## Dependency-closed paper proof

Let `A` be any commutative ring, `T(a,b)=(a+b,b)`, and `s(a)=(a,0)`.
For each nonnegative integer `k` define `I_k=ker(T^k-id)` and
`A[k]={b in A : (k:A)*b=0}`.

1. Induction gives `T^k(a,b)=(a+(k:A)*b,b)`. At zero this is the identity;
   applying one more shear adds one further copy of `b`.
2. Subtracting `(a,b)` shows `(a,b) in I_k` iff `(k:A)*b=0`.
3. The maps `(a,b) -> (a,b)` and its inverse, with the second coordinate restricted
   to `A[k]`, give an explicit `A`-linear equivalence `I_k ≃ A × A[k]`.
4. Under this equivalence, `s` is inclusion of the first factor. Consequently
   `range(s)=I_k` iff multiplication by `k` has trivial kernel. This includes
   `k=0` and the zero ring without an omitted edge case.
5. Over any characteristic-zero integral domain, `k=m+1` has nonzero scalar,
   so step 4 gives equality for every `m`. Over `Z/kZ`, that scalar is zero and
   every vector is invariant. At `k=2`, `(0,1)` explicitly lies outside `range(s)`.

This proves the full additional invariant channel, not just one counterexample.
It also identifies the defect of commuting invariant formation with coefficient reduction:
the integral invariant line remains rank one for positive `k`, but its reduction does not
exhaust invariants when coefficient torsion is killed by `k`.

## Geometric normalization and scope

The Legendre family `y^2=x(x-1)(x-t)` has local monodromy `T^2` at `t=0`.
After an order-`m` source pullback its local action is conjugate to `T^(2m)`.
This follows from composing the local loop with a map of winding degree `m`.
The analytic-family identification is external classical geometry; the new Lean module will
certify the exact coefficient algebra and actual Xi multiplicity specialization only.

Primary source: Carlson, Müller-Stach, Peters, *Period Mappings and Period Domains*,
second edition, §1.1, pp. 20–21, [publisher preview](https://api.pageplace.de/preview/DT0400.9781108118989_A30888647/preview-9781108118989_A30888647.pdf).
The displayed monodromies are `[[1,2],[0,1]]` and `[[1,0],[-2,1]]`.

The complex coefficient invariant line is unchanged for every actual positive Xi
multiplicity. Thus this correction neither obstructs the existing complex terminal jet nor
supplies horizontal arithmetic equivariance. Reduced fibres and even their characteristic-zero
invariant lines still fail to locate zeros. Torsion records ramification, not horizontal position.

## Audit and plan

- [x] Source inspection and primary-source normalization checked.
- [x] Corpus research queried directly; candidate lemmas and source arguments inspected.
- [x] Complete paper classification; exact counterexample and positive survivor.
- [x] Lean generic classification, split equivalence, characteristic-zero and modular cases.
- [x] Actual Xi multiplicity coefficient specialization.
- [x] Targeted final audits, standard-foundation axiom checks, umbrella wiring.
- [ ] Global lint green: blocked by unrelated current-tree failures listed below.

Search snapshots: `/tmp/rh-conductor-search-20261006.json` and
`/tmp/rh-ramified-node-search-20261006.json`. Neither reports partial execution; semantic
coverage is not exhaustive and compiler records include pending/stale entries. Exact source
search found no ramified version of the existing conductor theorem. This is not a global
novelty certificate.

## No-go closure

- **Exact killing mechanism:** coefficient reduction can annihilate `k` and make `T^k` identity.
- **Strongest positive survivor:** full linear splitting `I_k ≃ A × A[k]`, with an exact
  coefficient criterion for conductor exhaustion.
- **New insight for this route:** retain the Legendre factor two and source multiplicity before
  changing coefficients; invariant-line equality over `C` cannot justify the same claim modulo primes.
- **Status:** paper proof and exact Lean replacement closed. General conductor route remains open.

## Formal result and verification

`HTGeometry/RamifiedNodeConductor.lean` contains the exact shear-power theorem,
`ramifiedNodeInvariantEquiv`, the conductor exhaustion equivalence, characteristic-zero
domain theorem, modular classification, and strict modulo-two counterexample.
`RHTower/XiThetaRamifiedConductor.lean` instantiates the split at twice the actual Xi
multiplicity, proves conductor exhaustion over characteristic-zero domains, and retains the
nonzero terminal Xi coefficient under the corrected shear.

Both `lake --old build +GaloisForLFunctions.HTGeometry.RamifiedNodeConductor` and
`lake --old build +GaloisForLFunctions.RHTower.XiThetaRamifiedConductor` exited zero.
Only the requested leaves were newly built; the latter command replayed existing dependency
warnings. No full or umbrella build was run.

Final, sequential commands all exited zero:

```
lake env lean GaloisForLFunctions/HTGeometry/RamifiedNodeConductor.lean
lake env lean GaloisForLFunctions/RHTower/XiThetaRamifiedConductor.lean
lake env lean /tmp/rh-ramified-conductor-axioms.lean
```

Both source-audit logs are empty: no errors or warnings. All 17 new declarations were audited;
their axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound` (or subsets).
Both modules occur once in their area umbrellas. No new premise, axiom, computation,
heartbeat override, commit, or push.

`scripts/formal_tools.py index` completed after the final source edit. Global
`scripts/formal_tools.py lint --check-generated` exits one in the concurrently edited tree:
five tracked umbrella omissions (`ApertureConeCalculus`, `ApertureConeWinding`,
`ApertureLogTranslation`, `ApertureOpenHistoryIdeal`, `BoundaryCoronaCStarAlgebra`), an additional
unwired `ImStripAlmostPeriodicZeroDensity` with three `sorry` findings, and generated-index
drift. None of those files was changed by this cycle. No clean global gate is claimed.
Evidence: `/tmp/rh-ramified-{generic,xi,axioms}-final-20261006.log` and
`/tmp/rh-ramified-lint-final-20261006.log`.

## Research assessment

No new scientific knowledge beyond classical monodromy and linear algebra is claimed.
This fixes a concrete admission gap, not the RH-bearing producer. No difficult step was
deferred because of effort: the remaining actual-source problem is construction of horizontal
transport compatible with local geometric classes. The next cycle must specify its base and
path groupoid and attack that source construction, rather than add further local coefficient
models. The full RH goal remains active.
