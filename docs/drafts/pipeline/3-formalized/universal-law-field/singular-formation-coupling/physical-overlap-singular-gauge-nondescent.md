# Physical-overlap singular-gauge non-descent

- **ID:** `ULF-POSGND-001`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** `ULF-TCPSS-001`, `ULF-IFOCC-001`
- **Status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT RH SELECTION]`
- **Lean status:** not formalized; no Lean was written or built in this research pass

## Big-picture interpretation

Theta completion exists on each physical Pluecker packet, but not as a function on the physical
cells those packets share. Consecutive packets demand different half-density values on the same
prime-depth cell. The completion therefore lives on formation histories before their physical
identification, not on the collapsed observer space.

This changes the mechanism. The obstruction is not finite curvature: the depth path has no cycles,
and its transition law is an exact coboundary. The obstruction is that the unique trivializing
gauge is unbounded and does not descend through the overlap quotient. It is a properness-at-infinity
defect.

## Checked corpus shadows

- `[CORPUS]` `gammaSewnCriticalAdjacentPrime_PluckerPhysicalLabel_depth_overlap_zero/one` prove
  literal overlap of consecutive physical packets.
- `[CORPUS]` `gammaSewnCriticalPrimeDepthPacket_node_depth_overlap` proves the same overlap at the
  source-node level.
- `[CORPUS]` `gammaSewnCriticalPhysicalPlucker_depthGaugeCoefficient_eq` shows compatible local
  kernel coefficients must be constant across depth; `depthGaugeCoefficient_zero` then kills the
  nonnormalizable constant section in physical `ell2`.
- `[CORPUS]` `EulerPrimitiveJointDepthOffDiagonalCountertransport` proves ordinary finite diagonal
  similarity is a flat coboundary and determinant/cyclic-trace blind.
- `[CORPUS]` `routePPrimitiveJointDepth_no_complex_scalar_intertwiner` kills a universal scalar
  identification; its positive survivor is prime-log operator-valued transport.
- `[CORPUS]` `ULF-IFOCC-001` paper-proves that the unique local theta-completion half-density has
  unit formation residue and grows linearly.

These facts jointly suggest that the missing invariant cannot be finite curvature or a common
scalar. It must remember the topology of the formation cover and the growth class of its
trivialization.

## Formation cover

Fix `p<q`. Define the packet-label cover

```text
P_pq = {(e,i): e in N, i in {0,1,2,3}}
```

and the physical cell set

```text
X_pq = {p,q} x N.
```

The quotient map is

```text
lambda(e,0)=(p,e),    lambda(e,1)=(p,e+1),
lambda(e,2)=(q,e),    lambda(e,3)=(q,e+1).             (POSGND.1)
```

Let `s_e>0` be the unique block-scalar half-density from the physical Pluecker depth law to theta
first-exit law. A pointwise physical descent would be a function `g:X_pq->R_{>0}` such that

```text
g(lambda(e,i))=s_e for every e,i.                      (POSGND.2)
```

## Non-descent theorem

**Theorem POSGND-A.** No pointwise physical descent `(POSGND.2)` exists. This remains false even
if `g` is allowed to be unbounded and no continuity, summability, or operator-domain condition is
imposed.

**Proof.** The shared cell `(p,e+1)` has two packet presentations:

```text
lambda(e,1)=(p,e+1)=lambda(e+1,0).
```

Therefore `(POSGND.2)` would give `s_e=s_(e+1)` for every `e`; the sequence would be constant.
But `ULF-TPFOI-001` proves `s_e/e->c_pq>0`, so `s` is unbounded and in particular nonconstant.
Contradiction. QED.

Thus the edgewise trace-class sandwich `ULF-TCPSS-001` is a genuine operator on the packet direct
sum but cannot be pushed to a diagonal congruence on the shared physical cell Hilbert space.

## Positive survivor: canonical formation connection

Define the transition coefficient on the depth path by

```text
tau_e=s_(e+1)/s_e.                                     (POSGND.3)
```

**Theorem POSGND-B.** The transitions are positive, reconstruct the unique local gauges by

```text
s_n=s_0 product_(e<n) tau_e,                            (POSGND.4)
```

and satisfy

```text
tau_e=1+1/e+O(e^-2),
lim e log(tau_e)=1.                                    (POSGND.5)
```

For every finite interval the connection is an exact multiplicative coboundary, but its
trivializing section has linear escape:

```text
product_(e<n) tau_e=s_n/s_0 ~ (c_pq/s_0)n.             (POSGND.6)
```

**Proof.** Positivity and `(POSGND.4)` are immediate from telescoping. Equations `(POSGND.5-6)`
are `ULF-IFOCC-001`. QED.

The strongest positive statement is therefore not “descent fails.” It is:

> the packet cover carries a canonical algebraically flat connection whose only source-faithful
> trivialization has integral residue one and escapes every bounded physical descent class.

## Hostile review

**Wrong first:** covers, descent, cocycles, flat connections, and unbounded trivializations are
standard mathematics. Renaming this structure would not create a new field.

**Why ordinary holonomy misses it:** every finite depth interval is a tree, so the connection is
exact there. Determinants, cyclic traces, and finite holonomy tests necessarily see no obstruction,
matching the corpus's diagonal-similarity blindness. The invariant is the growth class of the
trivialization at the open end.

**Why this is stronger than the bounded-gauge no-go:** POSGND-A excludes every pointwise physical
gauge, including unbounded ones. The failure is caused by quotient identification, not operator
norm.

**Possible insignificance attack:** the proof is elementary once the local gauge is known. Its
significance comes from identifying exactly why the paper-proved singular sandwich cannot yet be
the global physical completion and from extracting the correct replacement carrier.

**Verdict:** the no-go and survivor are unconditional and structurally significant, but the
general descent language is a bridge. Scientific novelty of the source-specific unit-residue
non-descent remains unverified.

## Exact RH-chain consequence

The missing global object cannot be a diagonal operator on prime-depth cells. It must retain
formation histories and their transition connection until after completion. Only then may it be
projected to physical cells.

This gives a new exact order of operations:

```text
integer formation cover
  -> attach physical Pluecker packet kernels
  -> apply unit-residue theta completion connection on the cover
  -> subtract universal formation-order anomaly
  -> descend the residual relation to physical cells
  -> identify completed Xi boundary and prove residual zero.
```

Any route that identifies overlapping cells before completion necessarily destroys the only
nontrivial source datum and falls into the existing flat-coboundary/scalar-ghost no-gos.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.PhysicalOverlapSingularGaugeNondescent`, `GaloisForLFunctions.HTGeometry.IntegralFormationOrderCharge`, `GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Module `GaloisForLFunctions.HTGeometry.PhysicalOverlapSingularGaugeNondescent` (12 constants) on top of `GaloisForLFunctions.HTGeometry.IntegralFormationOrderCharge` (ULF-IFOCC-001) and `GaloisForLFunctions.HTGeometry.ThetaPluckerFormationOrderIndex` (ULF-TPFOI-001); all axiom-audit clean. `λ(e,i) = gammaSewnOrderedPrimeDepthPlucker_cell e p q i`, `s = formationHalfDensity p q`, `c_pq = formationOrderSlope p q`.

| Claim | Lean declaration |
|-|-|
| (POSGND.1) cover `ℕ × Fin 4 → {p,q} × ℕ`, overlaps `λ(e,1) = λ(e+1,0)`, `λ(e,3) = λ(e+1,2)` | `formationCover_overlap`, `formationCover_mem_physicalCells` |
| Theorem POSGND-A, (POSGND.2): no function `g` on physical cells (any growth) with `g(λ(e,i)) = s_e` | `not_exists_physical_descent` |
| (POSGND.3) `τ_e = s_{e+1}/s_e > 0` | `formationConnection`, `formationConnection_pos` |
| (POSGND.4) `s_n = s_0 ∏_{e<n} τ_e` (exact coboundary on every finite interval) | `formationHalfDensity_eq_mul_prod` |
| (POSGND.5) `τ_e = 1 + 1/e + O(e⁻²)`, `e log τ_e → 1` | `isBigO_formationConnection`, `tendsto_mul_log_formationConnection` |
| (POSGND.6) `(∏_{e<n} τ_e)/n → c_pq/s_0 > 0`; the trivialization is unbounded | `tendsto_prod_formationConnection_div`, `not_bddAbove_prod_formationConnection` |
| Theorem POSGND (summary) | `physical_overlap_singular_gauge_nondescent` |

The hostile review and RH-chain consequence are interpretation and audit.

## Log

- 2026-09-29 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
