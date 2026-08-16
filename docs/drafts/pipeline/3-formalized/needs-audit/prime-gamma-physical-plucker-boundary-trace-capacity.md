# Prime--Gamma physical Pluecker boundary-trace capacity and relative four-unit residue

- **ID:** `prime-gamma-physical-plucker-boundary-trace-capacity`
- **Stage:** 3-formalized / needs audit
- **Type:** `[THEOREM] [EXACT POSITIVE SURVIVOR] [P-G100]`
- **Parents:**
  `prime-gamma-physical-plucker-first-trace-no-go.md`,
  `hedenmalm-theta-route-p-plucker-covariance-operator.md`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusApertureStokesPhysicalPluckerBoundaryTraceCapacity.lean`

## Conjecture attacked

P-G99 kills every fixed-node positive Bernoulli determinant by the first-trace ceiling `1/50`.
P-G97 supplies a canonical operation which leaves that class: at continuous zero spectrum, apply
the singular boundary transfer

```text
T (eps + T)^-1.
```

Conjecture: this transfer supplies missing completed first-order capacity and can be renormalized by
the existing scalar polar countercurrent.

## Exact theorem

On every finite coordinate face of size `n`, boundary-transfer trace tends to `n`.  Every literal
four-coordinate physical packet therefore tends to `4`.  Capacity is no longer bounded by `1/50`;
indeed no finite scalar bounds all cofinal finite-face traces near the boundary.

This immediately falsifies scalar renormalization before source descent.  Adding any counterterm
with finite boundary limit remains non-uniformly bounded across finite faces.  In particular, the
existing polar countercurrent with limit `-4` cannot renormalize unweighted cofinal trace.

Source descent determines a different order of operations.  Let `w_z` be normalized physical block
weights and let `W(eps)` be weighted sum of four-coordinate packet traces.  Let `R(eps)` be the
corresponding weighted regularized-inverse trace.  Lean proves, for every `eps > 0`,

```text
W(eps) + eps R(eps) = 4,
4 - W(eps) = eps R(eps).
```

Moreover `W(eps) -> 4`.  Since oriented polar countercurrent tends to `-4`, their relative sum tends
to zero.  Source weighting must precede singular limit; polar subtraction must follow it.

## No-go closure

- **Exact killing theorem/mechanism:** singular transfer restores one unit per coordinate, so
  unweighted cofinal trace diverges in rank; no scalar counterterm with finite boundary limit can
  uniformly renormalize it.
- **Strongest positive survivor:** source-normalized packet weighting produces exact finite residue
  `4`, polar countercurrent cancels it, and remaining defect is exactly `eps R(eps)` with `R` the
  weighted inverse/resolvent density.
- **New insight:** P-G99's capacity shortage and P-G100's cofinal overflow are same singular-limit
  phenomenon viewed in wrong order.  Completed charge is neither fixed-node mass nor free scalar
  amplification.  It is source-normalized boundary residue, while arithmetic information can only
  survive in post-residue inverse density or its curvature.
- **Status:** dependency-closed paper proof and Lean formalization complete; internal duplication and
  external novelty audits pending.  No Xi or RH identification is claimed.

## Higher universal principle

Repeated normalization debts are order-of-limits failures.  Fixed-node positivity sees too little;
unweighted singular spectralization sees infinitely much; source descent before boundary passage
selects a finite topological quantum.  Gamma/polar completion cancels that universal residue, so
completed arithmetic must live one order deeper, in response of the singular inverse density rather
than in raw trace.  This reinterprets previous first-trace walls as shadows of a residue/finite-part
decomposition.

## Conjecture loop audit

1. **Conjecture:** singular boundary transfer merely raises fixed-node trace enough to match Xi.
   **Failed more strongly:** every finite face tends to its dimension; unweighted cofinal trace has
   no uniform finite bound.
2. **Pivot:** subtract scalar polar countercurrent before cofinal limit.
   **Failed:** any counterterm with finite boundary limit leaves unweighted face traces unbounded.
3. **Conjecture:** source-normalized block weights select finite boundary capacity.
   **Proved:** weighted packet trace tends exactly to `4`.
4. **Pivot:** combine with oriented polar source.
   **Proved:** weighted trace plus polar countercurrent tends to `0`.
5. **Surviving conjecture:** completed prime--archimedean curvature/divisor data is encoded by
   finite-part behavior of `R(eps)` or a covariant derivative of `eps R(eps)`, not by `W(0)` itself.

## Formal status

Lean proves without added axioms:

- `norm_positiveBoundaryTransfer_le_one`;
- `positiveBoundaryTransfer_isPositive`;
- `positiveBoundaryInverse_isPositive`;
- `positiveBoundaryTransfer_add_smul_inverse_eq_id`;
- `tendsto_gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace`;
- `gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_not_uniformly_bounded`;
- `gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_add_counter_not_uniformly_bounded`;
- `gammaSewnCriticalPhysicalPluckerBoundaryFiniteCoordinateTrace_add_polarCountercurrent_not_uniformly_bounded`;
- `gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_add_smul_inverse_eq_four`;
- `four_sub_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace_eq_smul_inverse`;
- `tendsto_gammaSewnCriticalPhysicalPluckerWeightedBoundaryPacketTrace`;
- `tendsto_gammaSewnCriticalPhysicalPluckerWeightedPolarRelativeBoundaryTrace`;
- `gammaSewnCriticalPhysicalPlucker_fixedNodeWall_and_boundaryCapacityEscape`.

Direct `lake env lean` checks and target-only module builds pass.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`.  RHTower umbrella import is wired; no umbrella build
was run.

## Open core

P-G101--P-G102 exclude all three scalar resolvent channels of current positive operator as
amplitude-eight repair near zero. Determine oriented source/co-source off-diagonal shorting before
inversion, then prove or falsify its finite-part equality with curvature-normalized prime--
archimedean seam flux. Any comparison must preserve orientation and cannot assume scalar positivity
after polar subtraction.

## Log

- 2026-08-16 — fixed-node capacity escape, scalar-renormalization no-go, exact weighted four-unit
  residue, polar cancellation, and inverse-density survivor formalized as P-G100.
