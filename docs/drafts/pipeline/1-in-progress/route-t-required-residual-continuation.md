# Route-T required residual continuation

- **ID:** `route-t-required-residual-continuation`
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) / THEOREM (Lean)
- **Source:** Route-T relative orbit leakage + prime-gap mesh continuation + Wold lower-Hardy
  renormalization
- **Statement:** After subtracting the canonical continued logarithmic mesh and static holonomy
  from the meromorphic Wold current, one obtains a source-defined continuation of the actual
  lower-Hardy residual. At every zeta zero right of the critical line this continuation retains
  the exact nonzero residue `-m`; hence neither mesh nor holonomy can carry the required
  compensating principal part.

## Heavy conjecture loop

### C0 — all regular Route-T terms cancel the Wold pole

Conjecture that logarithmic mesh, holonomy, and lower-Hardy residual all continue regularly to
`s = rho - 1`; then the safe identity would continue across the wall and contradict the Wold
residue.

**Failed.** Holonomy is entire and critical prime-gap energy makes the mesh regular, but the
lower-Hardy series is only analytic for `Re s > 0`. Its square-root-log coefficient decay gives
all boundary derivatives but does not overcome `p^{-s}` growth for `Re s < 0`. Regularity of the
residual continuation is exactly the missing RH-strength assertion.

### C1 — theta-Green boundedness supplies residual regularity

Conjecture that the Wold/theta-Green vertical-line bound identifies the lower-Hardy residual with
a compact-source analytic Green function across the Laplace wall.

**Failed.** Corpus proves boundedness and asymptotic carrier equality in vertical time, but no
coefficient-faithful equality with the Laplace residual on a complex neighbourhood. Treating the
two as equal would insert the missing source-to-physical specialization.

### C2 — define the forced continuation before asking for regularity

Define, under critical prime-gap energy,

```text
R_req(s) = W_cont(s) - M_cont(s) - H(s),
```

where `W_cont` is the four-shift valuation-one continuation, `M_cont` is the canonical mesh
continuation, and `H` is the static holonomy counterterm.

**Proved.** On `Re s > 0`, `W_cont` equals the Wold current and `M_cont` equals the original mesh
current. The exact renormalization identity therefore gives

```text
R_req(s) = lowerHardy(-i s).
```

If `zeta(rho)=0` and `Re rho>1/2`, the Wold term has residue `-m(rho)` at `s0=rho-1` with
`m(rho)>=1`. Mesh continuation and holonomy are continuous at `s0`, hence each has zero residue.
Subtracting their punctured-neighbourhood limits leaves residue `-m(rho)` in `R_req`.

### C3 — glue a reflected upper Hardy carrier by edge of the wedge

Conjecture that source reflection supplies an upper-half-plane mate with the same real-boundary
values as the bounded lower-Hardy residual. Edge-of-the-wedge would then continue the physical
residual through the Laplace wall.

**Failed.** The reflected theta packet is formally the negative of the original packet, not an
independent upper-Hardy germ. The residual coefficient bound is exponential in
`-sqrt(log p)`: it gives every polynomial boundary jet but only Gevrey-2-scale control, not a
quasianalytic boundary class. Thus smooth boundary agreement cannot manufacture the missing
continuation. The forced pole is naturally a Stokes jump of a square-root-frequency lift; killing
it requires a new source law, not ordinary reflection or finite jets.

### C4 — transport the simple Wold pole to a fixed Route-U contact

Conjecture that the multiplicity-exact first-order Wold pole forces one fixed finite
shifted-Hankel contact, thereby excluding Route-U's cofinal degree drift.

**Failed.** The Route-U reciprocal moments coalesce under large mass shift and scalarize away the
divisor label carried by the Wold residue. The corpus has no coefficient-faithful map from the
labeled Wold principal part to a fixed Hankel null face. Building that map as an assumption would
insert the missing producer. The surviving typed coupling is instead the formal quotient-orbit
head: it retains the same exact multiplicity and proves every off-line completion needs a nonzero
compensator.

## Theorem

Assume the already-isolated critical prime-gap energy is summable. Define

```text
requiredResidual(s)
  = xiHeatCassiniWoldLaplaceContinuation(s)
  - xiHeatCassiniLogMeshLaplaceContinuation(s)
  - xiHeatCassiniWoldLaplaceHolonomyCounterterm(s).
```

Then:

1. for every `Re s>0`, `requiredResidual(s)` is exactly
   `xiHeatCassiniWoldResidualLowerHardyKernel(-i*s)`;
2. for every zeta zero `rho` with `Re rho>1/2`, there is its exact multiplicity `m>=1` such that
   `(s-(rho-1))*requiredResidual(s) -> -m` on the punctured neighbourhood;
3. consequently the required residual continuation is not continuous at `rho-1` and cannot be
   replaced by any continuation having zero residue there.
4. under critical prime-gap energy, RH is equivalent to continuity of this one forced residual
   continuation at every possible right-half zeta pole.

## Proof

For (1), rewrite Wold continuation by its safe-side equality, mesh continuation by its
critical-energy continuation equality, and use the existing prime-zeta/mesh/holonomy normal form
of the lower-Hardy kernel.

For (2), take the multiplicity-exact Wold residue theorem. The mesh zero-residue theorem applies
because nontrivial zeta zeros satisfy `Re rho<1`, so `rho-1` lies in the open mesh continuation
half-strip and is nonzero. The holonomy counterterm is entire, hence also has zero residue.
The limit of the product with `requiredResidual` is therefore `-m-0-0=-m`.

For (3), continuity at the pole would make the product with the vanishing local coordinate tend
to zero, contradicting uniqueness of limits because `m>=1`.

For (4), use the corpus criterion `RH iff zeta has no zero with Re>1/2`. Under RH the regularity
condition is vacuous. Conversely, any such zero forces noncontinuity by (2)--(3), contradicting
the proposed regularity.

## New knowledge

Route T no longer has three undifferentiated possible compensators. Subject only to its explicit
prime-gap input, mesh and holonomy are proved incapable of compensation. The entire off-line
principal part is forced into one canonical, source-derived continuation of the physical
lower-Hardy residual. Thus the remaining producer is exact and coefficient-faithful:

```text
prove requiredResidual has zero principal part on the physical half-strip.
```

This statement simultaneously meets the formal quotient-orbit leakage law: off line, the
anti-reflected physical head requires nonzero compensating orbit charge, and analytically the
only surviving carrier of that charge is `requiredResidual`. Lean couples the two statements with
one existential multiplicity `m`, rather than merely proving separate nonvanishing results.

## RH status

Not an RH proof. Critical prime-gap energy remains an explicit input, and no unconditional theorem
yet kills the forced residual pole. The result removes mesh and holonomy from the open producer
and makes residual regularity the sole Route-T analytic gate.

## Formalization

Formalized in
`formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldRequiredResidualContinuation.lean`.
The preceding `XiHeatCassiniWoldRelativeOrbitLeakage` module owns the continuation and residue;
this module adds forced discontinuity, the conditional RH equivalence, and the analytic/formal
same-m compensator theorem without duplicating those declarations. Direct foreground elaboration
with `lake env lean` passes. The module is wired into the RHTower umbrella. Targeted module build
passes. Axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`. Global formal
lint reaches the module but fails on unrelated shared-tree umbrella reachability debt in existing
Deninger, Gauss-Hodge, Suzuki, and `CriticalSchurIdealInertiaTransport` modules.
