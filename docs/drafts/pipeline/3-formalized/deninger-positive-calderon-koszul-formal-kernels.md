# Positive Calderón--Koszul formal kernels

- **ID:** `deninger-positive-calderon-koszul-formal-kernels`
- **Stage:** 3-formalized
- **Type:** LEAN 4 THEOREM BATCH
- **Labels:** `DAC_POSITIVE_GRAPH_CONORMAL_INTERSECTION_LEAN`,
  `DAC_SCALED_CHAIN_CONTRACTION_EXACTNESS_LEAN`
- **Lean module:**
  `GaloisForLFunctions.RHTower.Deninger.DeningerArithmeticPositiveCalderonKoszul`

## Formalized statements

1. `deningerPositiveCalderonGraph_inf_conormal_eq_bot`

   For a real inner-product space, a linear map \(A\) satisfying
   \[
   x\ne0\Longrightarrow
   0<\langle Ax,x\rangle
   \]
   has
   \[
   \operatorname{Graph}(A)
   \cap(L\times L^\perp)=\{0\}
   \]
   for every linear incidence subspace \(L\).  The Lean theorem is
   stronger than the paper intersection statement because it needs no
   finite-dimensional hypothesis.  It does not claim the
   finite-dimensional sum/transversality conclusion.

2. `deninger_exact_of_scaled_chainContraction`

   Over any field, if
   \[
   dh+hd=a\,\mathrm{id},\qquad a\ne0,
   \]
   then every \(d\)-cycle is a \(d\)-boundary.  This is the abstract
   algebraic kernel of the Euler contraction on each
   positive-total-degree Hodge--Koszul summand.

3. `deninger_exact_of_chainContraction`

   Unit-scaled specialization of statement 2.

## Verification

- Direct command:
  `lake env lean GaloisForLFunctions/RHTower/Deninger/DeningerArithmeticPositiveCalderonKoszul.lean`
- Result: passed.
- Axiom audit in `/tmp`: only Lean/mathlib standard
  `propext`, `Classical.choice`, and `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` declaration.
- Project lint reaches this module through the `RHTower` umbrella.
  The workspace-wide lint run then stopped on a concurrently added,
  unrelated unreachable `HTGeometry.CofinitePacketCriterion` module.
- No `lake build` was run; final module build is reserved for final
  audit.

## Exact boundary

The explicit polynomial/exterior Euler identity
\[
 dh+hd=(r+p)\operatorname{id}
\]
from `DAC_POSITIVE_HODGE_KOSZUL_CONTRACTION` is still a paper theorem.
This Lean batch formalizes its positivity intersection and abstract
contraction consequences, not the entire symmetric/exterior cdga.

## Log

- 2026-07-27 — Added and directly checked unconditional graph--conormal
  kernel and scaled chain-contraction exactness.
