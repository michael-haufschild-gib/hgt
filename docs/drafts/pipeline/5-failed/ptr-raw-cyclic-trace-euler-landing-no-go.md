# PTR raw cyclic-trace Euler landing no-go

- **ID:** ptr-raw-cyclic-trace-euler-landing-no-go
- **Stage:** 5-failed
- **Type:** FALSIFIED; positive survivor THEOREM (Lean)
- **Source:** Literal temporal-Maxwell prime two-cycles in `PhotonicTemporalMaxwellSlabRealization.lean`; [PTR frontier](../1-in-progress/rh-current-frontier-map.md#candidate-ptr) (read only).
- **Chain tested:** physical prime cells → order-insensitive scalar Euler source → prime conormal/RH landing.

## No-go closure

- **Exact killing theorem:** For any three distinct primes `p,q,r`, the raw cyclic trace of the literal physical word `TₚT_qTᵣ` differs from that of `TₚTᵣT_q`. Thus cyclic trace does not descend to commutative prime occupation, despite hiding order in every two-cell trace. The source algebra's earlier no-abelianization theorem did not by itself exclude this nonmultiplicative trace readout.
- **Strongest positive survivor:** With `Nₚ=Tₚ−1` and `Lₚ=log p`, the source-defined cubic orientation is
  `tr(NₚN_qNᵣ) = (1728/125)·(L_q−Lₚ)(Lᵣ−L_q)(Lₚ−Lᵣ)/(LₚL_qLᵣ)`.
  It is nonzero for distinct primes and changes sign under reversing two cells. The physical three-word trace difference is twice this current.
- **New insight:** Trace does not remove the source's noncommutative orientation; its first visible obstruction is cubic, not pairwise. An order-insensitive landing must explicitly symmetrize or use a different source/port, and then separately justify retention of the arithmetic coefficient.
- **Status:** Paper identity and unconditional Lean theorem in [`PhotonicPrimeTripleCyclicTraceNoGo.lean`](../../../../formal/GaloisForLFunctions/RHTower/PhotonicPrimeTripleCyclicTraceNoGo.lean). Direct `lake env lean` and targeted `lake build --old GaloisForLFunctions.RHTower.PhotonicPrimeTripleCyclicTraceNoGo` pass; umbrella import wired without umbrella build. No claim about a symmetrized/nonlinear/nonlocal readout or the separate rotating-cylinder PTR source. No RH proof or full PTR kill.

## Method

The literal source has `Tₚ=1+Nₚ` and rank-one `Nₚ`. Direct matrix multiplication yields the cubic Vandermonde. The two-cell terms cancel in the difference of reversed three-word traces by cyclicity; the surviving cubic terms are opposites.
