# Route E parity-column load circularity no-go

- **ID:** `ROUTE-E-PARITY-COLUMN-CIRCULARITY-001`
- **Stage:** 3-formalized
- **RH used:** no
- **Computation used:** no
- **Lean:** `RHTower/RouteEParityColumnLoadCircularityNoGo.lean`
- **Audit:** targeted `lake build` passed; axioms only `propext`, `Classical.choice`, `Quot.sound`

For any finite row-stochastic kernel supported on sign-reversing edges,

\[
2\sum_i s_i=\sum_j s_j(1-L_j),\qquad L_j=\sum_iP_{ij}.
\]

Hence \(\lvert\sum_i s_i\rvert\le\frac12\sum_j\lvert1-L_j\rvert\). For literal Möbius signs,
an all-strict-half total column-defect bound implies Littlewood's Mertens criterion and RH.

**Route consequence:** strict-half unit-load control is an RH receiver, not unsigned kernel
anti-concentration. Surviving Route E work must produce pre-scalar column-load gradient/cross-seam
cancellation; stochastic normalization cannot create it.

Corpus/literature search found no prior Möbius--Littlewood column-load formulation. Generic
doubly-stochastic kernel facts do not state this arithmetic circularity classification.
