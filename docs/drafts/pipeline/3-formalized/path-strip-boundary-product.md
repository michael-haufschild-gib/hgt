# Exact strip-boundary product in actual covering monodromy

- **ID:** PATH-STRIP-BOUNDARY-PRODUCT-20261009
- **Stage:** 3-formalized
- **Type:** BRIDGE; external novelty unverified; corpus only
- **Parent:** `../1-in-progress/polynomial-rectangle-meridian-product.md`

## Exact result and complete paper proof

In any topological space, choose bottom vertices b_i, top vertices t_i, horizontal paths h_i:b_i→b_{i+1} and k_i:t_i→t_{i+1}, and vertical paths v_i:b_i→t_i. Construct the row prefixes, positive cell boundary h_i v_{i+1} k_i⁻¹ v_i⁻¹, its conjugate C_i based at b_0, and the outer boundary W_m of the first m cells.

Traversing C_i followed by W_i cancels the reverse bottom prefix against its forward copy and then the two opposite traversals of v_i. The result is W_{i+1}. W_0 contracts by inverse-path cancellation. The installed fundamental-group multiplication reverses traversal order, so induction gives [W_m]=[C_0]⋯[C_{m−1}]. Applying native covering monodromy gives the same ascending permutation product. No plane presentation, branch behavior, finiteness or commutativity is assumed.

## Corpus audit

The parent records the documented lexical searches. The proof uses the inspected path-groupoid associativity and inverse cancellation laws and the actual `FundamentalGroup.mul_def`. `FundamentalGroup.fromPath` preserves the precise endomorphism-group type through rewriting. No external sources or numerical enumeration were used.

## Formal certificate — 2026-10-09

`formal/GaloisForLFunctions/HTGeometry/PathStripBoundaryProduct.lean` contains ten explicit public declarations. Production leaf build, all ten public axiom reports and final actual-source `lake env lean` check pass; final log is empty. Included in the seven-module, forty-declaration audit `/tmp/hgt-rectangle-geometry-axioms.log`. Final log: `/tmp/hgt-PathStripBoundaryProduct-final.log`. Wired into the HTGeometry umbrella; completed implementation scratch removed. Index/lint refresh follows.

The actual polynomial strip paths, local meridian identification and exterior comparison remain to be instantiated. This is the exact product mechanism required for that construction, not a completed polynomial realization or RH result.

Index refresh passed (`/tmp/hgt-rectangle-geometry-index.log`). Authoritative global lint reports only the unrelated unreachable module `HTGeometry.BandKernelOperators`; no error concerns these seven modules (`/tmp/hgt-rectangle-geometry-lint.log`).
