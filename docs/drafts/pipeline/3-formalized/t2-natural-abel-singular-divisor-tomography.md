# T2 natural-Abel singular-divisor tomography

- **ID:** T2-NASDT
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` route T2 open core
- **Statement:** The canonical critical Wold continuation minus the continued integer-log mesh agrees with the literal natural Abel germ on `Re s > 0`, and at every nonreal translated point `rho - 1` with `1/2 <= Re rho` it is complex differentiable exactly when `zeta(rho) != 0`; at a zero its punctured residue is the negative analytic multiplicity.

## Goal

Discharge T2's constructive singular-support premise. Exact RH chain:

`literal ordered-prime natural Abel germ`
→ `canonical principal-relative singular continuation`
→ `exact translated right-half zeta-divisor tomography`
→ `source exclusion of strict-interior poles`
→ `zeta zero-free for Re rho > 1/2`
→ `RH`.

This theorem does not assume zero locations or RH. It leaves one genuine producer: derive strict-interior regularity from literal source structure. It removes freedom to choose another singular carrier or residue normalization.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem names frozen, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

Define the carrier as

`critical Wold Laplace continuation - integer-log mesh continuation`.

Safe-germ agreement follows from the unconditional natural Abel summation-by-parts identity, the strict/critical Wold overlap, and mesh continuation identity. At a strict-right zeta zero, transfer the known Wold residue across the critical/strict overlap and subtract the holomorphic mesh. At a critical-line zero, use the critical Wold residue directly and again subtract the mesh. Away from a zero, prove differentiability: use the existing critical-wall regularity theorem on the wall; in the strict-right interior use holomorphy of `-zeta'/zeta`, the higher-valuation tail, and the later Euler shifts. Nonzero residue contradicts differentiability, giving the exact iff.

Internal corpus audit used `scripts/formal_tools.py research` for natural Abel continuation, Wold zero residues, critical-wall regularity, mesh continuation, and zeta log-derivative regularity. Corpus has the ingredients and one-sided residue statements, but no canonical natural-Abel singular carrier and no exact closed-right-half differentiability tomography. External primary-source search found standard prime/zeta meromorphic-continuation and zero-divisor literature, but no statement for this corpus-specific Wold natural-Abel-minus-mesh carrier. Novelty label: `[NEW]` for the route-specific carrier/tomography; ingredients are `[BRIDGE]`.

## Paper proof

**[PROVED HERE]** Put
`A(s) = Wcrit(s) - M(s)`, where `Wcrit` is the critical Wold continuation and `M` is the continued integer-log mesh. On `Re s > 0`, the critical and strict Wold continuations coincide, the strict continuation equals the ordered Wold current, and `M` equals the integer mesh current. Unconditional Abel summation by parts therefore gives `A = abelDirichlet woldNatDifferenceCoeff`.

Let `rho` be nonreal with `Re rho >= 1/2` and put `s0 = rho - 1`. The mesh is holomorphic at `s0`, so `(s-s0)M(s) -> 0`. If `zeta(rho)=0`, the critical-boundary residue theorem handles `Re rho=1/2`; for `Re rho>1/2`, openness of the strict overlap transfers the strict Wold residue theorem to `Wcrit`. In both cases `(s-s0)A(s) -> -m`, where `m>=1` is the analytic multiplicity.

If `zeta(rho) != 0`, regularity on the wall is already available. In the strict interior, `-zeta'/zeta` is holomorphic at `rho`; the doubled higher-valuation model is holomorphic because `Re(2 rho)>1`; all three later Wold shifts lie in the Euler half-plane. Hence `Wcrit`, the mesh, and therefore `A` are differentiable at `s0`. Conversely, differentiability of `A` would force `(s-s0)A(s)->0`, contradicting the nonzero zero-residue. This proves exact differentiability iff zeta nonvanishing. Failure of RH supplies a nonreal strict-right zeta zero, while RH gives strict-right nonvanishing, yielding the terminal equivalence.

Lean module: `GaloisForLFunctions.RHTower.XiHeatCassiniWoldNaturalAbelSingularDivisorTomography`.
Principal declarations:

- `woldNatSingularAbelContinuation_eq_naturalAbel`
- `woldNatSingularAbelContinuation_zero_residue`
- `differentiableAt_woldNatSingularAbelContinuation_iff`
- `riemannHypothesis_iff_woldNatSingularAbelContinuation_strictRight_regular`

Targeted build: 12,965 jobs, PASS. Axioms: only `propext`, `Classical.choice`, `Quot.sound`. Global lint remains red only for pre-existing unreachable modules; this module is umbrella-reachable and absent from lint errors.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** dependency-closed paper proof and Lean formalization complete; T2 constructive singular-carrier/divisor-classification premise discharged. Remaining producer is source-derived strict-interior regularity/no-off-line-support.

## Log

- 2026-08-30 — created directly in Stage 1 after internal corpus audit, external collision search, exact RH-chain audit, and frozen conjecture.
- 2026-08-30 — proved on paper and formalized in Lean; targeted module build and axiom audit passed.
