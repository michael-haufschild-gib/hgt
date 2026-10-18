# Spectral and operator plumbing across the RH receivers

- **ID:** spectral-operator-plumbing-2026-10-18
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** User attachment `a23ff0b4-fd3b-4dea-91c8-25aa0a058181/pasted-text-1.txt`.
- **Statement:** Resolve requested cardinal spanning, radical quotients, general-grid attainment and even-polar ground operator, and explicit receiver-coordinate equivalences without new unproved premises.

## Full requested scope and completion evidence

1. **Task 5:** Cardinal packets span the CHMD bound-state sector in `(1/2,1)`; establish closed range. Inspect `CHMDCardinalGraphGeometry`, `CHMDBoundStateInertia`, and all newer spectral results. Completion requires an exact theorem relating actual packet coordinates to the actual resolvent spectral subspace, not merely negative energy or matching dimensions.
2. **Task 6:** Actual Hilbert quotient `SourceGraph ⧸ signedRadical`, descended CHMD/RW/EWU/OWU forms, and coercivity stated with quotient norm. Completion requires an exhaustive downstream inventory and verified descent/transport; raw mass cannot silently be called quotient mass.
3. **Task 7:** Collar optimizer attainment on arbitrary finite prime-power grids and actual finite-window even-polar de Branges ground operator. Completion requires concrete optimizer/operator constructions and all domain, normalization, pole and prime constraints.
4. **Task 8:** Explicit isometric equivalences SZ–RW–CHMD, PA–GTA–WL, SC Frobenius/Verschiebung–BVI `selbergMultiplesCoord`/`sieveLagMultiplier`, PCS–CTF. Audit named adjacent routes JAS, RN, APF, CDC, EGC, MSC, PTR, SEC. Logical equivalence of positivity criteria is not an isometry. Completion requires actual carriers, maps, inverse laws, norm/form identities and operator intertwining where requested.

## Working plan

- [x] Read attachment and repository instructions; inspect relevant memories and frontier.
- [x] Run corpus search and inspect its source-only/freshness limitations.
- [ ] Audit every requested construction and distinguish existing theorems from missing statements.
- [ ] Complete paper proofs of exact missing statements before Lean.
- [ ] Formalize, integrate leaf imports, run foreground leaf checks and external axiom audits.
- [ ] Run formal lint; record exact failures if unrelated concurrent work prevents global success.
- [ ] Requirement-by-requirement completion audit of all four tasks.

`update_plan` and `multi_tool_use.parallel` are unavailable in this session. This card tracks work; independent reads use `Promise.allSettled`. Serena's active language is Python; symbol operations reject Lean, so Lean source reads/edits use `rg` and standard file tools.

## Verified starting facts

- `CHMDCriticalBandReduction.lean`: `signedRadical` is closed, complete and infinite dimensional; `reducedSource` preserves signed pairings and primitive pairing. `source_mass_decomposition` explicitly retains discarded critical mass.
- `CHMDFullSpectralNullspace.lean`: radical is exactly the joint kernel of all actual Xi samples and both polar samples; `radical_polarCosine_zero`, `radical_polarSine_zero`.
- `CHMDContinuousOrbitProjection.lean`: actual finite-rank orbit projections and their signed splitting exist.
- `CHMDBoundStateDimension.lean`: total finite dimensionality currently takes `offLineZeros.Finite`; finite multiplicity above the essential threshold does not itself justify finite dimension over the whole open band. Newer `CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality.lean` must be inspected before adding spanning results.
- No `SourceGraph ⧸ signedRadical` declaration found by exhaustive source-text search.
- `OddSectorArithmeticGroundOperator` and `OddSectorFiniteGroundReduction` already exist; their even-polar analogue must retain both polar constraints rather than copying odd parity mechanically.

## Paper proof: actual radical quotient (BRIDGE)

Let `H=SourceGraph`, `K=signedRadical`, `B=sourcePair`. Since K is a closed subspace of the Hilbert graph, H/K has the standard quotient Hilbert norm and is linearly isometric to K-perp. The inverse representative is `r(p)=p-P_K p`. For every p,q, B(r(p),r(q))=B(p,q), because B annihilates K in both slots. Thus define the quotient form by B on those representatives. It is continuous, symmetric and bilinear. Its diagonal agrees exactly with source energy. If a quotient class pairs to zero with every class, its orthogonal representative pairs to zero with every graph vector, hence lies in both K and K-perp and is zero. The quotient norm is exactly the graph norm of r(p), not the original mass norm. Every continuous linear readout annihilating K descends; in particular both polar moments and all actual zero samples do. No positivity or RH assumption enters. This is standard Hilbert quotient theory applied to the actual arithmetic graph; no external mathematical novelty is claimed.

## External audit

- Suzuki, *On the Hilbert space derived from the Weil distribution*, <https://arxiv.org/abs/2301.00421>: its positive Hilbert-space identification assumes RH. An unconditional signed-form identity must not be promoted to positivity.
- Suzuki, *Weil's quadratic form via the screw function*, <https://arxiv.org/html/2606.09096v1>: finite-window semibounded operators are distinct from the global positive Weil completion; check exact domains and hypotheses.
- Burnol, *Two complete and minimal systems associated with the zeros of the Riemann zeta function*, <https://arxiv.org/abs/math/0203120>: completeness in specific Sonine/co-Poisson spaces does not automatically identify the CHMD resolvent eigenspace.
- Noor, *A Hardy space analysis of the Báez-Duarte criterion for the RH*, <https://arxiv.org/abs/1809.09577>: relevant parent for the requested PCS/CTF transport; carrier and shift must be matched explicitly.

## Validation and continuation

`CHMDSignedRadicalQuotient.lean` is added and wired exactly once. Direct foreground `lake env lean GaloisForLFunctions/RHTower/CHMDSignedRadicalQuotient.lean -o .lake/build/lib/lean/GaloisForLFunctions/RHTower/CHMDSignedRadicalQuotient.olean` exited 0 without diagnostics. It constructs the actual complete Hilbert quotient, isometry, continuous signed form, exact pullback, nondegeneracy and quotient-norm coercivity equivalence. Axiom audit and global lint remain pending. All four requested tasks remain open. Use one foreground Lean process at a time, `lake --old` for dependency checks, final direct `lake env lean <leaf>`, no full/umbrella builds, no numerical experiments, no heartbeat increases, no new axioms or unproved receiver premises. Preserve unrelated worktree edits.

## Full Weil polar correction: paper proof and exact boundary

Write g for the quotient ground class and o for the quotient odd polar class. Set C(x)=-B(g,x) and S(x)=B(o,x). Existing source identities give C(g)=S(o)=1/2, S(g)=C(o)=0. The full Weil form is W(x,y)=B(x,y)+2C(x)C(y)-2S(x)S(y), with exact pullback to `CHMDPolar.weilBilin`. Thus g is a nonzero quotient class with W(g,g)=0: quotienting only `signedRadical` cannot give strict coercivity of the full Weil form on the entire quotient.

The positive survivor is exact polar splitting. Define r(x)=x-2C(x)g-2S(x)o. Then C(r(x))=S(r(x))=0 and B(r(x),y)=W(x,y)=B(r(x),r(y)). Hence the Weil radical on the signed quotient is exactly the two-dimensional polar plane, and the restriction to the closed subspace C=S=0 is nondegenerate and equals the signed form. This follows by expanding the bilinear form and using its already-proved quotient nondegeneracy. No sign or spectral-gap premise is used. This is a BRIDGE from established polar identities, not a claim of external novelty.

The initial `/tmp/hgt_plumbing_weil.lean` check found a namespace qualification error, two mistaken `add_eq_zero` applications, and a heartbeat timeout from implicit inference in the continuity composition. Fixing the expression explicitly; no resource limits are being raised. This scratch is not yet a verified deliverable.

## Spectral coordinates and orbit projections: paper proof

An observable node is an actual Xi zero or one of the two polar nodes. Every such node lies in the closed half-strip. The existing continuous graph Fourier readout annihilates the signed radical at precisely the required nodes, so its composition with the quotient representative is a bounded linear readout with exact pullback. The full spectral nullspace theorem then says that equality of all these node readings is equivalent to equality in the quotient. No square-summability norm on the sample family is asserted.

For each positive-real-part Xi zero, the already-constructed continuous orbit projector kills the radical, hence descends to the quotient. Its idempotence, signed symmetry and energy splitting descend by surjectivity of the quotient map. Its range is closed because it is the fixed-point set of a continuous operator. This proves exact closed range for each actual cardinal orbit projector; it does not identify the whole resolvent bound-state subspace with a cardinal span.

## Scope decisions and further source findings

- User instructed “do all. decide yourself”. Proceed across all four tasks without further clarification. Target the entire closed `(1/2,1)` band through exact eigenspace spanning and closure; do not assume unconditional finiteness of the whole band.
- `CHMDExactParityBoundStateDimensionAndShiftedThetaOrthogonality` proves `offLineZeros_finite_iff_finiteDimensional_boundStateSpace` and exact parity dimensions. Its `reflectGraph_imVector` shows the original cardinal negative vectors are even; full-sector spanning requires the translated odd cardinal construction too.
- Asked for the actual factorial-grid collar attainment module/theorem in task 7. Source searches find no such base theorem. `FiniteGridTraceSharpness` already covers every finite grid, but that is a different functional from measurable physical collar allocations. `ProductCoupledCollarHierarchy` explicitly works without optimizer attainment. Do not substitute one problem for another.
- `CCMRestrictedWeilEvenSectorCrossZeros` already proves finite-window even-polar ground attainment, finite-dimensional ground subspace and existence of a transform with zeros on the two axes; a named concrete de Branges operator still needs precise identification.

## Projected cardinal completeness: dependency-closed paper proof (BRIDGE)

Take every real and imaginary actual cardinal source, translated by every admissible small shift. For a fixed eigenvalue `1/2 < μ < 1`, project their mass components orthogonally onto the resolvent eigenspace Eμ. This is an actual spectral projection of the packets, not an assertion that the original packets are eigenvectors.

If w in Eμ is orthogonal to every projected packet, it is orthogonal to every original packet. The universal Riesz/eigenvector pairing law makes `sourcePair (rieszLift w)` vanish against those packets. Actual translated-cardinal detection then makes every shifted cosine sample vanish, and phase separation makes every Fourier sample at an Xi zero vanish. Thus `rieszLift w` lies in the full spectral nullspace. Since μ differs from 1, self-adjointness makes w orthogonal to the ground state, so its Riesz lift has zero cosine polar moment. The exact full-nullspace energy formula is consequently `2 * polarSine^2 ≥ 0`. But the resolvent lower-bound energy estimate gives energy at most `-μ(2μ-1)‖w‖²`; hence w=0. The projected packets have trivial orthogonal complement. Eμ is finite dimensional by the unconditional above-threshold multiplicity theorem, so their algebraic span is all Eμ and is closed. The closed span of these projected packets over every μ in `(1/2,1)` therefore equals the closed span of all eigenvectors in that band. No global finiteness premise is added.

## Additional verified leaves

- `CHMDQuotientWeilForm.lean`: direct leaf audit exited 0, no diagnostics. Full Weil pullback, polar radical classification, polar restriction nondegeneracy, and obstruction to positive full-quotient coercivity.
- `CHMDQuotientSpectralCoordinates.lean`: direct leaf audit exited 0, no diagnostics. Actual zero-plus-pole readings separate quotient points; actual orbit projectors descend with idempotence, closed range and signed splitting.

## Log

- 2026-10-18 — Created full-scope card after source and literature audit; selected the actual quotient as the first dependency shared by the requested constructions.
