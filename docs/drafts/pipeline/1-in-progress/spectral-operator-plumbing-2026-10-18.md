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
- `CHMDProjectedCardinalSpanning.lean`: scratch and final direct leaf checks exited 0 without diagnostics. Contains eigenspace spanning, finite packet selection and exact full-band closed spanning. Wired into the umbrella exactly once. Global finite dimensionality is deliberately not claimed.

## Even-polar operator: dependency-closed paper proof (BRIDGE)

Use the existing `CCMEvenSector.evenPolarSubmodule a` in the complete archimedean form domain, with both literal pole coordinates zero. It is closed, being the intersection of the closed polar kernel and the fixed-point subspace of continuous reflection. Its physical Hilbert carrier is the closure of its image under the actual aperture embedding J. Restrict and corestrict J to these spaces. This embedding is injective, dense and compact. Compress the actual bounded Weil remainder B by the physical inclusion and its adjoint; the compressed remainder is bounded self-adjoint and gives exactly the original restricted Weil form on every pair of even-polar form vectors.

Apply the existing explicit bounded-perturbation Friedrichs construction: with c equal to the compressed remainder norm plus one, the operator is the graph inverse of `J(1+J*BJ+cJ*J)^(-1)J*`, minus c. This is self-adjoint with compact resolvent. The existing even-polar variational ground satisfies the constrained shifted-form radical identity, hence belongs to this operator's actual domain and is an eigenvector at the existing `evenGroundEnergy a`. This proves an actual compressed eigen-equation; it does not assert an unforced eigen-equation for the unrestricted operator.

## Quotient parity and all-domain coercivity transport: paper proof (BRIDGE)

Graph reflection is an involutive linear isometry preserving the signed form. It preserves its radical and the radical's Hilbert orthogonal complement, hence induces an involutive linear isometry on the actual quotient, with the canonical representative commuting with reflection. The fixed and negative-fixed subspaces are closed Hilbert subspaces. The cosine moment is even and the sine moment odd, so the full Weil correction is respectively `+2C²` and `-2S²`; the two parity sectors are signed-orthogonal. For any source domain S, including finite-window, even-polar and odd source domains, a quotient-norm bound on its literal quotient image is equivalent to the original form bound with `norm (reducedSource p)`, by surjectivity onto that image. This universal image theorem covers domains not preserved by changing representatives; do not claim aperture support is radical-saturated.

## Physical collar attainment: proof mechanism under development

The existing `PhysicalCollarPartition n` is an infinite-dimensional measurable allocation space, including on a finite grid. Its coefficient is nevertheless amenable to weak compactness. Encode the finitely many shares in L2 on the bounded physical collar union. Nonnegative shares, support conditions and partition of unity define a nonempty closed convex bounded set. The integrated mass term is independent of allocation by exact signed transport. The remaining deficit is the integral of `sqrt(W(y)^2+B(rho,y)^2)-W(y)`, where B is a finite sum of Euclidean block norms of weighted transported shares. This is convex in rho and nonnegative. Its Lipschitz bound in the block variables, followed by the bounded physical weight and finite-measure Cauchy-Schwarz, gives norm continuity in L2 despite the origin singularity of W. Thus it is weakly lower semicontinuous and attains a minimum on the weakly compact feasible set. Measurable representatives can be repaired on a null set using the existing equal-multiplicity partition, recovering all pointwise structure fields.

The argument uses finiteness of the grid, a bounded collar union separated from the physical origin, and finite block incidence; it uses no factorial arithmetic. The concrete L2 encoding, closure/convexity, continuity estimate and representative repair remain to be formalized and must be discharged before claiming attainment.

Implementation refinement: `PhysicalCollarDualCertificate.integral_remainder` and its nonnegativity already give exact supporting affine upper bounds for the coefficient. The physical price vector has coordinates `archLevySinhWeight(x)*physicalPrice(rho,k,x)` and lies in the finite-product L2 carrier because each price is in [0,1] and the physical interval stays above the positive collar radius. Its inner product with an allocation equals the existing physical cost. Thus every coefficient superlevel is the feasible set intersected with all affine-price halfspaces; equality is recovered by choosing the partition itself as price source. This supplies closed convex superlevels directly and replaces the more cumbersome nonlinear continuity argument. The actual fibre constraints and a measurable null-set repair are being formalized; final attainment must instantiate the generic Hilbert direct method and then identify the existing `optimalCoefficient`.

## Finite BVI isometric coordinates: paper proof (BRIDGE)

For each N, take raw real coefficients on the actual active interval `[1,N]`. Map c to the Euclidean vector with q coordinate `sqrt(phi(q)) * selbergMultiplesCoord N c q`. The exact full-period bilinear formula identifies its Euclidean inner product with the literal mean of the product of the two divisor-sieve responses over the factorial period. The truncated multiples transform is injective. Its explicit inverse divides each Euclidean coordinate by `sqrt(phi(q))` and applies the existing `pmRamanujanResidueCoeff`; the already-proved finite Ramanujan inversion supplies both inverse laws. Thus the native mean-square form defines an actual Hilbert norm, and this coordinate map is a linear isometric equivalence, not just an equality of RH predicates.

The existing literal translation predictor transports under this isometry to the diagonal multiplier `sieveLagMultiplier q h`. It is a compression of true periodic translation, not a unitary translation in general. An SC Frobenius/Verschiebung identification must preserve this distinction and cannot be inferred just from similar divisor notation.

## Log

### PCS/CTF carrier obstruction and positive survivor (paper proof, BRIDGE)

For every integer p>1 the native PCS isometry V_p is not onto: every vector in its range has coordinate 1 equal to zero, whereas the basis vector e_1 has coordinate 1 equal to one. Its adjoint kills e_1 and therefore is not injective. The actual chronological half-line dilation is a unitary: conjugate translation by log(p) with the existing half-density exponential isometry; its inverse is translation by -log(p). Consequently no linear isometric equivalence of the full native carriers can intertwine V_p with that dilation, and no injective map can intertwine V_p* with the invertible dilation. This obstruction is independent of RH.

The positive survivor is the exact native physical/logarithmic/Mellin isometric chain, including the inverse dilation and the modulation multiplier. The PCS defect projection E_p=1-V_p V_p* already supplies the source-side complementary sector. The new bridge will certify the carrier obstruction and expose the actual physical isometry; it must not manufacture a PCS/CTF equivalence by discarding the defect sector.

- Native Selberg Hilbert-coordinate and quotient parity/coercivity scratch modules passed Lean. Integrated leaves awaiting final path audits.

### Identification of the cardinal band with the existing spectral sector

The open-band closed eigenvector span equals `boundStateSpace ⊓ primitiveSector`. Inclusion into the existing closed bound-state space is immediate; every eigenvector with eigenvalue below one is orthogonal to the ground. For the reverse inclusion project the existing bound-state space onto the primitive hyperplane. This projection kills the eigenspace at one, which the existing unconditional ground-rigidity theorem identifies with `span oneL`, and fixes every other bound-state eigenvector. Every nonzero primitive eigenvector has eigenvalue strictly below one. Continuity extends the projection statement to the closed span; it fixes every primitive vector. Combining this identity with projected-cardinal synthesis identifies the literal existing closed spectral sector, with no off-line-zero finiteness premise.

### Native Witt/Selberg finite receiver diagram (paper proof, BRIDGE)

Use the literal big-Witt ghost component ring homomorphisms over the reals. At cutoff N, finite Ramanujan inversion sends the actual first N ghost values to a unique native sieve coefficient vector. Its weighted Selberg isometry has coordinate `sqrt(phi(q))*ghost_q(w)`, so its norm is the actual sieve period mean and the weighted ghost square sum. The native Frobenius-two ring endomorphism satisfies `ghost_q(F_2 w)=ghost_(2q)(w)`; the receiving cutoff N therefore reads cutoff 2N of the original source, not an endomorphism of an insufficient N-cutoff. Literal Verschiebung is power-series expansion `f(T) -> f(T^m)`. The existing logarithmic-ghost expansion identity gives `ghost_q(V_m w)=m*ghost_(q/m)(w)` when m divides q, and zero otherwise. The same receiver construction transports these laws to exact Selberg-coordinate formulas. Compressed lag prediction multiplies each retained ghost by the existing `sieveLagMultiplier`. No claim identifies Frobenius, Verschiebung or prediction with unitary translation of the full SC source.

External audit: the operation laws are standard big-Witt theory; see [Hazewinkel, *Witt vectors. Part 1*, §13](https://arxiv.org/pdf/0804.3888). The contribution here is the explicit native Selberg receiver diagram, not a new Witt identity.

### Adjacent receiver audit

All eight requested adjacent routes were checked against their named source modules and the current frontier ledger. None supplies an unconditional missing positivity or orientation input merely through a change of coordinates.

| Route | Concrete receiver evidence | Boundary for this task |
| --- | --- | --- |
| JAS | `JointAncestryLevelOneCapstones.riemannHypothesis_iff_jasDressedPSD_one` and cosine/Euler variants | Exact sign criteria; no unconditional source PSD producer or Hilbert isometry follows. |
| RN | `PaperThetaUnregularizedExtensionObstruction.no_continuous_unregularized_native_realization`, `no_continuous_extension_of_nativeFiniteSynthesis` | Native unregularized completion is obstructed. An isometric completion cannot bypass the established topology obstruction. |
| APF | `PaperPrimeFredholmReconstruction.paperUnitTrace_grade_formula`, `paperXi_eq_zero_iff_unitTrace`, all-prime physical-span reconstruction | Literal reconstruction is available; transverse orientation remains a separate input. |
| CDC | `ConstitutiveDaggerConfluence.actualRepairProofErasureConsistent_iff_re_eq_half`, `admitsRadiallyCalibratedDaggerConfluence_iff_re_eq_half` | Calibrated confluence selects the wall. Existence of the selecting source potential is not supplied by coordinate transport. |
| EGC | `PaperEGCCompleteCorrection.tendstoUniformly_paperEGCCompleteCorrection`, `paperEGCCompleteCorrection_centered_re_neg` | Complete correction and its sign are retained; this is not a positive Hilbert receiver. |
| MSC | `SquarefreeDiscrepancyHilbertTransport.memLp_hilbertSourceFunction`, `inner_hilbertSource_evaluation`, `hilbertCountReadout_source`, `fixedArithmeticClockPair` | Actual source admission and count/clock readouts exist. Admission alone provides no missing zero-orientation inequality. |
| PTR | `PhotonicLosslessProductPortRH.ptrPairSlab_entry`, `riemannHypothesis_iff_XiC_limit_losslessProductPort` | Finite lossless slabs and an exact approximation criterion exist. The RH-direction construction uses zero data; a source-independent prime producer is still needed. |
| SEC | `XiPrimeSeamAdjacentEssentialNormNoGo.essentialNorm_primeSeamCoboundary_exact`, `tendsto_primeRay_adjacent_essentialNorm_zero` | Essential norm measures the seam exactly, but asymptotic smallness across large primes is nonselective. |

- 2026-10-18 — Created full-scope card after source and literature audit; selected the actual quotient as the first dependency shared by the requested constructions.

### Continued proof and validation progress

The even-polar operator now passes the combined scratch audit, including its actual domain/eigenstate theorem. Freezing the inherited Hilbert instances resolved the elaboration cost without a heartbeat increase. The original cardinal-band identification, PCS/CTF obstruction, Witt/Selberg diagram, real Hilbert direct method, and exact physical-partition/L2 correspondence also pass their scratch checks. Final-path audits are running sequentially; final success and axiom/lint checks still need recording.

The original logarithmic collar attainment proof is implemented. The only remaining errors in its latest scratch run were final theorem elaboration, subsequently corrected but not yet rechecked. The proof uses the actual bounded physical prices as L2 vectors. The exact dual remainder yields supporting affine upper bounds, exact at each partition. Hence negative-coefficient sublevels are intersections of closed convex halfspaces. The direct method gives a feasible minimizer; the explicit representative repair recovers an original pointwise measurable partition with the same coefficient. This is BRIDGE, not a new compactness theorem.

For arbitrary selected finite prime-power grids, retain a finite containing integer window and mask the physical densities by the selected indices. Use only the union of selected collars as the selected physical support. The objective is the actual masked finite-block kernel, not the full-window coefficient. Impose the additional closed convex constraint that unselected shares vanish on this union; an equal-multiplicity selected allocation there, joined with the original allocation outside, proves nonemptiness. The same dual slopes and exact affine collar substitutions give continuous affine supports for the masked objective. This proves attainment on the selected grid without inventing coverage of gaps or replacing its coefficient by the containing-window coefficient. This extension remains to be formalized.

### Quartic receiver boundary and positive survivor (paper proof, BRIDGE)

The native GTA local charge is Q(a,b)=100 b²(6a²+23b²). A linear map T with squared Hilbert norm Q is impossible: evaluation at (0,1) and (0,2) conflicts with quadratic versus quartic scaling. The exact positive survivor is the nonlinear degree-two feature (10√6 ab,10√23 b²), whose squared Euclidean norm is Q and whose zero set is exactly b=0. Finite charge sums are sums of these feature norms. This rules out only the charge-preserving linear Hilbert claim; it does not rule out unrelated carrier isometries or exact signed trace coordinate maps. Scratch formalization is written, validation pending.

The actual common smooth core also has an explicit SZ/RW/CHMD coordinate: inverse-Doob test lift followed by signed-radical quotient. Existing exact zeta-Weil and screw identities identify its full quotient Weil energy with both the RW closed form and Suzuki's screw form. Completion isometries in differing norms are not inferred from this core identity.
