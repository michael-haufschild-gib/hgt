# Route L: full-source fixed-reader agreement

- **ID:** RH-L-C53
- **Stage:** 1-in-progress
- **Type:** CANDIDATE — comparison remains unproved
- **Source:** rh-current-frontier-map.md, Route L; user request, 2026-09-12
- **Statement:** Derive the fixed physical reader's agreement with the normalized cyclic source reader on the complete original Green/BV boundary from the actual source equations.

## Exact objective

Proof chain: complete original source → fixed physical-reader agreement → conormal vanishing → RH. Preserve the original prime, native Tate depth, every multiplicity copy, Xi coefficient, Gamma normalization and horizontal anchor. No critical-line placement, reader agreement, source stationarity or isometry may be supplied as a hypothesis.

The checked degree-six comparison is `RouteRDegreeSixBVGreenFixedReaderEquality rho` in `RouteRDegreeSixGammaCoronaLocalGlobalFracture.lean`. The canonical reader is `(5/6) • d₁ + d₆`; it kills the literal Hochschild boundary. Its physical reflected readout is `routeRDeningerBVGreenReflectedBoundary rho`. Existing theorems identify equality with this readout's vanishing and hence with `rho.re = 1/2`. Those equivalences isolate the missing theorem; they do not prove it.

C51 admits the original source at fixed real damping `a > 1`. C52 proves the scalar damping continuation has pole order twice the actual zero multiplicity, and supplies its exact nonzero regularized coefficient. Neither result supplies reader agreement or a zero-damping source-domain limit.

## Conjecture / proof-or-failure log

### A. Actual-source Ward cancellation — insufficient for the retained reader

**Conjecture tested:** The unconditional cancellation of the theta-source quadratic ghost and cyclic boundary anomaly forces the physical boundary readout to vanish.

**Source inspection:** `FrankensteinXiGreenStokesQuadraticGhostNormalForm.lean` proves the literal identity `ghost + anomaly = 0`, preserving prime and multiplicity. But `XiResolvedStokesWardCharacter.lean` resolves the pair as `(ghost, -ghost)`: its codiagonal is zero while its relative character is `2 • ghost`. The pinned mean of that relative character is `-2*m*oppositeBoundaryCurvature(log(p)*centeredRate rho)`. The physical derivative-range admission of either component is equivalent to critical-line placement. Killing the pair's sum does not establish the fixed reader's annihilation of either retained component.

**Positive survivor:** The already-formalized resolved Ward double retains an exact relative character despite total cancellation. No new Lean wrapper is warranted. The next attempt must derive an actual comparison/transgression for the fixed reader, with its residual term included.

### B. Complete-source approximation — the finite readout already retains the defect

**Conjecture tested:** Apply cyclicity on finite source packets, then continuity to the complete original Green boundary.

Write `H(a,p,q) = deningerOriginalPrimeGreenXiField a p q`, `g(q)=2*Re(q.1)-1`, and `R(g)=deningerGammaSixFixedSoninPhysicalReceiver g`. C51 identifies the original-prime Tate differential at every native depth with the corresponding full graph prefix. Combining that identification with `deningerGammaSixCofinalGraphPhysicalTransport_finiteGraph` and `deningerGammaSixCofinalFiniteActualGammaTransport_averagingPacket` gives the same physical value `H(a,p,q) • R(g(q))` at every depth. The limit has this exact value by `deningerOriginalPrimeGreenXiGraphBoundary_physical`. The coefficient is nonzero by `deningerOriginalPrimeGreenXiField_apply_ne_zero`.

Thus the desired finite physical vanishing is already missing; continuity does not supply it. Source exactness is a statement about the source differential, not a proved chain-map identity for this fixed physical reader. **Positive survivor:** the existing coefficient-preserving continuous extension identifies the complete readout exactly; there is no unknown tail that this particular limit could cancel.

### C. Transport a categorical trace — matching the actual receiver is still missing

**Conjecture tested:** A source adjunction could transport the cyclic trace to the physical reader.

Erlikhman's September 2026 paper, found through the broad search `torsion`, constructs Hochschild trace transport from a functor with a colimit-preserving right adjoint. Its Proposition 4.16 verifies that property using perfect complexes and proper finite support. Those are proved properties of its geometric construction, not properties supplied for our Green/Sonin comparison. [Representation Varieties of Stacks and Trace Maps, §§2.1–2.2, 4.3](https://arxiv.org/html/2609.09633v1).

The direct analytic realization tested here would preserve the trace-class source subobject up to compact physical operators. `DeningerGammaSixTraceIdealSoninStrictLiftObstruction.lean` already proves its exact failure: the complete Wold coface is trace class, while the difference between its transported image and `R(g)` retains the whole essential norm of `R(g)`, including the reflected-curvature lower bound. Exactness within this class is equivalent to `g=0`.

**Positive survivor:** the essential-norm class is an invariant of every such comparison. This excludes the tested trace-ideal realization; it does not identify categorical compactness with analytic compactness or rule out every possible use of the paper.

### D. Actual Gibbs transport and continuation — the source forces a twist

**Conjecture tested:** The source-defined Gibbs reader could supply ordinary cyclicity, or its critical Abel limit could continue to the required original horizontal point.

In its exact convergence chamber `sigma > 1/2`, `deningerOrdinaryIntegerGibbsReader_physicalExchange` gives

`tau_sigma(S_n* T S_n) = n^(2*sigma-1) * tau_sigma(T P_n)`.

Here `S_n*` denotes the existing Wold backward map and `P_n` its range projection. On the literal Green boundary, `deningerOrdinaryIntegerGibbsReader_boundary` gives `1/n - n^(-2*sigma)`, and `deningerOrdinaryIntegerGibbsReader_eq_physicalBV` identifies this with the fixed physical evaluation. For `n>=2` it is nonzero in that chamber. Thus actual source-to-physical equality is available there, but it is a twisted exchange law, not the required cyclic annihilation.

The critical Abel path replaces `sigma` by `(1+epsilon)/2`. Its boundary value tends to zero but has the already-proved nonzero slope `log(n)/n`; the complete integral source multiplies that slope by its retained coefficient. This changes the regulator and does not prove equality at `sigma=Re(rho)`. Continuation of `f(delta)=(1/6)*(1-6^(-delta))` retains its nonconstant dependence. A zero at `delta=0` cannot establish its value at a different `delta`. In the spectral variable the physical expression depends on `Re(s)`, so the holomorphic identity theorem cannot be applied to its critical-line vanishing.

**Positive survivor:** the exact physical exchange factor and full-source first variation are already formal in `DeningerOrdinaryIntegerGibbsOperatorDomain.lean` and `DeningerGammaSixCriticalAbelReader.lean`.

### E. Strengthening to all native jets — too strong

The unrestricted statement that the actual full integral source is prime-pair cyclic on every retained native jet is not the same as the selected physical boundary comparison. `deningerGammaSixIntegralOperator_prime_cyclic_iff` classifies the former by vanishing of `iteratedDeriv k XiC w * iteratedDeriv l XiC z`. At multiplicity-top order the product is nonzero. The exact theorem `deningerGammaSixIntegral_top_jet_not_prime_cyclic` applies to every divisor with `Re(rho)>1/3` and every reader parameter `sigma>1/2`; this includes critical divisors if present. The domain restriction is retained, not silently extended to every divisor.

Lower jets do give zero columns and hence cyclicity; they erase the required leading coefficient. This cannot be promoted to a solution preserving multiplicity-top information. **Positive survivor:** the existing full integral-column classification distinguishes the zero lower jets from the nonzero top jet without a simplicity assumption.

### F. Symmetric companion with controlled error — no matching companion constructed

Shen's September 10 paper, also found through `torsion`, transfers reflection from an exactly symmetric companion to finite sums. Proposition 2.4 requires matching nonzero leading coefficients and uniform Gevrey remainder control for the whole companion. Proposition 2.5 then requires an error margin beyond the final observable's scale and the assembly norm cost. [The Chen–Yang volume conjecture for long integral fillings of fundamental shadow links, §2.6](https://arxiv.org/html/2609.11839v1).

**Conjecture tested:** Use the normalized cyclic reader as a symmetric companion and the physical readout as its approximation. On the admitted original-prime Tate sequence in B, the proposed discrepancy is the constant `H(a,p,q) • R(g(q))`; no decaying comparison error has been proved. For a nonzero receiver its norm cannot satisfy an error bound tending to zero. Thus the needed companion comparison is the unresolved theorem itself. The paper's transfer lemma does not supply that comparison. No numerical checks from the paper were used.

## Search audit

`route-l-full-source-reader-defect-search.json`: generation 879115; 57,036 inventoried files (47,426 Lean, 9,610 prose), partial text/source/decomposition coverage under the deadline, compiler coverage mostly pending. All 20 candidate statements, 20 method records and returned ingredient groups inspected. Actual Ward cancellation above was the substantive new lead. Other hits required domain/decay, self-duality, retained equivariance or the comparison itself. Definition records labeled as proof methods were not treated as proved producers. The proposed cyclic-symmetry ingredient group never establishes physical-reader agreement.

- `route-l-reader-transgression-search.json`: generation 879163, coverage status pending; partial text/source retrieval and reranking. All 20 candidates and 20 method records inspected. The source Möbius transgression supplies a covariant identity, not a zero defect; the Green observation splitting theorem retains a secondary boundary term. No ingredient group or proof idea returned.
- `route-l-source-gibbs-comparison-search.json`: generation 879167; complete inventory of 57,039 files, including 47,428 Lean files, but partial semantic retrieval and malformed/incomplete filter output. All 20 candidates and 20 method records inspected. C51's exact original-source Mellin identity was recovered; other useful records require decay, commutator vanishing or a different source domain. No reader-agreement producer returned.
- `route-l-gibbs-cyclicity-search.json`: `partial=false`, no reported execution errors; query generation 879175, coverage snapshot generation 879181, 57,041 inventoried/indexed files (47,430 Lean, 9,611 prose). The snapshot reports 707,244 ready methods and 1,011 stale ones; most compiler statuses remain pending. All 20 candidates, 20 method records and the proposed ingredient group inspected. This recovered the exact full-source cyclicity and native-jet classifications used in D–E. The proposed group confuses a cyclic GNS vector with a cyclic trace and leaves diagonal vanishing as an obligation; it does not prove the requested agreement. A completed search request is not a kernel audit of the whole corpus.

The broad newest-first arXiv search also returned astrophysical torsion models and representation-theoretic filtration results. They supplied no applicable source comparison. Only the two papers above were pursued to their relevant theorem statements and arguments. The arXiv search listing and abstract page differed by one day for Erlikhman's paper; its version page identifies September 9, 2026.

## Validation and remaining work

**Full-source fixed-reader agreement is not established.** C53 adds no Lean theorem, and no existing theorem was rebuilt merely to restate an obstruction. Existing source statements and proof bodies were inspected; their earlier build claims are not fresh C53 verification. C52 retains its separate successful named leaf-build record.

The still-needed operation is a source-derived identity for the fixed physical reader on the complete boundary that preserves the nonzero coefficient and original horizontal anchor. It cannot be supplied by total Ward cancellation, continuity of the already-identified finite readout, trace-ideal-preserving transport, or moving the Gibbs regulator to its neutral endpoint. Any new construction must exhibit the actual comparison map and account for its boundary term before cyclicity is invoked. Unrestricted cyclicity on all retained top jets is excluded by E and must not be substituted for this selected comparison.

No new route-independent fact was added to `universal-law-field/STATUS.md`: this pass tested already-formalized obstructions and two external mechanisms, without proving a new universal law. No axioms were printed, no elaboration limit was raised, and no Lean process was started for C53.

## Log

- 2026-09-12 — Direct comparison investigation opened after the user's request to establish full-source reader agreement. Candidate A checked against actual definitions and rejected as a proof of fixed-reader agreement; original objective remains open.
- 2026-09-12 — Attempts B–F audited directly against full-source definitions, native-jet domain restrictions, and fresh external theorem premises. All four corpus searches inspected, including returned method and ingredient records. No unconditional producer found or claimed.
