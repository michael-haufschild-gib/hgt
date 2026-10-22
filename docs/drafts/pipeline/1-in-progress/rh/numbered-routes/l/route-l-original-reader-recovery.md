# Route L: original-reader recovery from the complete source

- **ID:** RH-L-C56
- **Stage:** 1-in-progress
- **Type:** proof investigation
- **Target:** Construct the source-forced comparison with the prescribed physical reader at its unchanged horizontal anchor.
- **RH status:** UNPROVED

The chain is complete original source → fixed physical-reader agreement → conormal vanishing → RH. C55 proved that the actual complete tail has a component outside its pure leading source, and ruled out domination by that leading state. It did not construct an environmental map or a physical-reader comparison. This investigation tests those missing identifications directly; generic recovery structures with the desired intertwining as a field do not qualify.

## Current tests

1. Search the full Lean corpus for relative modular recovery and source-boundary comparison, inspecting both statements and proof-method assumptions.
2. Test recently published sewing/recovery mechanisms against the actual source and its retained anomaly, using the complete original domains and normalizations.
3. Attempt a source-derived comparison; if a proposed theorem assumes the comparison or drops the horizontal defect, record the precise failure and pivot before writing Lean wrappers.

## Search and source audit — 2026-09-12

All three deep searches finished. All 20 candidate statements, all 20 source-method entries and every proposed ingredient group in each result were inspected. These are partial retrievals, not exhaustive absence certificates. The inventory covers 57,064 indexed files, including 47,446 Lean files and 9,618 prose files; retrieved compiler records are predominantly source-only. No retrieved description is treated as a checked theorem.

| Result | Index generation | Unfinished retrieval | Applicability |
|---|---:|---|---|
| `route-l-relative-recovery-comparison-search.json` | 879777 | recovery/faithfulness queries and text/source retrieval | Kernel faithfulness preserves the retained residue coefficient; the relevant outer-uniqueness and Hasse results assume the missing boundary-modulus or local/global identification. |
| `route-l-sewing-locality-comparison-search.json` | 879799 | determinant/cocycle queries and text/source retrieval | Determinant twists, cocycle identities and existing range criteria do not construct a local modular functor for the original source or preserve its fixed normalization. |
| `route-l-boundary-variation-comparison-search.json` | 879837 | locality, parameter dependence, generator uniqueness, text/source retrieval | Projective jet calibration assumes the source/boundary factorization; bounded variation gives no physical comparison. The proposed total-variation/local-bounded-variation group does not establish the required maps. |

The last search's coverage snapshot is generation 879843 with 735,487 declarations. Its automated `model_suggests_sufficient_sources` assessment does not settle applicability: the first method, `rankOneCoefficientPairedBoundaryCurrent_projectiveJetCalibration`, explicitly requires `hfactor`. Several other results are definitions or instances, including the purported ABHN exactness and boundary-loop injectivity methods.

## Conjecture → test → failure → retained statement

### 1. Recover the prescribed reader by faithfulness or outer uniqueness

**Conjecture.** A faithful recovery or uniqueness theorem identifies the original source reader with the physical reader.

**Test.** Read the complete `BurnolStableResidueRegularOperatorClassification.lean`, the actual outer-uniqueness statement in `HTGeometry/SmirnovBoundaryInnerOuterFactor.lean`, and the local/global hypotheses in `DeningerCauchyHasse.lean`.

**Failure.** Regular expressions in translation and the Stein operator act on the stable residue line by their exact scalar gain. Killing that line requires zero gain; coefficient faithfulness requires nonzero gain. Outer uniqueness requires both outer numerators and almost-everywhere boundary-modulus equality. The Hasse comparison requires the assertion that local boundaries lift to a global boundary. None produces the missing identification.

**Positive survivor.** The existing regular-operator classification identifies exactly which operators retain the coefficient and which erase it. Its paper and Lean statements already exist; no duplicate wrapper was added. This rules out this transfer, not every possible recovery construction.

### 2. Use sewing universality to identify the original normalizations

A broad newest-first arXiv search for `sewing` led to Maibach–Peltola, [*Universality of the conformal anomaly*](https://arxiv.org/pdf/2608.23201), August 24, 2026. The PDF was read at Theorem 1.1, the locality criterion in Proposition 3.9, and the isomorphism/trivialization construction in Section 5. Equal central charge gives an isomorphism of **local Frölicher smooth real one-dimensional modular functors**. The proof changes trivializations; equality in the original chosen frames is an additional issue. Neither a Segal sewing structure nor its locality follows from commuting arithmetic edges.

**Conjecture tested.** Matching composition cocycles and normalization at the unit could force the original mate gain to be one.

**Actual-source countertest.** `DeningerOneSidedFramedMateCurvatureTransgression.lean` defines

\[
\chi_s(n)=\exp((2\Re s-1)\log n).
\]

For positive integers it is positive, multiplicative, and equals one at the unit. Consequently its multiplicative coboundary is one for every spectral parameter. Yet the exact physical mate curvature is `χ_s(n) − χ_s(n)⁻¹`, and `χ_s(n)` is the inverse-square half-density norm. The radial character survives matching those cocycles. This disproves the weakened transfer, not the paper's theorem.

`DeningerFailureNerveMixedDaggerCoboundary.lean` independently retains the exact modular ratio `‖λ‖⁻²`: the mixed defect is cobar-exact and Bianchi-closed for every parameter, while its physical vanishing still requires unit norm.

**Positive survivor.** The original positive character and its exact physical curvature remain available. Their substantive identities are already formalized. To use the cited theorem, construct the actual local modular functors and derive an isomorphism preserving the prescribed Gamma frame and horizontal anchor. Assuming that preservation would insert the comparison.

### 3. Force equality by a variation or terminal-value comparison

The same broad search found Friz–Song–Zhang–Zhang, [*Rough backward stochastic differential equations*](https://arxiv.org/html/2609.06606v2), September 10, 2026. Theorem 4.3 compares already constructed scalar solutions with controlled conditional norms, compatible rough driver and ordered terminal/drift data. Its proof, equation (4.2), retains both terminal and drift differences under an exponential integrating factor. Corollary 4.6 gives uniqueness for the same complete data. These hypotheses do not supply equality of terminal data.

**Actual-source test.** `DeningerOriginalPrimeGreenXiAdmission.lean` proves that the complete original-prime graph prefix converges at native depth, and that the completed boundary's physical image is the original Green–Xi coefficient times the fixed Sonin physical receiver. The original coefficient is retained and nonzero. Treating the physical terminal datum as zero discards the very comparison to be proved. No adapted source dynamics satisfying the paper's assumptions have been constructed here.

**Positive survivor.** Exact source admission and the coefficient-times-receiver formula remain unchanged. A comparison argument must evaluate the actual terminal and forcing differences; a common equation alone cannot remove them. No new Lean statement was claimed.

### 4. Test cancellation in the complete tensor, including both cross terms

**Conjecture.** The tail omitted by pure-leading domination might cancel the physical defect after Xi evaluation.

**Test.** Read the source definitions and exact tensor decomposition in `DeningerGammaSixFullSourcePrincipalClass.lean`, the admitted Fourier–Laplace product and conormal formulas in `DeningerGammaSixTensorRemainderXiJets.lean`, and the scalarization in `DeningerGammaSixFullSourceScalarization.lean`.

The actual remainder is `H⊗T + T⊗H + T⊗T`. Its internally promoted Fourier–Laplace value, on the proved convergence domain, is

\[
 h_m^2\bigl(M_m(w)M_m(z)-1\bigr)
 \Xi^{(k)}(w)\Xi^{(l)}(z).
\]

On the diagonal, its multiplier is `(M_m(w) − 1)(M_m(w) + 1)`. It tends to zero but is eventually nonzero. The existing divisor theorem retains the adjacent internal conormal pair `(0,c_m)` with `c_m ≠ 0`; restoring the forced half-density and successor scale gives a nonzero top-jet limit. Vanishing unpromoted Xi values therefore do not erase the retained conormal datum.

The bounded full-source scalarization does keep the complete correction and literal Wold compression. Its diagonal differs from the reciprocal Green diagonal by a summable sequence; the existing theorem explicitly rules out prime-pair cyclicity in each open Gibbs domain. It is not the required physical comparison.

**Positive survivor.** The complete tensor has an admitted exact two-variable formula and a nonzero normalized native jet. Those statements already exist in Lean. This turn inspected their proof bodies but did not independently rebuild them, modify them or claim their authorship.

## Remaining mathematical obligation and next attack

Full-source reader agreement is **not established**. The chain still stops at

\[
 \text{complete original source}\quad\not\Longrightarrow\quad
 \text{prescribed physical-reader agreement}.
\]

The endpoint is `RouteRDegreeSixBVGreenFixedReaderEquality`. Its source cyclic reader kills the literal degree-six boundary; its physical side is the reflected boundary and vanishes exactly on the critical line. Requiring agreement, unit gain, an anchor-preserving recovery map or zero terminal physical data would assume the missing assertion.

Next attack: evaluate the **difference of the two prescribed readers on the complete internally promoted source before quotienting**, retaining the native top Xi coefficient and the two tensor cross terms. Any asymptotic comparison must control that difference below the forced half-density/successor scale, rather than merely prove the unnormalized remainder tends to zero. The required estimate or exact source identity has not been derived.

## Validation and ledger status

- Three completed whole-corpus deep/method searches and direct source/paper applicability tests; no new comparison proof.
- No Lean code added or changed this turn; no build, heartbeat adjustment, numerical experiment or axiom-print audit performed.
- No route retired. The positive survivors cited above were already formalized; their conditional inputs and reader changes remain explicit.
- No new route-neutral STATUS entry: the current ledger already records the failures of assumed trivialization, defect-erasing comparison and unnormalized decay. Adding the same restrictions again would not advance the proof.
