# Route L: an actual correction with the complete source retained

- **ID:** RH-L-C59
- **Stage:** 1-in-progress
- **Target:** Full-source fixed physical-reader agreement.
- **RH status:** UNPROVED

Chain: complete original source → fixed-reader agreement → conormal vanishing → RH.
C58 tested quotient annihilation against retained source residues without closing the comparison. C59 tests the actual Gamma correction and a resolvent-based singular construction, preserving the original anchor and the coupled native-depth remainder.

## 1. Actual complete Gamma correction

**Conjecture tested:** retaining and adjusting the complete Gamma tensor remainder supplies the missing scalar cyclicity.

`DeningerGammaSixFullSourcePrincipalClass.lean` defines the full rectangular operator from `EllTwo` to the depth-indexed tensor Hilbert space. Its coordinate is the actual tensor square, not its leading approximation. Subtracting the principal operator gives exactly the complete remainder operator, which is trace class. The tensor remainder includes both leading–tail cross terms and the tail square.

`DeningerGammaSixFullSourceScalarization.lean` then derives the actual bounded scalarization `Q+R`, with reciprocal diagonal `Q` and summable diagonal `R`, including the finite omitted head. Its existing theorem excludes prime-pair cyclicity for every open Gibbs parameter. Thus choosing another summable scalar correction cannot establish that stronger property. This does not exclude the requested selected-boundary comparison at its singular endpoint.

**Positive survivor:** complete source decomposition, admission, bounded scalarization and exact logarithmic coface are already formalized. No duplicate wrapper was added. The full tensor Fourier–Laplace remainder retains `(M_m(w) M_m(z)-1)` and both Xi-jet factors; its scalarization is not a proof of fixed physical-reader agreement.

## 2. Dressed resolvent construction

Broad newest-first arXiv `renormalization` found Erman–Turgut, [Renormalization of One-Dimensional Semirelativistic Bosons with Contact Interactions](https://arxiv.org/html/2609.09068), September 8, 2026. Sections 5.1 and 8 construct a resolvent using a physically fixed subtraction energy and contact maps after a free resolvent. The counterterm is independent of spectral energy, allowing cancellation in the two-energy difference. Appendix B.4 controls the finite interaction by a sector-dependent constant and the principal part from below by a logarithm. These imply invertibility at sufficiently negative energy. An exact pseudo-resolvent identity and strong identity recovery then reconstruct the operator. Sectorwise self-adjointness does not require a common lower spectral bound across particle numbers.

**Conjecture tested:** the same construction converts the complete Gamma source into a self-adjoint model while preserving its original physical reading.

The inspected Gamma operator is rectangular. An auxiliary Schur-complement construction therefore needs its own source-derived contact map, subtraction and operator identities. Its trace-class remainder alone does not give those data. The existing `DeningerSkewAdjointResolventExists.lean` requires dense domain, skew-adjointness and closedness; it does not prove them for this source. `DeningerArithmeticWeilArakelovResolvent.lean` constructs a source quotient inverse only away from the Xi divisor. Neither closes the missing source comparison.

The search also returned `physical_defect_laplace` in `ThetaCuspHawkingBMPhysicalVolterraEquation.lean`. Direct inspection shows that its defect contains the twice-integrated actual forcing term. Its zero transform establishes the forced Volterra relation, not a zero physical boundary for Route L. Similarly, the Suzuki dressed-wall identity retains its scalar Krein defect and source weight.

**Result:** no dressed-resolvent transfer established. The paper remains a method candidate; its contact model has not been identified with the complete Gamma source. The source-selected two-energy identity and fixed-reader compatibility remain mathematical obligations, not premises available for a theorem.

## 3. Explicit subtraction test before a full-source lift

The hybrid search found the existing exact scalar six-tail continuation in `DeningerGammaSixResidueLanding.lean`:

```text
F(s) = A(s) + Xi(s) P6(s).
```

**Candidate correction:** subtract `A(s)` from the continued product. The resulting product is exactly `Xi(s) P6(s)`, so its value vanishes at every Xi zero. At a zero in the critical strip the removed contribution `A(rho)` is nonzero, by the source file's explicit factor theorem. A finite correction to the multiplier instead contributes `Xi(rho) E = 0` and cannot remove it.

This is a concrete cancellation of a scalar value, not preservation of the original physical reader or of its native multiplicity jet. The full difference retains

```text
[F(s)-A(s)] - [F(t)-A(t)]
  = F(s)-F(t) - [A(s)-A(t)].
```

In a direct scalar transfer using `s` as spectral energy, the last term must be evaluated; it cannot be discarded by invoking the paper's energy-independent subtraction. No correspondence between that scalar parameter and a source-derived physical resolvent has been proved. Nor has this scalar correction been lifted to the full depth-indexed tensor source. These are limits of this proposed transfer, not an exclusion of other resolvent constructions.

A separate corpus hit, `CCMBlockFockCommonCarrierSquareObstruction.lean`, also prevents treating two separately constructed block–Fock interfaces as one positive Gram without checking their cross entries: its literal two-node matrix is not positive semidefinite, and the exact necessary diagonal correction is already classified. This specific matrix is not the paper's contact space or the full Gamma tensor, so no general auxiliary-space no-go is inferred.

## Search evidence and verification

| Artifact | Mode / result | Coverage |
| --- | --- | --- |
| `route-l-complete-source-correction-search.json` | Deep, partial; all 20 candidates, 20 source arguments and the proposed ingredient group inspected | Index 880067; snapshot 880076, current 880077; 57072 files, 47450 Lean files, 735542 declarations |
| `route-l-dressed-resolvent-source-search.json` | Deep, partial; no candidates or arguments, local runtime deadline expired | Index and snapshot 880077; same file/declaration counts |
| `route-l-resolvent-counterterm-search.json` | Broadened hybrid search, `partial=false`, no reported errors; all 20 candidate statements and 20 source arguments inspected | Index 880086; snapshot 880077, current 880086; same counts |

All used `--any`, a 120-second budget and `--no-refresh`. Empty partial output triggered a broader query and mode change, not an absence claim. Source-only metadata and model method descriptions were not treated as kernel verification. The completed hybrid request does not certify exhaustive semantic coverage of the corpus.

No new Lean theorem or code change. No builds, numerical experiments, heartbeat changes, axiom-printing audits, commits or agent delegation. All three search processes completed. No new route-independent STATUS fact: these attempts have not established a new universal constraint beyond the current ledger.

## Remaining target

Full-source reader agreement remains unproved, with no new mathematical closure in C59. The tested correction changes the Gamma contribution; the singular operator construction has no source-to-reader identification yet.

Next attack: derive the complete Gamma source's two-parameter divided difference with its counterterm variation and coupled native-depth remainder retained. Test whether that exact expression admits the required physical resolvent factorization. Preserve every original prime, multiplicity copy, Xi coefficient, Gamma normalization and horizontal anchor; no self-adjointness or reader equality may be assumed.
