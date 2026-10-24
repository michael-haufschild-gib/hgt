# Proof audit — 24 October 2026

Scope: canonical main.tex/body.tex. Historical variants have separate ledgers. This is an internal verification record, not an independent referee report.

## Admission rule

Every mathematical statement in the replacement is an exact specialization or direct composition of closed Lean declarations listed in claim-trace.md. The main physical capstones discharge all spectral and Diophantine inputs. Structural model restrictions are stated explicitly.

## New load-bearing mathematics

1. ConnectedGraphSpectralAffineEscape.lean proves real affine spectral escape on the actual named site-product local Hermitian submodule for every finite connected graph, with arbitrary site dimensions at least two. One/two-site cases use full matrix space. Larger graphs use a connected vertex deletion, existing all-site physical witnesses, and exact leaf transport.
2. Its hypergraph theorem uses the two-section inclusion in the support-contained local space.
3. ConnectedNetworkAllObserverRecurrenceLaw.lean constructs canonical coordinates of the entire submodule, joins generic maximality with generic all-observer extremality, and proves graph and hypergraph capstones.
4. The same module proves the exact normalized pure-state fidelity-return specialization, including proper support, the phase-sign bridge, and the constant-threshold conversion. This avoids reliance on an incidental broad import with an unrelated missing vendor IR artifact.
5. PhysicalTwoQubitGraphSeed.lean was refactored: a pre-existing one-million-heartbeat override was removed. Six separate Pauli identities now prove the same theorem under default limits. This is proof organization, not numerical experimentation or a trusted computation shortcut.

## Closed proof chain

- Physical seed → all-site connected/nonbipartite probe witnesses → Hermitian leaf constant-action rigidity → finite permutation avoidance → graph-local affine escape.
- Real escape → no local affine relation for every observer gap-ratio map → analytic extremality → finite labelled-graph intersection and countable chart cover.
- Observer displacement identity → positive forest/root comparison → continuous-clock exponent → exact graph law.
- Projector identity and finite-dimensional nuclear/Hilbert–Schmidt norm comparison → pure/mixed state corollaries.
- All collision moments → unique stationary law → point-spectrum scaling → connected compact pure-point hull → interval support and exact upper edge.
- C*-algebra Duhamel inequality → uniform finite-time observer stability.

No unproved premise was moved into a typeclass, stored witness, interface or imported axiom. Existing structures describing physical witnesses are inhabited by closed construction theorems used by the capstone.

## Direct source checks

All commands ran from formal/, in the foreground, one Lean process at a time:

    lake --old env lean GaloisForLFunctions/HTGeometry/ConnectedGraphSpectralAffineEscape.lean
    lake --old env lean GaloisForLFunctions/HTGeometry/ConnectedNetworkAllObserverRecurrenceLaw.lean
    lake --old env lean GaloisForLFunctions/HTGeometry/PhysicalTwoQubitGraphSeed.lean
    lake --old env lean GaloisForLFunctions/RHTower/UniversalStationaryRecurrenceLaw.lean

All four passed. The observer capstone emits one cosmetic simplifier suggestion. The seed emits cosmetic linter suggestions in its unchanged downstream finite-case proof; no elaboration error or timeout remains. These are not suppressed by added options.

One olean/ilean pair was created for ConnectedGraphSpectralAffineEscape, because the new observer capstone imports it. Existing oleans were not rebuilt. No capstone olean was created merely for the audit. Both new modules are wired into HTGeometry.lean; no umbrella was compiled.

## Transitive axiom audit

All 31 declaration roots in audit/declarations.txt passed the final source-based audit with Lean 4.32.2. Every reported transitive axiom set is exactly propext, Classical.choice, and Quot.sound. No custom axiom or sorryAx occurs. The complete output is preserved in audit/axioms.log; the command exited successfully.

The reproducible audit checks a temporary copy of the current observer capstone source, adds imports for the stationary and C*-algebra results, and executes #print axioms for each name in audit/declarations.txt. It does not treat a wrapper's explicit assumptions as discharged: final graph/hypergraph signatures and their actual applications were inspected separately.

The earlier reduced audit also checked the generic observer theorem, path capstone, nuclear-norm transfer, stationary scaling and occupation conservation; only standard logical axioms occurred.

A source scan of the two new modules and the changed seed found no sorry, admit, sorryAx, custom axiom, opaque, unsafe, native_decide or raised proof-limit setting.

## Quantifiers and boundaries

- Simple spectrum and arithmetic regularity are conclusions on a conull coefficient set.
- Every finite matrix observer and nonnegative weighting is chosen after H. Constants are not uniform in that choice.
- Time cutoff is fixed and strictly positive; this is not an exit-time theorem.
- Natural subtraction is truncated, covering capacity zero/one and pure support one/two.
- Graph connectedness is a physical model condition. Hypergraph support includes lower-body terms.
- No genericity in the full space is transferred without proof to a smaller constrained family.
- The stationary result is stated for arbitrary probability energy measures. Its operator-language interpretation does not replace the actual measure-level theorem.
- Stationary support is distributional, not an eventual pointwise ceiling.
- No chaos, nonintegrability, circuit complexity, Anderson localization, uniform onset or fixed-error thermodynamic lower bound is inferred.

## Artifact verification

The replacement main.pdf has nine A4 pages. Tectonic completed without warnings, missing references, overfull boxes or underfull boxes. Every final rendered page was inspected at readable resolution: equations, theorem statements, page breaks and references are legible, with no clipping or overlap. The inspected PDF was copied to the canonical manuscript directory. The final TeX log is preserved as audit/pdf-build.log; source and artifact hashes are recorded in audit/manifest.sha256.

Direct observer, seed and stationary source-check outputs are preserved in audit/source-connected-observer.log, audit/source-two-qubit-seed.log and audit/source-stationary.log. The graph escape source check and its required dependency artifact creation both completed without output or warnings. No numerical experiment was used.

Unrelated worktree changes were preserved, including other agents' additions to HTGeometry.lean. Existing historical PDFs, auxiliary files and output directories were not deleted.

## Completion revalidation

The original request was reread against the current worktree. All 24 recorded artifact/source fingerprints matched the delivered state before this recheck. The twelve numbered manuscript items (eleven mathematical results and one definition) are covered by the claim trace. Current graph/hypergraph capstone signatures and the arbitrary-probability stationary signature were inspected again; their spectral and arithmetic inputs remain discharged. The 31 axiom records, both umbrella imports, nine-page PDF, bibliography and scope ledgers remain consistent with those signatures.

Revalidation corrected two stale status sentences in the research card and made the observer module's exponent comment explicit as max(r - 1, 0) / 2. No Lean theorem or proof term changed. The final direct observer source check after that comment correction passed; its output is preserved in audit/source-connected-observer.log. The canonical TeX and inspected PDF were unchanged. Own temporary proof and rendering files remain absent. The preceding goal turn made progress by completing the manuscript, proofs, verification and cleanup; no pending mathematical or delivery gate remains.
