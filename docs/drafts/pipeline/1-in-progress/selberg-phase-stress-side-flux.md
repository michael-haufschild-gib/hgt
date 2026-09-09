# Complete original phase stress and vertical-side flux

- **Stage:** 1-in-progress
- **Parent:** [Selberg conjecturing loop](selberg-quarter-conjecturing-loop.md), cycle53.
- **Objective:** Evaluate the actual aggregate phase stress and vertical-side dilation flux, then connect that physical record to the original cusp Fourier/Bessel data needed by the full quarter comparison.

## Evidence and conjecture

The preceding goal turn made concrete progress:26 checked declarations proved the original mixed-loss bound and integrated core–cusp/Rellich consequence. PhaseRellich and MixedLoss source hashes were revalidated unchanged. The full Selberg endpoint remains active and unproved.

A broad explicit-OR corpus query for phase stress, Gram polarization, translation stress, Noether, and boundary Ward retrieved293 declarations across26 modules. Inspected the actual QNMNoetherFlux finite-interval FTC/endpoint-current/conservation proofs, the original character projector's exact eigenspace and block-commutation proofs, and the complete phase observation norm/derivative identities. Counts describe discovery metadata, not whole-corpus proof reads. Artifacts use `/tmp/selberg_stress55_`.

First conjecture: polarizing the complete phase observation norm identity recovers the original real mixed Gram loss `Re(inner v w)-Re(inner Tv Tw)`. All three aggregate stress components should therefore be exactly stress(F)-stress(TF), retaining both physical derivatives and the original potential. Actual upper-block motion acts by the exact input character on Tv; consequently the full aggregate stress should be unit-periodic. The physical dilation x-coordinates differ by one across the vertical sides, so the complete sidePhaseFlux should equal the integral of the actual horizontal phase stress. No side sign, omitted mixed term, or spectral coercivity is assumed.

## Proof loop

- [x] Recover the complete mixed phase Gram form and exact input-character transformation.
- [x] Identify all three actual aggregate source stress components.
- [x] Prove their unit-translation law and the full physical side-jump formula.
- [x] Integrate the side formula with every original phase/coordinate contribution retained.
- [x] Audit complete scratch/source/targeted-final/axiom/index/wiring/lint results with one foreground Lean worker at a time.

Then compare the resulting side/top boundary record with the original cusp Fourier and Bessel energy. The complete quarter inequality remains a conclusion to prove.

## Complete positive proof

The full scratch and exact source checks passed cleanly. `phaseAverage_pair` recovers `Re(inner v w)-Re(inner Tv Tw)` from the literal phase observations, including the mixed derivative terms. `inversionTransfer_upper_motion` proves the exact input-character law; every complete Gram loss is invariant under the actual upper-block action. All three physical phase stresses therefore retain their original unit-translation symmetry.

The dilation side jump is exactly horizontal phase stress. Source regularity and complete finite-sum/integral interchange prove

`sidePhaseFlux(Y) = integral_(arcFloor..Y) phaseStressXX(1/2,y)`

and

`topPhaseFlux(Y) = integral_(-1/2..1/2) [x*phaseStressXY(x,Y)+Y*phaseStressYY(x,Y)]`.

The phase Rellich identity and full original core–cusp bound now use this explicit physical boundary record. Every original phase and deck coordinate, mixed derivative, spectral mass, angular energy, and side/top term is retained. Source [SelbergMaassPhaseStress](../../../../formal/GaloisForLFunctions/RHTower/SelbergMaassPhaseStress.lean) has312 lines and28 public declarations; all final targeted audits passed.

A further explicit-OR query for mixed Parseval, weighted Fourier, boundary Gram, bilinear Parseval, and spectral current retrieved113 declarations in49 modules (`/tmp/selberg_stress55_fourier.json`). Inspected the literal slice pairing, its derivative product rule, and its real-integral representation in `SelbergMaassBoundaryFlux.lean` (namespace `SelbergMaassFlux`). These provide source-based boundary pairings for the next Fourier/Bessel comparison; they do not by themselves remove the top's horizontal weight or any off-diagonal mode contribution.

## Final audit

Complete scratch and exact source `lake env lean` checks passed cleanly. The final single-module `lake build GaloisForLFunctions.RHTower.SelbergMaassPhaseStress` rebuilt only this module (10s). All28 public declarations passed post-build `#print axioms`, with only standard `propext`, `Classical.choice`, and `Quot.sound`. Source SHA256 is unchanged. Exact-module research results and generated API rows cover all28 declarations, and the umbrella import occurs exactly once. Index refresh and repository formal lint passed. Earlier concurrent HTGeometry wiring errors are historical; this latest lint snapshot is green. Artifacts: `/tmp/selberg_stress55_manifest.json`, `/tmp/selberg_stress55_audit.json`, and matching scratch/source/build/axiom/index/coverage/lint logs.

Every task-owned Lean/check/build handle is terminal. This turn used strictly serial foreground Lean commands; no full or umbrella build, numerical experiment, added axiom, commit, or push. The full Selberg endpoint remains active and unproved.

## Next arithmetic estimate

A focused explicit-OR gramKernel/unipotent/Kloosterman corpus query found98 declarations in5 SelbergMaass modules (`/tmp/selberg_stress55_arithmetic.json`). Re-read the actual fibreWeight_at_word, fibreWeight_convolution, transferGram_convolution, exact kernel magnitude, and support proofs. These retain the middle-residue annihilator multiplicities, including composite-level nonunits, and the actual complex character phases.

Cycle54 proved the full complex kernel identity with the correct first-slot conjugation. The actual original mode ODEs then produced a stronger positive result: the cross-frequency boundary Wronskian is a squared-frequency difference times an actual positive cusp-tail Gram kernel. Genuine original cusp integrability proves the upper endpoint is zero. A complex two-mode test yields a quantitative current bound by the two tail-loss masses. [Complete proof and audit](selberg-kernel-wronskian.md).

Next derive the exact horizontal Fourier weight in the physical top stress and combine it with the current/tail relation. Retain the full complex kernel, signed frequencies, and all same-residue interference; positivity of the underlying tail kernel does not supply the still-unproved full weighted boundary/core comparison.
